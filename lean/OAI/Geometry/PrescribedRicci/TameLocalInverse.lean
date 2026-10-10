import Mathlib
import OAI.Geometry.PrescribedRicci.SobolevCommutatorBound
import OAI.Geometry.PrescribedRicci.SobolevFamilyBounds
import OAI.Geometry.PrescribedRicci.SobolevInterpolation

namespace OAI

/-! Tame Local Inverse. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Classical ComplexOrder MatrixOrder
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

lemma perturbation_commutator_bound (k : ℕ) (hk : Module.finrank ℝ E + 1 < k)
    (ws : List E) (hws : ws.length ≤ k) (v : ι → E) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : SmoothCoefficients ι E),
      (∀ i j, ‖schwartzCoord (k:ℝ) (a i j)‖ ≤ M) → ∀ u : 𝓢(E,ℂ),
      ‖schwartzCoord 0 (schwartzWord ws (smoothPerturbation v a u) -
        smoothPerturbation v a (schwartzWord ws u))‖ ≤ C * ‖schwartzCoord ((k:ℝ)+1) u‖ := by
  choose C hC hB using fun i j => second_order_commutator_bound k hk ws hws (v i) (v j)
  refine ⟨(∑ i, ∑ j, C i j)*M, mul_nonneg (Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hC i j))) hM, fun a ha u => ?_⟩
  have he : schwartzWord ws (smoothPerturbation v a u) -
      smoothPerturbation v a (schwartzWord ws u) =
      ∑ i, ∑ j, (schwartzWord ws (SchwartzMap.smulLeftCLM ℂ (a i j) (∂_{v i} (∂_{v j} u))) -
        SchwartzMap.smulLeftCLM ℂ (a i j) (∂_{v i} (∂_{v j} (schwartzWord ws u)))) := by
    simp only [smoothPerturbation_apply,map_sum,Finset.sum_sub_distrib]
  rw [he,schwartzCoord_sum]
  simp_rw [schwartzCoord_sum]
  calc
    _ ≤ ∑ i, ∑ j, C i j * (M*‖schwartzCoord ((k:ℝ)+1) u‖) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact (hB i j (a i j) u).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (ha i j) (norm_nonneg _)) (hC i j))
    _ = _ := by simp_rw [← Finset.sum_mul]; ring

end SobolevChart

namespace FrozenPoisson.ParameterRegularity
open SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]

 

structure TameData (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (v : ι → EC n) (k : ℕ) (M θ E : ℝ) where
  a : SmoothCoefficients ι (EC n)
  f : 𝓢(EC n,ℂ)
  u : 𝓢(EC n,ℂ)
  coefficient_bound : ∀ i j, ‖schwartzCoord (k:ℝ) (a i j)‖ ≤ M
  small : perturbationBound v (coefficientBCF a)*E ≤ θ
  equation : u = schwartzResolvent H t (f + smoothPerturbation v a u)

lemma tame_word_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hk : Module.finrank ℝ (EC n)+1 < k) (M : ℝ) (hM : 0 ≤ M)
    (θ : ℝ) (hθ : θ < 1) (ws : List (EC n)) (hws : ws.length ≤ k) :
    FamilyBound 2 (fun x : TameData H t v k M θ (ellipticBound H hH) =>
      ‖schwartzCoord (k:ℝ) x.f‖ + ‖schwartzCoord ((k:ℝ)+1) x.u‖)
      (fun x => schwartzWord ws x.u) := by
  have hw : (ws.length : ℝ) ≤ k := by exact_mod_cast hws
  obtain ⟨C,hC,hc⟩ := coreBound_word ws (s:=(k:ℝ)) (t:=0) (by linarith)
  obtain ⟨D,hD,hd⟩ := perturbation_commutator_bound k hk ws hws v hM
  let B := ellipticBound H hH
  have hB : 0 ≤ B := (ellipticBound_pos H hH).le
  refine ⟨B*(C+D)/(1-θ),div_nonneg (mul_nonneg hB (add_nonneg hC hD)) (by linarith),fun x => ?_⟩
  let z := schwartzWord ws x.u
  let e := schwartzWord ws (smoothPerturbation v x.a x.u)-smoothPerturbation v x.a z
  have he : z = schwartzResolvent H t (smoothPerturbation v x.a z +
      (schwartzWord ws x.f + e)) := by
    have he := congrArg (schwartzWord ws) x.equation
    rw [schwartz_word_resolvent ws H hH t ht,map_add] at he
    change z = _ at he
    apply he.trans
    congr 1
    dsimp only [e]
    abel
  have hr := schwartzResolvent_bound H hH t ht
    (smoothPerturbation v x.a z+(schwartzWord ws x.f+e))
  rw [← he,schwartzCoord_add,schwartzCoord_add] at hr
  have hg := (norm_add_le (schwartzCoord 0 (smoothPerturbation v x.a z))
    (schwartzCoord 0 (schwartzWord ws x.f)+schwartzCoord 0 e)).trans
      (add_le_add le_rfl (norm_add_le _ _))
  have hh := hr.trans (mul_le_mul_of_nonneg_left hg hB)
  have hp := smoothPerturbation_bound v x.a z
  have hf := hc x.f
  have hc' := hd x.a x.coefficient_bound x.u
  have hs := mul_le_mul_of_nonneg_right x.small (norm_nonneg (schwartzCoord 2 z))
  have hy : (1-θ)*‖schwartzCoord 2 z‖ ≤
      B*(C+D)*(‖schwartzCoord (k:ℝ) x.f‖+‖schwartzCoord ((k:ℝ)+1) x.u‖) := by
    have h0 := mul_le_mul_of_nonneg_left hp hB
    have h1 := mul_le_mul_of_nonneg_left hf hB
    have h2 := mul_le_mul_of_nonneg_left hc' hB
    change ‖schwartzCoord 0 e‖ ≤ _ at hc'
    dsimp only [B] at *
    nlinarith [mul_nonneg (mul_nonneg hB hC) (norm_nonneg (schwartzCoord ((k:ℝ)+1) x.u)),
      mul_nonneg (mul_nonneg hB hD) (norm_nonneg (schwartzCoord (k:ℝ) x.f))]
  rw [div_mul_eq_mul_div,le_div_iff₀ (show 0 < 1-θ by linarith)]
  simpa only [z,mul_comm] using hy

lemma tame_preestimate (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hk : Module.finrank ℝ (EC n)+1 < k) (M : ℝ) (hM : 0 ≤ M)
    (θ : ℝ) (hθ : θ < 1) :
    FamilyBound ((k:ℝ)+2) (fun x : TameData H t v k M θ (ellipticBound H hH) =>
      ‖schwartzCoord (k:ℝ) x.f‖ + ‖schwartzCoord ((k:ℝ)+1) x.u‖) (fun x => x.u) := by
  rw [add_comm]
  exact familyBound_of_words_integer k _ (fun ws hws => tame_word_bound H hH t ht v k hk M hM θ hθ ws hws)

 

theorem tame_estimate (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hk : Module.finrank ℝ (EC n)+1 < k) (M : ℝ) (hM : 0 ≤ M)
    (θ : ℝ) (hθ : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : TameData H t v k M θ (ellipticBound H hH),
      ‖schwartzCoord ((k:ℝ)+2) x.u‖ ≤
        C*(‖schwartzCoord (k:ℝ) x.f‖+‖schwartzCoord 2 x.u‖) := by
  obtain ⟨C,hC,hc⟩ := tame_preestimate H hH t ht v k hk M hM θ hθ
  let D := C+1
  have hD : 0 < D := by dsimp [D]; linarith
  let ε := (2*D)⁻¹
  have hε : 0 < ε := inv_pos.mpr (mul_pos (by norm_num) hD)
  have he : D*ε = 1/2 := by dsimp [ε]; field_simp
  obtain ⟨J,hJ,hj⟩ := schwartz_sobolev_interpolation (E:=EC n) 2 ((k:ℝ)+1) ((k:ℝ)+2)
    (by linarith) hε
  refine ⟨2*D*(1+J),by positivity,fun x => ?_⟩
  have h1 := hj x.u
  have h0 := (hc x).trans (mul_le_mul_of_nonneg_right
    (show C ≤ D by dsimp [D]; linarith)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have h2 := mul_le_mul_of_nonneg_left h1 hD.le
  have h3 : D*(ε*‖schwartzCoord ((k:ℝ)+2) x.u‖) =
      (1/2)*‖schwartzCoord ((k:ℝ)+2) x.u‖ := by rw [← mul_assoc,he]
  nlinarith [mul_nonneg (mul_nonneg hD.le hJ) (norm_nonneg (schwartzCoord (k:ℝ) x.f)),
    mul_nonneg hD.le (norm_nonneg (schwartzCoord 2 x.u))]

private lemma combine_estimate {a f u C B : ℝ} (hC : 0 ≤ C)
    (h : a ≤ C*(f+u)) (hu : u ≤ B*f) : a ≤ C*(1+B)*f := by
  have hh := mul_le_mul_of_nonneg_left hu hC
  nlinarith

lemma tame_low_estimate (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ) (M θ : ℝ) (hθ : θ < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : TameData H t v k M θ (ellipticBound H hH),
      ‖schwartzCoord 2 x.u‖ ≤ B*‖schwartzCoord (k:ℝ) x.f‖ := by
  obtain ⟨J,hJ,hj⟩ := coreBound_word ([] : List (EC n)) (s:=(k:ℝ)) (t:=0) (by simp)
  let B := ellipticBound H hH*J/(1-θ)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (ellipticBound_pos H hH).le hJ) (by linarith)
  refine ⟨B,hB,fun x => ?_⟩
  have hh := schwartzResolvent_bound H hH t ht (x.f+smoothPerturbation v x.a x.u)
  rw [← x.equation,schwartzCoord_add] at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (ellipticBound_pos H hH).le)
  have hp := mul_le_mul_of_nonneg_left (smoothPerturbation_bound v x.a x.u) (ellipticBound_pos H hH).le
  have hsmall := mul_le_mul_of_nonneg_right x.small (norm_nonneg (schwartzCoord 2 x.u))
  have hforce := mul_le_mul_of_nonneg_left (hj x.f) (ellipticBound_pos H hH).le
  dsimp only [B]
  rw [div_mul_eq_mul_div,le_div_iff₀ (show 0 < 1-θ by linarith)]
  simp only [schwartzWord,ContinuousLinearMap.id_apply] at hforce
  nlinarith

 

theorem tame_solution_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hk : Module.finrank ℝ (EC n)+1 < k) (M : ℝ) (hM : 0 ≤ M)
    (θ : ℝ) (hθ : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : TameData H t v k M θ (ellipticBound H hH),
      ‖schwartzCoord ((k:ℝ)+2) x.u‖ ≤ C*‖schwartzCoord (k:ℝ) x.f‖ := by
  obtain ⟨C,hC,hc⟩ := tame_estimate H hH t ht v k hk M hM θ hθ
  obtain ⟨B,hB,hb⟩ := tame_low_estimate H hH t ht v k M θ hθ
  refine ⟨C*(1+B),mul_nonneg hC (by linarith),fun x => ?_⟩
  exact combine_estimate hC (hc x) (hb x)

 

theorem tame_inverse_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hk : Module.finrank ℝ (EC n)+1 < k) (M : ℝ) (hM : 0 ≤ M)
    (θ : ℝ) (hθ : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : SmoothCoefficients ι (EC n))
      (_ha : ∀ i j, ‖schwartzCoord (k:ℝ) (a i j)‖ ≤ M)
      (hs : perturbationBound v (coefficientBCF a)*ellipticBound H hH ≤ θ),
      ∀ f : 𝓢(EC n,ℂ), ‖schwartzCoord ((k:ℝ)+2)
        (schwartzLocal H hH t ht v a (hs.trans_lt hθ) f)‖ ≤ C*‖schwartzCoord (k:ℝ) f‖ := by
  obtain ⟨C,hC,hc⟩ := tame_solution_bound H hH t ht v k hk M hM θ hθ
  refine ⟨C,hC,fun a ha hs f => ?_⟩
  exact hc ⟨a,f,schwartzLocal H hH t ht v a (hs.trans_lt hθ) f,ha,hs,
    schwartzLocal_fixed H hH t ht v a (hs.trans_lt hθ) f⟩

end FrozenPoisson.ParameterRegularity

end
end

end OAI
