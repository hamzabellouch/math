import Mathlib
import OAI.Geometry.PrescribedRicci.TameLocalInverse

namespace OAI

/-! Tame Stability. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Classical ComplexOrder MatrixOrder
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma smoothPerturbation_coeff_sub (v : ι → E) (a b : SmoothCoefficients ι E)
    (u : 𝓢(E,ℂ)) : smoothPerturbation v (a-b) u =
      smoothPerturbation v a u - smoothPerturbation v b u := by
  ext x
  simp only [smoothPerturbation_apply,_root_.sum_apply,_root_.sub_apply,
    Pi.sub_apply]
  simp only [SchwartzMap.smulLeftCLM_apply_apply (a _ _).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (b _ _).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (a _ _ - b _ _).hasTemperateGrowth,
    _root_.sub_apply,smul_eq_mul,sub_mul,Finset.sum_sub_distrib]

lemma perturbation_high_bound (k : ℕ) (hk : Module.finrank ℝ E < k) (v : ι → E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : SmoothCoefficients ι E) (u : 𝓢(E,ℂ)),
      ‖schwartzCoord (k:ℝ) (smoothPerturbation v a u)‖ ≤
        C * (∑ i, ∑ j, ‖schwartzCoord (k:ℝ) (a i j)‖) *
          ‖schwartzCoord ((k:ℝ)+2) u‖ := by
  obtain ⟨C,hC,hc⟩ := schwartz_sobolev_product_bound (E:=E) k hk
  choose D hD hd using fun i j => coreBound_word [v i,v j] (s:=(k:ℝ)+2) (t:=(k:ℝ)) (by simp)
  let B := ∑ i, ∑ j, D i j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j))
  have hDB (i j : ι) : D i j ≤ B :=
    (Finset.single_le_sum (fun l _ => hD i l) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun m _ => hD l m)) (Finset.mem_univ i))
  refine ⟨C*B,mul_nonneg hC hB,fun a u => ?_⟩
  rw [smoothPerturbation_apply,schwartzCoord_sum]
  simp_rw [schwartzCoord_sum]
  calc
    _ ≤ ∑ i, ∑ j, C*B*‖schwartzCoord (k:ℝ) (a i j)‖*‖schwartzCoord ((k:ℝ)+2) u‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (hc (a i j) (∂_{v i} (∂_{v j} u))).trans
      have hb := (hd i j u).trans (mul_le_mul_of_nonneg_right (hDB i j) (norm_nonneg _))
      change ‖schwartzCoord (k:ℝ) (∂_{v i} (∂_{v j} u))‖ ≤ _ at hb
      have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg hC (norm_nonneg (schwartzCoord (k:ℝ) (a i j))))
      convert hh using 1 <;> ring
    _ = _ := by simp_rw [← Finset.sum_mul,← Finset.mul_sum]

end SobolevChart
namespace FrozenPoisson.ParameterRegularity
open SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]

lemma tame_difference_equation (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (v : ι → EC n) (k : ℕ) (M θ E : ℝ) (x y : TameData H t v k M θ E) :
    x.u-y.u = schwartzResolvent H t
      ((x.f-y.f+smoothPerturbation v (x.a-y.a) y.u) + smoothPerturbation v x.a (x.u-y.u)) := by
  rw [smoothPerturbation_coeff_sub,map_sub]
  have he : x.f-y.f+(smoothPerturbation v x.a y.u-smoothPerturbation v y.a y.u)+
      (smoothPerturbation v x.a x.u-smoothPerturbation v x.a y.u) =
      (x.f+smoothPerturbation v x.a x.u)-(y.f+smoothPerturbation v y.a y.u) := by abel
  rw [he,map_sub,← x.equation,← y.equation]

lemma tame_difference_bound (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (v : ι → EC n) (k : ℕ) (M θ E C : ℝ)
    (hc : ∀ x : TameData H t v k M θ E,
      ‖schwartzCoord ((k:ℝ)+2) x.u‖ ≤ C*‖schwartzCoord (k:ℝ) x.f‖)
    (x y : TameData H t v k M θ E) :
    ‖schwartzCoord ((k:ℝ)+2) (x.u-y.u)‖ ≤ C*‖schwartzCoord (k:ℝ)
      (x.f-y.f+smoothPerturbation v (x.a-y.a) y.u)‖ :=
  hc ⟨x.a,x.f-y.f+smoothPerturbation v (x.a-y.a) y.u,x.u-y.u,
    x.coefficient_bound,x.small,tame_difference_equation H t v k M θ E x y⟩

lemma high_forcing_difference_bound (k : ℕ) (v : ι → EC n) (B : ℝ)
    (hb : ∀ (a : SmoothCoefficients ι (EC n)) (u : 𝓢(EC n,ℂ)),
      ‖schwartzCoord (k:ℝ) (smoothPerturbation v a u)‖ ≤
        B*(∑ i, ∑ j, ‖schwartzCoord (k:ℝ) (a i j)‖)*‖schwartzCoord ((k:ℝ)+2) u‖)
    (a b : SmoothCoefficients ι (EC n)) (f g u : 𝓢(EC n,ℂ)) :
    ‖schwartzCoord (k:ℝ) (f-g+smoothPerturbation v (a-b) u)‖ ≤
      ‖schwartzCoord (k:ℝ) (f-g)‖+
        B*(∑ i, ∑ j, ‖schwartzCoord (k:ℝ) (a i j-b i j)‖)*‖schwartzCoord ((k:ℝ)+2) u‖ := by
  rw [schwartzCoord_add]
  have h1 := norm_add_le (schwartzCoord (k:ℝ) (f-g))
    (schwartzCoord (k:ℝ) (smoothPerturbation v (a-b) u))
  have h2 := add_le_add (le_refl ‖schwartzCoord (k:ℝ) (f-g)‖) (hb (a-b) u)
  exact h1.trans h2

 

theorem tame_stability (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hk : Module.finrank ℝ (EC n)+1 < k) (M : ℝ) (hM : 0 ≤ M)
    (θ : ℝ) (hθ : θ < 1) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x y : TameData H t v k M θ (ellipticBound H hH),
      ‖schwartzCoord ((k:ℝ)+2) (x.u-y.u)‖ ≤ C *
        (‖schwartzCoord (k:ℝ) (x.f-y.f)‖ +
          B * (∑ i, ∑ j, ‖schwartzCoord (k:ℝ) (x.a i j-y.a i j)‖) *
            ‖schwartzCoord ((k:ℝ)+2) y.u‖) := by
  obtain ⟨C,hC,hc⟩ := tame_solution_bound H hH t ht v k hk M hM θ hθ
  obtain ⟨B,hB,hb⟩ := perturbation_high_bound k (by omega) v
  refine ⟨C,B,hC,hB,fun x y => ?_⟩
  exact (tame_difference_bound H t v k M θ _ C hc x y).trans
    (mul_le_mul_of_nonneg_left (high_forcing_difference_bound k v B hb x.a y.a x.f y.f y.u) hC)

end FrozenPoisson.ParameterRegularity

end
end

end OAI
