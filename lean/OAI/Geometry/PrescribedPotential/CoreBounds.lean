import Mathlib
import OAI.Geometry.PrescribedPotential.LocalRegularity

namespace OAI

/-! Core Bounds. -/

section

 

noncomputable section
open Filter Topology MeasureTheory LineDeriv TemperedDistribution
open scoped ContDiff SchwartzMap Classical Laplacian

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

 
def CoreBound (s t : ℝ) (T : 𝓢(E, ℂ) → 𝓢(E, ℂ)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f, ‖schwartzCoord t (T f)‖ ≤ C * ‖schwartzCoord s f‖

lemma CoreBound.comp {s t r : ℝ} {S T : 𝓢(E, ℂ) → 𝓢(E, ℂ)}
    (hS : CoreBound t r S) (hT : CoreBound s t T) : CoreBound s r (S ∘ T) := by
  obtain ⟨C, hC, hc⟩ := hS
  obtain ⟨D, hD, hd⟩ := hT
  refine ⟨C * D, mul_nonneg hC hD, fun f => ?_⟩
  exact (hc (T f)).trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hd f) hC)

lemma CoreBound.add {s t : ℝ} {S T : 𝓢(E, ℂ) → 𝓢(E, ℂ)}
    (hS : CoreBound s t S) (hT : CoreBound s t T) :
    CoreBound s t (fun f => S f + T f) := by
  obtain ⟨C, hC, hc⟩ := hS
  obtain ⟨D, hD, hd⟩ := hT
  refine ⟨C + D, add_nonneg hC hD, fun f => ?_⟩
  rw [schwartzCoord_add, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hc f) (hd f))

lemma CoreBound.sum {ι : Type*} {s t : ℝ} (I : Finset ι)
    (T : ι → 𝓢(E, ℂ) → 𝓢(E, ℂ)) (hh : ∀ i ∈ I, CoreBound s t (T i)) :
    CoreBound s t (fun f => ∑ i ∈ I, T i f) := by
  choose C hC h using fun i : I => hh i i.property
  refine ⟨∑ i : I, C i, Finset.sum_nonneg (fun i _ => hC i), fun f => ?_⟩
  rw [schwartzCoord_sum]
  calc
    _ ≤ ∑ i ∈ I, ‖schwartzCoord t (T i f)‖ := norm_sum_le _ _
    _ = ∑ i : I, ‖schwartzCoord t (T i f)‖ := (Finset.sum_coe_sort I _).symm
    _ ≤ ∑ i : I, C i * ‖schwartzCoord s f‖ := Finset.sum_le_sum (fun i _ => h i f)
    _ = _ := (Finset.sum_mul ..).symm

lemma CoreBound.id {s t : ℝ} (hst : t ≤ s) : CoreBound (E := E) s t id := by
  let B := liftOperator (E := E) s t (ContinuousLinearMap.id ℂ _) (fun _ hu => hu.mono hst)
  refine ⟨‖B‖, norm_nonneg _, fun f => ?_⟩
  have hb : B (schwartzCoord s f) = schwartzCoord t f := by
    apply realize_injective t
    exact (realize_liftOperator s t _ _ _).trans (by simp only [realize_schwartzCoord, ContinuousLinearMap.id_apply])
  rw [Function.id_def, ← hb]
  exact B.le_opNorm _

lemma coreBound_deriv {s t : ℝ} (v : E) (hst : t ≤ s - 1) :
    CoreBound s t (fun f : 𝓢(E, ℂ) => ∂_{v} f) := by
  let B := liftOperator s t (lineDerivOpCLM ℂ 𝓢'(E, ℂ) v)
    (fun _ hu => hu.lineDerivOp.mono hst)
  refine ⟨‖B‖, norm_nonneg _, fun f => ?_⟩
  have hb : B (schwartzCoord s f) = schwartzCoord t (∂_{v} f) := by
    apply realize_injective t
    exact (realize_liftOperator s t _ _ _).trans (by
      rw [realize_schwartzCoord, realize_schwartzCoord]
      exact lineDerivOp_toTemperedDistributionCLM_eq f v)
  rw [← hb]
  exact B.le_opNorm _

lemma coreBound_word (ws : List E) {s t : ℝ} (hst : t ≤ s - ws.length) :
    CoreBound s t (schwartzWord ws) := by
  induction ws generalizing t with
  | nil => exact CoreBound.id (by simpa using hst)
  | cons v ws ih =>
    have hw : CoreBound s (t + 1) (schwartzWord ws) := ih (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hst; linarith)
    exact (coreBound_deriv v (s := t + 1) (t := t) (by linarith)).comp hw

lemma schwartzCoord_distribution (s : ℝ) (f : 𝓢(E, ℂ)) :
    (schwartzCoord s f : 𝓢'(E, ℂ)) = besselPotential E ℂ s (f : 𝓢'(E, ℂ)) := by
  rw [← realize_schwartzCoord s f, bessel_realize]

lemma schwartzCoord_raise_two (s : ℝ) (f : 𝓢(E, ℂ)) :
    schwartzCoord (s + 2) f = schwartzCoord s f - (((2 * Real.pi)^2 : ℝ) : ℂ)⁻¹ •
      ∑ j, schwartzCoord s (∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E j} f)) := by
  apply l2_injective
  simp only [Lp.toTemperedDistributionCLM_apply, map_sub, map_smul, map_sum,
    schwartzCoord_distribution]
  rw [add_comm s 2, ← besselPotential_besselPotential_apply 2 s,
    bessel_two_laplacian, map_sub, map_smul]
  congr 2
  rw [TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E), map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← lineDerivOp_toTemperedDistributionCLM_eq,
    ← lineDerivOp_toTemperedDistributionCLM_eq]

lemma schwartzCoord_raise_two_norm (s : ℝ) (f : 𝓢(E, ℂ)) :
    ‖schwartzCoord (s + 2) f‖ ≤ ‖schwartzCoord s f‖ +
      ‖(((2 * Real.pi)^2 : ℝ) : ℂ)⁻¹‖ * ∑ j, ‖schwartzCoord s
        (∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E j} f))‖ := by
  let u := schwartzCoord s f
  let D (j : Fin (Module.finrank ℝ E)) := schwartzCoord s
    (∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E j} f))
  let c : ℂ := (((2 * Real.pi)^2 : ℝ) : ℂ)⁻¹
  rw [schwartzCoord_raise_two]
  change ‖u - c • ∑ j, D j‖ ≤ ‖u‖ + ‖c‖ * ∑ j, ‖D j‖
  have hs := norm_smul c (∑ j, D j)
  calc
    _ ≤ ‖u‖ + ‖c • ∑ j, D j‖ := norm_sub_le _ _
    _ = ‖u‖ + ‖c‖ * ‖∑ j, D j‖ := congrArg (fun z : ℝ => ‖u‖ + z) hs
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg c)) _

lemma coreBound_raise_two {s t : ℝ} (T : 𝓢(E, ℂ) → 𝓢(E, ℂ))
    (hT : CoreBound s t T)
    (hD : ∀ j, CoreBound s t (fun f => ∂_{stdOrthonormalBasis ℝ E j}
      (∂_{stdOrthonormalBasis ℝ E j} (T f)))) : CoreBound s (t + 2) T := by
  obtain ⟨C, hC, hc⟩ := hT
  choose D hD0 hdb using hD
  let c : ℝ := ‖(((2 * Real.pi)^2 : ℝ) : ℂ)⁻¹‖
  have hc0 : 0 ≤ c := norm_nonneg _
  refine ⟨C + c * ∑ j, D j, add_nonneg hC (mul_nonneg hc0 (Finset.sum_nonneg (fun j _ => hD0 j))), fun f => ?_⟩
  apply (schwartzCoord_raise_two_norm t (T f)).trans
  have hd := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hdb j f)
  have hsum := add_le_add (hc f) (mul_le_mul_of_nonneg_left hd hc0)
  convert hsum using 1; rw [← Finset.sum_mul]; ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma schwartzWord_append (vs ws : List E) (f : 𝓢(E, ℂ)) :
    schwartzWord (vs ++ ws) f = schwartzWord vs (schwartzWord ws f) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa only [List.cons_append, schwartzWord, ContinuousLinearMap.comp_apply] using congrArg (lineDerivOpCLM ℂ 𝓢(E, ℂ) v) ih

 

lemma coreBound_of_words (k : ℕ) {s : ℝ} (T : 𝓢(E, ℂ) → 𝓢(E, ℂ))
    (h : ∀ ws : List E, ws.length ≤ 2 * k → CoreBound s 0 (fun f => schwartzWord ws (T f))) :
    CoreBound s (2 * (k : ℝ)) T := by
  induction k generalizing T with
  | zero => simpa [schwartzWord] using h [] (by simp)
  | succ k ih =>
    have ht := ih T (fun ws hw => h ws (by omega))
    have hd (j : Fin (Module.finrank ℝ E)) := ih
      (fun f => ∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E j} (T f)))
      (fun ws hw => by
        have hh := h (ws ++ [stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E j])
          (by simp only [List.length_append, List.length_cons, List.length_nil] ; omega)
        simpa only [schwartzWord_append, schwartzWord, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, lineDerivOpCLM_apply] using hh)
    convert coreBound_raise_two T ht hd using 1; push_cast; ring

end SobolevChart

end
end

end OAI
