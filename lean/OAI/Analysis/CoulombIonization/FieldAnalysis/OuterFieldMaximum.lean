import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialCountSelection

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom

def conditionalOutMaximum {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun o : Option (Fin M) =>
    o.elim 0 (fun i => normalizedCoreField Z lam (coreSlice ψ s u) (u i)))

lemma conditionalOutMaximum_nonneg {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) : 0 ≤ conditionalOutMaximum Z lam ψ s u := by
  exact Finset.le_sup' (fun o : Option (Fin M) =>
    o.elim 0 (fun i => normalizedCoreField Z lam (coreSlice ψ s u) (u i))) (Finset.mem_univ none)

lemma conditionalField_le_outMaximum {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) (i : Fin M) :
    normalizedCoreField Z lam (coreSlice ψ s u) (u i) ≤ conditionalOutMaximum Z lam ψ s u := by
  exact Finset.le_sup' (fun o : Option (Fin M) =>
    o.elim 0 (fun i => normalizedCoreField Z lam (coreSlice ψ s u) (u i))) (Finset.mem_univ (some i))

lemma conditionalOutMaximum_le {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i, normalizedCoreField Z lam (coreSlice ψ s u) (u i) ≤ B) :
    conditionalOutMaximum Z lam ψ s u ≤ B := by
  apply Finset.sup'_le
  intro o _
  cases o with
  | none => exact hB
  | some i => exact hf i

lemma conditionalOutMaximum_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) :
    AEMeasurable (conditionalOutMaximum Z lam ψ s) := by
  obtain ⟨F,hF,he⟩ := coreSlice_field_measurable_rep hψ s Z lam
  let f : Option (Fin M) → Configuration M → ℝ := fun o u => o.elim 0 (fun i => F (u,u i))
  have hf (o : Option (Fin M)) : Measurable (f o) := by
    cases o with
    | none => exact measurable_const
    | some i => exact hF.comp (measurable_id.prodMk (measurable_pi_apply i))
  have hh := Finset.measurable_sup' Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => hf i)
  apply hh.aemeasurable.congr
  filter_upwards [he] with u hu
  simp only [Finset.sup'_apply]
  unfold conditionalOutMaximum
  congr 1
  funext o
  cases o with
  | none => rfl
  | some i => exact hu (u i)

lemma normalizedCoreField_le_nuclear {N : ℕ} (ψ : FormVector N)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (z : Space) :
    normalizedCoreField Z lam ψ z ≤ Z/‖z‖ := by
  by_cases hm : formMass ψ = 0
  · simp only [normalizedCoreField,hm,mul_zero,div_zero,zero_sub]
    exact (neg_nonpos.mpr hlam).trans (div_nonneg hZ (norm_nonneg z))
  · have hmp : 0 < formMass ψ := lt_of_le_of_ne (formMass_nonneg ψ) (Ne.symm hm)
    unfold normalizedCoreField
    rw [sub_div]
    have he : Z*formMass ψ/‖z‖/formMass ψ = Z/‖z‖ := by
      rw [mul_div_right_comm,mul_div_assoc,div_self hm,mul_one]
    rw [he]
    have hc := div_nonneg (coreCoulombAt_nonneg ψ z) hmp.le
    linarith

lemma orderedCutForm_slice_mass_zero {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c))
    (i : Fin (cutOutNumber c)) (hi : (p 1).value (u i) = 0) :
    formMass (coreSlice (orderedCutForm p hp ψ c) s u) = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  have hz (x : Configuration (cutCoreNumber c)) :
      (coreSlice (orderedCutForm p hp ψ c) s u).value t x = 0 := by
    apply orderedCutForm_zero_of_factor p hp ψ c _ _ i
    simpa only [joinLists_right] using hi
  simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),integral_zero]

lemma coreFirstRadialCut_out_zero (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (z : Space) (hz : t+b ≤ ‖z-y‖) : (coreFirstRadialCut y ht hb 1).value z = 0 := by
  simp only [coreFirstRadialCut,Matrix.cons_val_one,Matrix.cons_val_zero,radialInside,
    radialPhase_pi_half ht hb hz,Real.cos_pi_div_two]

lemma radial_out_position_nuclear {L : ℕ} (ψ : FormVector L) (y : Space)
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c))
    (hm : formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u) ≠ 0) (i : Fin (cutOutNumber c)) :
    b ≤ ‖u i‖ := by
  have hi : ‖u i-y‖ < t+b := by
    by_contra! h
    apply hm
    exact orderedCutForm_slice_mass_zero _ _ ψ c s u i (coreFirstRadialCut_out_zero y ht hb _ h)
  have hn := norm_le_norm_sub_add y (u i)
  rw [norm_sub_rev y (u i)] at hn
  linarith

lemma radial_conditionalOutMaximum_bound {L : ℕ} (ψ : FormVector L) (y : Space)
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c)) :
    conditionalOutMaximum Z lam (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u ≤ Z/b := by
  apply conditionalOutMaximum_le _ _ _ _ _ (by positivity)
  intro i
  by_cases hm : formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u) = 0
  · simp only [normalizedCoreField,hm,mul_zero,div_zero,zero_sub]
    exact (neg_nonpos.mpr hlam).trans (by positivity)
  · exact (normalizedCoreField_le_nuclear _ hZ hlam _).trans
      (div_le_div_of_nonneg_left hZ hb (radial_out_position_nuclear ψ y ht hb hy c s u hm i))

lemma radial_outMaximum_square_integrable {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let χ := orderedCutForm (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
    Integrable (fun u => conditionalOutMaximum Z lam χ s u^2*formMass (coreSlice χ s u)) := by
  dsimp only
  have hχ := orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ c
  exact (hχ.coreSlice_mass_integrable s).bdd_mul
    ((conditionalOutMaximum_aemeasurable hχ s Z lam).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun u => norm_sq_le_of_nonneg (conditionalOutMaximum_nonneg _ _ _ _ _)
      (radial_conditionalOutMaximum_bound ψ y ht hb hy hZ hlam c s u)))

end CoulombAtom

end

end OAI
