import Mathlib
import OAI.Analysis.CoulombRadii.Screening.UniformCountConsequences

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

theorem AtomicBudgetHistory.universal_positive_field {J n j : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ a B : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hB : B ≤ atomicCountConstant*screenEnergy δ a) (hδ : 0 ≤ δ) (ha : 0 < a)
    (T : AtomicBudgetHistory S ψ B j) (hT : ∀ i, AtomicScaleWindow a (4^j) (T.target i))
    (y : Space) (hy : AtomicScaleWindow a (4^j) y) :
    Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y)) ≤
      2*atomicBudgetRecursionC^(j+2)*screenFieldUnit δ atomicCountConstant a := by
  apply T.positive_field S hatom ψ hm hE hstate hB hδ
    (by linarith [atomicCountConstant_ge_two]) ha _ hT y hy
  intro z hz
  exact (screenCountParameter_controls ψ hm δ hz).trans
    (mul_le_mul_of_nonneg_right (screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ) (sq_nonneg _))

def AtomicBudgetHistory.initial {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) : AtomicBudgetHistory S ψ 0 0 where
  ensemble := RecordedEnsemble.initial ψ
  target := Fin.elim0
  nonzero := fun i => Fin.elim0 i
  law := RecordedEnsemble.initial_conserves ψ
  fermionic := RecordedEnsemble.initial_fermionic ψ hψ
  support := by simpa only [atomicPatchRegion,Set.iUnion_of_empty] using RecordedEnsemble.initial_supported ψ
  mass_eq := RecordedEnsemble.initial_mass ψ
  energy := by simp only [RecordedEnsemble.initial_form,Finset.univ_eq_empty,Finset.sum_empty,add_zero,le_refl]

lemma RecordedEnsemble.mean_raw_le_sqrt {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (hm : mass ψ=1) (T : RecordedEnsemble n) (hT : T.Conserves ψ)
    (hTm : T.totalMass=mass ψ) (y : Space) {a : ℝ} (ha : 0 < a) :
    max (attraction S y-restrictedCorePotential ψ {z | 40*a ≤ ‖z-y‖} y) 0 ≤
      Real.sqrt (T.rawSquare S y a) := by
  let A : Set Space := {z | 40*a ≤ ‖z-y‖}
  have hA : MeasurableSet A := (isClosed_le continuous_const (by fun_prop)).measurableSet
  let W : Configuration n → ℝ := rawSignedField (attraction S y) A y
  have hW : Measurable W := rawSignedField_measurable _ hA y
  let B : ℝ := |attraction S y|+(n:ℝ)/(40*a)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB : ∀ x, |W x| ≤ B := rawSignedField_abs_le _ _ y (by positivity) (fun _ h => h)
  have hcons := hT W hW ⟨B,hB⟩
  have hreindex (p) (x : Configuration (T.out p+T.core p)) :
      W (reindexConfiguration (T.labels p) x)=rawSignedField (attraction S y) A y x :=
    rawSignedField_reindex _ _ _ _ _
  have H := conditional_ensemble_positive_jensen T.out T.core T.vector
    (fun p x => W (reindexConfiguration (T.labels p) x))
    (fun p => by simpa only [hreindex] using (rawSignedField_measurable (n:=T.out p+T.core p) (attraction S y) hA y))
    hB0 (fun p x => hB _) (hTm.trans hm)
  change (max (∑ p, potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p)) 0)^2 ≤ _ at H
  rw [hcons,potentialForm_rawSignedField ψ _ hA y (by positivity) (fun _ h => h),hm,mul_one] at H
  simp_rw [hreindex] at H
  exact (Real.le_sqrt (le_max_right _ _) (T.rawSquare_nonneg S y a)).mpr H

theorem atomic_expected_raw_field_bound {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) {y : Space} (hy : y≠0) :
    max (attraction S y-restrictedCorePotential ψ {z | 40*atomicCellScale y ≤ ‖z-y‖} y) 0 ≤
      2*atomicBudgetRecursionC^2*screenFieldUnit δ atomicCountConstant (atomicCellScale y) := by
  let T := AtomicBudgetHistory.initial S ψ hψ
  have ha := atomicCellScale_pos hy
  have hB : (0:ℝ) ≤ atomicCountConstant*screenEnergy δ (atomicCellScale y) :=
    mul_nonneg (by linarith [atomicCountConstant_ge_two]) (div_nonneg (sq_nonneg _) ha.le)
  have H := T.universal_positive_field S hatom ψ hψ hm hE hstate hB hδ ha
    (fun i => Fin.elim0 i) y (by simp only [pow_zero,AtomicScaleWindow,one_mul,le_refl,and_self])
  exact (T.ensemble.mean_raw_le_sqrt S ψ hm T.law T.mass_eq y ha).trans H

end Coulomb
end

end
end

end OAI
