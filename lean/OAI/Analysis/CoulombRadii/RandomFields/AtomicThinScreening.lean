import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.AtomicThinCounts

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def RecordedEnsemble.deletedSquare {n : ℕ} (T : RecordedEnsemble n) (y : Space) (t b : ℝ) : ℝ :=
  ∑ p, sliceExpectation (T.vector p) (fun _ x => (localCount {z | t-7*b≤‖z-y‖} x)^2)

lemma RecordedEnsemble.deletedSquare_le {n : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hC : T.Conserves ψ) {y : Space} {t b : ℝ}
    (hs : T.OutSupported (Metric.closedBall y (t+b))) :
    T.deletedSquare y t b≤localCountSecondMoment ψ (deletedShell y t b) := by
  have HE : T.deletedSquare y t b=
      ∑ p, sliceExpectation (T.vector p) (fun _ x => (localCount (deletedShell y t b) x)^2) := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro s hs'
    apply integral_congr_ae
    filter_upwards [(hs p).recorded_positions s] with x hx
    by_cases hm : mass ((T.vector p).coreSlice s x)=0
    · simp only [hm,zero_mul]
    · congr 2
      apply Finset.sum_congr rfl
      intro i hi
      have hi : ‖position x i-y‖≤t+b := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx hm i
      have he : (position x i∈{z | t-7*b≤‖z-y‖}) ↔ position x i∈deletedShell y t b := by
        change (t-7*b≤‖position x i-y‖) ↔ (t-7*b≤‖position x i-y‖ ∧ ‖position x i-y‖≤t+b)
        exact ⟨fun h => ⟨h,hi⟩,And.left⟩
      simp only [Set.indicator_apply,he]
  rw [HE]
  exact hC.recorded_secondMoment (deletedShell_measurable y t b)

theorem exists_atomic_thin_screened {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) (hstate : form S ψ≤E+δ)
    (hδ : 0≤δ) {y : Space} (hy : y≠0) {b : ℝ} (hb : 0<b)
    (hsmall : 18*b≤atomicCellScale y)
    (hcond : atomicCellScale y≤b^2*Real.sqrt (screenCountParameter ψ δ)*screenMass δ (atomicCellScale y)) :
    ∃ t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1,
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+b)) ∧
      T.ensemble.deletedSquare y t b≤
        18*atomicPatchCountFactor*(b/atomicCellScale y)*screenCountParameter ψ δ*(screenMass δ (atomicCellScale y))^2 ∧
      (∑ p, (T.ensemble.out p:ℝ)^2*mass (T.ensemble.vector p))≤
        atomicPatchCountFactor*screenCountParameter ψ δ*(screenMass δ (atomicCellScale y))^2 ∧
      (∀ v, AtomicScaleWindow (atomicCellScale y) 4 v →
        Real.sqrt (T.ensemble.rawSquare S v (atomicCellScale v))≤
          2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*
            screenFieldUnit δ (screenCountParameter ψ δ) (atomicCellScale y)) := by
  let P := screenCountParameter ψ δ
  have hP : 1≤P := screenCountParameter_ge_one ψ δ
  have hP0 : 0≤P := le_trans zero_le_one hP
  have hc := fun z hz => screenCountParameter_controls ψ hm δ (y:=z) hz
  obtain ⟨t,ht,hdel⟩ := exists_atomic_deletedShell ψ hm hδ hy hb hsmall
  have ht0 : 0≤t := by nlinarith [ht.1,atomicCellScale_nonneg y]
  have hwidth : t+b≤80*atomicCellScale y := by linarith [ht.2,atomicCellScale_nonneg y]
  obtain ⟨T,hTr,ho,hcs,hos⟩ := thin_localization_history S ψ hψ hy ht0 hb hwidth
  have hbudget := thinIMS_budget ψ hm hδ hP hc hy hb hwidth hcond
  have hP' : 1≤thinReserveFactor*P := by nlinarith [thinReserveFactor_ge_one]
  have hc' (z : Space) (hz : z≠0) : localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z))≤
      (thinReserveFactor*P)*(screenMass δ (atomicCellScale z))^2 :=
    (hc z hz).trans (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left hP0 thinReserveFactor_ge_one) (sq_nonneg _))
  refine ⟨t,ht,T,ho,hcs,hos,(RecordedEnsemble.deletedSquare_le T.law hos).trans hdel,?_,?_⟩
  · exact (RecordedEnsemble.out_square_le T.law measurableSet_closedBall hos).trans
      ((localCountSecondMoment_mono ψ measurableSet_closedBall (Metric.closedBall_subset_closedBall hwidth)).trans
        (atomicPatch_secondMoment ψ hδ hP0 hc hy))
  · intro v hv
    have H := T.positive_field S hatom ψ hm hE hstate hbudget hδ hP' (atomicCellScale_pos hy) hc'
      (fun i => by rw [hTr i]; constructor <;> norm_num <;> linarith [atomicCellScale_nonneg y])
      v (by simpa only [pow_one] using hv)
    convert H using 1
    simp only [screenFieldUnit,Real.sqrt_mul thinReserveFactor_nonneg]
    ring

end Coulomb
end

end
end

end OAI
