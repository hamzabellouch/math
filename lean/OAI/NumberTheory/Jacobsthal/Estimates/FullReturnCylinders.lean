import OAI.NumberTheory.Jacobsthal.Paths.HistoryRestrictionAlgebra

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels

noncomputable def avoidOddReturns (a m b : ℕ) (hab : a+2*m ≤ b) : Set (RawHistory b) :=
  {h | ∀ j : Fin m, h ⟨a+2*(j.1+1),Finset.mem_Iic.mpr (by have hj := j.2; omega)⟩ ∉ regenerationSet}

lemma avoidOddReturns_measurable (a m b : ℕ) (hab : a+2*m ≤ b) :
    MeasurableSet (avoidOddReturns a m b hab) := by
  unfold avoidOddReturns
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact (regenerationSet_measurable.preimage (measurable_pi_apply _)).compl

noncomputable def lastRegeneration (b : ℕ) : Set (RawHistory b) :=
  {h | h ⟨b,by simp⟩ ∈ regenerationSet}

lemma lastRegeneration_measurable (b : ℕ) : MeasurableSet (lastRegeneration b) :=
  regenerationSet_measurable.preimage (measurable_pi_apply _)

noncomputable def survivingHistory (a m : ℕ) : Kernel (RawHistory a) (RawHistory (a+2*m)) :=
  (rawExtension a (a+2*m)).restrict (avoidOddReturns_measurable a m (a+2*m) le_rfl)

noncomputable def firstReturnHistory (a n : ℕ) : Kernel (RawHistory a) (RawHistory (a+2*(n+1))) :=
  (rawExtension a (a+2*(n+1))).restrict
    ((avoidOddReturns_measurable a n (a+2*(n+1)) (by omega)).inter (lastRegeneration_measurable _))

instance survivingHistory_isFiniteKernel (a m : ℕ) : IsFiniteKernel (survivingHistory a m) := by
  unfold survivingHistory
  infer_instance

instance firstReturnHistory_isFiniteKernel (a n : ℕ) : IsFiniteKernel (firstReturnHistory a n) := by
  unfold firstReturnHistory
  infer_instance

lemma avoidOddReturns_prefix {a m b c : ℕ} (hab : a+2*m ≤ b) (hbc : b ≤ c) :
    rawPrefix hbc ⁻¹' avoidOddReturns a m b hab = avoidOddReturns a m c (hab.trans hbc) := by
  rfl

lemma avoidOddReturns_succ (a n : ℕ) :
    avoidOddReturns a (n+1) (a+2*(n+1)) le_rfl =
      (rawPrefix (show a+2*n ≤ a+2*(n+1) by omega) ⁻¹'
        avoidOddReturns a n (a+2*n) le_rfl) ∩ (lastRegeneration (a+2*(n+1)))ᶜ := by
  rw [avoidOddReturns_prefix]
  ext h
  change (∀ j : Fin (n+1), _ ∉ regenerationSet) ↔
    (∀ j : Fin n, _ ∉ regenerationSet) ∧ _ ∉ regenerationSet
  constructor
  · intro hh
    constructor
    · intro j
      exact hh j.castSucc
    · exact hh (Fin.last n)
  · rintro ⟨hh,hlast⟩ j
    by_cases hj : j.1 < n
    · exact hh ⟨j.1,hj⟩
    · have he : j.1=n := by have hjn := j.2; omega
      simpa only [he] using hlast

theorem survivingHistory_succ (a n : ℕ) :
    survivingHistory a (n+1) =
      ((rawExtension (a+2*n) (a+2*(n+1))).restrict (lastRegeneration_measurable _).compl) ∘ₖ
        survivingHistory a n := by
  unfold survivingHistory
  have he := rawExtension_restrict_comp (show a ≤ a+2*n by omega)
    (show a+2*n ≤ a+2*(n+1) by omega)
    (avoidOddReturns_measurable a n (a+2*n) le_rfl) (lastRegeneration_measurable _).compl
  rw [← he]
  congr 1
  exact avoidOddReturns_succ a n

theorem firstReturnHistory_eq_capture_after_survival (a n : ℕ) :
    firstReturnHistory a n =
      ((rawExtension (a+2*n) (a+2*(n+1))).restrict (lastRegeneration_measurable _)) ∘ₖ
        survivingHistory a n := by
  unfold firstReturnHistory survivingHistory
  rw [← rawExtension_restrict_comp (show a ≤ a+2*n by omega)
    (show a+2*n ≤ a+2*(n+1) by omega)
    (avoidOddReturns_measurable a n (a+2*n) le_rfl) (lastRegeneration_measurable _)]
  congr 1

lemma firstReturnHistory_ae_cylinder (a n : ℕ) (h : RawHistory a) :
    ∀ᵐ z ∂firstReturnHistory a n h,
      (∀ j : Fin n, z ⟨a+2*(j.1+1),Finset.mem_Iic.mpr (by have hj := j.2; omega)⟩ ∉ regenerationSet) ∧
      z ⟨a+2*(n+1),by simp⟩ ∈ regenerationSet := by
  rw [firstReturnHistory,Kernel.restrict_apply]
  exact ae_restrict_mem ((avoidOddReturns_measurable a n (a+2*(n+1)) (by omega)).inter (lastRegeneration_measurable _))

lemma firstReturnHistory_retains_past (a n : ℕ) (h : RawHistory a) :
    ∀ᵐ z ∂firstReturnHistory a n h, rawPrefix (show a ≤ a+2*(n+1) by omega) z = h := by
  rw [firstReturnHistory,Kernel.restrict_apply]
  exact ae_restrict_of_ae (rawExtension_retains_prefix (by omega) h)

noncomputable def firstReturnHistoryWithFirst (a n : ℕ) {E : Set CostState} (hE : MeasurableSet E) :
    Kernel (RawHistory a) (RawHistory (a+2*(n+1))) :=
  (firstReturnHistory a n).restrict (hE.preimage
    (measurable_pi_apply (⟨a+1,Finset.mem_Iic.mpr (by omega)⟩ : Finset.Iic (a+2*(n+1)))))

lemma firstReturnHistoryWithFirst_apply (a n : ℕ) {E : Set CostState} (hE : MeasurableSet E)
    (h : RawHistory a) {S : Set (RawHistory (a+2*(n+1)))} (hS : MeasurableSet S) :
    firstReturnHistoryWithFirst a n hE h S = rawExtension a (a+2*(n+1)) h
      ((S ∩ {z | z ⟨a+1,Finset.mem_Iic.mpr (by omega)⟩ ∈ E}) ∩
        (avoidOddReturns a n (a+2*(n+1)) (by omega) ∩ lastRegeneration _)) := by
  rw [firstReturnHistoryWithFirst,Kernel.restrict_apply' _ _ _ hS,
    firstReturnHistory,Kernel.restrict_apply' _ _ _
      (hS.inter (hE.preimage (measurable_pi_apply _)))]
  rfl

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
