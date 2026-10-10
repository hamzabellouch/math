import OAI.Analysis.CircleDomains.Uniformization.CyclicCircularization

namespace OAI

/-! Exact restart identities for the deterministic finite circularization. -/
open Set Function Metric Filter
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity.FiniteJordanConfiguration
variable {I:Type*} [Finite I]

lemma iterate_add (C:FiniteJordanConfiguration I) (s:ℕ→I) (a b:ℕ) :
    iterate C s (a+b)=iterate (iterate C s a) (fun n => s (a+n)) b := by
  induction b with
  | zero => simp only [Nat.add_zero,iterate]
  | succ b ih =>
    exact congrArg (fun D : FiniteJordanConfiguration I =>
      (chosenStep D (s (a+b))).target) ih

lemma stageMap_add (C:FiniteJordanConfiguration I) (s:ℕ→I) (a b:ℕ) :
    stageMap C s (a+b)=stageMap (iterate C s a) (fun n => s (a+n)) b := by
  exact congrArg (fun D : FiniteJordanConfiguration I =>
    (chosenStep D (s (a+b))).map) (iterate_add C s a b)

lemma cumulativeMap_add (C:FiniteJordanConfiguration I) (s:ℕ→I) (a b:ℕ) :
    cumulativeMap C s (a+b)=cumulativeMap (iterate C s a) (fun n => s (a+n)) b ∘
      cumulativeMap C s a := by
  induction b with
  | zero => simp only [Nat.add_zero,cumulativeMap,id_comp]
  | succ b ih =>
    change stageMap C s (a+b) ∘ cumulativeMap C s (a+b) = _
    rw [stageMap_add C s a b,ih]
    rfl

lemma cyclicSchedule_cycle_add (m n:ℕ) : cyclicSchedule m (m+1+n)=cyclicSchedule m n := by
  apply Fin.ext
  simp [cyclicSchedule]

lemma iterate_cycle_add {m:ℕ} (C:FiniteJordanConfiguration (Fin (m+1))) (n:ℕ) :
    iterate C (cyclicSchedule m) (m+1+n)=
      iterate (iterate C (cyclicSchedule m) (m+1)) (cyclicSchedule m) n := by
  rw [iterate_add]
  congr 1
  funext k
  exact cyclicSchedule_cycle_add m k

lemma selectedCenter_cycle_add {m:ℕ} (C:FiniteJordanConfiguration (Fin (m+1))) (n:ℕ) :
    selectedCenter C (cyclicSchedule m) (m+1+n)=
      selectedCenter (iterate C (cyclicSchedule m) (m+1)) (cyclicSchedule m) n := by
  unfold selectedCenter
  rw [cyclicSchedule_cycle_add]
  exact congrArg (fun D : FiniteJordanConfiguration (Fin (m+1)) =>
    (chosenStep D (cyclicSchedule m n)).center) (iterate_cycle_add C n)

lemma selectedRadius_cycle_add {m:ℕ} (C:FiniteJordanConfiguration (Fin (m+1))) (n:ℕ) :
    selectedRadius C (cyclicSchedule m) (m+1+n)=
      selectedRadius (iterate C (cyclicSchedule m) (m+1)) (cyclicSchedule m) n := by
  unfold selectedRadius
  rw [cyclicSchedule_cycle_add]
  exact congrArg (fun D : FiniteJordanConfiguration (Fin (m+1)) =>
    (chosenStep D (cyclicSchedule m n)).radius) (iterate_cycle_add C n)

lemma visitTime_succ {m:ℕ} (n:ℕ) (i:Fin (m+1)) :
    visitTime (n+1) i=m+1+visitTime n i := by
  simp only [visitTime,Nat.add_mul,Nat.one_mul]
  omega

end CircleDomainRigidity.FiniteJordanConfiguration

end

end OAI
