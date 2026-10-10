import OAI.Combinatorics.ContingencyTables.Sampling.ProfileVectorMeasureBounds
import OAI.Combinatorics.ContingencyTables.Machines.ScheduledScalarBounds

namespace OAI

/-! # Polynomial binary sizes before finite tabulation begins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

theorem tabulation_preparation_polynomial : ∃ p : Polynomial ℕ,∀ z,
    let M := p.eval (scheduledCountInputMeasure z)
    weight (scheduledOuterInput z) ≤ M ∧
    parameterDimension z+parameterAccuracy z+parameterCompletionWidth z ≤ M ∧
    (∀ v∈profileBoxViews (initialCheck z.1),weight v ≤ M) ∧
    (∀ o∈originalCandidates z.1,weight o ≤ M ∧ weight (o.getD []) ≤ M) ∧
    (∀ u∈profileBoxViews (initialCheck z.1),∀ v∈profileBoxViews (initialCheck z.1),
      weight (scheduledMatrixParameters z,(u,v)) ≤ M) := by
  obtain ⟨a,ha⟩ := work_scheduledOuterInput
  obtain ⟨b,hb⟩ := schedule_numeric_polynomial
  obtain ⟨c,hc⟩ := polynomial_initialCheck
  obtain ⟨v,hv⟩ := profileBoxViews_point_polynomial
  obtain ⟨o,ho⟩ := originalCandidates_point_polynomial
  obtain ⟨t,ht⟩ := polynomial_optionalTrialInput
  let w := a+b+v.comp c+o+X+1
  let g := w+t.comp (1+2*w)+2+3*w
  refine ⟨g,?_⟩
  intro z
  let K := scheduledCountInputMeasure z
  have hz : weight z ≤ K := by unfold K scheduledCountInputMeasure; omega
  have hmargin : weight z.1 ≤ K := (weight_fst z).trans hz
  have houter : weight (scheduledOuterInput z) ≤ a.eval K :=
    (Nat.le_add_left _ _).trans (ha z)
  have hnum : parameterDimension z+parameterAccuracy z+parameterCompletionWidth z ≤ b.eval K := hb z
  have hcheck : weight (initialCheck z.1) ≤ c.eval K :=
    (Nat.le_add_left _ _).trans ((hc z.1).trans (polynomial_eval_monotone c hmargin))
  have hview (u : List ℕ×List ℕ) (hu : u∈profileBoxViews (initialCheck z.1)) :
      weight u ≤ (v.comp c).eval K := by
    rw [eval_comp]
    exact (hv _ u hu).trans (polynomial_eval_monotone v hcheck)
  have horig (u : Option MatrixCode) (hu : u∈originalCandidates z.1) :
      weight u ≤ o.eval K := (ho _ u hu).trans (polynomial_eval_monotone o hmargin)
  have hwa : a.eval K ≤ w.eval K := by simp only [w,eval_add,eval_one,eval_X]; omega
  have hwb : b.eval K ≤ w.eval K := by simp only [w,eval_add,eval_one,eval_X]; omega
  have hwv : (v.comp c).eval K ≤ w.eval K := by simp only [w,eval_add,eval_one,eval_X]; omega
  have hwo : o.eval K ≤ w.eval K := by simp only [w,eval_add,eval_one,eval_X]; omega
  have hwg : w.eval K ≤ g.eval K := by simp only [g,eval_add,eval_mul,eval_ofNat]; omega
  have hwalk : weight (scheduledWalkInput z) ≤ w.eval K := by
    have hp : (scheduledOuterInput z).1.1=scheduledWalkInput z := rfl
    rw [←hp]
    exact ((weight_fst _).trans (weight_fst _)).trans (houter.trans hwa)
  refine ⟨(houter.trans hwa).trans hwg,(hnum.trans hwb).trans hwg,
    (fun u hu => ((hview u hu).trans hwv).trans hwg),?_,?_⟩
  · intro u hu
    have hou : weight u ≤ w.eval K := (horig u hu).trans hwo
    refine ⟨hou.trans hwg,?_⟩
    have hi : weight (scheduledWalkInput z,u) ≤ (1+2*w).eval K := by
      simp only [weight_prod,eval_add,eval_one,eval_mul,eval_ofNat]
      omega
    have hdef : weight (u.getD []) ≤ t.eval ((1+2*w).eval K) :=
      (weight_snd (optionalTrialInput (scheduledWalkInput z,u))).trans
        ((Nat.le_add_left _ _).trans ((ht _).trans (polynomial_eval_monotone t hi)))
    apply hdef.trans
    change t.eval ((1+2*w).eval K) ≤ g.eval K
    simp only [g,eval_add,eval_comp,eval_mul,eval_ofNat,eval_one]
    omega
  · intro u hu v' hv'
    have hu' := (hview u hu).trans hwv
    have hv'' := (hview v' hv').trans hwv
    have hm : weight (scheduledMatrixParameters z) ≤ w.eval K := by
      have hp : (scheduledWalkInput z).1=scheduledMatrixParameters z := rfl
      rw [←hp]
      exact (weight_fst _).trans hwalk
    change weight (scheduledMatrixParameters z,(u,v')) ≤ g.eval K
    simp only [weight_prod,g,eval_add,eval_mul,eval_ofNat]
    omega

end ContingencyTables.ProfilePrograms

end OAI
