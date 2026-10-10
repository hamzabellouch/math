import OAI.Combinatorics.ContingencyTables.Sampling.ProfileSamplingProgram

namespace OAI

/-! # The bounded profile program for the all-small branch -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms Polynomial

abbrev UnitStepInput := ProfileConfiguration×List Bool

def unitCandidateInput (z : UnitStepInput) : ProfileStepInput :=
  (currentParameters z.1,(z.2,[]))
def unitCandidateInputRealizer : Realizer unitCandidateInput :=
  pair (composition first currentParametersRealizer) (pair second (constant []))

theorem polynomial_unitCandidateInput : PolynomialTime unitCandidateInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_currentParameters)
    (polynomial_pair polynomial_second (polynomial_constant []))

def unitNext (z : UnitStepInput) : List ℕ×List ℕ :=
  capViews (z.1.1.1.1,stepCandidateViews (unitCandidateInput z))
def unitNextRealizer : Realizer unitNext :=
  composition (f := fun z : UnitStepInput =>
      (z.1.1.1.1,stepCandidateViews (unitCandidateInput z))) (g := capViews)
    (pair (composition (composition (composition first first) first) first)
      (composition (f := unitCandidateInput) (g := stepCandidateViews)
        unitCandidateInputRealizer stepCandidateViewsRealizer)) capViewsRealizer

theorem polynomial_unitNext : PolynomialTime unitNextRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition polynomial_unitCandidateInput polynomial_stepCandidateViews)) polynomial_capViews

def unitAdvance (z : List Bool×ProfileConfiguration) : ProfileConfiguration :=
  (z.2.1,unitNext (z.2,z.1))
def unitAdvanceRealizer : Realizer unitAdvance :=
  pair (composition second first) (composition (f := fun z : List Bool×ProfileConfiguration => (z.2,z.1))
    (g := unitNext) (pair second first) unitNextRealizer)

theorem polynomial_unitAdvance : PolynomialTime unitAdvanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_unitNext)

lemma unitAdvance_weight (word : List Bool) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z.1≤S) : weight (unitAdvance (word,z))≤20*(S+1)^3 := by
  let q := z.1.1.1.1.1.1.length
  let U := z.1.1.1.2
  have hq : q≤S := (list_length_le_weight _).trans ((weight_fst z.1.1.1.1.1).trans
    ((weight_fst z.1.1.1.1).trans ((weight_fst z.1.1.1).trans ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))))
  have hU : U.size≤S := (size_le_weight U).trans
    ((weight_snd z.1.1.1).trans ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))
  have hx := capView_weight q U (stepCandidateViews (unitCandidateInput (z,word))).1
  have hy := capView_weight q U (stepCandidateViews (unitCandidateInput (z,word))).2
  change weight (z.1,(capView ((q,U),(stepCandidateViews (unitCandidateInput (z,word))).1),
    capView ((q,U),(stepCandidateViews (unitCandidateInput (z,word))).2)))≤20*(S+1)^3
  rw [weight_prod z.1 _,weight_prod (capView ((q,U),(stepCandidateViews (unitCandidateInput (z,word))).1))
    (capView ((q,U),(stepCandidateViews (unitCandidateInput (z,word))).2))]
  have hm : q*(4*U.size+2)≤S*(4*S+2) := by gcongr
  nlinarith

def unitProfileWalk (z : ProfileConfiguration×List (List Bool)) : ProfileConfiguration :=
  z.2.foldl (fun state word => unitAdvance (word,state)) z.1

def unitProfileWalkRealizer : Realizer unitProfileWalk :=
  composition (pair second first) (fold unitAdvanceRealizer)

lemma unitFold_fixed (words : List (List Bool)) (z : ProfileConfiguration) :
    (words.foldl (fun state word => unitAdvance (word,state)) z).1=z.1 := by
  induction words generalizing z with
  | nil => rfl
  | cons w ws ih => exact ih _

lemma unitFold_weight (words : List (List Bool)) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z≤S) :
    weight (words.foldl (fun state word => unitAdvance (word,state)) z)≤20*(S+1)^3 := by
  induction words using List.reverseRecOn with
  | nil =>
    have hpow : S+1≤(S+1)^3 := Nat.le_self_pow (by decide) _
    simpa using hz.trans (by omega : S≤20*(S+1)^3)
  | append_singleton words w _ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    apply unitAdvance_weight
    rw [unitFold_fixed]
    exact (weight_fst z).trans hz

theorem polynomial_unitProfileWalk : PolynomialTime unitProfileWalkRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_unitAdvance (20*(X+1)^3)
  intro words z pre post _
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  exact unitFold_weight pre z (weight (words,z)) (weight_snd (words,z))

end ContingencyTables.ProfilePrograms

end OAI
