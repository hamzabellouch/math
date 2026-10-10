import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTransitionProgram

namespace OAI

/-! # A polynomial loop for the encoded small-profile walk -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def capView (z : (ℕ×ℕ)×List ℕ) : List ℕ :=
  (z.2.take z.1.1).map (fun a => min a z.1.2)

def capViewRealizer : Realizer capView :=
  composition (pair (composition first second)
    (composition (pair second (composition first first)) takeFast))
    (mapWith (composition (pair second first) minimum))

theorem polynomial_capView : PolynomialTime capViewRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_first)) polynomial_takeFast))
    (polynomial_mapWith (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      polynomial_minimum))

lemma capView_weight (q U : ℕ) (xs : List ℕ) :
    weight (capView ((q,U),xs))≤q*(4*U.size+2)+1 := by
  have hw := weight_map_bound (f := fun a => min a U) (as := xs.take q) (N := 4*U.size+1)
    (fun a _ => (weight_nat_le _).trans (by
      have hs := Nat.size_le_size (min_le_right a U)
      omega))
  change weight (capView ((q,U),xs))≤(xs.take q).length*(4*U.size+2)+1 at hw
  exact hw.trans (by
    have hl : (xs.take q).length≤q := by simp only [List.length_take]; exact min_le_left _ _
    gcongr)

lemma capView_eq (q U : ℕ) (xs : List ℕ) (hq : xs.length=q)
    (hU : ∀ a∈xs,a≤U) : capView ((q,U),xs)=xs := by
  unfold capView
  rw [←hq,List.take_length]
  calc
    xs.map (fun a => min a U)=xs.map id := List.map_congr_left (fun a ha => min_eq_left (hU a ha))
    _ = xs := List.map_id xs

def capViews (z : ProfileCheckData×(List ℕ×List ℕ)) : List ℕ×List ℕ :=
  (capView ((z.1.1.1.1.length,z.1.2),z.2.1),capView ((z.1.1.1.1.length,z.1.2),z.2.2))

def capBounds (z : ProfileCheckData×(List ℕ×List ℕ)) : ℕ×ℕ :=
  (z.1.1.1.1.length,z.1.2)

def capBoundsRealizer : Realizer capBounds :=
  pair (composition (composition
    (f := fun z : ProfileCheckData×(List ℕ×List ℕ) => z.1)
    (g := fun z : ProfileCheckData => z.1.1.1) first profileCatalog) listLength)
    (composition first second)

theorem polynomial_capBounds : PolynomialTime capBoundsRealizer :=
  polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_profileCatalog) polynomial_listLength)
    (polynomial_composition polynomial_first polynomial_second)

def capViewsRealizer : Realizer capViews :=
  pair (composition (pair capBoundsRealizer (composition second first)) capViewRealizer)
    (composition (pair capBoundsRealizer (composition second second)) capViewRealizer)

theorem polynomial_capViews : PolynomialTime capViewsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_capBounds
      (polynomial_composition polynomial_second polynomial_first)) polynomial_capView)
    (polynomial_composition (polynomial_pair polynomial_capBounds
      (polynomial_composition polynomial_second polynomial_second)) polynomial_capView)

abbrev ProfileConfiguration := ResidualParameters×(List ℕ×List ℕ)
abbrev ProfileWord := List Bool×List Bool

def currentParameters (z : ProfileConfiguration) : ResidualParameters :=
  ((candidateData (z.1.1.1,z.2),z.1.1.2),z.1.2)

def currentParametersRealizer : Realizer currentParameters :=
  pair (pair (composition (pair (composition (composition first first) first) second)
      candidateDataRealizer) (composition (composition first first) second))
    (composition first second)

theorem polynomial_currentParameters : PolynomialTime currentParametersRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) polynomial_candidateData)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
    (polynomial_composition polynomial_first polynomial_second)

def boundedNext (z : ProfileConfiguration×ProfileWord) : List ℕ×List ℕ :=
  capViews (z.1.1.1.1,profileStep (currentParameters z.1,z.2))

def boundedNextRealizer : Realizer boundedNext := by
  let check : Realizer (fun z : ProfileConfiguration×ProfileWord => z.1.1.1.1) :=
    composition (composition (composition first first) first) first
  let input : Realizer (fun z : ProfileConfiguration×ProfileWord => (currentParameters z.1,z.2)) :=
    pair (composition first currentParametersRealizer) second
  exact composition (pair check (composition input profileStepRealizer)) capViewsRealizer

theorem polynomial_boundedNext : PolynomialTime boundedNextRealizer := by
  unfold boundedNextRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_currentParameters) polynomial_second)
      polynomial_profileStep)) polynomial_capViews

def advanceProfile (z : ProfileWord×ProfileConfiguration) : ProfileConfiguration :=
  (z.2.1,boundedNext (z.2,z.1))

def advanceProfileRealizer : Realizer advanceProfile :=
  pair (composition second first) (composition
    (f := fun z : ProfileWord×ProfileConfiguration => (z.2,z.1)) (g := boundedNext)
    (pair second first) boundedNextRealizer)

theorem polynomial_advanceProfile : PolynomialTime advanceProfileRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_boundedNext)

lemma advanceProfile_weight (word : ProfileWord) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z.1≤S) : weight (advanceProfile (word,z))≤20*(S+1)^3 := by
  let q := z.1.1.1.1.1.1.length
  let U := z.1.1.1.2
  have hq : q≤S := (list_length_le_weight _).trans ((weight_fst z.1.1.1.1.1).trans
    ((weight_fst z.1.1.1.1).trans ((weight_fst z.1.1.1).trans ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))))
  have hU : U.size≤S := (size_le_weight U).trans
    ((weight_snd z.1.1.1).trans ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))
  have hx := capView_weight q U (profileStep (currentParameters z,word)).1
  have hy := capView_weight q U (profileStep (currentParameters z,word)).2
  change weight (z.1,(capView ((q,U),(profileStep (currentParameters z,word)).1),
    capView ((q,U),(profileStep (currentParameters z,word)).2)))≤20*(S+1)^3
  rw [weight_prod z.1 _,weight_prod (capView ((q,U),(profileStep (currentParameters z,word)).1))
    (capView ((q,U),(profileStep (currentParameters z,word)).2))]
  have hm : q*(4*U.size+2)≤S*(4*S+2) := by gcongr
  nlinarith

def profileWalk (z : ProfileConfiguration×List ProfileWord) : ProfileConfiguration :=
  z.2.foldl (fun state word => advanceProfile (word,state)) z.1

def profileWalkRealizer : Realizer profileWalk :=
  composition (pair second first) (fold advanceProfileRealizer)

lemma profileFold_fixed (words : List ProfileWord) (z : ProfileConfiguration) :
    (words.foldl (fun state word => advanceProfile (word,state)) z).1=z.1 := by
  induction words generalizing z with
  | nil => rfl
  | cons w ws ih => exact ih _

lemma profileFold_weight (words : List ProfileWord) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z≤S) :
    weight (words.foldl (fun state word => advanceProfile (word,state)) z)≤20*(S+1)^3 := by
  induction words using List.reverseRecOn with
  | nil =>
    have hpow : S+1≤(S+1)^3 := Nat.le_self_pow (by decide) _
    simpa using hz.trans (by omega : S≤20*(S+1)^3)
  | append_singleton words w _ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    apply advanceProfile_weight
    rw [profileFold_fixed]
    exact (weight_fst z).trans hz

theorem polynomial_profileWalk : PolynomialTime profileWalkRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_advanceProfile (20*(X+1)^3)
  intro words z pre post _
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  exact profileFold_weight pre z (weight (words,z)) (weight_snd (words,z))

end ContingencyTables.ProfilePrograms

end OAI
