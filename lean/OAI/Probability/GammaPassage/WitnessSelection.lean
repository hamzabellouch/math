import OAI.Probability.GammaPassage.SpatialWitnessCounts

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP
open Set

/-- Preserve every chunk position while truncating the concatenated witness list. -/
def takeWitnessPacks {α : Type*} : ℕ → List (List α) → List (List α)
  | _,[] => []
  | t,ws::packs => ws.take t :: takeWitnessPacks (t-ws.length) packs

lemma takeWitnessPacks_length {α : Type*} (t : ℕ) (packs : List (List α)) :
    (takeWitnessPacks t packs).length=packs.length := by
  induction packs generalizing t with
  | nil => rfl
  | cons ws packs ih => simp [takeWitnessPacks,ih]

lemma takeWitnessPacks_flatten {α : Type*} (t : ℕ) (packs : List (List α)) :
    (takeWitnessPacks t packs).flatten=packs.flatten.take t := by
  induction packs generalizing t with
  | nil => simp [takeWitnessPacks]
  | cons ws packs ih => simp [takeWitnessPacks,ih,List.take_append]

lemma takeWitnessPacks_assign {α β : Type*} (R : α → β → Prop) (t : ℕ)
    (packs : List (List α)) (is : List β)
    (h : List.Forall₂ (fun ws i => ∀ q ∈ ws, R q i) packs is) :
    List.Forall₂ (fun ws i => ∀ q ∈ ws, R q i) (takeWitnessPacks t packs) is := by
  induction h generalizing t with
  | nil => exact List.Forall₂.nil
  | @cons ws i packs is hws htail ih =>
    exact List.Forall₂.cons (fun q hq => hws q (List.mem_of_mem_take hq)) (ih _)

/-- The exact source selection threshold, with a convenient sufficient N≥4. -/
lemma long_path_witness_count (H a : ℝ) (ha : 0 < a) (N M : ℕ) (hN : 4 ≤ N)
    (hlower : ((N : ℝ)-1)*a-4*a*M ≤ H) (hcheap : H < N*a/2) :
    N/16 ≤ M := by
  have hM : (N : ℝ)/8-1/4 < M := by nlinarith
  have hdiv : ((N/16 : ℕ) : ℝ)*16 ≤ N := by exact_mod_cast Nat.div_mul_le_self N 16
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : ((N/16 : ℕ) : ℝ) ≤ M := by linarith
  exact_mod_cast hh

/-- A list of event labels determined only by the ordered chunk indices
and by the number of selected witnesses in each position. -/
def witnessLabels : List ℕ → List (ℤ×ℤ) → List (ℤ×ℤ)
  | [],_ => []
  | _,[] => []
  | n::ns,i::is => List.replicate n i ++ witnessLabels ns is

lemma witnessLabels_length (ns : List ℕ) (is : List (ℤ×ℤ)) (h : ns.length=is.length) :
    (witnessLabels ns is).length=ns.sum := by
  induction ns generalizing is with
  | nil => simp [witnessLabels]
  | cons n ns ih =>
    cases is with
    | nil => simp at h
    | cons i is => simp [witnessLabels,ih is (by simpa using h)]

theorem witnessPacks_strictDisjoint (w : Edge → ℝ) (b m₀ am ap K η : ℝ) (k m : ℕ)
    (packs : List (List GammaFPP.BK.StrictPathWitness)) (is : List (ℤ×ℤ))
    (hassign : List.Forall₂ (fun ws ih => ∀ q ∈ ws,
      q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w) packs is)
    (hpair : packs.flatten.Pairwise (fun q r => Disjoint q.edges r.edges)) :
    GammaFPP.BK.StrictDisjointPaths (spatialListSupport b k m (witnessLabels (packs.map List.length) is))
      ((witnessLabels (packs.map List.length) is).map (spatialWitnessFamily b m₀ am ap K η k m)) w := by
  let labels := witnessLabels (packs.map List.length) is
  have hlabels : List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w)
      packs.flatten labels := by
    clear hpair
    induction hassign with
    | nil => exact List.Forall₂.nil
    | @cons ws i packs is hws htail ih =>
      change List.Forall₂ _ (ws++packs.flatten) ((List.replicate ws.length i)++_)
      induction ws with
      | nil => exact ih
      | cons q qs ih =>
        exact List.Forall₂.cons (hws q (by simp)) (ih (fun r hr => hws r (by simp [hr])))
  refine ⟨packs.flatten,?_,hpair⟩
  have hsupp (ih : ℤ×ℤ) (hi : ih ∈ labels) : spatialWitnessSupport b k m ih ⊆ spatialListSupport b k m labels := by
    intro e he
    exact Finset.mem_biUnion.mpr ⟨ih,List.mem_toFinset.mpr hi,he⟩
  have hall : List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧
      q.edges ⊆ spatialListSupport b k m labels ∧ q.Good w) packs.flatten labels := by
    have enrich (ps : List GammaFPP.BK.StrictPathWitness) (js : List (ℤ×ℤ))
        (hh : List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w) ps js)
        (hsub : ∀ i ∈ js, i ∈ labels) :
        List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧
          q.edges ⊆ spatialListSupport b k m labels ∧ q.Good w) ps js := by
      induction hh with
      | nil => exact List.Forall₂.nil
      | @cons q i ps js hq ht rec =>
        exact List.Forall₂.cons
          ⟨hq.1,(spatialWitness_edges b m₀ am ap K η k m i q hq.1).trans (hsupp i (hsub i (by simp))),hq.2⟩
          (rec (fun j hj => hsub j (by simp [hj])))
    exact enrich _ _ hlabels (fun _ hi => hi)
  exact List.forall₂_map_right_iff.mpr hall

end GammaFPP.CrossingBridge

end OAI
