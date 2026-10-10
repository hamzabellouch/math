import OAI.Combinatorics.BalancedRyser.Candidates.Candidates
import OAI.Combinatorics.BalancedRyser.Construction.ValidChoice
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence

namespace OAI

namespace Balanced.CandidateValidityWitness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def SuccessfulOn (M : MergedPairs F) (T : FourTuple F) (S : Line F) : Prop :=
  Function.Injective T.generator ∧ (∀ i, T.generator i ≠ S.1) ∧
  Function.Injective (tuplePoint M T) ∧ (∀ i, OnLine (tuplePoint M T i) S)

def PairWitness (M : MergedPairs F) (d : Direction F) (x y : Point F) : Prop :=
  ∃ s : Bool, OnLine x (constituent M d s) ∧
    OnLine y (constituent M d (!s))

omit [Fintype F] [DecidableEq F] in
theorem adjacent_iff_witness (M : MergedPairs F) (S : Line F) (x y : Point F) :
    Adjacent M S x y ↔ OnLine x S ∧ OnLine y S ∧ x ≠ y ∧
      ∃ d, d ≠ S.1 ∧ PairWitness M d x y := by
  constructor
  · rintro ⟨hx, hy, hne, d, hd, h⟩
    refine ⟨hx, hy, hne, d, hd, ?_⟩
    rcases h with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨hx, hy, hne, d, hd, s, hxs, hys⟩
    refine ⟨hx, hy, hne, d, hd, ?_⟩
    cases s
    · exact Or.inl ⟨hxs, hys⟩
    · exact Or.inr ⟨hxs, hys⟩

omit [Fintype F] [DecidableEq F] in
private theorem target_constituent_intersection_unique
    {M : MergedPairs F} {S : Line F} {d : Direction F} {s : Bool}
    (hd : d ≠ S.1) {x y : Point F}
    (hx : OnLine x S) (hy : OnLine y S)
    (hxd : OnLine x (constituent M d s))
    (hyd : OnLine y (constituent M d s)) : x = y := by
  apply common_point_eq_of_lines_ne S (constituent M d s)
    (fun h => hd (congrArg Prod.fst h).symm) x y hx hxd hy hyd

private theorem previous_next (i : Fin 4) : (i + 3) + 1 = i := by
  fin_cases i <;> decide

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem adjacent_generators_ne {T : FourTuple F}
    (hT : Function.Injective T.generator) (i : Fin 4) :
    T.generator i ≠ T.generator (i + 1) := by
  intro h
  have hi := hT h
  fin_cases i <;> simp at hi

omit [Fintype F] [DecidableEq F] in

theorem purposeful_endpoints {M : MergedPairs F} {T : FourTuple F}
    (hT : Function.Injective T.generator) (i : Fin 4) :
    OnLine (tuplePoint M T i) (constituent M (T.generator i) (T.side i)) ∧
    OnLine (tuplePoint M T (i + 3))
      (constituent M (T.generator i) (!(T.side i))) := by
  constructor
  · exact onLine_lineIntersection_left _ _ (adjacent_generators_ne hT i)
  · have h := onLine_lineIntersection_right
      (constituent M (T.generator (i + 3)) (T.side (i + 3)))
      (constituent M (T.generator ((i + 3) + 1)) (!(T.side ((i + 3) + 1))))
      (adjacent_generators_ne hT (i + 3))
    simpa only [tuplePoint, previous_next] using h

omit [Fintype F] [DecidableEq F] in

theorem used_constituents_distinct {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) (i : Fin 4) :
    M (T.generator i) false ≠ M (T.generator i) true := by
  intro heq
  have hend := purposeful_endpoints (M := M) h.1 i
  have hlines : constituent M (T.generator i) (T.side i) =
      constituent M (T.generator i) (!(T.side i)) := by
    cases T.side i <;> simp [constituent, heq]
  have hp := target_constituent_intersection_unique (h.2.1 i)
    (h.2.2.2 i) (h.2.2.2 (i + 3)) hend.1 (hlines.symm ▸ hend.2)
  have hi := h.2.2.1 hp
  fin_cases i <;> simp at hi

omit [Fintype F] [DecidableEq F] in

theorem on_used_constituent_endpoint {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) (i : Fin 4) (s : Bool)
    {x : Point F} (hx : OnLine x S)
    (hxd : OnLine x (constituent M (T.generator i) s)) :
    x = tuplePoint M T i ∨ x = tuplePoint M T (i + 3) := by
  have hend := purposeful_endpoints (M := M) h.1 i
  by_cases hs : s = T.side i
  · left
    exact target_constituent_intersection_unique (h.2.1 i) hx (h.2.2.2 i)
      (hs ▸ hxd) hend.1
  · have hs' : s = !(T.side i) := Bool.eq_not_of_ne hs
    right
    exact target_constituent_intersection_unique (h.2.1 i) hx (h.2.2.2 (i + 3))
      (hs' ▸ hxd) hend.2

omit [Fintype F] in

theorem external_not_on_used_constituent {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) {x : Point F}
    (hx : OnLine x S) (hex : x ∉ designated M ⟨S, T⟩)
    (i : Fin 4) (s : Bool) :
    ¬ OnLine x (constituent M (T.generator i) s) := by
  intro hxd
  rcases on_used_constituent_endpoint h i s hx hxd with he | he
  · exact hex (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩)
  · exact hex (Finset.mem_image.mpr ⟨i + 3, Finset.mem_univ _, he.symm⟩)

omit [Fintype F] in

theorem opposite_witness_not_generator {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) (i : Fin 4) {d : Direction F}
    (hw : PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2))) :
    d ∉ generatorSet T := by
  intro hd
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨s, hs, ht⟩ := hw
  have hi := on_used_constituent_endpoint h j s (h.2.2.2 i) hs
  have hi' := on_used_constituent_endpoint h j (!s) (h.2.2.2 (i + 2)) ht
  have ha : i = j ∨ i = j + 3 := hi.imp (fun he => h.2.2.1 he) (fun he => h.2.2.1 he)
  have hb : i + 2 = j ∨ i + 2 = j + 3 := hi'.imp (fun he => h.2.2.1 he) (fun he => h.2.2.1 he)
  fin_cases i <;> fin_cases j <;> simp_all

omit [Fintype F] in

theorem external_witness_not_generator {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) {x y : Point F}
    (hx : OnLine x S) (hex : x ∉ designated M ⟨S, T⟩) {d : Direction F}
    (hw : PairWitness M d x y) : d ∉ generatorSet T := by
  intro hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨s, hs, _⟩ := hw
  exact external_not_on_used_constituent h hx hex i s hs

omit [Fintype F] [DecidableEq F] in

theorem pairWitness_partner_unique {M : MergedPairs F} {S : Line F}
    {d : Direction F} (hd : d ≠ S.1) {x y z : Point F}
    (hx : OnLine x S) (hy : OnLine y S) (hz : OnLine z S)
    (hne : x ≠ y) (hxy : PairWitness M d x y) (hxz : PairWitness M d x z) :
    y = z := by
  obtain ⟨s, hxs, hys⟩ := hxy
  obtain ⟨t, hxt, hzt⟩ := hxz
  cases s <;> cases t
  · exact target_constituent_intersection_unique hd hy hz hys hzt
  · exact False.elim (hne (target_constituent_intersection_unique hd hx hy hxt hys))
  · exact False.elim (hne (target_constituent_intersection_unique hd hx hy hxt hys))
  · exact target_constituent_intersection_unique hd hy hz hys hzt

omit [Fintype F] in

theorem external_witness_directions_distinct {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) {x : Point F}
    (hx : OnLine x S) (hex : x ∉ designated M ⟨S, T⟩)
    {i j : Fin 4} (hij : i ≠ j) {d e : Direction F}
    (hd : d ≠ S.1) (hi : PairWitness M d x (tuplePoint M T i))
    (hj : PairWitness M e x (tuplePoint M T j)) : d ≠ e := by
  intro hde
  subst e
  have hne : x ≠ tuplePoint M T i := by
    intro he
    exact hex (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩)
  exact hij (h.2.2.1 (pairWitness_partner_unique hd hx
    (h.2.2.2 i) (h.2.2.2 j) hne hi hj))

def OppositeWitness (M : MergedPairs F) (T : FourTuple F) (S : Line F) : Prop :=
  ∃ (i : Fin 4) (d : Direction F), d ≠ S.1 ∧ d ∉ generatorSet T ∧
    PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2))

def ExternalDoubleWitness (M : MergedPairs F) (T : FourTuple F) (S : Line F) : Prop :=
  ∃ (x : Point F) (i j : Fin 4) (d e : Direction F),
    OnLine x S ∧ x ∉ designated M ⟨S, T⟩ ∧ i ≠ j ∧ d ≠ e ∧
    d ≠ S.1 ∧ e ≠ S.1 ∧ d ∉ generatorSet T ∧ e ∉ generatorSet T ∧
    PairWitness M d x (tuplePoint M T i) ∧
    PairWitness M e x (tuplePoint M T j)

theorem not_valid_has_bounded_witness {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S)
    (hnot : ¬ ValidChoice M S.1 ⟨S, T⟩) :
    S ∈ constituentLines M ∨ OppositeWitness M T S ∨ ExternalDoubleWitness M T S := by
  classical
  by_cases hS : S ∈ constituentLines M
  · exact Or.inl hS
  right
  have hopp (i : Fin 4)
      (ha : Adjacent M S (tuplePoint M T i) (tuplePoint M T (i + 2))) :
      OppositeWitness M T S := by
    obtain ⟨_, _, _, d, hd, hw⟩ := (adjacent_iff_witness M S _ _).mp ha
    exact ⟨i, d, hd, opposite_witness_not_generator h i hw, hw⟩
  by_cases h0 : Adjacent M S (tuplePoint M T 0) (tuplePoint M T 2)
  · exact Or.inl (hopp 0 h0)
  by_cases h1 : Adjacent M S (tuplePoint M T 1) (tuplePoint M T 3)
  · exact Or.inl (hopp 1 h1)
  right
  by_contra hE
  apply hnot
  refine ⟨rfl, hS, h.1, h.2.1, h.2.2.1, h.2.2.2, h0, h1, ?_⟩
  intro x hx hex
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hai := (Finset.mem_filter.mp hi).2
  have haj := (Finset.mem_filter.mp hj).2
  obtain ⟨_, _, _, d, hd, hdi⟩ := (adjacent_iff_witness M S _ _).mp hai
  obtain ⟨_, _, _, e, he, hej⟩ := (adjacent_iff_witness M S _ _).mp haj
  exact hE ⟨x, i, j, d, e, hx, hex, hij,
    external_witness_directions_distinct h hx hex hij hd hdi hej,
    hd, he, external_witness_not_generator h hx hex hdi,
    external_witness_not_generator h hx hex hej, hdi, hej⟩

theorem bounded_witness_not_valid {M : MergedPairs F} {T : FourTuple F}
    {S : Line F}
    (hw : S ∈ constituentLines M ∨ OppositeWitness M T S ∨ ExternalDoubleWitness M T S) :
    ¬ ValidChoice M S.1 ⟨S, T⟩ := by
  intro hv
  rcases hw with hS | ho | he
  · exact hv.2.1 hS
  · obtain ⟨i, d, hd, _, hw⟩ := ho
    have hne : tuplePoint M T i ≠ tuplePoint M T (i + 2) := by
      intro heq
      have hi := hv.2.2.2.2.1 heq
      fin_cases i <;> simp at hi
    have hadj := (adjacent_iff_witness M S _ _).mpr
      ⟨hv.2.2.2.2.2.1 i, hv.2.2.2.2.2.1 (i + 2), hne, d, hd, hw⟩
    exact SplitGeometry.valid_no_opposite hv i hadj
  · obtain ⟨x, i, j, d, e, hx, hex, hij, _, hd, he, _, _, hdi, hej⟩ := he
    have hne (k : Fin 4) : x ≠ tuplePoint M T k := by
      intro heq
      exact hex (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, heq.symm⟩)
    have hai := (adjacent_iff_witness M S _ _).mpr
      ⟨hx, hv.2.2.2.2.2.1 i, hne i, d, hd, hdi⟩
    have haj := (adjacent_iff_witness M S _ _).mpr
      ⟨hx, hv.2.2.2.2.2.1 j, hne j, e, he, hej⟩
    exact hij (SplitGeometry.valid_external_unique hv x hx hex i j hai haj)

theorem not_valid_iff_bounded_witness {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) :
    ¬ ValidChoice M S.1 ⟨S, T⟩ ↔
      S ∈ constituentLines M ∨ OppositeWitness M T S ∨ ExternalDoubleWitness M T S :=
  ⟨not_valid_has_bounded_witness h, bounded_witness_not_valid⟩

omit [Field F] in

theorem constituent_target_iff (M : MergedPairs F) (S : Line F) :
    S ∈ constituentLines M ↔ ∃ s : Bool, S = constituent M S.1 s := by
  constructor
  · intro hS
    obtain ⟨⟨d, s⟩, _, h⟩ := Finset.mem_image.mp hS
    have hd : d = S.1 := congrArg Prod.fst h
    exact ⟨s, by simpa only [hd] using h.symm⟩
  · rintro ⟨s, hs⟩
    exact Finset.mem_image.mpr ⟨(S.1, s), Finset.mem_univ _, hs.symm⟩

end Balanced.CandidateValidityWitness

end OAI
