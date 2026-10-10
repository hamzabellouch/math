import OAI.Combinatorics.Ramsey.CycleClique.Construction.BallSeparation
import OAI.Combinatorics.Ramsey.CycleClique.Construction.Reduction

namespace OAI

/-! The neighbourhood inclusions and cardinal growth in Lemma `finite:ball-bounds`. -/

namespace CycleClique.Construction
variable {V : Type*} [Fintype V]

noncomputable def outsideBallFinset (G : SimpleGraph V) (X : Finset V)
    (x : V) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ∈ OutsideBall G (X : Set V) x r)

@[simp] theorem mem_outsideBallFinset {G : SimpleGraph V} {X : Finset V}
    {x v : V} {r : ℕ} :
    v ∈ outsideBallFinset G X x r ↔ v ∈ OutsideBall G (X : Set V) x r := by
  classical
  simp [outsideBallFinset]

theorem outsideBallFinset_mono {G : SimpleGraph V} {X : Finset V} {x : V}
    {r s : ℕ} (hrs : r ≤ s) :
    outsideBallFinset G X x r ⊆ outsideBallFinset G X x s := by
  intro v hv
  exact mem_outsideBallFinset.mpr (OutsideBall.mono hrs (mem_outsideBallFinset.mp hv))

omit [Fintype V] in
theorem outsideBall_step {G : SimpleGraph V} {X : Set V} {x u v : V} {r : ℕ}
    (hu : u ∈ OutsideBall G X x r) (hv : v ∉ X) (hadj : G.Adj u v) :
    v ∈ OutsideBall G X x (r + 1) := by
  obtain ⟨huX, p, hp, hsupp⟩ := hu
  have hedge : (boundaryGraph G X).Adj u v := ⟨hadj, Or.inl huX⟩
  refine ⟨hv, p.concat hedge, ?_, ?_⟩
  · simp only [SimpleGraph.Walk.length_concat]
    omega
  · intro w hw hwX
    have : w ∈ p.support ∨ w = v := by simpa using hw
    rcases this with hw | rfl
    · exact hsupp w hw hwX
    · exact False.elim (hv hwX)

/-- A preceding-ball independent set can acquire outside neighbours only
in the next ball. Specified vertices in `X` can be excluded separately. -/
theorem closedNeighborhood_ball_subset [DecidableEq V] {G : SimpleGraph V} {X A I : Finset V}
    {x : V} {r : ℕ} (hI : I ⊆ outsideBallFinset G X x r)
    (havoid : ∀ v ∈ A, v ∉ closedNeighborhood G I) :
    closedNeighborhood G I ⊆ outsideBallFinset G X x (r + 1) ∪ (X \ A) := by
  classical
  intro v hv
  by_cases hvX : v ∈ X
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨hvX, fun hvA => havoid v hvA hv⟩)
  · apply Finset.mem_union_left
    apply mem_outsideBallFinset.mpr
    rcases mem_closedNeighborhood.mp hv with hvI | ⟨u, huI, huv⟩
    · exact OutsideBall.mono (Nat.le_succ r) (mem_outsideBallFinset.mp (hI hvI))
    · exact outsideBall_step (mem_outsideBallFinset.mp (hI huI)) hvX huv

/-- Additive form of the recursive lower bound, avoiding truncated
subtractions when the numerical bound is nonpositive. -/
theorem outsideBall_growth {G : SimpleGraph V} {k : ℕ} {X A I : Finset V}
    {x : V} {r : ℕ} (hAX : A ⊆ X)
    (hI : I ⊆ outsideBallFinset G X x r)
    (havoid : ∀ v ∈ A, v ∉ closedNeighborhood G I)
    (hexpand : k * I.card + 1 ≤ (closedNeighborhood G I).card) :
    k * I.card + 1 + A.card ≤ (outsideBallFinset G X x (r + 1)).card + X.card := by
  classical
  have hc := Finset.card_le_card (closedNeighborhood_ball_subset hI havoid)
  have hu := Finset.card_union_le (outsideBallFinset G X x (r + 1)) (X \ A)
  have hd := Finset.card_sdiff_add_card_eq_card hAX
  omega

/-- The initial radius-zero bound uses just the singleton expansion
and certified nonneighbours in `X`. -/
theorem outsideBall_initial_growth {G : SimpleGraph V} {k : ℕ}
    {X A : Finset V} {x : V} (hx : x ∈ X) (hAX : A ⊆ X) (hxA : x ∉ A)
    (hanti : ∀ v ∈ A, ¬ G.Adj x v)
    (hexpand : k + 1 ≤ (closedNeighborhood G {x}).card) :
    k + 1 + A.card ≤ (outsideBallFinset G X x 0).card + X.card := by
  classical
  have hsub : closedNeighborhood G {x} ⊆ outsideBallFinset G X x 0 ∪ (X \ A) := by
    intro v hv
    have hvA : v ∉ A := by
      intro hvA
      rcases mem_closedNeighborhood.mp hv with hvx | ⟨w, hw, h⟩
      · have : v = x := Finset.mem_singleton.mp hvx
        exact hxA (this ▸ hvA)
      · have : w = x := Finset.mem_singleton.mp hw
        exact hanti v hvA (this ▸ h)
    by_cases hvX : v ∈ X
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvX, hvA⟩)
    · apply Finset.mem_union_left
      apply mem_outsideBallFinset.mpr
      apply (outsideBall_zero hx).mpr
      refine ⟨?_, hvX⟩
      rcases mem_closedNeighborhood.mp hv with hvx | ⟨w, hw, h⟩
      · exact False.elim (hvX ((Finset.mem_singleton.mp hvx) ▸ hx))
      · exact (Finset.mem_singleton.mp hw) ▸ h
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (outsideBallFinset G X x 0) (X \ A)
  have hd := Finset.card_sdiff_add_card_eq_card hAX
  omega

/-- The prohibited short outside paths supply exactly the unavailable
vertices needed in the recursive growth estimate. -/
theorem closedNeighborhood_avoids_forbidden {G : SimpleGraph V} {X A I : Finset V}
    {x : V} {r : ℕ} (hx : x ∈ X) (hAX : A ⊆ X) (hxA : x ∉ A)
    (hI : I ⊆ outsideBallFinset G X x r)
    (hforbid : ∀ y ∈ A, ∀ d, 1 ≤ d → d ≤ r + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d) :
    ∀ y ∈ A, y ∉ closedNeighborhood G I := by
  intro y hy hclosed
  have hyX : y ∈ (X : Set V) := hAX hy
  rcases mem_closedNeighborhood.mp hclosed with hyI | ⟨v, hvI, hvy⟩
  · exact (mem_outsideBallFinset.mp (hI hyI)).1 hyX
  · exact singleton_outside_ball_separated hx hyX (fun h => hxA (h ▸ hy))
      (hforbid y hy) v (mem_outsideBallFinset.mp (hI hvI)) hvy

end CycleClique.Construction

end OAI
