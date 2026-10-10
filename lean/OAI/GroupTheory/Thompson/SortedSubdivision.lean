import OAI.GroupTheory.Thompson.IntervalHomeomorph
import Mathlib.Data.Finset.Sort
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Sorting finite subdivisions of the unit interval

Sorting a finite set containing the endpoints produces a genuine subdivision.
If that set also contains the knots of an earlier subdivision, every new
closed piece is contained in an old closed piece.
-/

namespace ThompsonNonamenability

structure SortedSubdivision (S : Finset UnitInterval) where
  pieceCount : ℕ
  positive : 0 < pieceCount
  knots : Fin (pieceCount + 1) → UnitInterval
  strictMono_knots : StrictMono knots
  first : knots 0 = unitIntervalZero
  last : knots (Fin.last pieceCount) = unitIntervalOne
  cover : ∀ x : UnitInterval, ∃ i : Fin pieceCount,
    knots i.castSucc ≤ x ∧ x ≤ knots i.succ
  knots_mem : ∀ i, knots i ∈ S
  contains : ∀ x ∈ S, ∃ i, knots i = x

namespace SortedSubdivision

/-- The adjacent closed intervals cover the unit interval. Monotonicity is not
needed for this auxiliary fact: take the last left endpoint below the point. -/
theorem cover_of_endpoints {n : ℕ} (hn : 0 < n)
    (knots : Fin (n + 1) → UnitInterval)
    (hfirst : knots 0 = unitIntervalZero)
    (hlast : knots (Fin.last n) = unitIntervalOne) (x : UnitInterval) :
    ∃ i : Fin n, knots i.castSucc ≤ x ∧ x ≤ knots i.succ := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun i => knots i.castSucc ≤ x)
  let i₀ : Fin n := ⟨0, hn⟩
  have hi₀ : i₀.castSucc = 0 := by apply Fin.ext; rfl
  have hA : A.Nonempty := by
    refine ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hi₀, hfirst]
    exact x.property.1
  let i : Fin n := A.max' hA
  have hiA : i ∈ A := A.max'_mem hA
  refine ⟨i, (Finset.mem_filter.mp hiA).2, ?_⟩
  by_contra h
  have hlt : knots i.succ < x := lt_of_not_ge h
  have hisucc : i.val + 1 < n := by
    by_contra hbound
    have heq : i.succ = Fin.last n := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      have := i.isLt
      omega
    rw [heq, hlast] at hlt
    exact (not_lt_of_ge x.property.2) hlt
  let j : Fin n := ⟨i.val + 1, hisucc⟩
  have hjcast : j.castSucc = i.succ := by apply Fin.ext; rfl
  have hjA : j ∈ A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hjcast]
    exact hlt.le
  have hji : j ≤ i := A.le_max' j hjA
  change i.val + 1 ≤ i.val at hji
  omega

/-- Increasing enumeration of the actual finite knot set. -/
noncomputable def ofFinset (S : Finset UnitInterval)
    (h0 : unitIntervalZero ∈ S) (h1 : unitIntervalOne ∈ S) :
    SortedSubdivision S := by
  classical
  have hne : unitIntervalZero ≠ unitIntervalOne := by
    intro h
    have hv := congrArg (fun x : UnitInterval => (x : ℝ)) h
    exact zero_ne_one hv
  have hcard : 1 < S.card :=
    Finset.one_lt_card.mpr ⟨unitIntervalZero, h0, unitIntervalOne, h1, hne⟩
  let n := S.card - 1
  have hn : 0 < n := by dsimp [n]; omega
  have hc : S.card = n + 1 := by dsimp [n]; omega
  let e : Fin (n + 1) ↪o UnitInterval := S.orderEmbOfFin hc
  have hcontains : ∀ x ∈ S, ∃ i, e i = x := by
    intro x hx
    refine ⟨(S.orderIsoOfFin hc).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((S.orderIsoOfFin hc).apply_symm_apply ⟨x, hx⟩)
  have hfirst : e 0 = unitIntervalZero := by
    obtain ⟨j, hj⟩ := hcontains unitIntervalZero h0
    apply le_antisymm
    · calc
        e 0 ≤ e j := e.monotone (Fin.zero_le j)
        _ = unitIntervalZero := hj
    · exact (e 0).property.1
  have hlast : e (Fin.last n) = unitIntervalOne := by
    obtain ⟨j, hj⟩ := hcontains unitIntervalOne h1
    apply le_antisymm
    · exact (e (Fin.last n)).property.2
    · calc
        unitIntervalOne = e j := hj.symm
        _ ≤ e (Fin.last n) := e.monotone (Fin.le_last j)
  exact
    { pieceCount := n
      positive := hn
      knots := e
      strictMono_knots := e.strictMono
      first := hfirst
      last := hlast
      cover := cover_of_endpoints hn e hfirst hlast
      knots_mem := S.orderEmbOfFin_mem hc
      contains := hcontains }

/-- No point of the sorted knot set lies strictly between successive knots. -/
theorem no_mem_between {S : Finset UnitInterval} (r : SortedSubdivision S)
    (i : Fin r.pieceCount) {x : UnitInterval} (hx : x ∈ S) :
    ¬ (r.knots i.castSucc < x ∧ x < r.knots i.succ) := by
  obtain ⟨j, rfl⟩ := r.contains x hx
  intro h
  have hleft := r.strictMono_knots.lt_iff_lt.mp h.1
  have hright := r.strictMono_knots.lt_iff_lt.mp h.2
  change i.val < j.val at hleft
  change j.val < i.val + 1 at hright
  exact (not_lt_of_ge (Nat.succ_le_of_lt hleft)) hright

/-- A refinement containing every original knot has each closed piece inside
one original closed piece. The interior point selects a piece even when a
refined endpoint is itself an original knot. -/
theorem adjacent_contained {S : Finset UnitInterval} (r : SortedSubdivision S)
    {n : ℕ} (old : Fin (n + 1) → UnitInterval) (_hold : StrictMono old)
    (hcover : ∀ x : UnitInterval, ∃ j : Fin n,
      old j.castSucc ≤ x ∧ x ≤ old j.succ)
    (hmem : ∀ j, old j ∈ S) (i : Fin r.pieceCount) :
    ∃ j : Fin n, old j.castSucc ≤ r.knots i.castSucc ∧
      r.knots i.succ ≤ old j.succ := by
  have hlt : (r.knots i.castSucc : ℝ) < (r.knots i.succ : ℝ) :=
    r.strictMono_knots (Fin.castSucc_lt_succ_iff.mpr le_rfl)
  obtain ⟨y, hleft, hright⟩ := exists_between hlt
  let x : UnitInterval := ⟨y,
    (r.knots i.castSucc).property.1.trans hleft.le,
    hright.le.trans (r.knots i.succ).property.2⟩
  have hlx : r.knots i.castSucc < x := hleft
  have hxr : x < r.knots i.succ := hright
  obtain ⟨j, hjleft, hjright⟩ := hcover x
  refine ⟨j, ?_, ?_⟩
  · by_contra h
    exact r.no_mem_between i (hmem j.castSucc)
      ⟨lt_of_not_ge h, hjleft.trans_lt hxr⟩
  · by_contra h
    exact r.no_mem_between i (hmem j.succ)
      ⟨hlx.trans_le hjright, lt_of_not_ge h⟩

end SortedSubdivision

end ThompsonNonamenability

end OAI
