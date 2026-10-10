import OAI.NumberTheory.DukePrimeDegree.Geometry.RowRootBox
import OAI.NumberTheory.DukePrimeDegree.Dynamics.UnipotentFreeness

namespace OAI

/-!
# Row-root boxes around arbitrary compact orbit pieces

Almost every lattice has a free row-group orbit. Every compact piece of
such an orbit therefore lies in one row-root box, by the local covering
map and the compact tube lemma. This allows conditional measures from
bounded boxes to be compared on arbitrarily large leaf neighborhoods.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rowRoot_injective {n : ℕ} (i : Fin n) : Function.Injective (rowRoot i) := by
  intro a b h
  apply Subtype.ext
  ext j
  have he := congrArg (fun g : G n => g.val i j) h
  simp only [rowRoot, rootRowElement_entry, ite_true] at he
  exact add_left_cancel he

theorem ae_rowRoot_stabilizer_trivial
    (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ (i : Fin (d + 1)) (a : RowTime i),
      rightAction x (rowRoot i a) = x → a = 0 := by
  filter_upwards [ae_no_coordinate_zero d μ hA] with x hx i a hfix
  apply rowRoot_injective i
  rw [rowRoot_zero]
  apply stabilizer_trivial_of_identity_column x hx _ hfix i
  intro r
  change (rootRowElement i a.val (rowTime_self a)).val r i = _
  simp only [rootRowElement_entry, rowTime_self, ite_self, add_zero]

lemma rowQuotientParametrization_injective_of_free {n : ℕ} (i k : Fin n)
    (s : RowRootSlice i k) (a : RowTime i)
    (hfree : ∀ b : RowTime i,
      rightAction (rowQuotientParametrization i k (s, a)) (rowRoot i b) =
        rowQuotientParametrization i k (s, a) → b = 0) :
    Function.Injective (fun t : RowTime i => rowQuotientParametrization i k (s, t)) := by
  intro t u heq
  have h := congrArg (fun x => rightAction x (rowRoot i (a - u))) heq
  rw [← rowQuotientParametrization_add, ← rowQuotientParametrization_add] at h
  have ht : t + (a - u) = a + (t - u) := by abel
  have hu : u + (a - u) = a := by abel
  rw [ht, hu, rowQuotientParametrization_add] at h
  exact sub_eq_zero.mp (hfree (t - u) h)

theorem rowRootBox_contains_compact_time {n : ℕ} (i k : Fin n)
    (s : RowRootSlice i k)
    (hinj : Function.Injective (fun t : RowTime i => rowQuotientParametrization i k (s, t)))
    (K : Set (RowTime i)) (hK : IsCompact K) :
    ∃ B : RowRootBox i k, s ∈ B.transverse ∧ K ⊆ B.time := by
  have hf := rowQuotientParametrization_localHomeomorph i k
  have hi : Set.InjOn (rowQuotientParametrization i k) ({s} ×ˢ K) := by
    rintro ⟨s₁, t₁⟩ ⟨hs₁, _⟩ ⟨s₂, t₂⟩ ⟨hs₂, _⟩ heq
    have h₁ : s₁ = s := hs₁
    have h₂ : s₂ = s := hs₂
    subst s₁
    subst s₂
    exact Prod.ext rfl (hinj heq)
  obtain ⟨W, hW, hKW, hemb⟩ := compact_injective_localHomeomorph_neighborhood hf
    (isCompact_singleton.prod hK) hi
  obtain ⟨U, V, hU, hV, hsU, hTV, hUV⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({s} : Set (RowRootSlice i k))) hK hW hKW
  have he := hemb.comp (Topology.IsOpenEmbedding.inclusion hUV
    ((hU.prod hV).preimage continuous_subtype_val))
  exact ⟨⟨U, V, hU, hV, he⟩, hsU (Set.mem_singleton s), hTV⟩

theorem rowRootBox_arbitrary_compact_of_free {n : ℕ} (i : Fin n)
    (x : X n) (hfree : ∀ a : RowTime i, rightAction x (rowRoot i a) = x → a = 0)
    (K : Set (RowTime i)) (hK : IsCompact K) :
    ∃ (k : Fin n) (B : RowRootBox i k) (s : RowRootSlice i k) (a : RowTime i),
      s ∈ B.transverse ∧ a ∈ B.time ∧ K ⊆ B.time ∧
        rowQuotientParametrization i k (s, a) = x := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨k, hk⟩ := exists_rootPivot i g
    let p : RootPivot i k := ⟨g, hk⟩
    let z := rowPivotHomeomorph i k p
    have hz : rowQuotientParametrization i k z = Quotient.mk _ g := by
      change Quotient.mk _ ((rowPivotHomeomorph i k).symm (rowPivotHomeomorph i k p)).val = _
      rw [(rowPivotHomeomorph i k).symm_apply_apply]
    have hinj := rowQuotientParametrization_injective_of_free i k z.1 z.2
      (fun b hb => hfree b (by simpa only [hz] using hb))
    obtain ⟨B, hs, hKB⟩ := rowRootBox_contains_compact_time i k z.1 hinj
      (K ∪ {z.2}) (hK.union isCompact_singleton)
    exact ⟨k, B, z.1, z.2, hs, hKB (Or.inr rfl), fun _ h => hKB (Or.inl h), hz⟩

end DukePrimeDegree

end

end OAI
