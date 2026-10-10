import Mathlib

namespace OAI

noncomputable section

open Set Function
open scoped Uniformity

namespace Problem340
namespace PeriodicEntropy

variable {X : Type*} {T : X → X} {k : ℕ}

theorem dynEntourage_period_subset (hk : 0 < k) (hperiod : T^[k] = id)
    (U : Set (X × X)) (n : ℕ) :
    Dynamics.dynEntourage T U k ⊆ Dynamics.dynEntourage T U n := by
  rintro ⟨x, y⟩ hxy
  rw [Dynamics.mem_dynEntourage] at hxy ⊢
  intro j _
  have hx : IsPeriodicPt T k x := by simp [IsPeriodicPt, IsFixedPt, hperiod]
  have hy : IsPeriodicPt T k y := by simp [IsPeriodicPt, IsFixedPt, hperiod]
  simpa only [hx.iterate_mod_apply j, hy.iterate_mod_apply j] using
    hxy (j % k) (Nat.mod_lt j hk)

theorem dynEntourage_eq_period (hk : 0 < k) (hperiod : T^[k] = id)
    (U : Set (X × X)) {n : ℕ} (hn : k ≤ n) :
    Dynamics.dynEntourage T U n = Dynamics.dynEntourage T U k :=
  Set.Subset.antisymm (Dynamics.dynEntourage_antitone T U hn)
    (dynEntourage_period_subset hk hperiod U n)

theorem isDynCoverOf_all_of_period (hk : 0 < k) (hperiod : T^[k] = id)
    {U : Set (X × X)} {F s : Set X}
    (hs : Dynamics.IsDynCoverOf T F U k s) (n : ℕ) :
    Dynamics.IsDynCoverOf T F U n s :=
  hs.mono_entourage (dynEntourage_period_subset hk hperiod U n)

theorem coverEntropy_eq_zero_of_period [UniformSpace X] [CompactSpace X] [Nonempty X]
    (hk : 0 < k) (hperiod : T^[k] = id) :
    Dynamics.coverEntropy T (Set.univ : Set X) = 0 := by
  apply le_antisymm _ (Dynamics.coverEntropy_nonneg T Set.univ_nonempty)
  unfold Dynamics.coverEntropy
  refine iSup₂_le fun U hU => ?_
  obtain ⟨s, hs⟩ := Dynamics.exists_isDynCoverOf_of_isCompact_invariant
    isCompact_univ (Set.mapsTo_univ T Set.univ) hU k
  have hspos : 0 < s.card := Finset.card_pos.mpr (hs.nonempty Set.univ_nonempty)
  have hbound : ∀ n, Dynamics.coverMincard T Set.univ U n ≤ (s.card : ℕ∞) :=
    fun n => (isDynCoverOf_all_of_period hk hperiod hs n).coverMincard_le_card
  unfold Dynamics.coverEntropyEntourage
  calc
    ExpGrowth.expGrowthSup (fun n =>
        (Dynamics.coverMincard T Set.univ U n).toENNReal) ≤
        ExpGrowth.expGrowthSup (fun _ : ℕ => ((s.card : ℕ∞).toENNReal)) :=
      ExpGrowth.expGrowthSup_monotone (fun n => ENat.toENNReal_mono (hbound n))
    _ = 0 := ExpGrowth.expGrowthSup_const (by exact_mod_cast hspos.ne') (by simp)

theorem coverEntropy_eq_zero_on_periodicSet [UniformSpace X]
    {F : Set X} (hcompact : IsCompact F) (hne : F.Nonempty)
    (hinv : Set.MapsTo T F F) (hk : 0 < k)
    (hperiod : ∀ x ∈ F, T^[k] x = x) :
    Dynamics.coverEntropy T F = 0 := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hcompact
  let : Nonempty F := hne.to_subtype
  rw [← Dynamics.coverEntropy_restrict hinv]
  apply coverEntropy_eq_zero_of_period hk
  funext x
  apply Subtype.ext
  simpa only [Set.MapsTo.iterate_restrict, Set.MapsTo.val_restrict_apply, id_eq] using
    hperiod x x.property

end PeriodicEntropy
end Problem340

end

end OAI
