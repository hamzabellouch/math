import OAI.Analysis.MetricEntropy.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring

namespace OAI

universe uι uJ uX

/-!
# Finite covering numbers and the cube packing bound

Centers are arbitrary ambient vectors throughout. Attainment and lower bounds
explicitly assume a finite cover exists, because the natural-number infimum of
the empty set is zero. Compactness and a neighborhood of zero supply that
hypothesis in the geometric application.
-/

noncomputable section

namespace MetricEntropyDuality

open Set Filter
open scoped Topology

variable {ι : Type uι} {A A' B B' : Set (RealSpace ι)}

/-- A finite family can be enumerated without changing its centers or count. -/
theorem exists_fin_cover_of_fintype_cover {J : Type uJ} [Fintype J]
    (c : J → RealSpace ι) (hc : ∀ x ∈ A, ∃ j, x - c j ∈ B) :
    ∃ d : Fin (Fintype.card J) → RealSpace ι, Covers A B d := by
  classical
  let e := Fintype.equivFin J
  refine ⟨fun j => c (e.symm j), ?_⟩
  intro x hx
  obtain ⟨j, hj⟩ := hc x hx
  exact ⟨e j, by simpa only [Equiv.symm_apply_apply] using hj⟩

/-- Enumerate a finite set of indices, retaining exactly its cardinality. -/
theorem exists_finset_cover {J : Type uJ} (s : Finset J)
    (c : J → RealSpace ι) (hc : ∀ x ∈ A, ∃ j ∈ s, x - c j ∈ B) :
    ∃ d : Fin s.card → RealSpace ι, Covers A B d := by
  classical
  refine ⟨fun j => c (s.equivFin.symm j), ?_⟩
  intro x hx
  obtain ⟨j, hj, hcov⟩ := hc x hx
  exact ⟨s.equivFin ⟨j, hj⟩, by simpa only [Equiv.symm_apply_apply] using hcov⟩

/-- Every actual finite cover bounds the literal natural infimum. -/
theorem coveringNumber_le_of_covers {M : ℕ} {c : Fin M → RealSpace ι}
    (hc : Covers A B c) : coveringNumber A B ≤ M :=
  Nat.sInf_le ⟨c, hc⟩

theorem coveringNumber_attained (hfin : Coverable A B) :
    ∃ c : Fin (coveringNumber A B) → RealSpace ι, Covers A B c := by
  exact Nat.sInf_mem hfin

/-- A lower bound on every finite cover bounds the actual minimum. -/
theorem le_coveringNumber {k : ℕ} (hfin : Coverable A B)
    (h : ∀ (M : ℕ) (c : Fin M → RealSpace ι), Covers A B c → k ≤ M) :
    k ≤ coveringNumber A B := by
  obtain ⟨c, hc⟩ := coveringNumber_attained hfin
  exact h _ c hc

theorem coveringNumber_pos (hne : A.Nonempty) (hfin : Coverable A B) :
    0 < coveringNumber A B := by
  obtain ⟨c, hc⟩ := coveringNumber_attained hfin
  obtain ⟨x, hx⟩ := hne
  obtain ⟨j, _⟩ := hc x hx
  exact lt_of_le_of_lt (Nat.zero_le j.val) j.isLt

theorem Covers.mono_left {M : ℕ} {c : Fin M → RealSpace ι}
    (hc : Covers A B c) (hA : A' ⊆ A) : Covers A' B c := by
  intro x hx
  exact hc x (hA hx)

theorem Covers.mono_right {M : ℕ} {c : Fin M → RealSpace ι}
    (hc : Covers A B c) (hB : B ⊆ B') : Covers A B' c := by
  intro x hx
  obtain ⟨j, hj⟩ := hc x hx
  exact ⟨j, hB hj⟩

theorem Coverable.mono_left (hfin : Coverable A B) (hA : A' ⊆ A) :
    Coverable A' B := by
  obtain ⟨M, c, hc⟩ := hfin
  exact ⟨M, c, hc.mono_left hA⟩

theorem Coverable.mono_right (hfin : Coverable A B) (hB : B ⊆ B') :
    Coverable A B' := by
  obtain ⟨M, c, hc⟩ := hfin
  exact ⟨M, c, hc.mono_right hB⟩

theorem coveringNumber_mono_left (hA : A' ⊆ A) (hfin : Coverable A B) :
    coveringNumber A' B ≤ coveringNumber A B := by
  obtain ⟨c, hc⟩ := coveringNumber_attained hfin
  exact coveringNumber_le_of_covers (hc.mono_left hA)

theorem coveringNumber_mono_right (hB : B ⊆ B') (hfin : Coverable A B) :
    coveringNumber A B' ≤ coveringNumber A B := by
  obtain ⟨c, hc⟩ := coveringNumber_attained hfin
  exact coveringNumber_le_of_covers (hc.mono_right hB)

/-- Translates of any neighborhood of zero finitely cover a compact set. -/
theorem coverable_of_isCompact_of_mem_nhds_zero (hA : IsCompact A)
    (hB : B ∈ 𝓝 (0 : RealSpace ι)) : Coverable A B := by
  classical
  let U : RealSpace ι → Set (RealSpace ι) := fun x => {y | y - x ∈ B}
  have hU : ∀ x ∈ A, U x ∈ 𝓝 x := by
    intro x _
    have hc : ContinuousAt (fun y : RealSpace ι => y - x) x :=
      continuousAt_id.sub continuousAt_const
    exact hc.preimage_mem_nhds (by simpa only [sub_self] using hB)
  obtain ⟨s, _, hs⟩ := hA.elim_nhds_subcover U hU
  have hcov : ∀ x ∈ A, ∃ j ∈ s, x - j ∈ B := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hjs, hmem⟩ := Set.mem_iUnion.mp hj
    exact ⟨j, hjs, hmem⟩
  obtain ⟨c, hc⟩ := exists_finset_cover s (fun x => x) hcov
  exact ⟨s.card, c, hc⟩

/-- The coordinate cube is a neighborhood of zero in a finite product. -/
theorem cube_mem_nhds_zero [Finite ι] : cube ι ∈ 𝓝 (0 : RealSpace ι) := by
  let U : Set (RealSpace ι) := ⋂ i, {x | |x i| < 1}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_abs.comp (continuous_apply i)) continuous_const
  have hzero : (0 : RealSpace ι) ∈ U := by
    simp [U]
  apply Filter.mem_of_superset (hU.mem_nhds hzero)
  intro x hx i
  exact (Set.mem_iInter.mp hx i).le

theorem coverable_cube_of_isCompact [Finite ι] (hA : IsCompact A) :
    Coverable A (cube ι) :=
  coverable_of_isCompact_of_mem_nhds_zero hA cube_mem_nhds_zero

/-- A cube translate has coordinate diameter at most two, for any center. -/
theorem cube_translate_diameter {x y z : RealSpace ι}
    (hx : x - z ∈ cube ι) (hy : y - z ∈ cube ι) (i : ι) :
    |x i - y i| ≤ 2 := by
  have hx' : |x i - z i| ≤ 1 := hx i
  have hy' : |y i - z i| ≤ 1 := hy i
  calc
    |x i - y i| = |(x i - z i) - (y i - z i)| := by congr 1; ring
    _ ≤ |x i - z i| + |y i - z i| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add hx' hy'
    _ = 2 := by norm_num

/-- Distinct points separated by more than two cannot share a cube translate. -/
theorem card_le_of_covers_cube {X : Type uX} [Fintype X]
    (p : X → RealSpace ι) (hp : ∀ x, p x ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ i, 2 < |p x i - p y i|)
    {M : ℕ} {c : Fin M → RealSpace ι} (hc : Covers A (cube ι) c) :
    Fintype.card X ≤ M := by
  classical
  choose j hj using fun x => hc (p x) (hp x)
  have hinj : Function.Injective j := by
    intro x y hxy
    by_contra hne
    obtain ⟨i, hi⟩ := hsep x y hne
    have hy : p y - c (j x) ∈ cube ι := by rw [hxy]; exact hj y
    exact (not_lt_of_ge (cube_translate_diameter (hj x) hy i)) hi
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective j hinj

/-- Packing lower bound for the genuine least number of arbitrary translates. -/
theorem card_le_coveringNumber_cube {X : Type uX} [Fintype X]
    (p : X → RealSpace ι) (hp : ∀ x, p x ∈ A)
    (hsep : ∀ x y, x ≠ y → ∃ i, 2 < |p x i - p y i|)
    (hfin : Coverable A (cube ι)) :
    Fintype.card X ≤ coveringNumber A (cube ι) := by
  obtain ⟨c, hc⟩ := coveringNumber_attained hfin
  exact card_le_of_covers_cube p hp hsep hc

end MetricEntropyDuality

end

end OAI
