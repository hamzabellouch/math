import OAI.Combinatorics.InfiniteMatroid.DoubleRay

namespace OAI

section
open Set Filter Matroid
namespace InfiniteMatroidCounterexample

def raySlice {α : Type*} (I : Set (ℤ × α)) (n : ℤ) (b : Bool) : Set α :=
  {d | (d,b) ∈ assignment I n}

lemma raySlice_central {α : Type*} (I : Set (ℤ × α)) :
    raySlice I (-1) false = (raySlice I 0 false)ᶜ := by
  ext d
  simp [raySlice,assignment,bundleAt]

lemma raySlice_right {α : Type*} (I : Set (ℤ × α)) (n : ℤ) (hn : 0 ≤ n) :
    raySlice I (n+1) false = (raySlice I n true)ᶜ := by
  have hn0 : ¬ n < 0 := not_lt.mpr hn
  have hn1 : ¬ n+1 < 0 := by omega
  by_cases hp : n % 2 = 0
  · have hp' : ¬ (n+1) % 2 = 0 := by omega
    ext d
    simp [raySlice,assignment,bundleAt,hn0,hn1,hp,hp']
  · have hp' : (n+1) % 2 = 0 := by omega
    ext d
    simp [raySlice,assignment,bundleAt,hn0,hn1,hp,hp']

lemma raySlice_left {α : Type*} (I : Set (ℤ × α)) (n : ℤ) (hn : n < 0) :
    raySlice I (n-1) false = (raySlice I n true)ᶜ := by
  have hn1 : n-1 < 0 := by omega
  by_cases hp : n % 2 = 0
  · have hp' : ¬ (n-1) % 2 = 0 := by omega
    ext d
    simp [raySlice,assignment,bundleAt,hn,hn1,hp,hp']
  · have hp' : (n-1) % 2 = 0 := by omega
    ext d
    simp [raySlice,assignment,bundleAt,hn,hn1,hp,hp']

def rayVertex (left : Bool) (k : ℕ) : ℤ := if left then -(k : ℤ)-1 else (k : ℤ)

lemma raySlice_step {α : Type*} (I : Set (ℤ × α)) (left : Bool) (k : ℕ) :
    raySlice I (rayVertex left (k+1)) false = (raySlice I (rayVertex left k) true)ᶜ := by
  cases left with
  | false => simpa only [rayVertex,Bool.false_eq_true,ite_false,Nat.cast_add,Nat.cast_one] using
      raySlice_right I (k : ℤ) (Int.natCast_nonneg k)
  | true =>
    have he : rayVertex true (k+1) = rayVertex true k - 1 := by simp [rayVertex]; ring
    rw [he]
    exact raySlice_left I _ (by simp [rayVertex]; omega)

section Descent
variable {α β : Type*} [LinearOrder β] [WellFoundedLT β]
variable (Q : Matroid (α × Bool)) (U : Ultrafilter α) (ρ : Set α → β)
variable (hanti : ∀ ⦃X Y : Set α⦄, X ∈ U → Y ∈ U → X ⊆ Y → ρ Y ≤ ρ X)
variable (hbasis : ∀ B, Q.IsBase B → (Prod.mk · false) ⁻¹' B ∈ U →
  ((Prod.mk · true) ⁻¹' B)ᶜ ∈ U ∧ ρ ((Prod.mk · true) ⁻¹' B)ᶜ < ρ ((Prod.mk · false) ⁻¹' B))
include hanti hbasis

omit [WellFoundedLT β] in
lemma independent_rank_step {X : Set (α × Bool)} (hX : Q.Indep X)
    (hl : (Prod.mk · false) ⁻¹' X ∈ U) :
    ((Prod.mk · true) ⁻¹' X)ᶜ ∈ U ∧ ρ ((Prod.mk · true) ⁻¹' X)ᶜ < ρ ((Prod.mk · false) ⁻¹' X) := by
  obtain ⟨B,hB,hXB⟩ := hX.exists_isBase_superset
  have hlu : (Prod.mk · false) ⁻¹' B ∈ U := mem_of_superset hl (preimage_mono hXB)
  obtain ⟨hy,hlt⟩ := hbasis B hB hlu
  have hyx : ((Prod.mk · true) ⁻¹' B)ᶜ ⊆ ((Prod.mk · true) ⁻¹' X)ᶜ :=
    compl_subset_compl.mpr (preimage_mono hXB)
  have hr : ((Prod.mk · true) ⁻¹' X)ᶜ ∈ U := mem_of_superset hy hyx
  refine ⟨hr,?_⟩
  exact lt_of_le_of_lt (hanti hy hr hyx)
    (lt_of_lt_of_le hlt (hanti hl hlu (preimage_mono hXB)))

lemma no_independent_partition {I : Set (ℤ × α)} (h0 : (rayMatroid Q false).Indep I)
    (h1 : (rayMatroid Q true).Indep Iᶜ) : False := by
  have hstart : ∃ left : Bool, raySlice I (rayVertex left 0) false ∈ U := by
    by_cases hc : raySlice I 0 false ∈ U
    · exact ⟨false,hc⟩
    · refine ⟨true,?_⟩
      change raySlice I (-1) false ∈ U
      rw [raySlice_central]
      exact Ultrafilter.compl_mem_iff_notMem.mpr hc
  obtain ⟨left,hstart⟩ := hstart
  let x (k : ℕ) := raySlice I (rayVertex left k) false
  have hstep (k : ℕ) (hk : x k ∈ U) : x (k+1) ∈ U ∧ ρ (x (k+1)) < ρ (x k) := by
    have hi := assignment_indep Q h0 h1 (rayVertex left k)
    have hs := independent_rank_step Q U ρ hanti hbasis hi hk
    change (raySlice I (rayVertex left k) true)ᶜ ∈ U ∧
      ρ (raySlice I (rayVertex left k) true)ᶜ < ρ (x k) at hs
    simpa only [x,raySlice_step] using hs
  have hx : ∀ k, x k ∈ U := by
    intro k
    induction k with
    | zero => exact hstart
    | succ k ih => exact (hstep k ih).1
  have hd : ∀ k, ρ (x (k+1)) < ρ (x k) := fun k ↦ (hstep k (hx k)).2
  exact (wellFounded_iff_isEmpty_descending_chain.mp (wellFounded_lt (α := β))).false ⟨fun k ↦ ρ (x k),hd⟩

lemma no_independent_cover (I J : Set (ℤ × α))
    (hI : (rayMatroid Q false).Indep I) (hJ : (rayMatroid Q true).Indep J) : I ∪ J ≠ univ := by
  intro hcover
  have hIJ : Iᶜ ⊆ J := by
    intro x hx
    have hm : x ∈ I ∪ J := hcover.symm ▸ mem_univ x
    exact hm.resolve_left hx
  exact no_independent_partition Q U ρ hanti hbasis hI (hJ.subset hIJ)

end Descent
end InfiniteMatroidCounterexample
end

end OAI
