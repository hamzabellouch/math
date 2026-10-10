import Mathlib

namespace OAI


noncomputable section

namespace Problem355.PlaneLines

open scoped LinearAlgebra.Projectivization

variable {K V A : Type*} [Field K] [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup A]

omit [FiniteDimensional K V] in

theorem card_lines (hV : Module.finrank K V = 2) :
    Nat.card (ℙ K V) = Nat.card K + 1 :=
  Projectivization.card_of_finrank_two K V hV

theorem line_index (hV : Module.finrank K V = 2) (p : ℙ K V) :
    p.submodule.toAddSubgroup.index = Nat.card K := by
  have hp : Nat.card p.submodule = Nat.card K := by
    rw [Module.natCard_eq_pow_finrank (K := K), p.finrank_submodule, pow_one]
  have hcardV : Nat.card V = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hV]
  have hindex := p.submodule.toAddSubgroup.card_mul_index
  change Nat.card p.submodule * p.submodule.toAddSubgroup.index = Nat.card V at hindex
  rw [hp, hcardV, pow_two] at hindex
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hindex

theorem line_preimage_index (hV : Module.finrank K V = 2)
    (f : A →+ V) (hf : Function.Surjective f) (p : ℙ K V) :
    (p.submodule.toAddSubgroup.comap f).index = Nat.card K := by
  rw [AddSubgroup.index_comap_of_surjective _ hf]
  exact line_index hV p

omit [Finite K] in

theorem exists_line_containing (hV : Module.finrank K V = 2)
    (W : Submodule K V) (hW : Module.finrank K W ≤ 1) :
    ∃ p : ℙ K V, W ≤ p.submodule := by
  by_cases hzero : Module.finrank K W = 0
  · have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K V)
    obtain ⟨p⟩ : Nonempty (ℙ K V) := inferInstance
    exact ⟨p, by rw [Submodule.finrank_eq_zero.mp hzero]; exact bot_le⟩
  · have hone : Module.finrank K W = 1 := by omega
    exact ⟨Projectivization.mk'' W hone, by simp⟩

omit [Finite K] in

theorem exists_line_containing_rows {κ : Type*} (hV : Module.finrank K V = 2)
    (rows : κ → V)
    (hrows : Module.finrank K (Submodule.span K (Set.range rows)) ≤ 1) :
    ∃ p : ℙ K V, ∀ i, rows i ∈ p.submodule := by
  obtain ⟨p, hp⟩ := exists_line_containing hV (Submodule.span K (Set.range rows)) hrows
  exact ⟨p, fun i => hp (Submodule.subset_span (Set.mem_range_self i))⟩

def normalMap (x : Fin 3 → K) : (Fin 3 → K) →ₗ[K] K := dotProductBilin K K x

omit [Finite K] in

theorem normalMap_surjective (x : Fin 3 → K) (hx : x ≠ 0) :
    Function.Surjective (normalMap x) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    apply hx
    funext i
    exact h i
  intro a
  refine ⟨Pi.single i (a / x i), ?_⟩
  change dotProduct x (Pi.single i (a / x i)) = a
  rw [dotProduct_single]
  field_simp

omit [Finite K] in

theorem normal_plane_finrank (x : Fin 3 → K) (hx : x ≠ 0) :
    Module.finrank K (normalMap x).ker = 2 := by
  have h := (normalMap x).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (normalMap_surjective x hx),
    finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at h
  norm_num at h
  omega

theorem card_normal_plane_lines (x : Fin 3 → K) (hx : x ≠ 0) :
    Nat.card (ℙ K (normalMap x).ker) = Nat.card K + 1 :=
  card_lines (normal_plane_finrank x hx)

def lineRows {κ : Type*} (s : Finset (κ → V)) (p : ℙ K V) : Finset (κ → V) := by
  classical
  exact s.filter fun rows => ∀ i, rows i ∈ p.submodule

theorem card_rows_le_lines_mul [Finite V] {κ : Type*}
    (hV : Module.finrank K V = 2) (s : Finset (κ → V)) (B : ℕ)
    (hrows : ∀ rows ∈ s,
      Module.finrank K (Submodule.span K (Set.range rows)) ≤ 1)
    (hcount : ∀ p : ℙ K V,
      (lineRows s p).card ≤ B) :
    s.card ≤ (Nat.card K + 1) * B := by
  classical
  let : Fintype (ℙ K V) := Fintype.ofFinite (ℙ K V)
  let parts : ℙ K V → Finset (κ → V) :=
    fun p => lineRows s p
  have hcover : s ⊆ Finset.univ.biUnion parts := by
    intro rows hrow
    obtain ⟨p, hp⟩ := exists_line_containing_rows hV rows (hrows rows hrow)
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, by
      change rows ∈ lineRows s p
      simp only [lineRows, Finset.mem_filter]
      exact ⟨hrow, hp⟩⟩
  calc
    s.card ≤ (Finset.univ.biUnion parts).card := Finset.card_le_card hcover
    _ ≤ (Finset.univ : Finset (ℙ K V)).card * B :=
      Finset.card_biUnion_le_card_mul _ parts B (fun p _ => hcount p)
    _ = (Nat.card K + 1) * B := by
      rw [Finset.card_univ, Fintype.card_eq_nat_card, card_lines hV]

def lineFiber {α κ : Type*} (s : Finset α) (rows : α → κ → V)
    (p : ℙ K V) : Finset α := by
  classical
  exact s.filter fun a => ∀ i, rows a i ∈ p.submodule

theorem card_family_le_lines_mul [Finite V] {α κ : Type*}
    (hV : Module.finrank K V = 2) (s : Finset α) (rows : α → κ → V) (B : ℕ)
    (hrank : ∀ a ∈ s,
      Module.finrank K (Submodule.span K (Set.range (rows a))) ≤ 1)
    (hcount : ∀ p : ℙ K V, (lineFiber (K := K) s rows p).card ≤ B) :
    s.card ≤ (Nat.card K + 1) * B := by
  classical
  let : Fintype (ℙ K V) := Fintype.ofFinite (ℙ K V)
  have hcover : s ⊆ Finset.univ.biUnion (lineFiber (K := K) s rows) := by
    intro a ha
    obtain ⟨p, hp⟩ := exists_line_containing_rows hV (rows a) (hrank a ha)
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, by
      simp only [lineFiber, Finset.mem_filter]
      exact ⟨ha, hp⟩⟩
  calc
    s.card ≤ (Finset.univ.biUnion (lineFiber (K := K) s rows)).card := Finset.card_le_card hcover
    _ ≤ (Finset.univ : Finset (ℙ K V)).card * B :=
      Finset.card_biUnion_le_card_mul _ _ B (fun p _ => hcount p)
    _ = (Nat.card K + 1) * B := by
      rw [Finset.card_univ, Fintype.card_eq_nat_card, card_lines hV]

end Problem355.PlaneLines

end

end OAI
