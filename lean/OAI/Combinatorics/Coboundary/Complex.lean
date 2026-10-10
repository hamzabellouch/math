import Mathlib

namespace OAI

noncomputable section

/-!
Finite pure complexes, weighted F2 norms, distance to actual coboundaries, and the full main statement.
-/

section
open scoped BigOperators
open Filter

namespace CoboundaryExpanders

/-- A finite abstract simplicial complex, including its empty face.  Every
labelled vertex is a vertex of the complex, so unused labels are disallowed. -/
structure Complex where
  vertexCount : ℕ
  faces : Finset (Finset (Fin vertexCount))
  empty_mem : ∅ ∈ faces
  downward : ∀ {σ τ}, σ ∈ faces → τ ⊆ σ → τ ∈ faces
  vertex_mem : ∀ v, {v} ∈ faces

namespace Complex

/-- Faces of dimension `i`, i.e. with exactly `i+1` vertices. -/
def facesOf (X : Complex) (i : ℕ) : Finset (Finset (Fin X.vertexCount)) :=
  X.faces.filter (fun σ => σ.card = i + 1)

def Face (X : Complex) (i : ℕ) := {σ // σ ∈ X.facesOf i}

instance (X : Complex) (i : ℕ) : Fintype (X.Face i) := Subtype.fintype _
instance (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := Classical.decEq _

/-- Nonempty top face set and every face contained in an `s`-face: exact purity. -/
def Pure (X : Complex) (s : ℕ) : Prop :=
  (X.facesOf s).Nonempty ∧
  ∀ σ ∈ X.faces, ∃ τ ∈ X.facesOf s, σ ⊆ τ

/-- Connectedness of the one-skeleton, including nonemptiness. -/
def Connected (X : Complex) : Prop :=
  Nonempty (Fin X.vertexCount) ∧
  ∀ v w : Fin X.vertexCount,
    Relation.ReflTransGen (fun a b => a ≠ b ∧ {a, b} ∈ X.faces) v w

abbrev Cochain (X : Complex) (i : ℕ) := X.Face i → ZMod 2

/-- Source equation (weights), with ambient pure dimension `s`. -/
def weight (X : Complex) (s i : ℕ) (σ : X.Face i) : ℝ :=
  (((X.facesOf s).filter (fun τ => σ.val ⊆ τ)).card : ℝ) /
    ((Nat.choose (s + 1) (i + 1) : ℝ) * (X.facesOf s).card)

/-- The source's weighted support norm, not the unweighted Hamming norm. -/
def norm (X : Complex) (s i : ℕ) (f : X.Cochain i) : ℝ :=
  ∑ σ : X.Face i, if f σ ≠ 0 then X.weight s i σ else 0

/-- Simplicial coboundary with coefficients in F₂. -/
def coboundary (X : Complex) (i : ℕ) (f : X.Cochain i) : X.Cochain (i + 1) :=
  fun τ => ∑ σ : X.Face i, if σ.val ⊆ τ.val then f σ else 0

/-- Actual coboundaries; in degree zero use constants, as in the manuscript. -/
def coboundaries (X : Complex) : (i : ℕ) → Set (X.Cochain i)
  | 0 => {f | ∃ c : ZMod 2, f = fun _ => c}
  | i + 1 => Set.range (X.coboundary i)

def cocycles (X : Complex) (i : ℕ) : Set (X.Cochain i) :=
  {f | X.coboundary i f = 0}

/-- Distance in the source norm. On a nonempty subspace of this finite cochain
space the infimum is a minimum; no closure or cocycle relaxation is used. -/
def distance (X : Complex) (s i : ℕ) (f : X.Cochain i)
    (A : Set (X.Cochain i)) : ℝ :=
  sInf ((fun a => X.norm s i (f - a)) '' A)

/-- Number of top-dimensional faces incident to the given vertex. -/
def topDegree (X : Complex) (s : ℕ) (v : Fin X.vertexCount) : ℕ :=
  ((X.facesOf s).filter (fun τ => v ∈ τ)).card

end Complex

/-- The complete main assertion `thm:main`. Both constants are chosen outside
all three quantifiers `m`, `i`, and `f`. Vertex growth is convergence to infinity,
not mere existence of one arbitrarily large complex. -/
def MainStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    ∃ (D : ℕ) (ε : ℝ), 0 < ε ∧
      ∃ X : ℕ → Complex,
        (∀ m, (X m).Pure d ∧ (X m).Connected) ∧
        Tendsto (fun m => ((X m).facesOf 0).card) atTop atTop ∧
        (∀ m (v : Fin (X m).vertexCount), (X m).topDegree d v ≤ D) ∧
        ∀ m i, i < d → ∀ f : (X m).Cochain i,
          ε * (X m).distance d i f ((X m).coboundaries i) ≤
            (X m).norm d (i + 1) ((X m).coboundary i f)

end CoboundaryExpanders

end

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.Complex

attribute [reducible] Face

local instance (X : Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
local instance (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := X.instDecidableEqFace i

@[simp] theorem mem_facesOf (X : Complex) (i : ℕ) (σ) :
    σ ∈ X.facesOf i ↔ σ ∈ X.faces ∧ σ.card = i + 1 := by
  simp [facesOf]

@[simp] theorem face_card {X : Complex} {i : ℕ} (σ : X.Face i) :
    σ.val.card = i + 1 := (mem_facesOf X i _).1 σ.property |>.2

theorem face_mem {X : Complex} {i : ℕ} (σ : X.Face i) :
    σ.val ∈ X.faces := (mem_facesOf X i _).1 σ.property |>.1

theorem weight_nonneg (X : Complex) (s i : ℕ) (σ : X.Face i) :
    0 ≤ X.weight s i σ := by
  exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem weight_pos {X : Complex} {s i : ℕ} (hX : X.Pure s) (hi : i ≤ s)
    (σ : X.Face i) : 0 < X.weight s i σ := by
  obtain ⟨τ, hτ, hστ⟩ := hX.2 σ.val (face_mem σ)
  have hn : 0 < ((X.facesOf s).filter (fun τ => σ.val ⊆ τ)).card :=
    Finset.card_pos.mpr ⟨τ, Finset.mem_filter.mpr ⟨hτ, hστ⟩⟩
  exact div_pos (Nat.cast_pos.mpr hn)
    (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ hi)))
      (Nat.cast_pos.mpr hX.1.card_pos))

@[simp] theorem norm_zero (X : Complex) (s i : ℕ) : X.norm s i 0 = 0 := by
  simp [norm]

theorem norm_nonneg (X : Complex) (s i : ℕ) (f : X.Cochain i) :
    0 ≤ X.norm s i f := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact X.weight_nonneg s i σ
  · exact le_rfl

theorem norm_eq_zero_iff {X : Complex} {s i : ℕ} (hX : X.Pure s) (hi : i ≤ s)
    (f : X.Cochain i) : X.norm s i f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    ext σ
    change f σ = 0
    by_contra hσ
    have hle : X.weight s i σ ≤ X.norm s i f := by
      have := Finset.single_le_sum (f := fun ρ : X.Face i =>
        if f ρ ≠ 0 then X.weight s i ρ else 0)
        (fun ρ (_ : ρ ∈ Finset.univ) => by
          split_ifs
          · exact X.weight_nonneg s i ρ
          · exact le_rfl) (Finset.mem_univ σ)
      simpa only [norm, ite_eq_left hσ] using this
    exact (not_le_of_gt (weight_pos hX hi σ)) (hf ▸ hle)
  · rintro rfl
    exact X.norm_zero s i

@[simp] theorem coboundary_zero (X : Complex) (i : ℕ) : X.coboundary i 0 = 0 := by
  ext τ
  simp [coboundary]

@[simp] theorem coboundary_add (X : Complex) (i : ℕ) (f g : X.Cochain i) :
    X.coboundary i (f + g) = X.coboundary i f + X.coboundary i g := by
  ext τ
  simp only [coboundary, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

@[simp] theorem coboundary_smul (X : Complex) (i : ℕ) (c : ZMod 2) (f : X.Cochain i) :
    X.coboundary i (c • f) = c • X.coboundary i f := by
  ext τ
  simp only [coboundary, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

def coboundaryLinear (X : Complex) (i : ℕ) : X.Cochain i →ₗ[ZMod 2] X.Cochain (i + 1) where
  toFun := X.coboundary i
  map_add' := X.coboundary_add i
  map_smul' := X.coboundary_smul i

@[simp] theorem zero_mem_coboundaries (X : Complex) (i : ℕ) :
    0 ∈ X.coboundaries i := by
  cases i with
  | zero => exact ⟨0, rfl⟩
  | succ i => exact ⟨0, X.coboundary_zero i⟩

theorem coboundaries_nonempty (X : Complex) (i : ℕ) :
    (X.coboundaries i).Nonempty := ⟨0, X.zero_mem_coboundaries i⟩

theorem distance_attained (X : Complex) (s i : ℕ) (f : X.Cochain i)
    (A : Set (X.Cochain i)) (hA : A.Nonempty) :
    ∃ a ∈ A, X.distance s i f A = X.norm s i (f - a) := by
  have hfin : (((fun a => X.norm s i (f - a)) '' A) : Set ℝ).Finite :=
    (Set.toFinite A).image _
  obtain ⟨a, ha, heq⟩ := (hA.image (fun a => X.norm s i (f - a))).csInf_mem hfin
  exact ⟨a, ha, heq.symm⟩

theorem distance_nonneg (X : Complex) (s i : ℕ) (f : X.Cochain i)
    (A : Set (X.Cochain i)) (hA : A.Nonempty) :
    0 ≤ X.distance s i f A := by
  obtain ⟨a, _, ha⟩ := X.distance_attained s i f A hA
  rw [ha]
  exact X.norm_nonneg s i (f - a)

theorem distance_le_norm (X : Complex) (s i : ℕ) (f : X.Cochain i)
    {A : Set (X.Cochain i)} {a : X.Cochain i} (ha : a ∈ A) :
    X.distance s i f A ≤ X.norm s i (f - a) := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨b, _, rfl⟩; exact X.norm_nonneg s i (f - b)⟩
  · exact ⟨a, ha, rfl⟩

theorem distance_eq_zero_iff {X : Complex} {s i : ℕ} (hX : X.Pure s) (hi : i ≤ s)
    (f : X.Cochain i) {A : Set (X.Cochain i)} (hA : A.Nonempty) :
    X.distance s i f A = 0 ↔ f ∈ A := by
  constructor
  · intro h
    obtain ⟨a, ha, hfa⟩ := X.distance_attained s i f A hA
    have heq : f - a = 0 := (norm_eq_zero_iff hX hi _).mp (hfa.symm.trans h)
    exact sub_eq_zero.mp heq ▸ ha
  · intro hf
    apply le_antisymm
    · simpa using X.distance_le_norm s i f hf
    · exact X.distance_nonneg s i f A hA

theorem cocycle_mem_coboundaries_of_expansion {X : Complex} {s i : ℕ}
    (hX : X.Pure s) (hi : i ≤ s) {ε : ℝ} (hε : 0 < ε)
    (hexp : ∀ f : X.Cochain i,
      ε * X.distance s i f (X.coboundaries i) ≤ X.norm s (i + 1) (X.coboundary i f))
    {f : X.Cochain i} (hf : f ∈ X.cocycles i) : f ∈ X.coboundaries i := by
  have he := hexp f
  change X.coboundary i f = 0 at hf
  rw [hf, X.norm_zero] at he
  have hd : X.distance s i f (X.coboundaries i) = 0 :=
    le_antisymm (by nlinarith)
      (X.distance_nonneg s i f _ (X.coboundaries_nonempty i))
  exact (distance_eq_zero_iff hX hi f (X.coboundaries_nonempty i)).mp hd

theorem card_between_faces {X : Complex} {i j k : ℕ}
    (σ : X.Face i) (τ : X.Face k) (hστ : σ.val ⊆ τ.val) (hij : i ≤ j) :
    (Finset.univ.filter (fun ρ : X.Face j =>
      σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val)).card =
      Nat.choose ((k + 1) - (i + 1)) ((j + 1) - (i + 1)) := by
  classical
  have himage :
      (Finset.univ.filter (fun ρ : X.Face j =>
        σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val)).image Subtype.val =
      (τ.val.powersetCard (j + 1)).filter (σ.val ⊆ ·) := by
    ext ρ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨ρ', ⟨hσρ, hρτ⟩, rfl⟩
      exact ⟨⟨hρτ, face_card ρ'⟩, hσρ⟩
    · rintro ⟨⟨hρτ, hρcard⟩, hσρ⟩
      exact ⟨⟨ρ, (mem_facesOf X j ρ).mpr
        ⟨X.downward (face_mem τ) hρτ, hρcard⟩⟩, ⟨hσρ, hρτ⟩, rfl⟩
  have h := Finset.card_filter_powersetCard_subset σ.val τ.val (j + 1) hστ
    (by simpa using Nat.succ_le_succ hij)
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective] at h
  simpa only [face_card] using h

@[simp] theorem coboundary_coboundary (X : Complex) (i : ℕ) (f : X.Cochain i) :
    X.coboundary (i + 1) (X.coboundary i f) = 0 := by
  classical
  ext τ
  change (∑ ρ : X.Face (i + 1), if ρ.val ⊆ τ.val then
    (∑ σ : X.Face i, if σ.val ⊆ ρ.val then f σ else 0) else 0) = 0
  calc
    _ = ∑ ρ : X.Face (i + 1), ∑ σ : X.Face i,
        if σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val then f σ else 0 := by
      apply Finset.sum_congr rfl
      intro ρ _
      by_cases h : ρ.val ⊆ τ.val <;> simp [h]
    _ = ∑ σ : X.Face i, ∑ ρ : X.Face (i + 1),
        if σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val then f σ else 0 := Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro σ _
      by_cases hστ : σ.val ⊆ τ.val
      · have hc : (Finset.univ.filter (fun ρ : X.Face (i + 1) =>
            σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val)).card = 2 := by
          simpa using card_between_faces σ τ hστ (Nat.le_succ i)
        rw [← Finset.sum_filter, Finset.sum_const, hc]
        have htwo : (2 : ZMod 2) = 0 := by decide
        simp [nsmul_eq_mul, htwo]
      · apply Finset.sum_eq_zero
        intro ρ _
        exact ite_eq_right (fun h => hστ (h.1.trans h.2))

theorem sum_face_eq {A : Type*} [AddCommMonoid A] (X : Complex) (i : ℕ)
    (g : Finset (Fin X.vertexCount) → A) :
    (∑ σ : X.Face i, g σ.val) = ∑ σ ∈ X.facesOf i, g σ :=
  (Finset.sum_subtype (X.facesOf i) (fun _ => Iff.rfl) g).symm

def cofaceCount (X : Complex) (s : ℕ) (σ : Finset (Fin X.vertexCount)) : ℕ :=
  ((X.facesOf s).filter (σ ⊆ ·)).card

theorem cofaceCount_eq_sum (X : Complex) (s : ℕ) (σ : Finset (Fin X.vertexCount)) :
    X.cofaceCount s σ = ∑ τ : X.Face s, if σ ⊆ τ.val then (1 : ℕ) else 0 := by
  rw [sum_face_eq X s (fun τ => if σ ⊆ τ then (1 : ℕ) else 0), Finset.sum_boole]
  rfl

theorem sum_cofaceCount {X : Complex} {i s n : ℕ} (σ : X.Face i) (his : i ≤ s) :
    (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.cofaceCount n ρ.val else 0) =
    X.cofaceCount n σ.val * Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) := by
  classical
  calc
    _ = ∑ ρ : X.Face s, ∑ τ : X.Face n,
        if σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro ρ _
      by_cases h : σ.val ⊆ ρ.val <;> simp [h, cofaceCount_eq_sum]
    _ = ∑ τ : X.Face n, ∑ ρ : X.Face s,
        if σ.val ⊆ ρ.val ∧ ρ.val ⊆ τ.val then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ τ : X.Face n, if σ.val ⊆ τ.val then
        Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) else 0 := by
      apply Finset.sum_congr rfl
      intro τ _
      by_cases hστ : σ.val ⊆ τ.val
      · rw [ite_eq_left hστ, Finset.sum_boole]
        exact card_between_faces σ τ hστ his
      · rw [ite_eq_right hστ]
        apply Finset.sum_eq_zero
        intro ρ _
        exact ite_eq_right (fun h => hστ (h.1.trans h.2))
    _ = _ := by
      rw [cofaceCount_eq_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro τ _
      split_ifs <;> simp

theorem sum_cofaceCount_real {X : Complex} {i s n : ℕ} (σ : X.Face i) (his : i ≤ s) :
    (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then (X.cofaceCount n ρ.val : ℝ) else 0) =
    (X.cofaceCount n σ.val : ℝ) * Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) := by
  exact_mod_cast sum_cofaceCount (n := n) σ his

theorem facesOf_nonempty_of_pure {X : Complex} {n s : ℕ}
    (hX : X.Pure n) (hsn : s ≤ n) : (X.facesOf s).Nonempty := by
  obtain ⟨τ, hτ⟩ := hX.1
  have hτcard := ((mem_facesOf X n τ).mp hτ).2
  obtain ⟨σ, hστ, hσcard⟩ := Finset.exists_subset_card_eq
    (show s + 1 ≤ τ.card by omega)
  exact ⟨σ, (mem_facesOf X s σ).mpr
    ⟨X.downward ((mem_facesOf X n τ).mp hτ).1 hστ, hσcard⟩⟩

theorem weight_eq_cofaceCount (X : Complex) (n i : ℕ) (σ : X.Face i) :
    X.weight n i σ = (X.cofaceCount n σ.val : ℝ) /
      ((Nat.choose (n + 1) (i + 1) : ℝ) * (X.facesOf n).card) := rfl

theorem weight_averaging {X : Complex} {i s n : ℕ} (hX : (X.facesOf n).Nonempty)
    (his : i ≤ s) (hsn : s ≤ n) (σ : X.Face i) :
    (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight n s ρ else 0) =
      (Nat.choose (s + 1) (i + 1) : ℝ) * X.weight n i σ := by
  classical
  have hF : ((X.facesOf n).card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hX.card_pos)
  have hAi : (Nat.choose (n + 1) (i + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ (his.trans hsn))))
  have hAs : (Nat.choose (n + 1) (s + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ hsn)))
  have hchoose :
      (Nat.choose (n + 1) (s + 1) : ℝ) * Nat.choose (s + 1) (i + 1) =
      (Nat.choose (n + 1) (i + 1) : ℝ) *
        Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1)) := by
    exact_mod_cast Nat.choose_mul (n := n + 1) (Nat.succ_le_succ his)
  calc
    _ = (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then (X.cofaceCount n ρ.val : ℝ) else 0) /
        ((Nat.choose (n + 1) (s + 1) : ℝ) * (X.facesOf n).card) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ρ _
      split_ifs <;> simp [weight_eq_cofaceCount]
    _ = ((X.cofaceCount n σ.val : ℝ) *
        Nat.choose ((n + 1) - (i + 1)) ((s + 1) - (i + 1))) /
        ((Nat.choose (n + 1) (s + 1) : ℝ) * (X.facesOf n).card) := by
      rw [sum_cofaceCount_real σ his]
    _ = _ := by
      rw [weight_eq_cofaceCount]
      field_simp
      linear_combination -(X.cofaceCount n σ.val : ℝ) * hchoose

@[simp] theorem cofaceCount_self {X : Complex} {i : ℕ} (σ : X.Face i) :
    X.cofaceCount i σ.val = 1 := by
  classical
  have hfilter : (X.facesOf i).filter (σ.val ⊆ ·) = {σ.val} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hτ, hστ⟩
      exact (Finset.eq_of_subset_of_card_le hστ (by
        rw [face_card σ, ((mem_facesOf X i τ).mp hτ).2])).symm
    · rintro rfl
      exact ⟨σ.property, Finset.Subset.refl _⟩
  simp [cofaceCount, hfilter]

@[simp] theorem weight_top {X : Complex} {s : ℕ} (σ : X.Face s) :
    X.weight s s σ = 1 / (X.facesOf s).card := by
  simp [weight_eq_cofaceCount]

def skeletonScale (X : Complex) (n s : ℕ) : ℝ :=
  ((Nat.choose (n + 1) (s + 1) : ℝ) * (X.facesOf n).card) / (X.facesOf s).card

theorem skeletonScale_pos {X : Complex} {n s : ℕ} (hX : X.Pure n) (hsn : s ≤ n) :
    0 < X.skeletonScale n s := by
  exact div_pos
    (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ hsn)))
      (Nat.cast_pos.mpr hX.1.card_pos))
    (Nat.cast_pos.mpr (facesOf_nonempty_of_pure hX hsn).card_pos)

theorem skeletonScale_mul_topweight {X : Complex} {n s : ℕ}
    (hX : X.Pure n) (hsn : s ≤ n) (ρ : X.Face s) :
    X.skeletonScale n s * X.weight n s ρ =
      (X.cofaceCount n ρ.val : ℝ) * X.weight s s ρ := by
  have hCount : ((X.facesOf n).card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hX.1.card_pos)
  have hChoose : (Nat.choose (n + 1) (s + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ hsn)))
  rw [skeletonScale, weight_eq_cofaceCount, weight_top]
  field_simp

theorem skeleton_topweight_comparison {X : Complex} {n s : ℕ}
    (hX : X.Pure n) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (ρ : X.Face s) :
    (X.skeletonScale n s / b) * X.weight n s ρ ≤ X.weight s s ρ ∧
      X.weight s s ρ ≤ (X.skeletonScale n s / a) * X.weight n s ρ := by
  have heq := skeletonScale_mul_topweight hX hsn ρ
  have hw := X.weight_nonneg s s ρ
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hb, heq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hcount ρ).2 hw
  · rw [div_mul_eq_mul_div, le_div_iff₀ ha, heq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hcount ρ).1 hw

theorem skeleton_weight_comparison {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i ≤ s) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (σ : X.Face i) :
    (X.skeletonScale n s / b) * X.weight n i σ ≤ X.weight s i σ ∧
      X.weight s i σ ≤ (X.skeletonScale n s / a) * X.weight n i σ := by
  classical
  have hXs := facesOf_nonempty_of_pure hX hsn
  obtain ⟨ρ₀, hρ₀⟩ := facesOf_nonempty_of_pure hX hsn
  have hb : 0 < b := (ha.trans_le (hcount ⟨ρ₀, hρ₀⟩).1).trans_le
    (hcount ⟨ρ₀, hρ₀⟩).2
  have hB : (0 : ℝ) < Nat.choose (s + 1) (i + 1) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_succ his))
  have sum_scaled (c : ℝ) (t : ℕ) :
      (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then c * X.weight t s ρ else 0) =
      c * ∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight t s ρ else 0 := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  constructor
  · have hlo :
        (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then
          (X.skeletonScale n s / b) * X.weight n s ρ else 0) ≤
        ∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight s s ρ else 0 := by
      apply Finset.sum_le_sum
      intro ρ _
      split_ifs
      · exact (skeleton_topweight_comparison hX hsn ha hb hcount ρ).1
      · exact le_rfl
    rw [sum_scaled, weight_averaging hX.1 his hsn σ,
      weight_averaging hXs his le_rfl σ] at hlo
    apply (mul_le_mul_iff_right₀ hB).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hlo
  · have hhi :
        (∑ ρ : X.Face s, if σ.val ⊆ ρ.val then X.weight s s ρ else 0) ≤
        ∑ ρ : X.Face s, if σ.val ⊆ ρ.val then
          (X.skeletonScale n s / a) * X.weight n s ρ else 0 := by
      apply Finset.sum_le_sum
      intro ρ _
      split_ifs
      · exact (skeleton_topweight_comparison hX hsn ha hb hcount ρ).2
      · exact le_rfl
    rw [sum_scaled, weight_averaging hX.1 his hsn σ,
      weight_averaging hXs his le_rfl σ] at hhi
    apply (mul_le_mul_iff_right₀ hB).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hhi

theorem norm_le_of_weight_le {X : Complex} {r s i : ℕ} {c : ℝ}
    (hw : ∀ σ : X.Face i, X.weight r i σ ≤ c * X.weight s i σ)
    (f : X.Cochain i) : X.norm r i f ≤ c * X.norm s i f := by
  rw [norm, norm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  split_ifs
  · exact hw σ
  · simp

theorem distance_le_of_weight_le {X : Complex} {r s i : ℕ} {c : ℝ}
    (hw : ∀ σ : X.Face i, X.weight r i σ ≤ c * X.weight s i σ)
    (f : X.Cochain i) {A : Set (X.Cochain i)} (hA : A.Nonempty) :
    X.distance r i f A ≤ c * X.distance s i f A := by
  obtain ⟨a, ha, heq⟩ := X.distance_attained s i f A hA
  rw [heq]
  exact (X.distance_le_norm r i f ha).trans (norm_le_of_weight_le hw (f - a))

theorem skeleton_norm_comparison {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i ≤ s) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (f : X.Cochain i) :
    (X.skeletonScale n s / b) * X.norm n i f ≤ X.norm s i f ∧
      X.norm s i f ≤ (X.skeletonScale n s / a) * X.norm n i f := by
  constructor
  · rw [norm, norm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    split_ifs
    · exact (skeleton_weight_comparison hX his hsn ha hcount σ).1
    · simp
  · exact norm_le_of_weight_le
      (fun σ => (skeleton_weight_comparison hX his hsn ha hcount σ).2) f

theorem skeleton_distance_comparison {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i ≤ s) (hsn : s ≤ n) {a b : ℝ} (ha : 0 < a)
    (hcount : ∀ ρ : X.Face s, a ≤ X.cofaceCount n ρ.val ∧ X.cofaceCount n ρ.val ≤ b)
    (f : X.Cochain i) {A : Set (X.Cochain i)} (hA : A.Nonempty) :
    (X.skeletonScale n s / b) * X.distance n i f A ≤ X.distance s i f A ∧
      X.distance s i f A ≤ (X.skeletonScale n s / a) * X.distance n i f A := by
  obtain ⟨ρ₀, hρ₀⟩ := facesOf_nonempty_of_pure hX hsn
  have hb : 0 < b := (ha.trans_le (hcount ⟨ρ₀, hρ₀⟩).1).trans_le
    (hcount ⟨ρ₀, hρ₀⟩).2
  constructor
  · obtain ⟨a₀, ha₀, heq⟩ := X.distance_attained s i f A hA
    rw [heq]
    exact (mul_le_mul_of_nonneg_left (X.distance_le_norm n i f ha₀)
      (le_of_lt (div_pos (skeletonScale_pos hX hsn) hb))).trans
      (skeleton_norm_comparison hX his hsn ha hcount (f - a₀)).1
  · exact distance_le_of_weight_le
      (fun σ => (skeleton_weight_comparison hX his hsn ha hcount σ).2) f hA

theorem skeleton_expansion_on_common_cochains {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i < s) (hsn : s ≤ n) {M η : ℝ}
    (hη : 0 ≤ η)
    (hcount : ∀ ρ : X.Face s, 1 ≤ (X.cofaceCount n ρ.val : ℝ) ∧ X.cofaceCount n ρ.val ≤ M)
    (hvanish : X.cocycles i = X.coboundaries i)
    (hcosystolic : ∀ f : X.Cochain i,
      η * X.distance n i f (X.cocycles i) ≤ X.norm n (i + 1) (X.coboundary i f))
    (f : X.Cochain i) :
    (η / M) * X.distance s i f (X.coboundaries i) ≤
      X.norm s (i + 1) (X.coboundary i f) := by
  obtain ⟨ρ₀, hρ₀⟩ := facesOf_nonempty_of_pure hX hsn
  have hM : 0 < M := (zero_lt_one.trans_le (hcount ⟨ρ₀, hρ₀⟩).1).trans_le
    (hcount ⟨ρ₀, hρ₀⟩).2
  have hΛ : 0 < X.skeletonScale n s := skeletonScale_pos hX hsn
  have hdist := (skeleton_distance_comparison hX his.le hsn zero_lt_one hcount
    f (X.coboundaries_nonempty i)).2
  simp only [div_one] at hdist
  have hexp := hcosystolic f
  rw [hvanish] at hexp
  calc
    _ ≤ (η / M) * (X.skeletonScale n s * X.distance n i f (X.coboundaries i)) :=
      mul_le_mul_of_nonneg_left hdist (div_nonneg hη hM.le)
    _ = (X.skeletonScale n s / M) *
        (η * X.distance n i f (X.coboundaries i)) := by ring
    _ ≤ (X.skeletonScale n s / M) * X.norm n (i + 1) (X.coboundary i f) :=
      mul_le_mul_of_nonneg_left hexp (div_nonneg hΛ.le hM.le)
    _ ≤ _ := (skeleton_norm_comparison hX his hsn zero_lt_one hcount
      (X.coboundary i f)).1

@[reducible] def skeleton (X : Complex) (s : ℕ) : Complex where
  vertexCount := X.vertexCount
  faces := X.faces.filter (fun σ => σ.card ≤ s + 1)
  empty_mem := Finset.mem_filter.mpr ⟨X.empty_mem, by simp⟩
  downward := by
    intro σ τ hσ hτ
    rw [Finset.mem_filter] at hσ ⊢
    exact ⟨X.downward hσ.1 hτ, (Finset.card_le_card hτ).trans hσ.2⟩
  vertex_mem := fun v => Finset.mem_filter.mpr ⟨X.vertex_mem v, by simp⟩

@[simp] theorem mem_skeleton_faces (X : Complex) (s : ℕ) (σ) :
    σ ∈ (X.skeleton s).faces ↔ σ ∈ X.faces ∧ σ.card ≤ s + 1 :=
  by simp only [skeleton, Finset.mem_filter]

@[simp] theorem skeleton_facesOf {X : Complex} {s i : ℕ} (his : i ≤ s) :
    (X.skeleton s).facesOf i = X.facesOf i := by
  ext σ
  simp only [mem_facesOf, skeleton, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, h.2 ▸ Nat.succ_le_succ his⟩, h.2⟩

theorem skeleton_pure {X : Complex} {n s : ℕ} (hX : X.Pure n) (hsn : s ≤ n) :
    (X.skeleton s).Pure s := by
  refine ⟨?_, ?_⟩
  · rw [skeleton_facesOf le_rfl]
    exact facesOf_nonempty_of_pure hX hsn
  · intro σ hσ
    obtain ⟨hσX, hσs⟩ := (mem_skeleton_faces X s σ).mp hσ
    obtain ⟨τ, hτ, hστ⟩ := hX.2 σ hσX
    obtain ⟨ρ, hσρ, hρτ, hρcard⟩ := Finset.exists_subsuperset_card_eq hστ hσs
      (by rw [((mem_facesOf X n τ).mp hτ).2]; exact Nat.succ_le_succ hsn)
    refine ⟨ρ, ?_, hσρ⟩
    rw [skeleton_facesOf le_rfl]
    exact (mem_facesOf X s ρ).mpr ⟨X.downward ((mem_facesOf X n τ).mp hτ).1 hρτ,
      hρcard⟩

theorem skeleton_connected {X : Complex} (hX : X.Connected) {s : ℕ} (hs : 1 ≤ s) :
    (X.skeleton s).Connected := by
  refine ⟨hX.1, fun v w => ?_⟩
  apply Relation.ReflTransGen.mono (fun a b hab => ?_) v w (hX.2 v w)
  refine ⟨hab.1, (mem_skeleton_faces X s _).mpr ⟨hab.2, ?_⟩⟩
  have hcard := Finset.card_insert_le a ({b} : Finset (Fin X.vertexCount))
  simp only [Finset.card_singleton] at hcard
  omega

def skeletonFaceEquiv (X : Complex) {i s : ℕ} (his : i ≤ s) :
    X.Face i ≃ (X.skeleton s).Face i :=
  Equiv.subtypeEquivRight (fun σ => by rw [skeleton_facesOf his])

@[simp] theorem skeletonFaceEquiv_val (X : Complex) {i s : ℕ} (his : i ≤ s)
    (σ : X.Face i) : (X.skeletonFaceEquiv his σ).val = σ.val := rfl

@[simp] theorem skeletonFaceEquiv_symm_val (X : Complex) {i s : ℕ} (his : i ≤ s)
    (σ : (X.skeleton s).Face i) : ((X.skeletonFaceEquiv his).symm σ).val = σ.val := rfl

def skeletonCochainEquiv (X : Complex) {i s : ℕ} (his : i ≤ s) :
    X.Cochain i ≃ₗ[ZMod 2] (X.skeleton s).Cochain i :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (X.skeletonFaceEquiv his).symm

@[simp] theorem skeletonCochainEquiv_apply (X : Complex) {i s : ℕ} (his : i ≤ s)
    (f : X.Cochain i) (σ : (X.skeleton s).Face i) :
    X.skeletonCochainEquiv his f σ = f ((X.skeletonFaceEquiv his).symm σ) := rfl

@[simp] theorem skeleton_weight (X : Complex) {i s : ℕ} (his : i ≤ s)
    (σ : X.Face i) :
    (X.skeleton s).weight s i (X.skeletonFaceEquiv his σ) = X.weight s i σ := by
  simp only [weight, skeleton_facesOf le_rfl, skeletonFaceEquiv_val]

@[simp] theorem skeleton_norm (X : Complex) {i s : ℕ} (his : i ≤ s)
    (f : X.Cochain i) :
    (X.skeleton s).norm s i (X.skeletonCochainEquiv his f) = X.norm s i f := by
  unfold norm
  apply (Fintype.sum_equiv (X.skeletonFaceEquiv his) _ _ ?_).symm
  intro σ
  simp only [skeletonCochainEquiv_apply, Equiv.symm_apply_apply, skeleton_weight]

@[simp] theorem skeleton_coboundary (X : Complex) {i s : ℕ} (his : i < s)
    (f : X.Cochain i) :
    (X.skeleton s).coboundary i (X.skeletonCochainEquiv his.le f) =
      X.skeletonCochainEquiv his (X.coboundary i f) := by
  ext τ
  simp only [coboundary, skeletonCochainEquiv_apply]
  apply (Fintype.sum_equiv (X.skeletonFaceEquiv his.le) _ _ ?_).symm
  intro σ
  simp only [Equiv.symm_apply_apply,
    skeletonFaceEquiv_val, skeletonFaceEquiv_symm_val]
  rfl

@[simp] theorem skeleton_distance_image (X : Complex) {i s : ℕ} (his : i ≤ s)
    (f : X.Cochain i) (A : Set (X.Cochain i)) :
    (X.skeleton s).distance s i (X.skeletonCochainEquiv his f)
      ((X.skeletonCochainEquiv his) '' A) = X.distance s i f A := by
  unfold distance
  congr 1
  rw [Set.image_image]
  have hf : (fun a => (X.skeleton s).norm s i
      (X.skeletonCochainEquiv his f - X.skeletonCochainEquiv his a)) =
      (fun a => X.norm s i (f - a)) := by
    funext a
    rw [← map_sub, skeleton_norm]
  rw [hf]

theorem skeleton_coboundaries (X : Complex) {i s : ℕ} (his : i ≤ s) :
    (X.skeletonCochainEquiv his) '' X.coboundaries i =
      (X.skeleton s).coboundaries i := by
  ext f
  cases i with
  | zero =>
    constructor
    · rintro ⟨g, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨fun _ => c, ⟨c, rfl⟩, rfl⟩
  | succ i =>
    have hi : i < s := his
    constructor
    · rintro ⟨g, ⟨a, rfl⟩, rfl⟩
      exact ⟨X.skeletonCochainEquiv hi.le a, X.skeleton_coboundary hi a⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a₀, rfl⟩ := (X.skeletonCochainEquiv hi.le).surjective a
      exact ⟨X.coboundary i a₀, ⟨a₀, rfl⟩, (X.skeleton_coboundary hi a₀).symm⟩

theorem skeleton_expansion {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (his : i < s) (hsn : s ≤ n) {M η : ℝ}
    (hη : 0 ≤ η)
    (hcount : ∀ ρ : X.Face s, 1 ≤ (X.cofaceCount n ρ.val : ℝ) ∧ X.cofaceCount n ρ.val ≤ M)
    (hvanish : X.cocycles i = X.coboundaries i)
    (hcosystolic : ∀ f : X.Cochain i,
      η * X.distance n i f (X.cocycles i) ≤ X.norm n (i + 1) (X.coboundary i f))
    (f : (X.skeleton s).Cochain i) :
    (η / M) * (X.skeleton s).distance s i f ((X.skeleton s).coboundaries i) ≤
      (X.skeleton s).norm s (i + 1) ((X.skeleton s).coboundary i f) := by
  obtain ⟨f₀, rfl⟩ := (X.skeletonCochainEquiv his.le).surjective f
  rw [← X.skeleton_coboundaries his.le, skeleton_distance_image,
    skeleton_coboundary X his, skeleton_norm]
  exact skeleton_expansion_on_common_cochains hX his hsn hη hcount hvanish hcosystolic f₀

def vertexFaceEquiv (X : Complex) : Fin X.vertexCount ≃ X.Face 0 :=
  Equiv.ofBijective (fun v => ⟨{v}, (mem_facesOf X 0 _).mpr
    ⟨X.vertex_mem v, Finset.card_singleton v⟩⟩) (by
      constructor
      · intro v w h
        exact Finset.singleton_injective (congrArg Subtype.val h)
      · intro σ
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (face_card σ)
        exact ⟨v, Subtype.ext hv.symm⟩)

@[simp] theorem vertexFaceEquiv_val (X : Complex) (v : Fin X.vertexCount) :
    (X.vertexFaceEquiv v).val = {v} := rfl

theorem card_facesOf_zero (X : Complex) : (X.facesOf 0).card = X.vertexCount := by
  have h := Fintype.card_congr X.vertexFaceEquiv
  simpa only [Fintype.card_fin, Fintype.card_coe] using h.symm

theorem coboundary_zero_degree (X : Complex) (f : X.Cochain 0) (τ : X.Face 1) :
    X.coboundary 0 f τ = ∑ v ∈ τ.val, f (X.vertexFaceEquiv v) := by
  rw [coboundary, ← Equiv.sum_comp X.vertexFaceEquiv]
  simp only [vertexFaceEquiv_val, Finset.singleton_subset_iff, Finset.sum_ite_mem,
    Finset.univ_inter]

@[simp] theorem coboundary_const (X : Complex) (c : ZMod 2) :
    X.coboundary 0 (fun _ => c) = 0 := by
  ext τ
  rw [coboundary_zero_degree]
  simp only [Finset.sum_const, face_card, Nat.reduceAdd, Pi.zero_apply, nsmul_eq_mul]
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp only [Nat.cast_ofNat, htwo, zero_mul]

theorem coboundaries_subset_cocycles (X : Complex) (i : ℕ) :
    X.coboundaries i ⊆ X.cocycles i := by
  cases i with
  | zero =>
    rintro f ⟨c, rfl⟩
    exact X.coboundary_const c
  | succ i =>
    rintro f ⟨g, rfl⟩
    exact X.coboundary_coboundary i g

theorem cocycles_zero_eq_coboundaries_of_connected {X : Complex} (hX : X.Connected) :
    X.cocycles 0 = X.coboundaries 0 := by
  apply Set.Subset.antisymm
  · intro f hf
    have hδ : X.coboundary 0 f = 0 := hf
    have hedge : ∀ v w : Fin X.vertexCount,
        v ≠ w ∧ {v, w} ∈ X.faces →
          f (X.vertexFaceEquiv v) = f (X.vertexFaceEquiv w) := by
      intro v w hvw
      let τ : X.Face 1 := ⟨{v, w}, (mem_facesOf X 1 _).mpr
        ⟨hvw.2, by simp [hvw.1]⟩⟩
      have he := congrFun hδ τ
      rw [coboundary_zero_degree] at he
      have hsum : f (X.vertexFaceEquiv v) + f (X.vertexFaceEquiv w) = 0 := by
        simpa [τ, hvw.1] using he
      have hchar : - f (X.vertexFaceEquiv w) = f (X.vertexFaceEquiv w) := by
        exact CharTwo.neg_eq _
      exact (eq_neg_of_add_eq_zero_left hsum).trans hchar
    have hpath : ∀ v w : Fin X.vertexCount,
        f (X.vertexFaceEquiv v) = f (X.vertexFaceEquiv w) := by
      intro v w
      induction hX.2 v w using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head hab _ ih => exact (hedge _ _ hab).trans ih
    obtain ⟨v₀⟩ := hX.1
    refine ⟨f (X.vertexFaceEquiv v₀), ?_⟩
    funext σ
    obtain ⟨v, rfl⟩ := X.vertexFaceEquiv.surjective σ
    exact hpath v v₀
  · exact X.coboundaries_subset_cocycles 0

end CoboundaryExpanders.Complex

end

end OAI
