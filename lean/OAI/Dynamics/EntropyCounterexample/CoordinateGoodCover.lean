import OAI.Dynamics.EntropyCounterexample.Definitions

namespace OAI

noncomputable section

open Set Metric
open scoped unitInterval

namespace Problem340
namespace CoordinateGoodCover

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sphereSlice (C : Set E) : Set (Metric.sphere (0 : E) 1) :=
  {x | (x : E) ∈ C}

theorem contractible_sphereSlice (C : Set E) (hconv : Convex ℝ C)
    (hscale : ∀ r : ℝ, 0 < r → ∀ x ∈ C, r • x ∈ C)
    (hzero : (0 : E) ∉ C) (hne : (sphereSlice C).Nonempty) :
    ContractibleSpace (sphereSlice C) := by
  obtain ⟨p, hp⟩ := hne
  let p' : sphereSlice C := ⟨p, hp⟩
  let blend : unitInterval × sphereSlice C → E :=
    fun z => (z.1 : ℝ) • (p : E) + (1 - (z.1 : ℝ)) • (z.2.1 : E)
  have hblend : Continuous blend := by
    dsimp [blend]
    fun_prop
  have hmem (z : unitInterval × sphereSlice C) : blend z ∈ C := by
    exact hconv hp z.2.property z.1.property.1
      (sub_nonneg.mpr z.1.property.2) (add_sub_cancel _ _)
  have hnezero (z : unitInterval × sphereSlice C) : blend z ≠ 0 := by
    intro hz
    exact hzero (hz ▸ hmem z)
  have hnorm (z : unitInterval × sphereSlice C) : ‖blend z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hnezero z)
  let H : unitInterval × sphereSlice C → sphereSlice C := fun z =>
    ⟨⟨‖blend z‖⁻¹ • blend z, by
      simpa [mem_sphere_zero_iff_norm] using
        (norm_smul_inv_norm (𝕜 := ℝ) (hnezero z))⟩,
      hscale _ (inv_pos.mpr (norm_pos_iff.mpr (hnezero z))) _ (hmem z)⟩
  have hH : Continuous H := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (hblend.norm.inv₀ hnorm).smul hblend
  apply (contractible_iff_id_nullhomotopic (sphereSlice C)).mpr
  refine ⟨p', ⟨⟨⟨H, hH⟩, ?_, ?_⟩⟩⟩
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    have hx : ‖(x.1 : E)‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using x.1.property
    simp [H, blend, hx]
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    have hp' : ‖(p : E)‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using p.property
    simp [H, blend, hp', p']

def positiveCone {ι : Type*} (L : ι → E →L[ℝ] ℝ) (s : Set ι) : Set E :=
  {x | ∀ i ∈ s, 0 < L i x}

theorem convex_positiveCone {ι : Type*} (L : ι → E →L[ℝ] ℝ) (s : Set ι) :
    Convex ℝ (positiveCone L s) := by
  intro x hx y hy a b ha hb hab i hi
  exact ((convex_Ioi (𝕜 := ℝ) (0 : ℝ)).linear_preimage (L i).toLinearMap)
    (hx i hi) (hy i hi) ha hb hab

theorem positiveCone_smul {ι : Type*} (L : ι → E →L[ℝ] ℝ) (s : Set ι)
    {r : ℝ} (hr : 0 < r) {x : E} (hx : x ∈ positiveCone L s) :
    r • x ∈ positiveCone L s := by
  intro i hi
  simpa only [map_smul, smul_eq_mul] using mul_pos hr (hx i hi)

theorem zero_not_mem_positiveCone {ι : Type*} (L : ι → E →L[ℝ] ℝ)
    (s : Set ι) (hs : s.Nonempty) : (0 : E) ∉ positiveCone L s := by
  obtain ⟨i, hi⟩ := hs
  intro h
  simpa only [map_zero, lt_self_iff_false] using h i hi

theorem contractible_positiveSphere {ι : Type*} (L : ι → E →L[ℝ] ℝ)
    (s : Set ι) (hs : s.Nonempty)
    (hne : (sphereSlice (positiveCone L s)).Nonempty) :
    ContractibleSpace (sphereSlice (positiveCone L s)) :=
  contractible_sphereSlice _ (convex_positiveCone L s)
    (fun _ hr _ hx => positiveCone_smul L s hr hx)
    (zero_not_mem_positiveCone L s hs) hne

end Cone

theorem contractible_pi {ι : Type*} (X : ι → Type*)
    [∀ i, TopologicalSpace (X i)] [∀ i, ContractibleSpace (X i)] :
    ContractibleSpace (∀ i, X i) := by
  choose p hp using fun i => id_nullhomotopic (X i)
  apply (contractible_iff_id_nullhomotopic (∀ i, X i)).mpr
  refine ⟨p, ?_⟩
  exact ContinuousMap.Homotopic.piMap hp

structure GoodCover (ι X : Type*) [TopologicalSpace X] where
  carrier : ι → Set X
  isOpen : ∀ i, IsOpen (carrier i)
  covers : ∀ x, ∃ i, x ∈ carrier i
  contractible : ∀ s : Finset ι, s.Nonempty →
    (⋂ i ∈ s, carrier i).Nonempty → ContractibleSpace (⋂ i ∈ s, carrier i)

theorem GoodCover.iUnion_eq_univ {ι X : Type*} [TopologicalSpace X]
    (U : GoodCover ι X) : (⋃ i, U.carrier i) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact U.covers x

def GoodCover.comap {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (U : GoodCover ι Y) (e : X ≃ₜ Y) : GoodCover ι X where
  carrier i := e ⁻¹' U.carrier i
  isOpen i := (U.isOpen i).preimage e.continuous
  covers x := U.covers (e x)
  contractible s hs hne := by
    let A := ⋂ i ∈ s, U.carrier i
    let B := ⋂ i ∈ s, e ⁻¹' U.carrier i
    have hset : B = e ⁻¹' A := by
      simp only [A, B, Set.preimage_iInter]
    have hA : A.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      refine ⟨e x, ?_⟩
      change x ∈ e ⁻¹' A
      rw [← hset]
      exact hx
    let := U.contractible s hs hA
    exact (e.sets hset).contractibleSpace

section Products

variable {ι κ X Y : Type*} [topologyX : TopologicalSpace X] [topologyY : TopologicalSpace Y]

omit topologyX topologyY in
theorem inter_prod_eq [TopologicalSpace X] [TopologicalSpace Y]
    (U : ι → Set X) (V : κ → Set Y) (s : Finset (ι × κ))
    [DecidableEq ι] [DecidableEq κ] :
    (⋂ i ∈ s, U i.1 ×ˢ V i.2) =
      (⋂ i ∈ s.image Prod.fst, U i) ×ˢ (⋂ j ∈ s.image Prod.snd, V j) := by
  ext x
  simp only [mem_iInter, mem_prod, Finset.mem_image]
  constructor
  · intro h
    constructor
    · rintro i ⟨j, hj, rfl⟩
      exact (h j hj).1
    · rintro i ⟨j, hj, rfl⟩
      exact (h j hj).2
  · rintro ⟨hU, hV⟩ i hi
    exact ⟨hU i.1 ⟨i, hi, rfl⟩, hV i.2 ⟨i, hi, rfl⟩⟩

def GoodCover.prod (U : GoodCover ι X) (V : GoodCover κ Y) :
    GoodCover (ι × κ) (X × Y) where
  carrier i := U.carrier i.1 ×ˢ V.carrier i.2
  isOpen i := (U.isOpen i.1).prod (V.isOpen i.2)
  covers x := by
    obtain ⟨i, hi⟩ := U.covers x.1
    obtain ⟨j, hj⟩ := V.covers x.2
    exact ⟨(i, j), hi, hj⟩
  contractible s hs hne := by
    classical
    rw [inter_prod_eq] at hne ⊢
    let A := ⋂ i ∈ s.image Prod.fst, U.carrier i
    let B := ⋂ j ∈ s.image Prod.snd, V.carrier j
    have hA : A.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x.1, hx.1⟩
    have hB : B.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x.2, hx.2⟩
    let := U.contractible _ (hs.image _) hA
    let := V.contractible _ (hs.image _) hB
    exact (Homeomorph.Set.prod A B).contractibleSpace

def piSubsetHomeomorph {α : Type*} {Z : α → Type*}
    [∀ i, TopologicalSpace (Z i)] (A : ∀ i, Set (Z i)) :
    (Set.pi Set.univ A) ≃ₜ (∀ i, A i) where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  invFun x := ⟨fun i => (x i).1, fun i _ => (x i).2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)

def GoodCover.pi {α : Type*} [Finite α] {J Z : α → Type*}
    [∀ i, TopologicalSpace (Z i)] (U : ∀ i, GoodCover (J i) (Z i)) :
    GoodCover (∀ i, J i) (∀ i, Z i) where
  carrier j := Set.pi Set.univ (fun i => (U i).carrier (j i))
  isOpen j := isOpen_set_pi Set.finite_univ fun i _ => (U i).isOpen (j i)
  covers x := by
    choose j hj using fun i => (U i).covers (x i)
    exact ⟨j, fun i _ => hj i⟩
  contractible s hs hne := by
    classical
    let A : ∀ i, Set (Z i) := fun i =>
      ⋂ j ∈ s.image (fun f => f i), (U i).carrier j
    have hset : (⋂ j ∈ s, Set.pi Set.univ (fun i => (U i).carrier (j i))) =
        Set.pi Set.univ A := by
      ext x
      simp only [mem_iInter, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro h i
        apply Set.mem_iInter₂.mpr
        intro j hj
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hj
        exact h f hf i
      · intro h j hj i
        exact Set.mem_iInter₂.mp (h i) (j i) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    rw [hset] at hne ⊢
    have hA (i : α) : (A i).Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x i, hx i (Set.mem_univ i)⟩
    let (i : α) : ContractibleSpace (A i) :=
      (U i).contractible _ (hs.image _) (hA i)
    let : ContractibleSpace (∀ i, A i) := contractible_pi (fun i => A i)
    exact (piSubsetHomeomorph A).contractibleSpace

end Products

section Coordinates

variable (n : ℕ)

def signedCoordinate (i : Bool × Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  if i.1 then EuclideanSpace.proj i.2 else -EuclideanSpace.proj i.2

def hemisphere (i : Bool × Fin n) : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  {x | 0 < signedCoordinate n i (x : EuclideanSpace ℝ (Fin n))}

theorem isOpen_hemisphere (i : Bool × Fin n) : IsOpen (hemisphere n i) :=
  isOpen_lt continuous_const ((signedCoordinate n i).continuous.comp continuous_subtype_val)

theorem hemisphere_covers (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∃ i, x ∈ hemisphere n i := by
  have hx : (x : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro h
    have hxnorm : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using x.property
    rw [h, norm_zero] at hxnorm
    exact zero_ne_one hxnorm
  have hi : ∃ i : Fin n, (x : EuclideanSpace ℝ (Fin n)) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (PiLp.ext h)
  obtain ⟨i, hi⟩ := hi
  rcases lt_or_gt_of_ne hi with h | h
  · exact ⟨(false, i), by simpa [hemisphere, signedCoordinate] using neg_pos.mpr h⟩
  · exact ⟨(true, i), by simpa [hemisphere, signedCoordinate] using h⟩

theorem hemisphere_inter_eq_slice (s : Finset (Bool × Fin n)) :
    (⋂ i ∈ s, hemisphere n i) =
      sphereSlice (positiveCone (signedCoordinate n) (s : Set (Bool × Fin n))) := by
  ext x
  simp [sphereSlice, positiveCone, hemisphere]

def sphereGoodCover : GoodCover (Bool × Fin n)
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) where
  carrier := hemisphere n
  isOpen := isOpen_hemisphere n
  covers := hemisphere_covers n
  contractible s hs hne := by
    rw [hemisphere_inter_eq_slice] at hne ⊢
    exact contractible_positiveSphere _ _ hs hne

end Coordinates

def clockSphereGoodCover : GoodCover ((Bool × Fin 2) × (Bool × Fin 3))
    (StandardClock × StandardSphere2) :=
  (sphereGoodCover 2).prod (sphereGoodCover 3)

def counterexampleGoodCover (q : ℕ) :
    GoodCover ((Bool × Fin 2) × (Fin (q + 1) → Bool × Fin 3))
      (CounterexampleManifold q) :=
  (sphereGoodCover 2).prod (GoodCover.pi fun _ : Fin (q + 1) => sphereGoodCover 3)

theorem card_counterexampleGoodCover_index (q : ℕ) :
    Fintype.card ((Bool × Fin 2) × (Fin (q + 1) → Bool × Fin 3)) =
      4 * 6 ^ (q + 1) := by
  simp [Fintype.card_prod]

end CoordinateGoodCover
end Problem340

end

end OAI
