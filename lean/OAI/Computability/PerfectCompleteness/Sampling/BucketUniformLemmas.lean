import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.SetTheory.Cardinal.Finite
import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.PerfectCompleteness.Sampling.BucketSampler
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RecordSeedSamplingLemmas
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI


namespace PerfectCompleteness.BucketUniform

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction)

variable {H : Type*} [AddCommGroup H] [Module F2 H]

def coordinateDirection {ℓ : Nat} (i : Fin ℓ) : Direction ℓ :=
  ⟨Pi.single i (1 : F2), by
    intro h
    have hi := congrFun h i
    simp at hi⟩

def evaluateLinear (ℓ : Nat) : (Direction ℓ → H) →ₗ[F2] (Fin ℓ → H) where
  toFun := BucketSampler.evaluate ℓ (id : H → H)
  map_add' t u := by
    funext i
    simp only [BucketSampler.evaluate, id_eq, Pi.add_apply, smul_add,
      Finset.sum_add_distrib]
  map_smul' a t := by
    funext i
    change (∑ v : Direction ℓ, v.val i • (a • t v)) =
      a • ∑ v : Direction ℓ, v.val i • t v
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun v _ => smul_comm _ _ _)

@[simp] theorem evaluateLinear_apply (ℓ : Nat) (t : Direction ℓ → H) :
    evaluateLinear ℓ t = BucketSampler.evaluate ℓ (id : H → H) t := rfl

theorem evaluate_single {ℓ : Nat} (v : Direction ℓ) (h : H) :
    evaluateLinear ℓ (Pi.single v h) = BucketSampler.rankOne v.val h := by
  funext i
  change (∑ w : Direction ℓ, w.val i • (Pi.single v h) w) = v.val i • h
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ hw
    simp [hw]
  · intro hv
    exact (hv (Finset.mem_univ v)).elim

theorem evaluate_coordinate_bucket {ℓ : Nat} (i : Fin ℓ) (h : H) :
    evaluateLinear ℓ (Pi.single (coordinateDirection i) h) = Pi.single i h := by
  rw [evaluate_single]
  funext j
  by_cases hij : i = j
  · subst j
    simp [BucketSampler.rankOne, coordinateDirection]
  · simp [BucketSampler.rankOne, coordinateDirection, Ne.symm hij]

def coordinateTape {ℓ : Nat} (rows : Fin ℓ → H) : Direction ℓ → H :=
  ∑ i : Fin ℓ, Pi.single (coordinateDirection i) (rows i)

theorem evaluate_coordinateTape {ℓ : Nat} (rows : Fin ℓ → H) :
    evaluateLinear ℓ (coordinateTape rows) = rows := by
  unfold coordinateTape
  rw [map_sum]
  simp only [evaluate_coordinate_bucket, Finset.univ_sum_single]

theorem evaluateLinear_surjective (ℓ : Nat) :
    Function.Surjective (evaluateLinear (H := H) ℓ) :=
  fun rows => ⟨coordinateTape rows, evaluate_coordinateTape rows⟩

theorem evaluate_surjective (ℓ : Nat) :
    Function.Surjective (BucketSampler.evaluate ℓ (id : H → H)) :=
  evaluateLinear_surjective ℓ

theorem uniform_evaluate_law [Fintype H] (ℓ : Nat) :
    (BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform H)).pushforward
        (BucketSampler.evaluate ℓ (id : H → H)) =
      FiniteDistribution.uniform (Fin ℓ → H) :=
  UniformLinearImage.product_uniform_linear_image
    (I := Direction ℓ) (Ω := fun _ => H) (R := F2) (V := Fin ℓ → H)
    (evaluateLinear (H := H) ℓ) (evaluateLinear_surjective (H := H) ℓ)

theorem uniform_array_law [Fintype H] (ℓ : Nat) :
    BucketSampler.law ℓ (FiniteDistribution.uniform H) (id : H → H) =
      FiniteDistribution.uniform (Fin ℓ → H) :=
  uniform_evaluate_law ℓ


variable {Ω : Type*} (V : Submodule F2 (Ω → F2))

def ofRowsLinear (ℓ : Nat) :
    (Fin ℓ → V) →ₗ[F2] (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2)) where
  toFun := EvaluationMatrix.ofRows V
  map_add' rows rows' := by
    apply LinearMap.ext
    intro q
    funext i
    exact map_add q (rows i) (rows' i)
  map_smul' a rows := by
    apply LinearMap.ext
    intro q
    funext i
    exact map_smul q a (rows i)

theorem ofRowsLinear_surjective [FiniteDimensional F2 V] (ℓ : Nat) :
    Function.Surjective (ofRowsLinear V ℓ) :=
  fun X => ⟨EvaluationMatrix.rows V X, EvaluationMatrix.ofRows_rows V X⟩

theorem uniform_matrix_law (ℓ : Nat) [Fintype V] [FiniteDimensional F2 V]
    [Fintype (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2))] :
    (BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).pushforward
        (fun t => EvaluationMatrix.ofRows V (BucketSampler.evaluate ℓ (id : V → V) t)) =
      FiniteDistribution.uniform (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2)) := by
  calc
    _ = ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).pushforward
        (BucketSampler.evaluate ℓ (id : V → V))).pushforward
          (EvaluationMatrix.ofRows V) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (FiniteDistribution.uniform (Fin ℓ → V)).pushforward
        (EvaluationMatrix.ofRows V) := by rw [uniform_evaluate_law]
    _ = _ := UniformLinearImage.uniform_pushforward_linearMap
      (ofRowsLinear V ℓ) (ofRowsLinear_surjective V ℓ)

end
end PerfectCompleteness.BucketUniform



namespace PerfectCompleteness.RecursiveSamplerBiasAlgebra

open PointwiseSpaces RecursiveSpaces RecursiveSampler
open scoped BigOperators

universe u w

variable (𝕜 : Type w) [Field 𝕜]

def squareProduct {X : Type u} (H : Submodule 𝕜 (X → 𝕜)) :
    H →ₗ[𝕜] H →ₗ[𝕜] squareSpace H :=
  LinearMap.mk₂ 𝕜
    (fun g h => ⟨g.val * h.val, mul_mem_squareSpace H g.property h.property⟩)
    (fun g g' h => Subtype.ext (add_mul g.val g'.val h.val))
    (fun c g h => Subtype.ext (smul_mul_assoc c g.val h.val))
    (fun g h h' => Subtype.ext (mul_add g.val h.val h'.val))
    (fun c g h => Subtype.ext (mul_smul_comm c g.val h.val))

@[simp] theorem squareProduct_val {X : Type u} (H : Submodule 𝕜 (X → 𝕜))
    (g h : H) : (squareProduct 𝕜 H g h).val = g.val * h.val := rfl

theorem square_functional_eq_zero_of_products {X : Type u}
    (H : Submodule 𝕜 (X → 𝕜)) (L : squareSpace H →ₗ[𝕜] 𝕜)
    (hL : ∀ g h : H, L (squareProduct 𝕜 H g h) = 0) : L = 0 := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  change L ⟨x, hx⟩ = 0
  refine Submodule.span_induction
    (p := fun y hy => L ⟨y, hy⟩ = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨g, hg, h, hh, rfl⟩
    exact hL ⟨g, hg⟩ ⟨h, hh⟩
  · exact map_zero L
  · intro y z hy hz hLy hLz
    change L ((⟨y, hy⟩ : squareSpace H) + ⟨z, hz⟩) = 0
    rw [map_add, hLy, hLz, add_zero]
  · intro c y hy hLy
    change L (c • (⟨y, hy⟩ : squareSpace H)) = 0
    rw [map_smul, hLy, smul_zero]

variable {branch : Nat → Nat} {n : Nat}

def childSquareLift (A : Slots branch (n + 1) → Type u) (i : Fin (branch n)) :
    squareSpace (space 𝕜 branch n (childFamily A i)) →ₗ[𝕜]
      space 𝕜 branch (n + 1) A where
  toFun g := ⟨pullback 𝕜 (childRestriction A i) g.val,
    child_square_le_space A i (Submodule.mem_map_of_mem g.property)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem childSquareLift_val (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (g : squareSpace (space 𝕜 branch n (childFamily A i))) :
    (childSquareLift 𝕜 A i g).val = pullback 𝕜 (childRestriction A i) g.val := rfl

def childProduct (A : Slots branch (n + 1) → Type u) (i : Fin (branch n)) :
    space 𝕜 branch n (childFamily A i) →ₗ[𝕜]
      space 𝕜 branch n (childFamily A i) →ₗ[𝕜] space 𝕜 branch (n + 1) A :=
  (squareProduct 𝕜 (space 𝕜 branch n (childFamily A i))).compr₂
    (childSquareLift 𝕜 A i)

@[simp] theorem childProduct_val (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (g h : space 𝕜 branch n (childFamily A i)) :
    (childProduct 𝕜 A i g h).val =
      pullback 𝕜 (childRestriction A i) (g.val * h.val) := rfl

def childBilinear (A : Slots branch (n + 1) → Type u) (i : Fin (branch n))
    (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜) :
    space 𝕜 branch n (childFamily A i) →ₗ[𝕜]
      space 𝕜 branch n (childFamily A i) →ₗ[𝕜] 𝕜 :=
  (childProduct 𝕜 A i).compr₂ f

@[simp] theorem childBilinear_apply (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜)
    (g h : space 𝕜 branch n (childFamily A i)) :
    childBilinear 𝕜 A i f g h =
      f (childSquareLift 𝕜 A i
        (squareProduct 𝕜 (space 𝕜 branch n (childFamily A i)) g h)) := rfl

theorem eq_zero_of_child_restrictions (A : Slots branch (n + 1) → Type u)
    (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜)
    (hzero : ∀ i : Fin (branch n), f.comp (childSquareLift 𝕜 A i) = 0) : f = 0 := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  change f ⟨x, hx⟩ = 0
  refine Submodule.iSup_induction'
    (fun i : Fin (branch n) =>
      (squareSpace (space 𝕜 branch n (childFamily A i))).map
        (pullback 𝕜 (childRestriction A i)))
    (motive := fun y hy => f ⟨y, hy⟩ = 0) ?_ ?_ ?_ hx
  · intro i y hy
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hy
    exact LinearMap.congr_fun (hzero i) ⟨g, hg⟩
  · exact map_zero f
  · intro y z hy hz hfy hfz
    change f ((⟨y, hy⟩ : space 𝕜 branch (n + 1) A) + ⟨z, hz⟩) = 0
    rw [map_add, hfy, hfz, add_zero]

theorem exists_child_restriction_ne_zero (A : Slots branch (n + 1) → Type u)
    (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜) (hf : f ≠ 0) :
    ∃ i : Fin (branch n), f.comp (childSquareLift 𝕜 A i) ≠ 0 := by
  classical
  by_contra h
  apply hf
  apply eq_zero_of_child_restrictions 𝕜 A f
  intro i
  by_contra hi
  exact h ⟨i, hi⟩

theorem childBilinear_ne_zero (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜)
    (hchild : f.comp (childSquareLift 𝕜 A i) ≠ 0) :
    childBilinear 𝕜 A i f ≠ 0 := by
  intro hzero
  apply hchild
  apply square_functional_eq_zero_of_products 𝕜 _ _
  intro g h
  exact LinearMap.congr_fun₂ hzero g h

theorem ordinary_or_bilinear_ne_zero (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜) (hf : f ≠ 0) :
    (∃ j : OffPath i, f.comp (childSquareLift 𝕜 A j.val) ≠ 0) ∨
      childBilinear 𝕜 A i f ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := exists_child_restriction_ne_zero 𝕜 A f hf
  by_cases hji : j = i
  · subst j
    exact Or.inr (childBilinear_ne_zero 𝕜 A i f hj)
  · exact Or.inl ⟨⟨j, hji⟩, hj⟩

noncomputable section

theorem combine_eq (A : Slots branch (n + 1) → Type u) (i : Fin (branch n))
    (r : Nat)
    (ordinary : (j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val)))
    (left right : Fin r → space 𝕜 branch n (childFamily A i)) :
    combine 𝕜 A i r ordinary left right =
      (∑ j : OffPath i, childSquareLift 𝕜 A j.val (ordinary j)) +
        ∑ h : Fin r, childProduct 𝕜 A i (left h) (right h) := by
  apply Subtype.ext
  change combineFunction 𝕜 A i r ordinary left right =
    (space 𝕜 branch (n + 1) A).subtype
      ((∑ j : OffPath i, childSquareLift 𝕜 A j.val (ordinary j)) +
        ∑ h : Fin r, childProduct 𝕜 A i (left h) (right h))
  rw [map_add, map_sum, map_sum]
  rfl

theorem map_combine (A : Slots branch (n + 1) → Type u) (i : Fin (branch n))
    (r : Nat) (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜)
    (ordinary : (j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val)))
    (left right : Fin r → space 𝕜 branch n (childFamily A i)) :
    f (combine 𝕜 A i r ordinary left right) =
      (∑ j : OffPath i, (f.comp (childSquareLift 𝕜 A j.val)) (ordinary j)) +
        ∑ h : Fin r, childBilinear 𝕜 A i f (left h) (right h) := by
  rw [combine_eq, map_add, map_sum, map_sum]
  rfl

end
end PerfectCompleteness.RecursiveSamplerBiasAlgebra



namespace PerfectCompleteness.RecursiveSampler

open PointwiseSpaces RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

abbrev CallIndex (repeats : Nat → Nat) (n : Nat) := Fin (repeats (n + 1)) × Bool

variable (𝕜 : Type w) [Field 𝕜]

abbrev OrdinaryTape (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u) :=
  (j : OffPath i) → DrawSpace 𝕜 repeats (.step i p) A (.inl j)

abbrev CallTapes (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u) :=
  CallIndex repeats n → Tape 𝕜 repeats p (childFamily A i)

def splitTapeEquiv (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u) :
    Tape 𝕜 repeats (.step i p) A ≃
      OrdinaryTape 𝕜 repeats i p A × CallTapes 𝕜 repeats i p A where
  toFun t := (fun j => t (.inl j), fun hb => subTape 𝕜 repeats i p A t hb.1 hb.2)
  invFun z j := match j with
    | .inl j => z.1 j
    | .inr j => z.2 j.1 j.2
  left_inv t := by
    funext j
    cases j <;> rfl
  right_inv z := by
    apply Prod.ext
    · funext j
      rfl
    · funext hb j
      rfl

noncomputable def evaluateCalls (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    (calls : CallTapes 𝕜 repeats i p A) :
    CallIndex repeats n → space 𝕜 branch n (childFamily A i) :=
  fun hb => evaluate 𝕜 repeats p (childFamily A i) (calls hb)

noncomputable def splitEvaluatedTape (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    (t : Tape 𝕜 repeats (.step i p) A) :
    OrdinaryTape 𝕜 repeats i p A ×
      (CallIndex repeats n → space 𝕜 branch n (childFamily A i)) :=
  ((splitTapeEquiv 𝕜 repeats i p A t).1,
    evaluateCalls 𝕜 repeats i p A (splitTapeEquiv 𝕜 repeats i p A t).2)

noncomputable def stepCombine (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    (z : OrdinaryTape 𝕜 repeats i p A ×
      (CallIndex repeats n → space 𝕜 branch n (childFamily A i))) :
    space 𝕜 branch (n + 1) A :=
  combine 𝕜 A i (repeats (n + 1)) z.1
    (fun h => z.2 (h, false)) (fun h => z.2 (h, true))

theorem stepCombine_splitEvaluatedTape (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    (t : Tape 𝕜 repeats (.step i p) A) :
    stepCombine 𝕜 repeats i p A (splitEvaluatedTape 𝕜 repeats i p A t) =
      evaluate 𝕜 repeats (.step i p) A t := rfl

noncomputable section

variable [Finite 𝕜]

instance childFamilyFinite (A : Slots branch (n + 1) → Type u)
    [hA : ∀ s, Finite (A s)] (i : Fin (branch n)) :
    ∀ s, Finite (childFamily A i s) := fun s => hA (i, s)

instance childSquareFintype (A : Slots branch (n + 1) → Type u)
    [hA : ∀ s, Finite (A s)] (i : Fin (branch n)) :
    Fintype (squareSpace (space 𝕜 branch n (childFamily A i))) := by
  letI : ∀ s, Finite (childFamily A i s) := fun s => hA (i, s)
  exact Fintype.ofFinite _

instance ordinaryDrawFintype (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] (j : OffPath i) :
    Fintype (DrawSpace 𝕜 repeats (.step i p) A (.inl j)) :=
  drawSpaceFintype 𝕜 repeats (.step i p) A (.inl j)

instance ordinaryTapeFintype (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] : Fintype (OrdinaryTape 𝕜 repeats i p A) := by
  letI : ∀ j : OffPath i, Fintype (DrawSpace 𝕜 repeats (.step i p) A (.inl j)) :=
    fun j => drawSpaceFintype 𝕜 repeats (.step i p) A (.inl j)
  exact Pi.instFintype

instance callTapesFintype (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [hA : ∀ s, Finite (A s)] : Fintype (CallTapes 𝕜 repeats i p A) := by
  letI : ∀ s, Finite (childFamily A i s) := fun s => hA (i, s)
  letI : Fintype (Tape 𝕜 repeats p (childFamily A i)) :=
    @Pi.instFintype (DrawIndex repeats p)
      (DrawSpace 𝕜 repeats p (childFamily A i))
      (drawIndexDecidableEq repeats p) (drawIndexFintype repeats p)
      (fun j => drawSpaceFintype 𝕜 repeats p (childFamily A i) j)
  exact Pi.instFintype

def ordinaryLaw (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [∀ s, Finite (A s)] :
    FiniteDistribution (OrdinaryTape 𝕜 repeats i p A) := by
  letI : ∀ j : OffPath i, Fintype (DrawSpace 𝕜 repeats (.step i p) A (.inl j)) :=
    fun j => drawSpaceFintype 𝕜 repeats (.step i p) A (.inl j)
  letI : ∀ j : OffPath i, Nonempty (DrawSpace 𝕜 repeats (.step i p) A (.inl j)) :=
    fun j => ⟨zeroDraw 𝕜 repeats (.step i p) A (.inl j)⟩
  exact FiniteProduct.law (fun j : OffPath i =>
    FiniteDistribution.uniform (DrawSpace 𝕜 repeats (.step i p) A (.inl j)))

def callTapeLaw (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [hA : ∀ s, Finite (A s)] :
    FiniteDistribution (CallTapes 𝕜 repeats i p A) := by
  letI : ∀ s, Finite (childFamily A i s) := fun s => hA (i, s)
  exact FiniteProduct.law (fun _ : CallIndex repeats n =>
    tapeLaw 𝕜 repeats p (childFamily A i))

theorem splitTape_law (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] :
    (tapeLaw 𝕜 repeats (.step i p) A).pushforward (splitTapeEquiv 𝕜 repeats i p A) =
      (ordinaryLaw 𝕜 repeats i p A).product (callTapeLaw 𝕜 repeats i p A) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  let : ∀ j : OffPath i ⊕ (CallIndex repeats n × DrawIndex repeats p),
      Fintype (DrawSpace 𝕜 repeats (.step i p) A j) :=
    fun j => drawSpaceFintype 𝕜 repeats (.step i p) A j
  change
    (∏ j : OffPath i ⊕ (CallIndex repeats n × DrawIndex repeats p),
      1 / (Fintype.card (DrawSpace 𝕜 repeats (.step i p) A j) : ℝ)) =
    (∏ j : OffPath i,
      1 / (Fintype.card (DrawSpace 𝕜 repeats (.step i p) A (.inl j)) : ℝ)) *
      ∏ _hb : CallIndex repeats n, ∏ j : DrawIndex repeats p,
        1 / (Fintype.card (DrawSpace 𝕜 repeats p (childFamily A i) j) : ℝ)
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Fintype.card_eq_nat_card]
  rfl

theorem subTape_tuple_law (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] :
    (tapeLaw 𝕜 repeats (.step i p) A).pushforward
        (fun t (hb : CallIndex repeats n) => subTape 𝕜 repeats i p A t hb.1 hb.2) =
      callTapeLaw 𝕜 repeats i p A := by
  calc
    _ = ((tapeLaw 𝕜 repeats (.step i p) A).pushforward
        (splitTapeEquiv 𝕜 repeats i p A)).pushforward Prod.snd :=
      (FiniteDistribution.pushforward_comp _ _ Prod.snd).symm
    _ = _ := by
      rw [splitTape_law, FiniteDistribution.product_pushforward_snd]

def callScalarLaw (𝕜 : Type w) [Field 𝕜] [Finite 𝕜]
    (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [hA : ∀ s, Finite (A s)]
    [Fintype (space 𝕜 branch n (childFamily A i))] :
    FiniteDistribution (CallIndex repeats n → space 𝕜 branch n (childFamily A i)) := by
  letI : ∀ s, Finite (childFamily A i s) := fun s => hA (i, s)
  exact FiniteProduct.law (fun _ : CallIndex repeats n =>
    law 𝕜 repeats p (childFamily A i))

theorem evaluateCalls_law (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] [Fintype (space 𝕜 branch n (childFamily A i))] :
    (callTapeLaw 𝕜 repeats i p A).pushforward (evaluateCalls 𝕜 repeats i p A) =
      callScalarLaw 𝕜 repeats i p A :=
  FiniteProduct.pushforward_map _ (fun _ => evaluate 𝕜 repeats p (childFamily A i))

theorem splitEvaluatedTape_law (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] [Fintype (space 𝕜 branch n (childFamily A i))] :
    (tapeLaw 𝕜 repeats (.step i p) A).pushforward
        (splitEvaluatedTape 𝕜 repeats i p A) =
      (ordinaryLaw 𝕜 repeats i p A).product (callScalarLaw 𝕜 repeats i p A) := by
  calc
    _ = ((tapeLaw 𝕜 repeats (.step i p) A).pushforward
        (splitTapeEquiv 𝕜 repeats i p A)).pushforward
          (fun z => (z.1, evaluateCalls 𝕜 repeats i p A z.2)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = ((ordinaryLaw 𝕜 repeats i p A).product
        (callTapeLaw 𝕜 repeats i p A)).pushforward
          (fun z => (z.1, evaluateCalls 𝕜 repeats i p A z.2)) := by
      rw [splitTape_law]
    _ = (ordinaryLaw 𝕜 repeats i p A).product
        ((callTapeLaw 𝕜 repeats i p A).pushforward
          (evaluateCalls 𝕜 repeats i p A)) := by
      simpa only [id_eq, FiniteDistribution.pushforward_id] using
        (FiniteDistribution.product_pushforward
          (ordinaryLaw 𝕜 repeats i p A) (callTapeLaw 𝕜 repeats i p A)
          (id : OrdinaryTape 𝕜 repeats i p A → OrdinaryTape 𝕜 repeats i p A)
          (evaluateCalls 𝕜 repeats i p A))
    _ = _ := by rw [evaluateCalls_law]

theorem law_step (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] [Fintype (space 𝕜 branch n (childFamily A i))]
    [Fintype (space 𝕜 branch (n + 1) A)] :
    law 𝕜 repeats (.step i p) A =
      ((ordinaryLaw 𝕜 repeats i p A).product
        (callScalarLaw 𝕜 repeats i p A)).pushforward
          (stepCombine 𝕜 repeats i p A) := by
  calc
    _ = ((tapeLaw 𝕜 repeats (.step i p) A).pushforward
        (splitEvaluatedTape 𝕜 repeats i p A)).pushforward
          (stepCombine 𝕜 repeats i p A) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by rw [splitEvaluatedTape_law]

end
end PerfectCompleteness.RecursiveSampler

end OAI
