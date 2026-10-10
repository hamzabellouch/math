import OAI.CategoryTheory.Thomason.Gray.SimplicialHomotopyWhiskering
import OAI.CategoryTheory.Thomason.Simplicial.BarycentricSortedCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.ExhaustionWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.FiniteSingularRelativeLifting
import OAI.CategoryTheory.Thomason.Transfer.SimplicialRangeGluing
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Bounded

namespace OAI

section

/-! # Every point is in an actual barycentric flag simplex

Sorting coordinates and their consecutive differences produces an exact
preimage under the affine map from the face-poset realization.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity PartialOrder RealizationPrism

noncomputable section

def permutationFaceMap (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) : Faces n →o Faces n where
  toFun A :=
    { finset := A.finset.image (fun a => ULift.up (σ a.down))
      nonempty := A.nonempty.image _
      comparable _ _ := le_total _ _ }
  monotone' _ _ h := Finset.image_subset_image h

theorem face_permutation (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) (A : Faces n) :
    face n (permutationFaceMap n σ A) = StdSimplex.map σ (face n A) := by
  classical
  have hi : Function.Injective (fun a : ULift.{0} (Fin (n+1)) => ULift.up (σ a.down)) := by
    intro a b h
    exact ULift.ext _ _ (σ.injective (congrArg ULift.down h))
  have hf : (permutationFaceMap n σ A).finset =
      A.finset.image (fun a => ULift.up (σ a.down)) := by
    change (A.finset.image (fun a => ULift.up (σ a.down))) = _
    congr
  apply StdSimplex.ext
  rw [StdSimplex.weights_map]
  simp only [face, hf]
  rw [Finset.card_image_of_injective _ hi, Finsupp.mapDomain_finsetSum,
    Finset.sum_image (fun a _ b _ h => hi h)]
  simp only [Finsupp.mapDomain_single]

private theorem point_permutation_simplex (n d : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (s : Fin (d+1) ⥤ Faces n) (p : StdSimplex ℝ (Fin (d+1))) :
    point n ((SSet.toTop.map (nerveMap (permutationFaceMap n σ).monotone.functor)).hom
      (simplexPoint (nerve (Faces n)) s p)) =
        StdSimplex.map σ (point n (simplexPoint (nerve (Faces n)) s p)) := by
  calc
    _ = point n (simplexPoint (nerve (Faces n))
        (s ⋙ (permutationFaceMap n σ).monotone.functor) p) :=
      congrArg (point n)
        (simplexPoint_naturality (nerveMap (permutationFaceMap n σ).monotone.functor) s p)
    _ = (StdSimplex.map (fun j => face n (permutationFaceMap n σ (s.obj j))) p).sConvexComb :=
      point_simplex n d (s ⋙ (permutationFaceMap n σ).monotone.functor) p
    _ = (StdSimplex.map (fun j => StdSimplex.map σ (face n (s.obj j))) p).sConvexComb := by
      congr 2
      funext j
      exact face_permutation n σ (s.obj j)
    _ = StdSimplex.map σ ((StdSimplex.map (fun j => face n (s.obj j)) p).sConvexComb) := by
      rw [StdSimplex.map_sConvexComb, StdSimplex.map_map]
    _ = _ := congrArg (StdSimplex.map σ) (point_simplex n d s p).symm

/-- The barycentric affine map respects relabelling of the original vertices. -/
theorem point_permutation (n : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (z : SSet.toTop.obj (nerve (Faces n))) :
    point n ((SSet.toTop.map (nerveMap (permutationFaceMap n σ).monotone.functor)).hom z) =
      StdSimplex.map σ (point n z) := by
  obtain ⟨d, s, p, rfl⟩ := point_representation_simplex (nerve (Faces n)) z
  exact point_permutation_simplex n d σ s p

/-- Every geometric point is represented by one actual simplex of the
barycentric face nerve. Zero flag weights handle ties and all boundary faces. -/
theorem point_surjective (n : ℕ) : Function.Surjective (point n) := by
  intro p
  obtain ⟨σ, hσ⟩ := exists_antitone_permutation n p.weights
  let a := sortedSequence n p σ
  have ha := sortedSequence_antitone n p σ hσ
  have hz := sortedSequence_zero n p σ
  have ht := sortedSequence_total n p σ
  let z := simplexPoint (nerve (Faces n)) (prefixSimplex n) (flagWeights n a ha hz ht)
  refine ⟨(SSet.toTop.map (nerveMap (permutationFaceMap n σ).monotone.functor)).hom z, ?_⟩
  rw [point_permutation]
  apply StdSimplex.ext
  apply Finsupp.ext
  intro i
  rw [StdSimplex.weights_map, Finsupp.mapDomain_equiv_apply]
  change (point n (simplexPoint (nerve (Faces n)) (prefixSimplex n)
    (flagWeights n a ha hz ht))).weights (σ.symm i) = p.weights i
  rw [point_prefix_weight]
  simp [a, sortedSequence, (σ.symm i).isLt]

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Uniqueness of affine coordinates on one barycentric flag

The triangular barycenter matrix is injective. Descending induction on
its coordinates avoids any nonconstructive matrix invertibility input.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity

noncomputable section

theorem prefix_point_injective (n : ℕ) : Function.Injective
    (fun p : StdSimplex ℝ (Fin (n+1)) => point n
      (RealizationPrism.simplexPoint (nerve (Faces n)) (prefixSimplex n) p)) := by
  intro p q hpq
  have hsum (j : Fin (n+1)) :
      (∑ i : Fin (n+1), (p.weights i-q.weights i) *
        (face n (prefixFace n i)).weights j) = 0 := by
    have hp := point_simplex_weight n n (prefixSimplex n) p j
    have hq := point_simplex_weight n n (prefixSimplex n) q j
    have he := congrArg (fun z : StdSimplex ℝ (Fin (n+1)) => z.weights j) hpq
    change _ = ∑ i, p.weights i * (face n (prefixFace n i)).weights j at hp
    change _ = ∑ i, q.weights i * (face n (prefixFace n i)).weights j at hq
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hp.symm.trans (he.trans hq))
  have hall : ∀ k : ℕ, ∀ j : Fin (n+1), n-j.val = k → p.weights j = q.weights j := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro j hj
      have hlarge (i : Fin (n+1)) (hji : j < i) : p.weights i = q.weights i := by
        apply ih (n-i.val) _ i rfl
        have hi := i.isLt
        have hj' := j.isLt
        have hji' : j.val < i.val := hji
        omega
      have hs : (∑ i : Fin (n+1), (p.weights i-q.weights i) *
          (face n (prefixFace n i)).weights j) =
          (p.weights j-q.weights j) * (face n (prefixFace n j)).weights j := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          by_cases hji : j ≤ i
          · rw [hlarge i (lt_of_le_of_ne hji (Ne.symm hij)), sub_self, zero_mul]
          · rw [prefixFace_weight, ite_eq_right hji, mul_zero]
        · intro h
          exact False.elim (h (Finset.mem_univ j))
      have hz := hsum j
      rw [hs, prefixFace_weight, ite_eq_left le_rfl] at hz
      have hd : (1 : ℝ) / ((j.val : ℝ)+1) ≠ 0 := by positivity
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hd)
  apply StdSimplex.ext
  exact Finsupp.ext (fun j => hall (n-j.val) j rfl)

/-- Relabelling the vertices preserves uniqueness of flag coordinates. -/
theorem permuted_prefix_point_injective (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    Function.Injective (fun p : StdSimplex ℝ (Fin (n+1)) => point n
      (RealizationPrism.simplexPoint (nerve (Faces n))
        (prefixSimplex n ⋙ (permutationFaceMap n σ).monotone.functor) p)) := by
  intro p q hpq
  have hperm (r : StdSimplex ℝ (Fin (n+1))) :
      point n (RealizationPrism.simplexPoint (nerve (Faces n))
        (prefixSimplex n ⋙ (permutationFaceMap n σ).monotone.functor) r) =
      StdSimplex.map σ (point n (RealizationPrism.simplexPoint (nerve (Faces n))
        (prefixSimplex n) r)) := by
    exact (congrArg (point n) (RealizationPrism.simplexPoint_naturality
      (nerveMap (permutationFaceMap n σ).monotone.functor) (prefixSimplex n) r)).symm.trans
        (point_permutation n σ _)
  have hp := hperm p
  have hq := hperm q
  have he : StdSimplex.map σ (point n (RealizationPrism.simplexPoint (nerve (Faces n))
      (prefixSimplex n) p)) = StdSimplex.map σ (point n
        (RealizationPrism.simplexPoint (nerve (Faces n)) (prefixSimplex n) q)) :=
    hp.symm.trans (hpq.trans hq)
  apply prefix_point_injective n
  apply StdSimplex.ext
  exact Finsupp.mapDomain_injective σ.injective (congrArg StdSimplex.weights he)

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Exact face compatibility of barycentric coordinates

The affine subdivision map preserves the whole prescribed face. Its
positive support is exactly the union of faces having positive mass.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity RealizationPrism

noncomputable section

/-- Positive coordinates of the affine barycentric map have an exact
combinatorial support description. -/
theorem point_weight_pos_iff (n : ℕ) (z : SSet.toTop.obj (nerve (Faces n)))
    (i : Fin (n+1)) :
    0 < (point n z).weights i ↔ ∃ A : Faces n,
      0 < (PosetGeometry.coordinates (Faces n) z).weights A ∧ ULift.up i ∈ A.finset := by
  classical
  let := Fintype.ofFinite (Faces n)
  rw [point_weight, Finset.sum_pos_iff_of_nonneg
    (fun A _ => mul_nonneg ((PosetGeometry.coordinates (Faces n) z).nonneg A)
      ((face n A).nonneg i))]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨A, hA⟩
    obtain h | h := mul_pos_iff.mp hA
    · exact ⟨A, h.1, (face_weight_pos_iff n A i).mp h.2⟩
    · exact False.elim ((not_lt_of_ge ((face n A).nonneg i)) h.2)
  · rintro ⟨A, hA, hi⟩
    exact ⟨A, mul_pos hA ((face_weight_pos_iff n A i).mpr hi)⟩

private theorem point_face_simplex {m n d : ℕ} (f : Fin (m+1) ↪o Fin (n+1))
    (s : Fin (d+1) ⥤ Faces m) (p : StdSimplex ℝ (Fin (d+1))) :
    point n ((SSet.toTop.map (nerveMap (faceMap f).monotone.functor)).hom
      (simplexPoint (nerve (Faces m)) s p)) =
        StdSimplex.map f (point m (simplexPoint (nerve (Faces m)) s p)) := by
  calc
    _ = point n (simplexPoint (nerve (Faces n))
        (s ⋙ (faceMap f).monotone.functor) p) :=
      congrArg (point n)
        (simplexPoint_naturality (nerveMap (faceMap f).monotone.functor) s p)
    _ = (StdSimplex.map (fun j => face n (faceMap f (s.obj j))) p).sConvexComb :=
      point_simplex n d (s ⋙ (faceMap f).monotone.functor) p
    _ = (StdSimplex.map (fun j => StdSimplex.map f (face m (s.obj j))) p).sConvexComb := by
      congr 2
      funext j
      exact (face_map f (s.obj j)).symm
    _ = StdSimplex.map f ((StdSimplex.map (fun j => face m (s.obj j)) p).sConvexComb) := by
      rw [StdSimplex.map_sConvexComb, StdSimplex.map_map]
    _ = _ := congrArg (StdSimplex.map f) (point_simplex m d s p).symm

/-- The affine map to the original simplex commutes with every injective
ordinal face map, at all points of the actual realization. -/
theorem point_face_naturality {m n : ℕ} (f : Fin (m+1) ↪o Fin (n+1))
    (z : SSet.toTop.obj (nerve (Faces m))) :
    point n ((SSet.toTop.map (nerveMap (faceMap f).monotone.functor)).hom z) =
      StdSimplex.map f (point m z) := by
  obtain ⟨d, s, p, rfl⟩ := point_representation_simplex (nerve (Faces m)) z
  exact point_face_simplex f s p

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # The exact inverse image of a face under barycentric subdivision

This retains complete faces, not just their vertices or their interiors.
It is the carrier compatibility needed for relative approximation.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity RealizationPrism

noncomputable section

private theorem carrier_le_fullSubposet_iff {P : Type} [PartialOrder P]
    (V : Set P) (z : SSet.toTop.obj (nerve P)) :
    carrier (nerve P) z ≤ fullSubposetComplex V ↔
      ∀ v, 0 < (PosetGeometry.coordinates P z).weights v → v ∈ V := by
  let s := (normalization (nerve P) z).1
  let p := (normalization (nerve P) z).2
  have hp : p ∈ fullSupport s.dim := normalization_fullSupport (nerve P) z
  have he : simplexPoint (nerve P) s.simplex p = z := denormalize_normalization (nerve P) z
  rw [← he, carrier_interior (nerve P) s.simplex p hp, SSet.Subcomplex.ofSimplex_le_iff]
  change (∀ i, s.simplex.obj i ∈ V) ↔ _
  constructor
  · intro h v hv
    have hs : v ∈ (PosetGeometry.coordinates P (simplexPoint (nerve P) s.simplex p)).weights.support :=
      Finsupp.mem_support_iff.mpr (ne_of_gt hv)
    obtain ⟨i, rfl⟩ := (PosetGeometry.coordinates_support_interior P s.simplex p hp v).mp hs
    exact h i
  · intro h i
    have hs : s.simplex.obj i ∈
        (PosetGeometry.coordinates P (simplexPoint (nerve P) s.simplex p)).weights.support :=
      (PosetGeometry.coordinates_support_interior P s.simplex p hp _).mpr ⟨i, rfl⟩
    exact h _ (lt_of_le_of_ne
      ((PosetGeometry.coordinates P (simplexPoint (nerve P) s.simplex p)).nonneg _)
      (Ne.symm (Finsupp.mem_support_iff.mp hs)))

/-- Faces of the original simplex are exactly the full subposets of
subdivision faces using only their permitted original vertices. -/
def permittedFaces (n : ℕ) (V : Set (Fin (n+1))) : Set (Faces n) :=
  {A | ∀ i : Fin (n+1), ULift.up i ∈ A.finset → i ∈ V}

/-- The affine barycentric map has exactly the expected face preimage.
The statement includes points on every lower-dimensional boundary. -/
theorem point_face_preimage (n : ℕ) (V : Set (Fin (n+1)))
    (z : SSet.toTop.obj (nerve (Faces n))) :
    (∀ i ∉ V, (point n z).weights i = 0) ↔
      carrier (nerve (Faces n)) z ≤ fullSubposetComplex (permittedFaces n V) := by
  rw [carrier_le_fullSubposet_iff]
  constructor
  · intro hz A hA i hi
    by_contra hn
    have hp := (point_weight_pos_iff n z i).mpr ⟨A, hA, hi⟩
    rw [hz i hn] at hp
    exact (lt_irrefl 0) hp
  · intro hz i hi
    apply le_antisymm
    · by_contra hn
      have hp : 0 < (point n z).weights i := lt_of_not_ge hn
      obtain ⟨A, hA, ha⟩ := (point_weight_pos_iff n z i).mp hp
      exact hi (hz A hA i ha)
    · exact (point n z).nonneg i

/-- In particular a specified codimension-one face is retained exactly,
even where several faces meet. -/
theorem point_zero_coordinate_iff (n : ℕ) (i : Fin (n+1))
    (z : SSet.toTop.obj (nerve (Faces n))) :
    (point n z).weights i = 0 ↔
      carrier (nerve (Faces n)) z ≤
        fullSubposetComplex (permittedFaces n {j | j ≠ i}) := by
  have h := point_face_preimage n {j | j ≠ i} z
  simpa only [Set.mem_ofPred_eq, not_not, forall_eq] using h

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # A quantitative mesh estimate for barycentric subdivision

The common vertex of a chain of faces retains a fixed positive mass.
Consequently every affine real coordinate oscillates by at most the
factor `1 - 1/(n+1)` on a subdivided characteristic simplex.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity

noncomputable section

/-- Evaluation of an affine real coordinate by its original vertex values. -/
def affineValue {n : ℕ} (x : Fin (n+1) → ℝ) (p : StdSimplex ℝ (Fin (n+1))) : ℝ :=
  ∑ i, p.weights i * x i

theorem affineValue_sub_constant {n : ℕ} (x : Fin (n+1) → ℝ)
    (p : StdSimplex ℝ (Fin (n+1))) (c : ℝ) :
    affineValue (fun i => x i - c) p = affineValue x p - c := by
  simp only [affineValue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    p.total_of_fintype, one_mul]

theorem affineValue_const_sub {n : ℕ} (x : Fin (n+1) → ℝ)
    (p : StdSimplex ℝ (Fin (n+1))) (c : ℝ) :
    affineValue (fun i => c - x i) p = c - affineValue x p := by
  simp only [affineValue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    p.total_of_fintype, one_mul]

/-- Removing a common vertex mass bounds the remaining affine variation. -/
theorem common_mass_bounds {n : ℕ} (x : Fin (n+1) → ℝ)
    (p : StdSimplex ℝ (Fin (n+1))) (v : Fin (n+1)) (ε lo hi : ℝ)
    (hmass : ε ≤ p.weights v) (hx : ∀ i, lo ≤ x i ∧ x i ≤ hi) :
    ε * x v + (1-ε) * lo ≤ affineValue x p ∧
      affineValue x p ≤ ε * x v + (1-ε) * hi := by
  have hl : ε * (x v - lo) ≤ affineValue (fun i => x i-lo) p := by
    calc
      _ ≤ p.weights v * (x v - lo) :=
        mul_le_mul_of_nonneg_right hmass (sub_nonneg.mpr (hx v).1)
      _ ≤ ∑ i, p.weights i * (x i-lo) :=
        Finset.single_le_sum (fun i _ => mul_nonneg (p.nonneg i)
          (sub_nonneg.mpr (hx i).1)) (Finset.mem_univ v)
  have hh : ε * (hi - x v) ≤ affineValue (fun i => hi-x i) p := by
    calc
      _ ≤ p.weights v * (hi - x v) :=
        mul_le_mul_of_nonneg_right hmass (sub_nonneg.mpr (hx v).2)
      _ ≤ ∑ i, p.weights i * (hi-x i) :=
        Finset.single_le_sum (fun i _ => mul_nonneg (p.nonneg i)
          (sub_nonneg.mpr (hx i).2)) (Finset.mem_univ v)
  rw [affineValue_sub_constant] at hl
  rw [affineValue_const_sub] at hh
  constructor <;> nlinarith

/-- A single interval of contracted width contains the entire image of a
subdivided characteristic simplex under any affine real coordinate. -/
theorem simplex_affine_interval (n m : ℕ) (s : Fin (m+1) ⥤ Faces n)
    (x : Fin (n+1) → ℝ) (lo hi : ℝ) (hx : ∀ i, lo ≤ x i ∧ x i ≤ hi) :
    ∃ v : Fin (n+1), ∀ p : StdSimplex ℝ (Fin (m+1)),
      let z := point n (RealizationPrism.simplexPoint (nerve (Faces n)) s p)
      (1 / ((n : ℝ)+1)) * x v + (1-1/((n : ℝ)+1)) * lo ≤ affineValue x z ∧
      affineValue x z ≤ (1 / ((n : ℝ)+1)) * x v + (1-1/((n : ℝ)+1)) * hi := by
  obtain ⟨v, hv⟩ := simplex_common_mass n m s
  exact ⟨v, fun p => common_mass_bounds x _ v _ lo hi (hv p) hx⟩

/-- The affine mesh contracts uniformly, including all boundary points. -/
theorem simplex_affine_oscillation (n m : ℕ) (s : Fin (m+1) ⥤ Faces n)
    (x : Fin (n+1) → ℝ) (lo hi : ℝ) (hx : ∀ i, lo ≤ x i ∧ x i ≤ hi)
    (p q : StdSimplex ℝ (Fin (m+1))) :
    |affineValue x (point n (RealizationPrism.simplexPoint (nerve (Faces n)) s p)) -
      affineValue x (point n (RealizationPrism.simplexPoint (nerve (Faces n)) s q))| ≤
        (1-1/((n : ℝ)+1)) * (hi-lo) := by
  obtain ⟨v, hv⟩ := simplex_affine_interval n m s x lo hi hx
  have hp := hv p
  have hq := hv q
  rw [abs_le]
  constructor <;> nlinarith [hp.1, hp.2, hq.1, hq.2]

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Euclidean mesh contraction for affine subdivided simplices

This estimate applies to arbitrary vertex locations. It can therefore be
iterated on the affine simplices arising at later subdivision stages.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity

noncomputable section

/-- A strict chain of faces cannot have greater dimension than its
original simplex. Degenerate repetitions are excluded explicitly. -/
theorem face_chain_dimension_le (n m : ℕ) (s : Fin (m+1) ⥤ Faces n)
    (hs : StrictMono s.obj) : m ≤ n := by
  classical
  let f : Fin (m+1) → Fin (n+1) := fun i =>
    ⟨(s.obj i).finset.card - 1, by
      have hc := Finset.card_le_univ (s.obj i).finset
      have hp := Finset.card_pos.mpr (s.obj i).nonempty
      simp only [Fintype.card_ulift, Fintype.card_fin] at hc
      omega⟩
  have hf : StrictMono f := by
    intro i j hij
    have hc : (s.obj i).finset.card < (s.obj j).finset.card :=
      Finset.card_lt_card (hs hij)
    have hp := Finset.card_pos.mpr (s.obj i).nonempty
    change (s.obj i).finset.card - 1 < (s.obj j).finset.card - 1
    omega
  have hcard := Fintype.card_le_of_injective f hf.injective
  simpa only [Fintype.card_fin, Nat.add_le_add_iff_right] using hcard

/-- Affine coordinates with arbitrary Euclidean vertex locations. -/
def affineCoordinates {n d : ℕ} (x : Fin (n+1) → Fin d → ℝ)
    (p : StdSimplex ℝ (Fin (n+1))) : Fin d → ℝ :=
  fun j => affineValue (fun i => x i j) p

/-- For any Euclidean realization of an n-simplex, every barycentrically
subdivided simplex has at most `1-1/(n+1)` times the original mesh. -/
theorem simplex_affine_dist (n m d : ℕ) (s : Fin (m+1) ⥤ Faces n)
    (x : Fin (n+1) → Fin d → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hx : ∀ i j, dist (x i) (x j) ≤ D)
    (p q : StdSimplex ℝ (Fin (m+1))) :
    dist (affineCoordinates x (point n (RealizationPrism.simplexPoint (nerve (Faces n)) s p)))
      (affineCoordinates x (point n (RealizationPrism.simplexPoint (nerve (Faces n)) s q))) ≤
        (1-1/((n : ℝ)+1)) * D := by
  have hρ : 0 ≤ 1-1/((n : ℝ)+1) := by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  apply (dist_pi_le_iff (mul_nonneg hρ hD)).mpr
  intro j
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ (fun i => x i j)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n+1))).Nonempty)
  obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ (fun i => x i j)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n+1))).Nonempty)
  have hbounds : ∀ i, x a j ≤ x i j ∧ x i j ≤ x b j :=
    fun i => ⟨ha i (Finset.mem_univ i), hb i (Finset.mem_univ i)⟩
  have hwidth : x b j - x a j ≤ D := by
    calc
      _ ≤ |x b j - x a j| := le_abs_self _
      _ = dist (x b j) (x a j) := (Real.dist_eq _ _).symm
      _ ≤ dist (x b) (x a) := dist_le_pi_dist (x b) (x a) j
      _ ≤ D := hx b a
  change |affineValue (fun i => x i j)
      (point n (RealizationPrism.simplexPoint (nerve (Faces n)) s p)) -
    affineValue (fun i => x i j)
      (point n (RealizationPrism.simplexPoint (nerve (Faces n)) s q))| ≤ _
  exact (simplex_affine_oscillation n m s (fun i => x i j) (x a j) (x b j)
    hbounds p q).trans (mul_le_mul_of_nonneg_left hwidth hρ)

/-- The corresponding setwise diameter estimate includes the complete
closed characteristic simplex, hence every face and vertex. -/
theorem simplex_affine_diam (n m d : ℕ) (s : Fin (m+1) ⥤ Faces n)
    (x : Fin (n+1) → Fin d → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hx : ∀ i j, dist (x i) (x j) ≤ D) :
    Metric.diam (Set.range (fun p : StdSimplex ℝ (Fin (m+1)) =>
      affineCoordinates x (point n (RealizationPrism.simplexPoint (nerve (Faces n)) s p)))) ≤
        (1-1/((n : ℝ)+1)) * D := by
  have hρ : 0 ≤ 1-1/((n : ℝ)+1) := by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg hρ hD)
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
  exact simplex_affine_dist n m d s x D hD hx p q

/-- A single ambient dimension gives a uniform contraction factor for
all lower-dimensional faces that occur in subsequent subdivisions. -/
theorem simplex_affine_dist_of_dim_le (n k m d : ℕ) (hkn : k ≤ n)
    (s : Fin (m+1) ⥤ Faces k) (x : Fin (k+1) → Fin d → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hx : ∀ i j, dist (x i) (x j) ≤ D)
    (p q : StdSimplex ℝ (Fin (m+1))) :
    dist (affineCoordinates x (point k (RealizationPrism.simplexPoint (nerve (Faces k)) s p)))
      (affineCoordinates x (point k (RealizationPrism.simplexPoint (nerve (Faces k)) s q))) ≤
        (1-1/((n : ℝ)+1)) * D := by
  have hden : (k : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hkn 1
  have hinv := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (k : ℝ)+1) hden
  have hρ : 1-1/((k : ℝ)+1) ≤ 1-1/((n : ℝ)+1) := by linarith
  exact (simplex_affine_dist k m d s x D hD hx p q).trans
    (mul_le_mul_of_nonneg_right hρ hD)

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Common-mass estimates on finite supported vertex families

Only vertices in the positive support need coordinate bounds. This lets
the barycentric mesh estimate be applied inside each original face,
without requiring a diameter bound on unrelated vertices.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open Convexity

noncomputable section

variable {P : Type} [Fintype P]

def finiteAffineValue (x : P → ℝ) (p : StdSimplex ℝ P) : ℝ :=
  ∑ i, p.weights i * x i

theorem finiteAffineValue_sub (x : P → ℝ) (p : StdSimplex ℝ P) (c : ℝ) :
    finiteAffineValue (fun i => x i-c) p = finiteAffineValue x p-c := by
  simp only [finiteAffineValue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    p.total_of_fintype, one_mul]

theorem finiteAffineValue_const_sub (x : P → ℝ) (p : StdSimplex ℝ P) (c : ℝ) :
    finiteAffineValue (fun i => c-x i) p = c-finiteAffineValue x p := by
  simp only [finiteAffineValue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    p.total_of_fintype, one_mul]

theorem supported_common_mass_bounds (x : P → ℝ) (p : StdSimplex ℝ P)
    (v : P) (ε lo hi : ℝ) (hmass : ε ≤ p.weights v)
    (hv : lo ≤ x v ∧ x v ≤ hi)
    (hx : ∀ i, p.weights i ≠ 0 → lo ≤ x i ∧ x i ≤ hi) :
    ε*x v + (1-ε)*lo ≤ finiteAffineValue x p ∧
      finiteAffineValue x p ≤ ε*x v + (1-ε)*hi := by
  have hl : ε*(x v-lo) ≤ finiteAffineValue (fun i => x i-lo) p := by
    calc
      _ ≤ p.weights v * (x v-lo) :=
        mul_le_mul_of_nonneg_right hmass (sub_nonneg.mpr hv.1)
      _ ≤ ∑ i, p.weights i * (x i-lo) := by
        apply Finset.single_le_sum _ (Finset.mem_univ v)
        intro i _
        by_cases hi : p.weights i = 0
        · simp only [hi, zero_mul, le_refl]
        · exact mul_nonneg (p.nonneg i) (sub_nonneg.mpr (hx i hi).1)
  have hh : ε*(hi-x v) ≤ finiteAffineValue (fun i => hi-x i) p := by
    calc
      _ ≤ p.weights v * (hi-x v) :=
        mul_le_mul_of_nonneg_right hmass (sub_nonneg.mpr hv.2)
      _ ≤ ∑ i, p.weights i * (hi-x i) := by
        apply Finset.single_le_sum _ (Finset.mem_univ v)
        intro i _
        by_cases hz : p.weights i = 0
        · simp only [hz, zero_mul, le_refl]
        · exact mul_nonneg (p.nonneg i) (sub_nonneg.mpr (hx i hz).2)
  rw [finiteAffineValue_sub] at hl
  rw [finiteAffineValue_const_sub] at hh
  constructor <;> nlinarith

theorem supported_common_mass_dist (x : P → ℝ) (p q : StdSimplex ℝ P)
    (v : P) (ε lo hi : ℝ) (hp : ε ≤ p.weights v) (hq : ε ≤ q.weights v)
    (hv : lo ≤ x v ∧ x v ≤ hi)
    (hpx : ∀ i, p.weights i ≠ 0 → lo ≤ x i ∧ x i ≤ hi)
    (hqx : ∀ i, q.weights i ≠ 0 → lo ≤ x i ∧ x i ≤ hi) :
    |finiteAffineValue x p-finiteAffineValue x q| ≤ (1-ε)*(hi-lo) := by
  have h₁ := supported_common_mass_bounds x p v ε lo hi hp hv hpx
  have h₂ := supported_common_mass_bounds x q v ε lo hi hq hv hqx
  rw [abs_le]
  constructor <;> nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Representing subdivision simplices by subdivided standard simplices -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem subdivision_simplex_representation (K : SSet.{0})
    (d : SimplexCategoryᵒᵖ) (x : (SSet.sd.obj K).obj d) :
    ∃ (n : SimplexCategory) (f : SSet.stdSimplex.obj n ⟶ K)
      (y : (SSet.sd.obj (SSet.stdSimplex.obj n)).obj d), (SSet.sd.map f).app d y = x := by
  have := subdividedSimplexCover_epi K
  have hcover : (⨆ s : K.N,
      SSet.Subcomplex.range (SSet.sd.map (SSet.yonedaEquiv.symm s.simplex))) = ⊤ := by
    rw [← SSet.Subcomplex.range_eq_top (subdividedSimplexCover K),
      SSet.range_eq_iSup_sigma_ι]
    simp only [subdividedSimplexCover_ι]
    rfl
  have hx : x ∈ (⨆ s : K.N,
      SSet.Subcomplex.range (SSet.sd.map (SSet.yonedaEquiv.symm s.simplex))).obj d := by
    rw [hcover]
    trivial
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj, Set.mem_range] at hx
  obtain ⟨s, y, hy⟩ := hx
  exact ⟨.mk s.dim, SSet.yonedaEquiv.symm s.simplex, y, hy⟩

end

end Thomason.Construction

end

section

/-! # Comparing the two last-vertex maps on double subdivision -/

namespace Thomason.Construction

open CategoryTheory PartialOrder MonoidalCategory
open scoped Simplicial

noncomputable section

def simplexDoubleFirst (n : SimplexCategory) :
    SSet.sd.obj (SimplexCategory.sd.{0}.obj n) ⟶ SimplexCategory.sd.obj n :=
  SSet.sd.map (simplexLastVertex.app n) ≫ SSet.stdSimplex.sdIso.hom.app n

def simplexDoubleLast (n : SimplexCategory) :
    SSet.sd.obj (SimplexCategory.sd.{0}.obj n) ⟶ SimplexCategory.sd.obj n :=
  lastVertex.app (SimplexCategory.sd.obj n)

/-- The ordinal map given by the maxima of the vertices of a simplex in
the chain-poset nerve. -/
def simplexMaximumMap {m n : SimplexCategory}
    (s : SSet.stdSimplex.{0}.obj m ⟶ SimplexCategory.sd.obj n) : m ⟶ n :=
  SimplexCategory.Hom.mk {
    toFun i := (chainMaximum (X := ULift.{0} (Fin (n.len + 1)))
      ((SSet.yonedaEquiv s).obj i)).down
    monotone' := by
      intro i j hij
      exact chainMaximum_monotone (X := ULift.{0} (Fin (n.len + 1)))
        (leOfHom (X := NonemptyFiniteChains (ULift.{0} (Fin (n.len + 1))))
          ((SSet.yonedaEquiv s).map (homOfLE hij))) }

theorem simplexMaximumMap_fac {m n : SimplexCategory}
    (s : SSet.stdSimplex.{0}.obj m ⟶ SimplexCategory.sd.obj n) :
    s ≫ simplexLastVertex.app n = SSet.stdSimplex.map (simplexMaximumMap s) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.objEquiv.injective
  ext i
  rfl

/-- Every maximum contributed by a smaller chain belongs to the greatest
chain in the simplex. This is the key ordered comparison. -/
theorem simplexMaximumMap_chain_le {m n : SimplexCategory}
    (s : SSet.stdSimplex.{0}.obj m ⟶ SimplexCategory.sd.obj n)
    (B : NonemptyFiniteChains (ULift.{0} (Fin (m.len + 1)))) :
    NonemptyFiniteChains.orderHomMap
        (SimplexCategory.toPartOrd.map (simplexMaximumMap s)).hom B ≤
      (SSet.yonedaEquiv s).obj (chainMaximum B).down := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := (NonemptyFiniteChains.mem_map_iff B _ z).mp hz
  have hs : (SSet.yonedaEquiv s).obj i.down ≤
      (SSet.yonedaEquiv s).obj (chainMaximum B).down :=
    leOfHom ((SSet.yonedaEquiv s).map (homOfLE (Finset.le_max' B.finset i hi)))
  change chainMaximum (X := ULift.{0} (Fin (n.len + 1)))
    ((SSet.yonedaEquiv s).obj i.down) ∈ _
  let A : NonemptyFiniteChains (ULift.{0} (Fin (n.len + 1))) :=
    (SSet.yonedaEquiv s).obj i.down
  have hm : chainMaximum A ∈ A.finset := Finset.max'_mem A.finset A.nonempty
  exact hs hm

theorem simplexLastVertex_zero_comp {m n : SimplexCategory}
    (s : SSet.stdSimplex.{0}.obj m ⟶ SimplexCategory.sd.obj n)
    (z : (SimplexCategory.sd.obj m) _⦋0⦌) :
    ((simplexLastVertex.app m ≫ s).app _ z).obj 0 =
      (SSet.yonedaEquiv s).obj
        (chainMaximum (X := ULift.{0} (Fin (m.len + 1))) (z.obj 0)).down := by
  obtain ⟨t, rfl⟩ := SSet.yonedaEquiv.symm.surjective s
  simp only [Equiv.apply_symm_apply]
  rfl

theorem simplexDoubleFirst_le (n : SimplexCategory)
    (x : (SSet.sd.obj (SimplexCategory.sd.{0}.obj n)) _⦋0⦌) :
    ((simplexDoubleFirst n).app _ x).obj 0 ≤
      ((simplexDoubleLast n).app _ x).obj 0 := by
  obtain ⟨m, s, y, rfl⟩ := subdivision_simplex_representation (SimplexCategory.sd.obj n) _ x
  let z := (SSet.stdSimplex.sdIso.hom.app m).app _ y
  have hy : (SSet.stdSimplex.sdIso.inv.app m).app _ z = y := by
    exact congrArg (fun f => f.app _ y) (SSet.stdSimplex.sdIso.hom_inv_id_app m)
  rw [← hy]
  have hfirst : SSet.stdSimplex.sdIso.inv.app m ≫ SSet.sd.map s ≫ simplexDoubleFirst n =
      SimplexCategory.sd.map (simplexMaximumMap s) := by
    calc
      _ = SSet.stdSimplex.sdIso.inv.app m ≫
          SSet.sd.map (s ≫ simplexLastVertex.app n) ≫ SSet.stdSimplex.sdIso.hom.app n := by
        simp only [simplexDoubleFirst, Functor.map_comp, Category.assoc]
      _ = _ := by
        rw [simplexMaximumMap_fac]
        have hn : SSet.sd.map (SSet.stdSimplex.map (simplexMaximumMap s)) ≫
            SSet.stdSimplex.sdIso.hom.app n =
            SSet.stdSimplex.sdIso.hom.app m ≫ SimplexCategory.sd.map (simplexMaximumMap s) :=
          SSet.stdSimplex.sdIso.hom.naturality _
        rw [hn, ← Category.assoc, SSet.stdSimplex.sdIso.inv_hom_id_app]
        exact Category.id_comp _
  have hlast : SSet.stdSimplex.sdIso.inv.app m ≫ SSet.sd.map s ≫ simplexDoubleLast n =
      simplexLastVertex.app m ≫ s := by
    have he : SSet.sd.map s ≫ lastVertex.app (SimplexCategory.sd.obj n) =
        lastVertex.app (SSet.stdSimplex.obj m) ≫ s := lastVertex.naturality s
    rw [simplexDoubleLast, he, ← Category.assoc, lastVertex_on_standard_simplex]
  have hf := congrArg (fun f => (f.app _ z).obj (0 : Fin 1)) hfirst
  have hl := congrArg (fun f => (f.app _ z).obj (0 : Fin 1)) hlast
  change ((SSet.stdSimplex.sdIso.inv.app m ≫ SSet.sd.map s ≫ simplexDoubleFirst n).app _ z).obj 0 ≤
    ((SSet.stdSimplex.sdIso.inv.app m ≫ SSet.sd.map s ≫ simplexDoubleLast n).app _ z).obj 0
  rw [hf, hl]
  rw [simplexLastVertex_zero_comp]
  exact simplexMaximumMap_chain_le s (z.obj 0)

def simplexDoubleHomotopy (n : SimplexCategory) :
    SSet.Homotopy (simplexDoubleFirst n) (simplexDoubleLast n) :=
  PosetGeometry.orderedVertexHomotopy _ _ (simplexDoubleFirst_le n)

def simplexDoublePrism (n : SimplexCategory) :
    SSet.sd.obj (SimplexCategory.sd.{0}.obj n) ⊗ Δ[1] ⟶ SimplexCategory.sd.obj n :=
  (simplexDoubleHomotopy n).h

theorem simplexDoublePrism_zero (n : SimplexCategory) :
    SSet.ι₀ ≫ simplexDoublePrism n = simplexDoubleFirst n := (simplexDoubleHomotopy n).h₀

theorem simplexDoublePrism_one (n : SimplexCategory) :
    SSet.ι₁ ≫ simplexDoublePrism n = simplexDoubleLast n := (simplexDoubleHomotopy n).h₁

theorem simplexDoubleFirst_naturality {m n : SimplexCategory} (a : m ⟶ n) :
    SSet.sd.map (SimplexCategory.sd.map a) ≫ simplexDoubleFirst n =
      simplexDoubleFirst m ≫ SimplexCategory.sd.map a := by
  have h : SimplexCategory.sd.map a ≫ simplexLastVertex.app n =
      simplexLastVertex.app m ≫ SSet.stdSimplex.map a := simplexLastVertex.naturality a
  calc
    _ = SSet.sd.map (SimplexCategory.sd.map a ≫ simplexLastVertex.app n) ≫
        SSet.stdSimplex.sdIso.hom.app n := by
      simp only [simplexDoubleFirst, Functor.map_comp, Category.assoc]
    _ = SSet.sd.map (simplexLastVertex.app m ≫ SSet.stdSimplex.map a) ≫
        SSet.stdSimplex.sdIso.hom.app n := by rw [h]
    _ = _ := by
      have hn : SSet.sd.map (SSet.stdSimplex.map a) ≫ SSet.stdSimplex.sdIso.hom.app n =
          SSet.stdSimplex.sdIso.hom.app m ≫ SimplexCategory.sd.map a :=
        SSet.stdSimplex.sdIso.hom.naturality a
      rw [Functor.map_comp, Category.assoc, hn]
      rfl

theorem simplexDoubleLast_naturality {m n : SimplexCategory} (a : m ⟶ n) :
    SSet.sd.map (SimplexCategory.sd.map a) ≫ simplexDoubleLast n =
      simplexDoubleLast m ≫ SimplexCategory.sd.map a :=
  lastVertex.naturality (SimplexCategory.sd.map a)

theorem simplexDoubleHomotopy_naturality {m n : SimplexCategory} (a : m ⟶ n) :
    (SSet.sd.map (SimplexCategory.sd.map a) ▷ Δ[1]) ≫ simplexDoublePrism n =
      simplexDoublePrism m ≫ SimplexCategory.sd.map a := by
  exact PosetGeometry.orderedVertexHomotopy_naturality
    (simplexDoubleFirst m) (simplexDoubleLast m)
    (simplexDoubleFirst n) (simplexDoubleLast n)
    (simplexDoubleFirst_le m) (simplexDoubleFirst_le n)
    (SSet.sd.map (SimplexCategory.sd.map a))
    (NonemptyFiniteChains.orderHomMap (SimplexCategory.toPartOrd.map a).hom)
    (simplexDoubleFirst_naturality a) (simplexDoubleLast_naturality a)

theorem lastVertex_standard_formula (n : SimplexCategory) :
    SSet.stdSimplex.sdIso.hom.app n ≫ simplexLastVertex.app n =
      lastVertex.app (SSet.stdSimplex.obj n) := by
  have h := congrArg (fun f => SSet.stdSimplex.sdIso.hom.app n ≫ f)
    (lastVertex_on_standard_simplex n)
  simpa only [← Category.assoc, SSet.stdSimplex.sdIso.hom_inv_id_app, Category.id_comp] using h.symm

theorem simplexDoubleFirst_conjugate (n : SimplexCategory) :
    SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) ≫ simplexDoubleFirst n ≫
      SSet.stdSimplex.sdIso.inv.app n =
      SSet.sd.map (lastVertex.app (SSet.stdSimplex.obj n)) := by
  calc
    _ = SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n ≫ simplexLastVertex.app n) := by
      simp only [simplexDoubleFirst, Functor.map_comp, Category.assoc,
        SSet.stdSimplex.sdIso.hom_inv_id_app]
      exact congrArg (fun k => SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) ≫ k)
        (Category.comp_id (SSet.sd.map (simplexLastVertex.app n)))
    _ = _ := congrArg SSet.sd.map (lastVertex_standard_formula n)

theorem simplexDoubleLast_conjugate (n : SimplexCategory) :
    SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) ≫ simplexDoubleLast n ≫
      SSet.stdSimplex.sdIso.inv.app n =
      lastVertex.app (SSet.sd.obj (SSet.stdSimplex.obj n)) := by
  have h : SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) ≫ simplexDoubleLast n =
      lastVertex.app (SSet.sd.obj (SSet.stdSimplex.obj n)) ≫
        SSet.stdSimplex.sdIso.hom.app n :=
    lastVertex.naturality (SSet.stdSimplex.sdIso.hom.app n)
  rw [← Category.assoc, h, Category.assoc, SSet.stdSimplex.sdIso.hom_inv_id_app]
  exact Category.comp_id _

/-- The comparison on the double subdivision of a standard simplex. -/
def standardDoubleHomotopy (n : SimplexCategory) :
    SSet.Homotopy (SSet.sd.map (lastVertex.app (SSet.stdSimplex.obj n)))
      (lastVertex.app (SSet.sd.obj (SSet.stdSimplex.obj n))) where
  h := (SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) ▷ Δ[1]) ≫
    simplexDoublePrism n ≫ SSet.stdSimplex.sdIso.inv.app n
  h₀ := by
    change SSet.ι₀ ≫ ((SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) ▷ Δ[1]) ≫
      simplexDoublePrism n ≫ SSet.stdSimplex.sdIso.inv.app n) =
        SSet.sd.map (lastVertex.app (SSet.stdSimplex.obj n))
    rw [← Category.assoc, SSet.ι₀_comp]
    simp only [Category.assoc]
    rw [← Category.assoc SSet.ι₀, simplexDoublePrism_zero]
    exact simplexDoubleFirst_conjugate n
  h₁ := by
    change SSet.ι₁ ≫ ((SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) ▷ Δ[1]) ≫
      simplexDoublePrism n ≫ SSet.stdSimplex.sdIso.inv.app n) =
        lastVertex.app (SSet.sd.obj (SSet.stdSimplex.obj n))
    rw [← Category.assoc, SSet.ι₁_comp]
    simp only [Category.assoc]
    rw [← Category.assoc SSet.ι₁, simplexDoublePrism_one]
    exact simplexDoubleLast_conjugate n
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

theorem standardDoubleHomotopy_naturality {m n : SimplexCategory} (a : m ⟶ n) :
    (SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map a)) ▷ Δ[1]) ≫
        (standardDoubleHomotopy n).h =
      (standardDoubleHomotopy m).h ≫ SSet.sd.map (SSet.stdSimplex.map a) := by
  have h : SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map a)) ≫
      SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) =
      SSet.sd.map (SSet.stdSimplex.sdIso.hom.app m) ≫
        SSet.sd.map (SimplexCategory.sd.map a) := by
    have hn : SSet.sd.map (SSet.stdSimplex.map a) ≫ SSet.stdSimplex.sdIso.hom.app n =
        SSet.stdSimplex.sdIso.hom.app m ≫ SimplexCategory.sd.map a :=
      SSet.stdSimplex.sdIso.hom.naturality a
    rw [← Functor.map_comp, hn, Functor.map_comp]
  change (_ ▷ Δ[1]) ≫ ((_ ▷ Δ[1]) ≫ _ ≫ _) = ((_ ▷ Δ[1]) ≫ _ ≫ _) ≫ _
  rw [← Category.assoc, ← comp_whiskerRight, h, comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc (SSet.sd.map (SimplexCategory.sd.map a) ▷ Δ[1])
    (simplexDoublePrism n) (SSet.stdSimplex.sdIso.inv.app n),
    simplexDoubleHomotopy_naturality]
  have hn : SimplexCategory.sd.map a ≫ SSet.stdSimplex.sdIso.inv.app n =
      SSet.stdSimplex.sdIso.inv.app m ≫ SSet.sd.map (SSet.stdSimplex.map a) :=
    SSet.stdSimplex.sdIso.inv.naturality a
  simp only [Category.assoc]
  rw [hn]

/-- The compatible comparison prism attached to each original simplex. -/
def doubleLastVertexPiece (K : SSet.{0}) (j : CostructuredArrow SSet.stdSimplex K) :
    SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.obj j.left)) ⊗ Δ[1] ⟶ SSet.sd.obj K :=
  (standardDoubleHomotopy j.left).h ≫ SSet.sd.map j.hom

theorem doubleLastVertexPiece_naturality (K : SSet.{0})
    {i j : CostructuredArrow SSet.stdSimplex K} (a : i ⟶ j) :
    (SSet.sd.map (SSet.sd.map (SSet.stdSimplex.map a.left)) ▷ Δ[1]) ≫
      doubleLastVertexPiece K j = doubleLastVertexPiece K i := by
  rw [doubleLastVertexPiece, ← Category.assoc, standardDoubleHomotopy_naturality,
    Category.assoc, ← Functor.map_comp, CostructuredArrow.w a]
  rfl

/-- The two canonical last-vertex maps from double subdivision are
actually simplicially homotopic, for every small simplicial set. -/
def subdivisionLastVertexHomotopy (K : SSet.{0}) :
    SSet.Homotopy (SSet.sd.map (lastVertex.app K))
      (lastVertex.app (SSet.sd.obj K)) := by
  apply SimplicialHomotopyDescent.homotopy (SSet.sd ⋙ SSet.sd) K (SSet.sd.obj K)
    (doubleLastVertexPiece K) (doubleLastVertexPiece_naturality K)
  · intro j
    change SSet.ι₀ ≫ ((standardDoubleHomotopy j.left).h ≫ SSet.sd.map j.hom) = _
    have he : lastVertex.app (SSet.stdSimplex.obj j.left) ≫ j.hom =
        SSet.sd.map j.hom ≫ lastVertex.app K := (lastVertex.naturality j.hom).symm
    rw [← Category.assoc, (standardDoubleHomotopy j.left).h₀,
      ← Functor.map_comp, he, Functor.map_comp]
    rfl
  · intro j
    change SSet.ι₁ ≫ ((standardDoubleHomotopy j.left).h ≫ SSet.sd.map j.hom) = _
    rw [← Category.assoc, (standardDoubleHomotopy j.left).h₁]
    exact (lastVertex.naturality (SSet.sd.map j.hom)).symm

end

end Thomason.Construction

end

section

/-! # The canonical extension is an actual weak equivalence

The natural double-subdivision homotopy, the proved last-vertex weak
equivalence, and actual weak-equivalence two-out-of-six discharge the
canonical-extension input without invoking Kan--Quillen.
-/

namespace Thomason.Construction

/-- The actual Goerss--Jardine canonical extension map is weak on every
small simplicial set, for the geometric-realization weak equivalences. -/
theorem canonicalExtension_weak (K : SSet.{0}) :
    realizationWeakEquivalences (canonicalExtension.app K) :=
  canonicalExtension_weak_of_subdivision_homotopy subdivisionLastVertexHomotopy K

end Thomason.Construction

end

section

/-! # The actual extension localization, without a Kan--Quillen input -/

namespace Thomason.Construction

open CategoryTheory

/-- Extension preserves and reflects the weak equivalences of actual
geometric realizations, using the weak canonical coaugmentation. -/
theorem extension_realization_weak_iff {X Y : SSet.{0}} (f : X ⟶ Y) :
    realizationWeakEquivalences (SSet.ex.map f) ↔ realizationWeakEquivalences f :=
  ex_map_iff realizationWeakEquivalences canonicalExtension canonicalExtension_weak f

/-- Both extension stages in the Thomason right adjoint preserve and
reflect the actual geometric weak-equivalence test. -/
theorem extension_twice_realization_weak_iff {X Y : SSet.{0}} (f : X ⟶ Y) :
    realizationWeakEquivalences ((SSet.ex ⋙ SSet.ex).map f) ↔
      realizationWeakEquivalences f :=
  realization_ex_twice_iff canonicalExtension_weak f

/-- The extension functor on the actual realization localizer uses no
model-category input. -/
noncomputable def constructedExtensionLocalizer :
    LocalizerMorphism realizationWeakEquivalences realizationWeakEquivalences where
  functor := SSet.ex
  map := by
    intro X Y f hf
    exact (extension_realization_weak_iff f).mpr hf

/-- The coaugmentation constructs the inverse of extension after
localization, without assuming Kan--Quillen or Street localization. -/
theorem constructedExtensionLocalizer_isLocalizedEquivalence :
    constructedExtensionLocalizer.IsLocalizedEquivalence := by
  let Φ := constructedExtensionLocalizer
  let Ψ := LocalizerMorphism.id realizationWeakEquivalences
  apply Φ.isLocalizedEquivalence_of_unit_of_unit Ψ
    (canonicalExtension ≫ (Functor.rightUnitor SSet.ex).inv)
    (canonicalExtension ≫ (Functor.leftUnitor SSet.ex).inv)
  · intro X
    change realizationWeakEquivalences (canonicalExtension.app X ≫ 𝟙 _)
    simpa using canonicalExtension_weak X
  · intro X
    change realizationWeakEquivalences (canonicalExtension.app X ≫ 𝟙 _)
    simpa using canonicalExtension_weak X

end Thomason.Construction

end

end OAI
