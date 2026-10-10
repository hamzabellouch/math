import OAI.Geometry.ProjectionVolume.PolytopeDefinitions
import OAI.Geometry.ProjectionVolume.ProductDefinition
import OAI.Geometry.ProjectionVolume.ProductFacetAreas
import OAI.Geometry.ProjectionVolume.Brightness

namespace OAI

universe uι uκ uα

noncomputable section
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace Pointwise

namespace Paper092

theorem cartesianBody_eq_preimage {r s : ℕ} (A : Set (Euclidean r)) (B : Set (Euclidean s)) :
    cartesianBody A B = splitEuclideanProduct r s ⁻¹' (A ×ˢ B) := rfl

def productLiftLeft (r s : ℕ) (x : Euclidean r) : Euclidean (r + s) :=
  (splitEuclideanProduct r s).symm (x, 0)

def productLiftRight (r s : ℕ) (x : Euclidean s) : Euclidean (r + s) :=
  (splitEuclideanProduct r s).symm (0, x)

@[simp] theorem split_productLiftLeft (r s : ℕ) (x : Euclidean r) :
    splitEuclideanProduct r s (productLiftLeft r s x) = (x, 0) :=
  (splitEuclideanProduct r s).apply_symm_apply _

@[simp] theorem split_productLiftRight (r s : ℕ) (x : Euclidean s) :
    splitEuclideanProduct r s (productLiftRight r s x) = (0, x) :=
  (splitEuclideanProduct r s).apply_symm_apply _

theorem inner_productLiftLeft (r s : ℕ) (x : Euclidean r) (y : Euclidean (r + s)) :
    ⟪productLiftLeft r s x, y⟫ = ⟪x, (splitEuclideanProduct r s y).1⟫ := by
  rw [splitEuclideanProduct_inner r s, split_productLiftLeft]
  simp

theorem inner_productLiftRight (r s : ℕ) (x : Euclidean s) (y : Euclidean (r + s)) :
    ⟪productLiftRight r s x, y⟫ = ⟪x, (splitEuclideanProduct r s y).2⟫ := by
  rw [splitEuclideanProduct_inner r s, split_productLiftRight]
  simp

@[simp] theorem productLiftLeft_norm (r s : ℕ) (x : Euclidean r) :
    ‖productLiftLeft r s x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, inner_productLiftLeft, split_productLiftLeft]
  exact real_inner_self_eq_norm_sq _

@[simp] theorem productLiftRight_norm (r s : ℕ) (x : Euclidean s) :
    ‖productLiftRight r s x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, inner_productLiftRight, split_productLiftRight]
  exact real_inner_self_eq_norm_sq _

theorem cartesianBody_isCompact {r s : ℕ} {A : Set (Euclidean r)} {B : Set (Euclidean s)}
    (hA : IsCompact A) (hB : IsCompact B) : IsCompact (cartesianBody A B) := by
  rw [cartesianBody_eq_preimage]
  exact (splitEuclideanProduct r s).toHomeomorph.isCompact_preimage.mpr (hA.prod hB)

theorem cartesianBody_convex {r s : ℕ} {A : Set (Euclidean r)} {B : Set (Euclidean s)}
    (hA : Convex ℝ A) (hB : Convex ℝ B) : Convex ℝ (cartesianBody A B) := by
  rw [cartesianBody_eq_preimage]
  exact (hA.prod hB).linear_preimage (splitEuclideanProduct r s).toLinearMap

theorem cartesianBody_interior_nonempty {r s : ℕ} {A : Set (Euclidean r)}
    {B : Set (Euclidean s)} (hA : (interior A).Nonempty) (hB : (interior B).Nonempty) :
    (interior (cartesianBody A B)).Nonempty := by
  rw [cartesianBody_eq_preimage]
  change (interior ((splitEuclideanProduct r s).toHomeomorph ⁻¹' (A ×ˢ B))).Nonempty
  rw [← Homeomorph.preimage_interior, interior_prod_eq]
  exact (hA.prod hB).preimage (splitEuclideanProduct r s).surjective

namespace HPolytope

variable {r s : ℕ} {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]

theorem body_interior_nonempty {d : ℕ} {α : Type uα} [Fintype α] (P : HPolytope d α) :
    (interior P.body).Nonempty := by
  obtain ⟨x, hx⟩ := P.strict_feasible
  let U : Set (Euclidean d) := {y | ∀ i, ⟪P.normal i, y⟫ < P.offset i}
  have hU : IsOpen U := by
    dsimp [U]
    rw [ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (innerSL ℝ (P.normal i)).continuous continuous_const
  have hsub : U ⊆ P.body := fun y hy i => (hy i).le
  exact ⟨x, interior_maximal hsub hU hx⟩

theorem volume_pos {d : ℕ} {α : Type uα} [Fintype α] (P : HPolytope d α) :
    0 < (volume P.body).toReal :=
  ENNReal.toReal_pos (ne_of_gt (Measure.measure_pos_of_nonempty_interior volume
    P.body_interior_nonempty)) P.compact.measure_lt_top.ne

def productNormal (A : HPolytope r ι) (B : HPolytope s κ) : ι ⊕ κ → Euclidean (r + s) :=
  Sum.elim (fun i => productLiftLeft r s (A.normal i))
    (fun i => productLiftRight r s (B.normal i))

def productOffset (A : HPolytope r ι) (B : HPolytope s κ) : ι ⊕ κ → ℝ :=
  Sum.elim A.offset B.offset

theorem product_halfspaces_eq (A : HPolytope r ι) (B : HPolytope s κ) :
    {x | ∀ i, ⟪productNormal A B i, x⟫ ≤ productOffset A B i} =
      cartesianBody A.body B.body := by
  ext x
  simp only [Set.mem_ofPred_eq, Sum.forall, productNormal, productOffset,
    Sum.elim_inl, Sum.elim_inr, inner_productLiftLeft, inner_productLiftRight,
    cartesianBody_eq_preimage, Set.mem_preimage, Set.mem_prod, body]

def product (A : HPolytope r ι) (B : HPolytope s κ) : HPolytope (r + s) (ι ⊕ κ) where
  normal := productNormal A B
  offset := productOffset A B
  normal_unit i := by cases i <;> simp [productNormal, A.normal_unit, B.normal_unit]
  compact := by
    rw [product_halfspaces_eq]
    exact cartesianBody_isCompact A.compact B.compact
  strict_feasible := by
    obtain ⟨a, ha⟩ := A.strict_feasible
    obtain ⟨b, hb⟩ := B.strict_feasible
    refine ⟨(splitEuclideanProduct r s).symm (a, b), ?_⟩
    intro i
    cases i <;>
      simp only [productNormal, productOffset, Sum.elim_inl, Sum.elim_inr,
        inner_productLiftLeft, inner_productLiftRight, ContinuousLinearEquiv.apply_symm_apply]
    · exact ha _
    · exact hb _
  distinct := by
    intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        apply congrArg Sum.inl
        apply A.distinct
        apply Prod.ext
        · have hh := congrArg (fun q => (splitEuclideanProduct r s q.1).1) h
          simpa only [productNormal, Sum.elim_inl, split_productLiftLeft] using hh
        · simpa only [productOffset, Sum.elim_inl, Sum.elim_inr] using
            congrArg (fun q : Euclidean (r + s) × ℝ => q.2) h
      | inr j =>
        have hh := congrArg (fun q => (splitEuclideanProduct r s q.1).1) h
        simp only [productNormal, Sum.elim_inl, Sum.elim_inr,
          split_productLiftLeft, split_productLiftRight] at hh
        have hn := A.normal_unit i
        rw [hh, norm_zero] at hn
        norm_num at hn
    | inr i =>
      cases j with
      | inl j =>
        have hh := congrArg (fun q => (splitEuclideanProduct r s q.1).2) h
        simp only [productNormal, Sum.elim_inl, Sum.elim_inr,
          split_productLiftLeft, split_productLiftRight] at hh
        have hn := B.normal_unit i
        rw [hh, norm_zero] at hn
        norm_num at hn
      | inr j =>
        apply congrArg Sum.inr
        apply B.distinct
        apply Prod.ext
        · have hh := congrArg (fun q => (splitEuclideanProduct r s q.1).2) h
          simpa only [productNormal, Sum.elim_inr, split_productLiftRight] using hh
        · simpa only [productOffset, Sum.elim_inl, Sum.elim_inr] using
            congrArg (fun q : Euclidean (r + s) × ℝ => q.2) h

@[simp] theorem product_body (A : HPolytope r ι) (B : HPolytope s κ) :
    (A.product B).body = cartesianBody A.body B.body := product_halfspaces_eq A B

theorem product_face_inl (A : HPolytope r ι) (B : HPolytope s κ) (i : ι) :
    (A.product B).face (.inl i) = cartesianBody (A.face i) B.body := by
  ext x
  change ((x ∈ (A.product B).body) ∧ ⟪productLiftLeft r s (A.normal i), x⟫ = A.offset i) ↔ _
  rw [product_body, cartesianBody_eq_preimage, inner_productLiftLeft, cartesianBody_eq_preimage]
  exact ⟨fun ⟨⟨ha, hb⟩, he⟩ => ⟨⟨ha, he⟩, hb⟩,
    fun ⟨⟨ha, he⟩, hb⟩ => ⟨⟨ha, hb⟩, he⟩⟩

theorem product_face_inr (A : HPolytope r ι) (B : HPolytope s κ) (i : κ) :
    (A.product B).face (.inr i) = cartesianBody A.body (B.face i) := by
  ext x
  change ((x ∈ (A.product B).body) ∧ ⟪productLiftRight r s (B.normal i), x⟫ = B.offset i) ↔ _
  rw [product_body, cartesianBody_eq_preimage, inner_productLiftRight, cartesianBody_eq_preimage]
  exact and_assoc

end HPolytope
end Paper092

end

end OAI
