import OAI.Analysis.KadisonSimilarity.Tracial.FullColumnTheorem
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixRealization

namespace OAI

/-! Cyclicity of finite tracial corners from dense algebra vectors and
partial-isometry transport. No corner cyclicity or density is assumed. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The concrete data of a tracial Hilbert representation. -/
structure TracialCornerGeometry (P H : Type*) [CStarAlgebra P]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  trace : P →ₗ[ℂ] ℂ
  vector : P →ₗ[ℂ] H
  left : P →⋆ₐ[ℂ] (H →L[ℂ] H)
  inner_vector : ∀ a b, inner ℂ (vector a) (vector b) = trace (star a * b)
  tracial : ∀ a b, trace (a * b) = trace (b * a)
  dense_vector : DenseRange vector
  left_vector : ∀ a b, left a (vector b) = vector (a * b)

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

def conjugation : H →ₗᵢ⋆[ℂ] H :=
  tracialConjugation G.trace G.vector G.inner_vector G.tracial G.dense_vector

@[simp] theorem conjugation_vector (a : P) : G.conjugation (G.vector a) = G.vector (star a) :=
  tracialConjugation_apply_vector G.trace G.vector G.inner_vector G.tracial G.dense_vector a

/-- Actual right multiplication, obtained from the tracial conjugation. -/
def right (b : P) : H →L[ℂ] H :=
  G.conjugation.toContinuousLinearMap.comp
    ((G.left (star b)).comp G.conjugation.toContinuousLinearMap)

@[simp] theorem right_vector (a b : P) : G.right b (G.vector a) = G.vector (a * b) := by
  change G.conjugation (G.left (star b) (G.conjugation (G.vector a))) = _
  rw [conjugation_vector, G.left_vector, conjugation_vector]
  simp only [star_mul, star_star]

theorem right_mul (a b : P) : G.right (a * b) = (G.right b).comp (G.right a) := by
  ext x
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [ContinuousLinearMap.comp_apply, right_vector, mul_assoc]

theorem right_mul_apply (a b : P) (x : H) :
    G.right (a * b) x = G.right b (G.right a x) :=
  congrArg (fun T : H →L[ℂ] H => T x) (G.right_mul a b)

theorem right_left (a b : P) : (G.right b).comp (G.left a) = (G.left a).comp (G.right b) := by
  ext x
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [ContinuousLinearMap.comp_apply, G.left_vector, right_vector, mul_assoc]

theorem right_adjoint (b : P) : (G.right b).adjoint = G.right (star b) := by
  have hinner (x y : H) : inner ℂ x (G.right (star b) y) = inner ℂ (G.right b x) y := by
    refine G.dense_vector.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
    intro a c
    simp only [right_vector, G.inner_vector, star_mul]
    simpa only [mul_assoc] using (G.tracial (star b) (star a * c)).symm
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (hinner x y).symm

/-- The actual Hilbert corner, defined by its two support equations. -/
def corner (e r : P) : ClosedSubmodule ℂ H where
  toSubmodule := (G.left e - ContinuousLinearMap.id ℂ H).ker ⊓
    (G.right r - ContinuousLinearMap.id ℂ H).ker
  isClosed' := (G.left e - ContinuousLinearMap.id ℂ H).isClosed_ker.inter
    (G.right r - ContinuousLinearMap.id ℂ H).isClosed_ker

@[simp] theorem mem_corner (e r : P) (x : H) :
    x ∈ G.corner e r ↔ G.left e x = x ∧ G.right r x = x := by
  simp only [corner, ClosedSubmodule.mem_mk, Submodule.mem_inf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]

def cornerProjection (e r : P) : H →L[ℂ] H := (G.left e).comp (G.right r)

@[simp] theorem cornerProjection_vector (e r a : P) :
    G.cornerProjection e r (G.vector a) = G.vector (e * a * r) := by
  simp only [cornerProjection, ContinuousLinearMap.comp_apply, right_vector, G.left_vector,
    mul_assoc]

theorem cornerProjection_mem (e r : P) (he : IsIdempotentElem e) (hr : IsIdempotentElem r)
    (x : H) : G.cornerProjection e r x ∈ G.corner e r := by
  refine G.dense_vector.induction_on x ((G.corner e r).isClosed.preimage
    (G.cornerProjection e r).continuous) ?_
  intro a
  rw [cornerProjection_vector, mem_corner]
  constructor
  · rw [G.left_vector]
    congr 1
    calc
      e * (e * a * r) = (e * e) * a * r := by noncomm_ring
      _ = e * a * r := by rw [he.eq]
  · rw [right_vector]
    congr 1
    calc
      e * a * r * r = e * a * (r * r) := by noncomm_ring
      _ = e * a * r := by rw [hr.eq]

def cornerInto (e r : P) (he : IsIdempotentElem e) (hr : IsIdempotentElem r) :
    H →L[ℂ] G.corner e r :=
  (G.cornerProjection e r).codRestrict (G.corner e r).toSubmodule
    (G.cornerProjection_mem e r he hr)

@[simp] theorem cornerInto_coe (e r : P) (he : IsIdempotentElem e) (hr : IsIdempotentElem r)
    (x : H) : (G.cornerInto e r he hr x : H) = G.cornerProjection e r x := rfl

theorem cornerInto_self (e r : P) (he : IsIdempotentElem e) (hr : IsIdempotentElem r)
    (x : G.corner e r) : G.cornerInto e r he hr x = x := by
  apply Subtype.ext
  have hx := (G.mem_corner e r x).mp x.property
  change G.left e (G.right r x) = x
  rw [hx.2, hx.1]

/-- Corner density is derived from the dense algebra vectors by a surjective
continuous projection. -/
theorem corner_vectors_dense (e r : P) (he : IsIdempotentElem e) (hr : IsIdempotentElem r) :
    DenseRange (fun a : P => G.cornerInto e r he hr (G.vector a)) := by
  have hs : Function.Surjective (G.cornerInto e r he hr) := fun x =>
    ⟨x, G.cornerInto_self e r he hr x⟩
  exact hs.denseRange.comp G.dense_vector (G.cornerInto e r he hr).continuous

theorem right_transfer_mem (e r v : P) (hv : star v * v = r) (x : G.corner e r) :
    G.right (star v) x ∈ G.corner e (v * star v) := by
  rw [mem_corner]
  have hx := (G.mem_corner e r x).mp x.property
  constructor
  · have hc := congrArg (fun T : H →L[ℂ] H => T (x : H)) (G.right_left e (star v))
    simp only [ContinuousLinearMap.comp_apply] at hc
    rw [← hc, hx.1]
  · calc
      G.right (v * star v) (G.right (star v) x) =
          G.right (star v * (v * star v)) x := (G.right_mul_apply _ _ _).symm
      _ = G.right (r * star v) x := by rw [← mul_assoc, hv]
      _ = G.right (star v) (G.right r x) := G.right_mul_apply _ _ _
      _ = G.right (star v) x := by rw [hx.2]

theorem right_transfer_back_mem (e r v : P) (hv : star v * v = r)
    (x : G.corner e (v * star v)) : G.right v x ∈ G.corner e r := by
  rw [mem_corner]
  have hx := (G.mem_corner e (v * star v) x).mp x.property
  constructor
  · have hc := congrArg (fun T : H →L[ℂ] H => T (x : H)) (G.right_left e v)
    simp only [ContinuousLinearMap.comp_apply] at hc
    rw [← hc, hx.1]
  · calc
      G.right r (G.right v x) = G.right (v * r) x := (G.right_mul_apply _ _ _).symm
      _ = G.right ((v * star v) * v) x := by rw [← hv, mul_assoc]
      _ = G.right v (G.right (v * star v) x) := G.right_mul_apply _ _ _
      _ = G.right v x := by rw [hx.2]

def rightTransferMap (e r v : P) (hv : star v * v = r) :
    G.corner e r →L[ℂ] G.corner e (v * star v) :=
  ((G.right (star v)).comp (G.corner e r).toSubmodule.subtypeL).codRestrict
    (G.corner e (v * star v)).toSubmodule (G.right_transfer_mem e r v hv)

def rightTransferBack (e r v : P) (hv : star v * v = r) :
    G.corner e (v * star v) →L[ℂ] G.corner e r :=
  ((G.right v).comp (G.corner e (v * star v)).toSubmodule.subtypeL).codRestrict
    (G.corner e r).toSubmodule (G.right_transfer_back_mem e r v hv)

@[simp] theorem rightTransferMap_coe (e r v : P) (hv : star v * v = r) (x : G.corner e r) :
    (G.rightTransferMap e r v hv x : H) = G.right (star v) x := rfl

@[simp] theorem rightTransferBack_coe (e r v : P) (hv : star v * v = r)
    (x : G.corner e (v * star v)) :
    (G.rightTransferBack e r v hv x : H) = G.right v x := rfl

theorem rightTransfer_norm (e r v : P) (hv : star v * v = r) (x : G.corner e r) :
    ‖G.rightTransferMap e r v hv x‖ = ‖x‖ := by
  have hx := (G.mem_corner e r x).mp x.property
  have hi : inner ℂ (G.right (star v) x) (G.right (star v) x) = inner ℂ (x : H) x := by
    rw [← ContinuousLinearMap.adjoint_inner_right, G.right_adjoint, star_star,
      ← G.right_mul_apply, hv, hx.2]
  have hn : ‖G.rightTransferMap e r v hv x‖ ^ 2 = ‖x‖ ^ 2 := by
    change ‖G.right (star v) x‖ ^ 2 = ‖(x : H)‖ ^ 2
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hi]
  nlinarith [norm_nonneg (G.rightTransferMap e r v hv x), norm_nonneg x]

theorem rightTransfer_rightInverse (e r v : P) (hv : star v * v = r)
    (x : G.corner e (v * star v)) :
    G.rightTransferMap e r v hv (G.rightTransferBack e r v hv x) = x := by
  apply Subtype.ext
  change G.right (star v) (G.right v x) = x
  rw [← G.right_mul_apply]
  exact ((G.mem_corner e (v * star v) x).mp x.property).2

/-- Right multiplication by `v*` is the actual unitary from `eL²r` onto
`eL²(vv*)`; its inverse is right multiplication by `v`. -/
def rightTransfer (e r v : P) (hv : star v * v = r) :
    G.corner e r ≃ₗᵢ[ℂ] G.corner e (v * star v) :=
  LinearIsometryEquiv.ofSurjective
    { (G.rightTransferMap e r v hv).toLinearMap with norm_map' := G.rightTransfer_norm e r v hv }
    (fun x => ⟨G.rightTransferBack e r v hv x, G.rightTransfer_rightInverse e r v hv x⟩)

@[simp] theorem rightTransfer_coe (e r v : P) (hv : star v * v = r) (x : G.corner e r) :
    (G.rightTransfer e r v hv x : H) = G.right (star v) x := rfl

end TracialCornerGeometry

/-- The range projection of an algebraic partial isometry is a projection. -/
theorem range_projection_of_initial_projection (r v : P) (hr : IsStarProjection r)
    (hv : star v * v = r) : IsStarProjection (v * star v) := by
  have hvr : v * r = v := by
    apply sub_eq_zero.mp
    apply (CStarRing.star_mul_self_eq_zero_iff (v * r - v)).mp
    calc
      star (v * r - v) * (v * r - v) =
          r * (star v * v) * r - r * (star v * v) - (star v * v) * r + star v * v := by
        rw [star_sub, star_mul, hr.isSelfAdjoint.star_eq]
        noncomm_ring
      _ = 0 := by simp only [hv, hr.isIdempotentElem.eq]; abel
  constructor
  · change (v * star v) * (v * star v) = v * star v
    calc
      _ = (v * (star v * v)) * star v := by noncomm_ring
      _ = _ := by rw [hv, hvr]
  · exact IsSelfAdjoint.mul_star_self v

variable {C : Type*} [CStarAlgebra C]

/-- A partial isometry transports the corner to one where the range
projection is a cyclic vector. The only corner-algebra data are its concrete
left action and the fact that every compression `eae` is represented. -/
theorem tracial_corner_cyclic_of_partial_isometry
    (G : TracialCornerGeometry P H) (e r : P) (he : IsStarProjection e) (hr : IsStarProjection r)
    (σ : C →⋆ₐ[ℂ] (G.corner e r →L[ℂ] G.corner e r)) (ι : C → P)
    (hfull : ∀ a : P, ∃ c : C, ι c = e * a * e)
    (haction : ∀ (c : C) (x : G.corner e r), (σ c x : H) = G.left (ι c) x)
    (v : P) (hv : star v * v = r) (hev : e * (v * star v) = v * star v) :
    CyclicStarRepresentation σ := by
  let p := v * star v
  have hp : IsStarProjection p := range_projection_of_initial_projection r v hr hv
  let U := G.rightTransfer e r v hv
  let η : G.corner e p := ⟨G.vector p, by
    rw [G.mem_corner]
    constructor
    · rw [G.left_vector, hev]
    · rw [G.right_vector, hp.isIdempotentElem.eq]⟩
  let ζ := U.symm η
  let f : C → G.corner e p := fun c => U (σ c ζ)
  have hf (c : C) : (f c : H) = G.left (ι c) (G.vector p) := by
    change G.right (star v) (σ c ζ) = G.left (ι c) (G.vector p)
    rw [haction]
    have hc := congrArg (fun T : H →L[ℂ] H => T (ζ : H)) (G.right_left (ι c) (star v))
    simp only [ContinuousLinearMap.comp_apply] at hc
    rw [hc]
    have hζ : G.right (star v) ζ = G.vector p :=
      congrArg (fun x : G.corner e p => (x : H)) (U.apply_symm_apply η)
    rw [hζ]
  have hdense : DenseRange f := by
    apply (G.corner_vectors_dense e p he.isIdempotentElem hp.isIdempotentElem).mono
    rintro x ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := hfull a
    refine ⟨c, ?_⟩
    apply Subtype.ext
    rw [hf, TracialCornerGeometry.cornerInto_coe,
      TracialCornerGeometry.cornerProjection_vector, G.left_vector, hc]
    congr 1
    calc
      e * a * e * p = e * a * (e * p) := by noncomm_ring
      _ = e * a * p := by rw [hev]
  refine ⟨ζ, ?_⟩
  have h := U.symm.surjective.denseRange.comp hdense U.symm.continuous
  simpa only [Function.comp_def, f, U.symm_apply_apply] using h

/-- The local cyclicity input in the full-column theorem is derived from
the actual tracial geometry and corner-algebra coordinates. -/
theorem tracialCornerCyclicityInput_of_geometry
    (G : TracialCornerGeometry P H) (e r : P) (he : IsStarProjection e) (hr : IsStarProjection r)
    (σ : C →⋆ₐ[ℂ] (G.corner e r →L[ℂ] G.corner e r)) (ι : C → P)
    (hfull : ∀ a : P, ∃ c : C, ι c = e * a * e)
    (haction : ∀ (c : C) (x : G.corner e r), (σ c x : H) = G.left (ι c) x) :
    TracialCornerCyclicityInput e r σ :=
  fun v hv hev => tracial_corner_cyclic_of_partial_isometry G e r he hr σ ι hfull haction v hv hev

end KadisonSimilarity

end

end OAI
