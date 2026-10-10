import OAI.Analysis.KadisonSimilarity.Tracial.TracialInclusionQuantization
import OAI.Analysis.KadisonSimilarity.Tracial.CornerTraceScaling

namespace OAI

/-! Local quantization inside every nonzero corner of the prescribed source. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open HochschildCorners
open scoped ComplexOrder

section CornerHom
variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The original inclusion restricted to matching corners. -/
def sourceCornerHom (φ : A →⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p) :
    Corner p hp →⋆ₐ[ℂ] Corner (φ p) (hp.map φ) where
  toFun x := ⟨φ (x : A), by
    constructor
    · rw [← map_mul, x.property.1]
    · rw [← map_mul, x.property.2]⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_one' := Subtype.ext rfl
  map_add' x y := Subtype.ext (map_add φ (x : A) (y : A))
  map_mul' x y := Subtype.ext (map_mul φ (x : A) (y : A))
  map_star' x := Subtype.ext (map_star φ (x : A))
  commutes' c := Subtype.ext (by
    change φ (c • p) = c • φ p
    exact map_smul φ c p)

@[simp] theorem sourceCornerHom_coe (φ : A →⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p)
    (x : Corner p hp) : (sourceCornerHom φ p hp x : B) = φ (x : A) := rfl

end CornerHom

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hNM : N ≤ M)

local instance sourceCornerAmbientClosed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
local instance sourceCornerSourceClosed : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (N : Set (H →L[ℂ] H))
  infer_instance

include υ in
/-- Corner irreducibility retains the given source inclusion. -/
theorem source_corner_irreducible
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a * c =
        c * coordinateInclusion hNM a) → ∃ z : ℂ, c = z • 1)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) :
    ∀ c : Corner (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM)),
      (∀ a : Corner p hp, sourceCornerHom (coordinateInclusion hNM) p hp a * c =
        c * sourceCornerHom (coordinateInclusion hNM) p hp a) → ∃ z : ℂ, c = z • 1 := by
  intro c hc
  let P := insideAlgebra (M := M) (P := N)
  have hi : ∀ b : M.toStarSubalgebra,
      (∀ a : P, (a : M.toStarSubalgebra) * b = b * (a : M.toStarSubalgebra)) →
      ∃ z : ℂ, b = z • 1 := by
    intro b hb
    exact hirr b (fun a => hb ⟨coordinateInclusion hNM a, a.property⟩)
  have hcomm (a : P) : Commute (c : M.toStarSubalgebra)
      (coordinateInclusion hNM p * (a : M.toStarSubalgebra) * coordinateInclusion hNM p) := by
    let b : N.toStarSubalgebra := ⟨a.val.val, a.property⟩
    let d : Corner p hp := ⟨p * b * p, compress_mem_corner hp b⟩
    have hh := congrArg
      (fun x : Corner (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM)) =>
        (x : M.toStarSubalgebra)) (hc d)
    change (coordinateInclusion hNM p * (a : M.toStarSubalgebra) * coordinateInclusion hNM p) *
      (c : M.toStarSubalgebra) = (c : M.toStarSubalgebra) *
      (coordinateInclusion hNM p * (a : M.toStarSubalgebra) * coordinateInclusion hNM p) at hh
    exact hh.symm
  obtain ⟨z, hz⟩ := corner_commutant_scalar υ P hi
    ⟨coordinateInclusion hNM p, hp.map (coordinateInclusion hNM)⟩ (c : M.toStarSubalgebra)
    c.property.1 c.property.2 hcomm
  exact ⟨z, Subtype.ext hz⟩

/-- The normalized source-corner inclusion has a simultaneous normal model. -/
theorem exists_source_corner_model (p : N.toStarSubalgebra) (hp : IsStarProjection p)
    (hp0 : p ≠ 0) :
    Nonempty (TracialInclusionModel (sourceCornerHom (coordinateInclusion hNM) p hp)
      (cornerTrace (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM))
        (vectorPositiveFunctional M υ.vector))) := by
  let φ := coordinateInclusion hNM
  let τN := vectorPositiveFunctional N υ.vector
  let τM := vectorPositiveFunctional M υ.vector
  let pM := φ p
  have hpM : IsStarProjection pM := hp.map φ
  have hpM0 : pM ≠ 0 := fun h => hp0
    (Subtype.ext (congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H)) h))
  have hfM (a : M.toStarSubalgebra) (ha : τM (star a * a) = 0) : a = 0 := by
    apply υ.separating a
    exact inner_self_eq_zero.mp ((baseVector_inner_trace υ a a).trans ha)
  let ρN := cornerTrace p hp τN
  let ρM := cornerTrace pM hpM τM
  let ψ := sourceCornerHom φ p hp
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : Corner pM hpM => c.val.val) hab
  have ht (a : Corner p hp) : ρM (ψ a) = ρN a := rfl
  exact exists_tracialInclusionModel
    (cornerPredualEquiv p hp (concretePredualEquiv N))
    (cornerPredualEquiv pM hpM (concretePredualEquiv M)) ρN ρM
    (cornerTrace_normal p hp _ τN (vectorPositiveFunctional_normal N υ.vector))
    (cornerTrace_normal pM hpM _ τM (vectorPositiveFunctional_normal M υ.vector))
    (cornerTrace_one pM hpM τM hfM hpM0)
    (cornerTrace_tracial pM hpM τM υ.trace_mul_comm)
    (cornerTrace_faithful pM hpM τM hfM hpM0) ψ hψ ht

include υ hNM in
/-- Scalar center of a nonzero source corner. -/
theorem source_corner_factor
    (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∀ c : Corner p hp, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1 := by
  let τN := vectorPositiveFunctional N υ.vector
  have hfN (a : N.toStarSubalgebra) (ha : τN (star a * a) = 0) : a = 0 := by
    apply (restrictedTrace υ hNM).separating a
    exact inner_self_eq_zero.mp ((baseVector_inner_trace (restrictedTrace υ hNM) a a).trans ha)
  have hdN : HochschildDiffuse.NoMinimalProjections N.toStarSubalgebra := by
    intro q hq hq0
    obtain ⟨r, hr, hr0, hrq, hqr, _⟩ := hdiff q hq hq0
    exact ⟨r, hr, (hr.le_iff_mul_eq_right hq).mpr hqr, hr0, hrq⟩
  have hcN := corner_factor p hp (concretePredualEquiv N) τN
    (vectorPositiveFunctional_normal N υ.vector)
    (vectorPositiveFunctional_one N υ.vector υ.norm_vector)
    (restrictedTrace υ hNM).trace_mul_comm hfN
    (fun b hb => hfactor b (fun a => (hb a).eq.symm)) hdN hp0
  exact fun c hc => hcN c (fun a => (hc a).symm)

/-- A nonzero projection in the source corner can be split there. -/
theorem source_corner_diffuse
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) :
    ∀ q : Corner p hp, IsStarProjection q → q ≠ 0 →
      ∃ r, IsStarProjection r ∧ r ≠ 0 ∧ r ≠ q ∧ q * r = r ∧ r * q = r := by
  have hdN : HochschildDiffuse.NoMinimalProjections N.toStarSubalgebra := by
    intro q hq hq0
    obtain ⟨r, hr, hr0, hrq, hqr, _⟩ := hdiff q hq hq0
    exact ⟨r, hr, (hr.le_iff_mul_eq_right hq).mpr hqr, hr0, hrq⟩
  intro q hq hq0
  obtain ⟨r, hr, hrq, hr0, hrne⟩ := corner_no_minimal p hp hdN q hq hq0
  exact ⟨r, hr, hr0, hrne, (hr.le_iff_mul_eq_right hq).mp hrq,
    (hr.le_iff_mul_eq_left hq).mp hrq⟩

/-- Centered coefficients in the normalized corner admit small source projections. -/
theorem exists_source_corner_compression
    (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a * c =
        c * coordinateInclusion hNM a) → ∃ z : ℂ, c = z • 1)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0)
    {I : Type*} [Fintype I]
    (x : I → Corner (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM)))
    (hx : ∀ i, cornerTrace (coordinateInclusion hNM p)
      (hp.map (coordinateInclusion hNM)) (vectorPositiveFunctional M υ.vector) (x i) = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : Corner p hp, IsStarProjection q ∧ q ≠ 0 ∧
      (cornerTrace (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM))
        (vectorPositiveFunctional M υ.vector) (sourceCornerHom (coordinateInclusion hNM) p hp q)).re < η ∧
      ∀ i, ‖(cornerTrace (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM))
        (vectorPositiveFunctional M υ.vector)).toPreGNS
          (sourceCornerHom (coordinateInclusion hNM) p hp q * x i *
            sourceCornerHom (coordinateInclusion hNM) p hp q)‖ ^ 2 <
        δ * (cornerTrace (coordinateInclusion hNM p) (hp.map (coordinateInclusion hNM))
          (vectorPositiveFunctional M υ.vector) (sourceCornerHom (coordinateInclusion hNM) p hp q)).re := by
  let φ := coordinateInclusion hNM
  let τN := vectorPositiveFunctional N υ.vector
  let τM := vectorPositiveFunctional M υ.vector
  let pM := φ p
  have hpM : IsStarProjection pM := hp.map φ
  have hpM0 : pM ≠ 0 := fun h => hp0
    (Subtype.ext (congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H)) h))
  have hfM (a : M.toStarSubalgebra) (ha : τM (star a * a) = 0) : a = 0 := by
    apply υ.separating a
    exact inner_self_eq_zero.mp ((baseVector_inner_trace υ a a).trans ha)
  let ρN := cornerTrace p hp τN
  let ρM := cornerTrace pM hpM τM
  let ψ := sourceCornerHom φ p hp
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : Corner pM hpM => c.val.val) hab
  let : Nontrivial (Corner p hp) := nontrivial_of_ne (1 : Corner p hp) 0
    (fun h => hp0 (congrArg (fun a : Corner p hp => (a : N.toStarSubalgebra)) h))
  exact exists_relative_compression_of_predual
    (cornerPredualEquiv p hp (concretePredualEquiv N))
    (cornerPredualEquiv pM hpM (concretePredualEquiv M)) ρN ρM
    (cornerTrace_normal p hp _ τN (vectorPositiveFunctional_normal N υ.vector))
    (cornerTrace_normal pM hpM _ τM (vectorPositiveFunctional_normal M υ.vector))
    (cornerTrace_one pM hpM τM hfM hpM0)
    (cornerTrace_tracial pM hpM τM υ.trace_mul_comm)
    (cornerTrace_faithful pM hpM τM hfM hpM0) ψ hψ (fun _ => rfl)
    (source_corner_factor υ hNM hfactor hdiff p hp hp0)
    (source_corner_diffuse hdiff p hp)
    (source_corner_irreducible υ hNM hirr p hp) x hx hδ hη

/-- Compression of a centered corner element in the original coordinates. -/
theorem sourceCorner_compressed_eq (p : N.toStarSubalgebra) (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q) (x : M.toStarSubalgebra) (c : ℂ) :
    let φ := coordinateInclusion hNM
    let ψ := sourceCornerHom φ p hp
    ((ψ q * (⟨φ p * x * φ p, compress_mem_corner (hp.map φ) x⟩ - c • 1) * ψ q :
      Corner (φ p) (hp.map φ)) : M.toStarSubalgebra) =
        φ (q : N.toStarSubalgebra) * x * φ (q : N.toStarSubalgebra) -
          c • φ (q : N.toStarSubalgebra) := by
  let φ := coordinateInclusion hNM
  have hqm : φ (q : N.toStarSubalgebra) * φ p = φ (q : N.toStarSubalgebra) := by
    rw [← map_mul, q.property.2]
  have hmq : φ p * φ (q : N.toStarSubalgebra) = φ (q : N.toStarSubalgebra) := by
    rw [← map_mul, q.property.1]
  have hqM := (corner_projection_coe p hp hq).map φ
  change φ (q : N.toStarSubalgebra) * (φ p * x * φ p - c • φ p) *
    φ (q : N.toStarSubalgebra) = _
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hqm, hqM.isIdempotentElem.eq]
  congr 1
  rw [← mul_assoc, ← mul_assoc, hqm, mul_assoc, hmq]

/-- Every nonzero source corner admits relative compression, with the
normalization expressed using the original ambient trace. -/
theorem exists_source_relative_small_corner
    (hfactor : ∀ c : N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a * c =
        c * coordinateInclusion hNM a) → ∃ z : ℂ, c = z • 1)
    (p : N.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0)
    {I : Type*} [Fintype I] (x : I → M.toStarSubalgebra)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧
      (υ.trace (coordinateInclusion hNM q)).re < η ∧
      ∀ i, ‖(vectorPositiveFunctional M υ.vector).toPreGNS
        (coordinateInclusion hNM q * x i * coordinateInclusion hNM q -
          (((υ.trace (coordinateInclusion hNM p)).re : ℂ)⁻¹ *
            υ.trace (coordinateInclusion hNM p * x i * coordinateInclusion hNM p)) •
              coordinateInclusion hNM q)‖ ^ 2 <
        δ * (υ.trace (coordinateInclusion hNM q)).re := by
  let φ := coordinateInclusion hNM
  let τM := vectorPositiveFunctional M υ.vector
  let pM := φ p
  have hpM : IsStarProjection pM := hp.map φ
  have hpM0 : pM ≠ 0 := fun h => hp0
    (Subtype.ext (congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H)) h))
  have hfM (a : M.toStarSubalgebra) (ha : τM (star a * a) = 0) : a = 0 := by
    apply υ.separating a
    exact inner_self_eq_zero.mp ((baseVector_inner_trace υ a a).trans ha)
  let ρM := cornerTrace pM hpM τM
  let ψ := sourceCornerHom φ p hp
  let y : I → Corner pM hpM := fun i => ⟨pM * x i * pM, compress_mem_corner hpM (x i)⟩
  let z : I → Corner pM hpM := fun i => y i - ρM (y i) • 1
  have hρ1 : ρM 1 = 1 := cornerTrace_one pM hpM τM hfM hpM0
  have hz (i : I) : ρM (z i) = 0 := by
    simp only [z, map_sub, map_smul, hρ1, smul_eq_mul, mul_one, sub_self]
  have htp : 0 < (τM pM).re := HochschildDiffuse.projection_trace_pos τM hfM hpM hpM0
  obtain ⟨q, hq, hq0, hqt, hqz⟩ := exists_source_corner_compression υ hNM
    hfactor hdiff hirr p hp hp0 z hz hδ (div_pos hη htp)
  have hqN := corner_projection_coe p hp hq
  have hqp := corner_projection_le p hp hq
  refine ⟨q, hqN, hqp, (fun h => hq0 (Subtype.ext h)), ?_, ?_⟩
  · exact original_trace_lt_of_corner pM hpM τM htp hqt
  · intro i
    have he := sourceCorner_compressed_eq hNM p hp q hq (x i) (ρM (y i))
    have hh := original_norm_bound_of_corner pM hpM τM htp (hqz i)
    change ((ψ q * z i * ψ q : Corner pM hpM) : M.toStarSubalgebra) = _ at he
    rw [he] at hh
    exact hh

end KadisonSimilarity

end

end OAI
