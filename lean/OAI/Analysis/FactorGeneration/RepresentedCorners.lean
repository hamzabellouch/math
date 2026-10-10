import OAI.Analysis.FactorGeneration.LocalQuantization

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual corner on pH. Extension by zero identifies its operators with
supported ambient operators; weak closedness is proved by WOT continuity. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)

def cornerSpace : Submodule ℂ H where
  carrier := {x | p.val.val x=x}
  zero_mem' := by simp
  add_mem' hx hy := by simp_all
  smul_mem' c x hx := by simp_all

@[simp] theorem mem_cornerSpace (x : H) : x ∈ cornerSpace p ↔ p.val.val x=x := Iff.rfl

instance cornerSpace_complete : CompleteSpace (cornerSpace p) := by
  have hc : IsClosed (cornerSpace p : Set H) := isClosed_eq p.val.val.continuous continuous_id
  exact hc.completeSpace_coe

def cornerProject : H →L[ℂ] cornerSpace p :=
  p.val.val.codRestrict (cornerSpace p) (fun x => by
    change p.val.val (p.val.val x)=p.val.val x
    exact congrArg (fun a : M.toStarSubalgebra => a.val x) p.property.isIdempotentElem.eq)

@[simp] theorem cornerProject_coe (x : H) : (cornerProject p x).val=p.val.val x := rfl
@[simp] theorem cornerProject_subtype (x : cornerSpace p) : cornerProject p x.val=x :=
  Subtype.ext x.property

theorem cornerProject_inner (x : H) (y : cornerSpace p) :
    inner ℂ (cornerProject p x) y=inner ℂ x y.val := by
  change inner ℂ (p.val.val x) y.val=inner ℂ x y.val
  have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  rw [← hs,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left,y.property]

def cornerExtend (a : cornerSpace p →L[ℂ] cornerSpace p) : H →L[ℂ] H :=
  (cornerSpace p).subtypeL.comp (a.comp (cornerProject p))

@[simp] theorem cornerExtend_apply (a : cornerSpace p →L[ℂ] cornerSpace p) (x : H) :
    cornerExtend p a x=(a (cornerProject p x)).val := rfl

@[simp] theorem cornerExtend_zero : cornerExtend p 0=0 := by ext x; rfl
@[simp] theorem cornerExtend_add (a b : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (a+b)=cornerExtend p a+cornerExtend p b := by ext x; rfl
@[simp] theorem cornerExtend_smul (c : ℂ) (a : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (c • a)=c • cornerExtend p a := by ext x; rfl
@[simp] theorem cornerExtend_one : cornerExtend p 1=p.val.val := by ext x; rfl
@[simp] theorem cornerExtend_mul (a b : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (a*b)=cornerExtend p a*cornerExtend p b := by
  ext x
  simp only [mul_apply_eq_comp,cornerExtend_apply,cornerProject_subtype]

@[simp] theorem cornerExtend_star (a : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p (star a)=star (cornerExtend p a) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [cornerExtend_apply,← cornerProject_inner,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (a (cornerProject p y)) (cornerProject p x)=_
  rw [← inner_conj_symm,cornerProject_inner,inner_conj_symm]
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem cornerExtend_injective : Function.Injective (cornerExtend p) := by
  intro a b hab
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => T x.val) hab
  simpa only [cornerExtend_apply,cornerProject_subtype] using h

@[simp] theorem cornerExtend_left (a : cornerSpace p →L[ℂ] cornerSpace p) :
    p.val.val*cornerExtend p a=cornerExtend p a := by
  ext x
  exact (a (cornerProject p x)).property

@[simp] theorem cornerExtend_right (a : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerExtend p a*p.val.val=cornerExtend p a := by
  rw [← cornerExtend_one p,← cornerExtend_mul,mul_one]

def cornerStarAlgebra : StarSubalgebra ℂ (cornerSpace p →L[ℂ] cornerSpace p) where
  carrier := {a | cornerExtend p a ∈ M}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' ha hb := by simpa using M.add_mem ha hb
  mul_mem' ha hb := by simpa using M.mul_mem ha hb
  algebraMap_mem' c := by
    change cornerExtend p (c • 1) ∈ M
    simpa using M.toStarSubalgebra.smul_mem p.val.property c
  star_mem' ha := by simpa using star_mem ha

theorem cornerExtend_wot_continuous : Continuous (fun a : cornerSpace p →WOT[ℂ] cornerSpace p =>
    ContinuousLinearMapWOT.ofCLM (cornerExtend p a.toCLM)) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  simp only [ContinuousLinearMapWOT.ofCLM_apply,cornerExtend_apply,← cornerProject_inner]
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_id _ _

theorem cornerStarAlgebra_wotClosed : WOTClosed (cornerStarAlgebra p) :=
  (vonNeumann_wotClosed M).preimage (cornerExtend_wot_continuous p)

def representedCorner : VonNeumannAlgebra (cornerSpace p) :=
  vonNeumannOfWOTClosed (cornerStarAlgebra p) (cornerStarAlgebra_wotClosed p)

def cornerEmbedding : (representedCorner p).toStarSubalgebra →⋆ₙₐ[ℂ] M.toStarSubalgebra where
  toFun a := ⟨cornerExtend p a.val,a.property⟩
  map_zero' := Subtype.ext (cornerExtend_zero p)
  map_add' a b := Subtype.ext (cornerExtend_add p a.val b.val)
  map_mul' a b := Subtype.ext (cornerExtend_mul p a.val b.val)
  map_smul' c a := Subtype.ext (cornerExtend_smul p c a.val)
  map_star' a := Subtype.ext (cornerExtend_star p a.val)

theorem cornerEmbedding_injective : Function.Injective (cornerEmbedding p) := by
  intro a b h
  exact Subtype.ext (cornerExtend_injective p (congrArg Subtype.val h))

@[simp] theorem cornerEmbedding_one : cornerEmbedding p 1=p.val :=
  Subtype.ext (cornerExtend_one p)
@[simp] theorem cornerEmbedding_left (a : (representedCorner p).toStarSubalgebra) :
    p.val*cornerEmbedding p a=cornerEmbedding p a := Subtype.ext (cornerExtend_left p a.val)
@[simp] theorem cornerEmbedding_right (a : (representedCorner p).toStarSubalgebra) :
    cornerEmbedding p a*p.val=cornerEmbedding p a := Subtype.ext (cornerExtend_right p a.val)

/-! Compression and extension are inverse on supported operators. -/

def cornerCompressOperator (x : H →L[ℂ] H) : cornerSpace p →L[ℂ] cornerSpace p :=
  (cornerProject p).comp (x.comp (cornerSpace p).subtypeL)

@[simp] theorem cornerCompressOperator_apply (x : H →L[ℂ] H) (y : cornerSpace p) :
    (cornerCompressOperator p x y).val=p.val.val (x y.val) := rfl

theorem cornerExtend_compress (x : H →L[ℂ] H) :
    cornerExtend p (cornerCompressOperator p x)=p.val.val*x*p.val.val := by ext y; rfl

@[simp] theorem cornerCompress_extend (x : cornerSpace p →L[ℂ] cornerSpace p) :
    cornerCompressOperator p (cornerExtend p x)=x := by
  apply cornerExtend_injective p
  rw [cornerExtend_compress,cornerExtend_left,cornerExtend_right]

def cornerCompress (x : M.toStarSubalgebra) : (representedCorner p).toStarSubalgebra :=
  ⟨cornerCompressOperator p x.val,by
    change cornerExtend p (cornerCompressOperator p x.val) ∈ M
    rw [cornerExtend_compress]
    exact M.mul_mem (M.mul_mem p.val.property x.property) p.val.property⟩

@[simp] theorem cornerEmbedding_compress (x : M.toStarSubalgebra) :
    cornerEmbedding p (cornerCompress p x)=p.val*x*p.val := Subtype.ext (cornerExtend_compress p x.val)

@[simp] theorem cornerCompress_embedding (x : (representedCorner p).toStarSubalgebra) :
    cornerCompress p (cornerEmbedding p x)=x := Subtype.ext (cornerCompress_extend p x.val)

theorem cornerEmbedding_range : Set.range (cornerEmbedding p)=
    {x : M.toStarSubalgebra | p.val*x=x ∧ x*p.val=x} := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨cornerEmbedding_left p a,cornerEmbedding_right p a⟩
  · rintro ⟨hl,hr⟩
    exact ⟨cornerCompress p x,by rw [cornerEmbedding_compress,hl,hr]⟩

end

/-! The normalized faithful vector trace on the actual corner pH. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (p : AlgebraProjection M)

theorem corner_norm₂_pos (hp : p.val ≠ 0) : 0 < τ.norm₂ p.val :=
  lt_of_le_of_ne (norm_nonneg _) (fun h => hp ((τ.norm₂_eq_zero_iff _).mp h.symm))

def normalizedCornerVector : cornerSpace p :=
  ((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p τ.vector

theorem normalizedCornerVector_norm (hp : p.val ≠ 0) : ‖normalizedCornerVector τ p‖=1 := by
  change ‖((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p τ.vector‖=1
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ τ.norm₂ p.val from norm_nonneg _)]
  change (τ.norm₂ p.val)⁻¹*τ.norm₂ p.val=1
  exact inv_mul_cancel₀ (corner_norm₂_pos τ p hp).ne'

theorem normalizedCornerVector_pairing (a : (representedCorner p).toStarSubalgebra) :
    inner ℂ (normalizedCornerVector τ p) (a.val (normalizedCornerVector τ p))=
      ((τ.norm₂ p.val : ℂ)^2)⁻¹ * τ.trace (cornerEmbedding p a) := by
  simp only [normalizedCornerVector,map_smul,inner_smul_left,inner_smul_right,
    map_inv₀,Complex.conj_ofReal]
  rw [cornerProject_inner]
  change (τ.norm₂ p.val : ℂ)⁻¹*((τ.norm₂ p.val : ℂ)⁻¹*τ.trace (cornerEmbedding p a))=_
  ring

def representedCornerTrace (hp : p.val ≠ 0) : TracialRepresentation (representedCorner p) where
  vector := normalizedCornerVector τ p
  norm_vector := normalizedCornerVector_norm τ p hp
  cyclic a b := by
    change inner ℂ (normalizedCornerVector τ p) ((a*b).val (normalizedCornerVector τ p))=
      inner ℂ (normalizedCornerVector τ p) ((b*a).val (normalizedCornerVector τ p))
    rw [normalizedCornerVector_pairing,normalizedCornerVector_pairing,map_mul,map_mul,τ.trace_mul_comm]
  separating a ha := by
    apply cornerEmbedding_injective p
    rw [map_zero]
    apply τ.separating
    have h : ((τ.norm₂ p.val : ℂ)⁻¹) • (a.val (cornerProject p τ.vector))=0 := by
      simpa only [normalizedCornerVector,map_smul] using ha
    have hscalar : (τ.norm₂ p.val : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.mpr (corner_norm₂_pos τ p hp).ne')
    have hz := (smul_eq_zero.mp h).resolve_left hscalar
    exact congrArg Subtype.val hz

theorem representedCornerTrace_norm₂ (hp : p.val ≠ 0)
    (a : (representedCorner p).toStarSubalgebra) :
    (representedCornerTrace τ p hp).norm₂ a=τ.norm₂ (cornerEmbedding p a)/τ.norm₂ p.val := by
  change ‖a.val (((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p τ.vector)‖=_
  rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ τ.norm₂ p.val from norm_nonneg _)]
  change (τ.norm₂ p.val)⁻¹*τ.norm₂ (cornerEmbedding p a)=_
  exact (div_eq_inv_mul _ _).symm

theorem representedCornerTrace_trace (hp : p.val ≠ 0)
    (a : (representedCorner p).toStarSubalgebra) :
    (representedCornerTrace τ p hp).trace a=τ.trace (cornerEmbedding p a)/τ.trace p.val := by
  change inner ℂ (normalizedCornerVector τ p) (a.val (normalizedCornerVector τ p))=_
  rw [normalizedCornerVector_pairing]
  have ht : τ.trace p.val=(τ.norm₂ p.val : ℂ)^2 := by
    have h := τ.trace_star_mul p.val
    rwa [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq] at h
  rw [ht,div_eq_inv_mul]

end

/-! Subcorner inclusion, inherited diffuseness/irreducibility, and L2 separability. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (p : AlgebraProjection M)

def projectionInSubalgebra (hpN : p.val.val ∈ N) : AlgebraProjection N :=
  ⟨⟨p.val.val,hpN⟩,⟨Subtype.ext (congrArg (fun a : M.toStarSubalgebra => a.val) p.property.isIdempotentElem.eq),
    Subtype.ext (congrArg (fun a : M.toStarSubalgebra => a.val) p.property.isSelfAdjoint.star_eq)⟩⟩

/-- Both corners act on the same pH; only the membership predicate changes. -/
def representedSubcorner (hpN : p.val.val ∈ N) : VonNeumannAlgebra (cornerSpace p) :=
  representedCorner (projectionInSubalgebra p hpN)

theorem representedSubcorner_le (hpN : p.val.val ∈ N) (hNM : N ≤ M) :
    representedSubcorner p hpN ≤ representedCorner p := fun _ h => hNM h

theorem representedCorner_diffuse
    (hdiff : ∀ r : M.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q) :
    ∀ r : (representedCorner p).toStarSubalgebra,IsStarProjection r → r ≠ 0 →
      ∃ q : (representedCorner p).toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q := by
  intro r hr hr0
  have hr' := hr.map (cornerEmbedding p)
  have hr0' : cornerEmbedding p r ≠ 0 := by
    intro h
    exact hr0 (cornerEmbedding_injective p (h.trans (map_zero (cornerEmbedding p)).symm))
  obtain ⟨q,hq,hq0,hqr,hrq,hqr'⟩ := hdiff _ hr' hr0'
  have hl : p.val*q=q := by
    rw [← hrq,← mul_assoc,cornerEmbedding_left,hrq]
  have hh : q*p.val=q := by
    rw [← hqr',mul_assoc,cornerEmbedding_right,hqr']
  let q' := cornerCompress p q
  have he : cornerEmbedding p q'=q := by rw [cornerEmbedding_compress,hl,hh]
  have hi := cornerEmbedding_injective p
  refine ⟨q',⟨?_,?_⟩,?_,?_,?_,?_⟩
  · apply hi
    rw [map_mul,he,hq.isIdempotentElem.eq]
  · apply hi
    rw [map_star,he,hq.isSelfAdjoint.star_eq]
  · intro hz
    apply hq0
    rw [← he,hz,map_zero]
  · intro hz
    exact hqr (he.symm.trans (congrArg (cornerEmbedding p) hz))
  · apply hi
    rw [map_mul,he,hrq]
  · apply hi
    rw [map_mul,he,hqr']

include τ in
theorem representedCorner_irreducible (hpN : p.val.val ∈ N) (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra)) :
    ∀ c : (representedCorner p).toStarSubalgebra,
      (∀ a : (representedSubcorner p hpN).toStarSubalgebra,
        coordinateInclusion (representedSubcorner_le p hpN hNM) a*c=
          c*coordinateInclusion (representedSubcorner_le p hpN hNM) a) →
      ∃ z : ℂ,c=z • (1 : (representedCorner p).toStarSubalgebra) := by
  intro c hc
  have hirr' : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),(a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra) := by
    intro c hh
    exact hirr c (fun a => hh ⟨coordinateInclusion hNM a,a.property⟩)
  obtain ⟨z,hz⟩ := corner_commutant_scalar τ (insideAlgebra (M := M) (P := N)) hirr' p
    (cornerEmbedding p c) (cornerEmbedding_left p c) (cornerEmbedding_right p c) (by
      intro a
      let b : (representedSubcorner p hpN).toStarSubalgebra :=
        cornerCompress (projectionInSubalgebra p hpN) ⟨a.val.val,a.property⟩
      have hb : cornerEmbedding p
          (coordinateInclusion (representedSubcorner_le p hpN hNM) b)=p.val*a.val*p.val :=
        Subtype.ext (cornerExtend_compress p a.val.val)
      have h := congrArg (cornerEmbedding p) (hc b)
      rw [map_mul,map_mul,hb] at h
      exact h.symm)
  refine ⟨z,cornerEmbedding_injective p ?_⟩
  simpa only [map_smul,cornerEmbedding_one] using hz

include τ in
theorem representedCorner_factor
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra)) :
    ∀ c : (representedCorner p).toStarSubalgebra,
      (∀ a : (representedCorner p).toStarSubalgebra,a*c=c*a) →
      ∃ z : ℂ,c=z • (1 : (representedCorner p).toStarSubalgebra) := by
  exact representedCorner_irreducible τ p p.val.property le_rfl hfactor

theorem representedCorner_separable (hp : p.val ≠ 0)
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    TopologicalSpace.IsSeparable (Set.range (baseVector (representedCornerTrace τ p hp))) := by
  let f : H → cornerSpace p := fun x => ((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p x
  have hf : Continuous f := by
    dsimp [f]
    exact (cornerProject p).continuous.const_smul ((τ.norm₂ p.val : ℂ)⁻¹)
  apply (hsep.image hf).mono
  rintro y ⟨a,rfl⟩
  refine ⟨baseVector τ (cornerEmbedding p a),⟨cornerEmbedding p a,rfl⟩,?_⟩
  change ((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p (a.val (cornerProject p τ.vector)).val=
    a.val (((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p τ.vector)
  rw [cornerProject_subtype,map_smul]

end

/-! Transport actual unit partitions on pH to ambient partitions of p. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)
namespace CornerPartition
variable (Q : CornerPartition (identityProjection (representedCorner p)))

def fromRepresentedCorner : CornerPartition p where
  size := Q.size
  piece i := ⟨cornerEmbedding p (Q.piece i).val,(Q.piece i).property.map (cornerEmbedding p)⟩
  orthogonal i j hij := by
    change cornerEmbedding p (Q.piece i).val*cornerEmbedding p (Q.piece j).val=0
    rw [← map_mul,Q.orthogonal i j hij,map_zero]
  total := by
    change (∑ i,cornerEmbedding p (Q.piece i).val)=p.val
    rw [← map_sum,Q.total]
    exact cornerEmbedding_one p

theorem fromRepresentedCorner_pinch (x : (representedCorner p).toStarSubalgebra) :
    (Q.fromRepresentedCorner p).pinch (cornerEmbedding p x)=cornerEmbedding p (Q.pinch x) := by
  unfold pinch
  change (∑ i,cornerEmbedding p (Q.piece i).val*cornerEmbedding p x*
    cornerEmbedding p (Q.piece i).val)=cornerEmbedding p _
  simp only [← map_mul,← map_sum]

theorem fromRepresentedCorner_pinch_compress (x : M.toStarSubalgebra) :
    (Q.fromRepresentedCorner p).pinch x=cornerEmbedding p (Q.pinch (cornerCompress p x)) := by
  rw [← Q.fromRepresentedCorner_pinch,cornerEmbedding_compress]
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  change cornerEmbedding p (Q.piece i).val*x*cornerEmbedding p (Q.piece i).val=
    cornerEmbedding p (Q.piece i).val*(p.val*x*p.val)*cornerEmbedding p (Q.piece i).val
  simp only [← mul_assoc,cornerEmbedding_right]
  simp only [mul_assoc,cornerEmbedding_left]

theorem fromRepresentedCorner_mem {N : VonNeumannAlgebra H} (hpN : p.val.val ∈ N)
    (hQ : ∀ i,(Q.piece i).val.val ∈ representedSubcorner p hpN) :
    ∀ i,((Q.fromRepresentedCorner p).piece i).val.val ∈ N := hQ

theorem fromRepresentedCorner_energy (τ : TracialRepresentation M) (hp : p.val ≠ 0)
    (x : M.toStarSubalgebra) :
    τ.norm₂ ((Q.fromRepresentedCorner p).pinch x)^2=
      (τ.trace p.val).re*(representedCornerTrace τ p hp).norm₂ (Q.pinch (cornerCompress p x))^2 := by
  rw [Q.fromRepresentedCorner_pinch_compress,representedCornerTrace_norm₂,projection_trace_sq τ _ p.property]
  field_simp [(corner_norm₂_pos τ p hp).ne']

end CornerPartition

end

/-! Actual centered pNp pinching partitions and local pieces. The corner,
normalized trace, structural properties, and separability are constructed. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_irreducible_corner_zero_trace_partition
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (hpN : p.val.val ∈ N)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (hx : ∀ i ∈ F,τ.trace (p.val*x i*p.val)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition p,(∀ i,(Q.piece i).val.val ∈ N) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε*(τ.trace p.val).re := by
  let τp := representedCornerTrace τ p hp
  let pN := projectionInSubalgebra p hpN
  let hinc := representedSubcorner_le p hpN hNM
  have hf := representedCorner_factor (restrictedTrace τ hNM) pN hfactor
  have hd := representedCorner_diffuse pN hdiff
  have hi := representedCorner_irreducible τ p hpN hNM hirr
  have hs := representedCorner_separable τ p hp hsep
  let y : ι → (representedCorner p).toStarSubalgebra := fun i => cornerCompress p (x i)
  have hy : ∀ i ∈ F,τp.trace (y i)=0 := by
    intro i hi
    rw [representedCornerTrace_trace,cornerEmbedding_compress,hx i hi,zero_div]
  obtain ⟨Q,hQ,hE⟩ := exists_irreducible_centered_partition τp hinc hf hd hi hs F y hy ε hε
  refine ⟨Q.fromRepresentedCorner p,Q.fromRepresentedCorner_mem p hpN hQ,?_⟩
  have henergy : (∑ i ∈ F,τ.norm₂ ((Q.fromRepresentedCorner p).pinch (x i))^2)=
      (τ.trace p.val).re*(∑ i ∈ F,τp.norm₂ (Q.pinch (y i))^2) := by
    simp only [Q.fromRepresentedCorner_energy p τ hp,Finset.mul_sum,τp,y]
  rw [henergy,mul_comm ε]
  exact mul_lt_mul_of_pos_left hE (projection_trace_pos τ p.val p.property hp)

theorem exists_irreducible_corner_centered_partition
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (hpN : p.val.val ∈ N)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition p,(∀ i,(Q.piece i).val.val ∈ N) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (cornerCentered τ p (x i)))^2) < ε^2*(τ.trace p.val).re := by
  apply exists_irreducible_corner_zero_trace_partition τ hNM hfactor hdiff hirr hsep
    p hp hpN F (fun i => cornerCentered τ p (x i)) _ (ε^2) (sq_pos_of_pos hε)
  intro i _
  rw [(cornerCentered_support τ p (x i)).1,(cornerCentered_support τ p (x i)).2,
    cornerCentered_trace τ p hp]

theorem exists_irreducible_corner_local_piece
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (hpN : p.val.val ∈ N)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : AlgebraProjection M,q ≤ p ∧ q.val ≠ 0 ∧ q.val.val ∈ N ∧
      ∀ i ∈ F,
        τ.norm₂ (q.val*x i*q.val-cornerScalar τ p (x i) • q.val) < ε*τ.norm₂ q.val ∧
        norm₁ τ (q.val*x i*q.val-cornerScalar τ p (x i) • q.val) < ε*(τ.trace q.val).re := by
  obtain ⟨Q,hQ,hE⟩ := exists_irreducible_corner_centered_partition τ hNM hfactor hdiff hirr hsep
    p hp hpN F x ε hε
  obtain ⟨j,hj,hjE⟩ := Q.exists_indexed_local_L2_piece τ F (fun i => cornerCentered τ p (x i)) (ε^2) hE
  refine ⟨Q.piece j,Q.piece_le j,hj,hQ j,fun i hi => ?_⟩
  have ht := hjE i hi
  rw [projection_trace_sq τ _ (Q.piece j).property] at ht
  have hn : τ.norm₂ ((Q.piece j).val*cornerCentered τ p (x i)*(Q.piece j).val) <
      ε*τ.norm₂ (Q.piece j).val := by
    nlinarith [show 0 ≤ τ.norm₂ ((Q.piece j).val*cornerCentered τ p (x i)*(Q.piece j).val) from norm_nonneg _,
      mul_nonneg hε.le (show 0 ≤ τ.norm₂ (Q.piece j).val from norm_nonneg _)]
  have h₁ := compression_norm₁_lt_of_norm₂ τ (Q.piece j) hj (cornerCentered τ p (x i)) ε hn
  rw [compress_cornerCentered τ (Q.piece_le j)] at hn h₁
  exact ⟨hn,h₁⟩

end Generator.Tracial

end

end OAI
