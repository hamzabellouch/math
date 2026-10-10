import Mathlib
import OAI.Analysis.BoundedHochschild.MatrixSystems
import OAI.Analysis.BoundedHochschild.MatrixCommutants
import OAI.Analysis.BoundedHochschild.WeakAlgebras

namespace OAI

/-! Spectral corners, corner preduals and factor structure. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def corner (p : M) (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ M where
  carrier := {a | p*a=a ∧ a*p=a}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    exact ⟨by rw [mul_add,ha,hb],by rw [add_mul,ha',hb']⟩
  mul_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    exact ⟨by rw [← mul_assoc,ha],by rw [mul_assoc,hb']⟩
  smul_mem' := by
    intro c a ha
    exact ⟨by rw [mul_smul_comm,ha.1],by rw [smul_mul_assoc,ha.2]⟩
  star_mem' := by
    intro a ha
    exact ⟨by simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha.2,
      by simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star ha.1⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma mem_corner {p a : M} {hp : IsStarProjection p} :
    a ∈ corner p hp ↔ p*a=a ∧ a*p=a := Iff.rfl

instance corner_closed (p : M) (hp : IsStarProjection p) : IsClosed (corner p hp : Set M) := by
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

omit [PartialOrder M] [StarOrderedRing M] in
lemma self_mem_corner {p : M} (hp : IsStarProjection p) : p ∈ corner p hp :=
  ⟨hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩

lemma projection_mem_corner {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q ≤ p) : q ∈ corner p hp :=
  ⟨(hq.le_iff_mul_eq_right hp).mp hqp,(hq.le_iff_mul_eq_left hp).mp hqp⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma compress_mem_corner {p : M} (hp : IsStarProjection p) (a : M) :
    p*a*p ∈ corner p hp := by
  exact ⟨by rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq],
    by rw [mul_assoc,hp.isIdempotentElem.eq]⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma posPart_mem_corner {p a : M} (hp : IsStarProjection p) (ha : a ∈ corner p hp) :
    a⁺ ∈ corner p hp := by
  exact cfcₙ_mem (𝕜' := ℂ) (·⁺ : ℝ → ℝ) ha

omit [PartialOrder M] [StarOrderedRing M] in
lemma negPart_mem_corner {p a : M} (hp : IsStarProjection p) (ha : a ∈ corner p hp) :
    a⁻ ∈ corner p hp := by
  exact cfcₙ_mem (𝕜' := ℂ) (·⁻ : ℝ → ℝ) ha

lemma support_le_corner {p a q : M} (hp : IsStarProjection p) (ha : a ∈ corner p hp)
    (hq : IsSupportProjection a q) : q ≤ p := by
  apply (hq.proj.le_iff_mul_eq_left hp).mpr
  have hh := hq.annihilate (1-p) (by rw [mul_sub,mul_one,ha.2,sub_self])
  rw [mul_sub,mul_one,sub_eq_zero] at hh
  exact hh.symm

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
include e in
lemma exists_corner_dyadic_projection {p a : M} (hp : IsStarProjection p)
    (ha : a ∈ corner p hp) (ha0 : 0 ≤ a) (ha1 : a ≤ p) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ 0 ≤ (2:ℝ) • a-q ∧ (2:ℝ) • a-q ≤ p := by
  let b : M := a-(1/2:ℝ) • p
  let c : M := b⁺
  let d : M := b⁻
  have hbsa : IsSelfAdjoint b := (IsSelfAdjoint.of_nonneg ha0).sub
    (IsSelfAdjoint.of_nonneg (smul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hp.nonneg))
  have hbmem : b ∈ corner p hp := by
    apply (corner p hp).sub_mem ha
    simpa only [Complex.coe_smul] using (corner p hp).smul_mem ((1/2:ℝ):ℂ) (self_mem_corner hp)
  have hcmem := posPart_mem_corner hp hbmem
  have hdmem := negPart_mem_corner hp hbmem
  have hb : c-d=b := CFC.posPart_sub_negPart b hbsa
  have hc0 : 0 ≤ c := CFC.posPart_nonneg b
  have hd0 : 0 ≤ d := CFC.negPart_nonneg b
  obtain ⟨q,hq⟩ := exists_support_projection e c hc0
  have hqp : q ≤ p := support_le_corner hp hcmem hq
  have hqd : q*d=0 := hq.annihilate d (CFC.posPart_mul_negPart b)
  have hdq : d*q=0 := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg hd0).star_eq,
      hq.proj.isSelfAdjoint.star_eq,star_zero] using congrArg star hqd
  have hcq : b*q=c := by rw [← hb,sub_mul,hq.right,hdq,sub_zero]
  have hqc : q*b=c := by rw [← hb,mul_sub,hq.left,hqd,sub_zero]
  have haq : Commute a q := by
    change a*q=q*a
    have hh := hcq.trans hqc.symm
    dsimp [b] at hh
    simpa only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,
      (hq.proj.le_iff_mul_eq_left hp).mp hqp,
      (hq.proj.le_iff_mul_eq_right hp).mp hqp,sub_left_inj] using hh
  have hap : Commute a p := ha.2.trans ha.1.symm
  have har : 0 ≤ a*(p-q) := (hap.sub_right haq).mul_nonneg ha0 (sub_nonneg.mpr hqp)
  have hal : 0 ≤ (p-a)*q :=
    ((show Commute p q from (hq.proj.commute_of_le hp hqp).symm).sub_left haq).mul_nonneg
      (sub_nonneg.mpr ha1) hq.proj.nonneg
  have hqa : a*q=c+(1/2:ℝ) • q := by
    dsimp [b] at hcq
    rw [sub_mul,smul_mul_assoc,(hq.proj.le_iff_mul_eq_right hp).mp hqp] at hcq
    exact sub_eq_iff_eq_add.mp hcq
  have hlow : 0 ≤ a-(1/2:ℝ) • q := by
    have he : a-(1/2:ℝ) • q=c+a*(p-q) := by
      rw [mul_sub,ha.2,hqa]
      module
    rw [he]
    exact add_nonneg hc0 har
  have hhigh : 0 ≤ (1/2:ℝ) • p-(a-(1/2:ℝ) • q) := by
    have he : (1/2:ℝ) • p-(a-(1/2:ℝ) • q)=(p-a)*q+d := by
      rw [sub_mul,(hq.proj.le_iff_mul_eq_right hp).mp hqp,hqa]
      have haa : a=c-d+(1/2:ℝ) • p := sub_eq_iff_eq_add.mp hb.symm
      conv_lhs => rw [haa]
      module
    rw [he]
    exact add_nonneg hal hd0
  refine ⟨q,hq.proj,hqp,?_,?_⟩
  · have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hlow
    convert hh using 1; module
  · apply sub_nonneg.mp
    have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hhigh
    convert hh using 1; module

omit [PartialOrder M] [StarOrderedRing M] in
lemma real_smul_mem_corner {p a : M} (hp : IsStarProjection p)
    (ha : a ∈ corner p hp) (r : ℝ) : r • a ∈ corner p hp := by
  exact ⟨by rw [mul_smul_comm,ha.1],by rw [smul_mul_assoc,ha.2]⟩

include e in
 

theorem dual_zero_on_corner (F : StrongDual ℂ M) {p : M}
    (hp : IsStarProjection p)
    (hF : ∀ q : M, IsStarProjection q → q ≤ p → F q=0)
    {a : M} (ha : a ∈ corner p hp) : F a=0 := by
  have hbound : ∀ n : ℕ, ∀ b : M, b ∈ corner p hp → 0 ≤ b → b ≤ p →
      ‖F b‖ ≤ (1/2:ℝ)^n * ‖F‖ := by
    intro n
    induction n with
    | zero =>
      intro b hb hb0 hbp
      simpa only [pow_zero,one_mul] using (F.le_opNorm b).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mpr (hbp.trans hp.le_one)))
    | succ n ih =>
      intro b hb hb0 hbp
      obtain ⟨q,hq,hqp,h0,h1⟩ := exists_corner_dyadic_projection e hp hb hb0 hbp
      have hmem : (2:ℝ) • b-q ∈ corner p hp :=
        (corner p hp).sub_mem (real_smul_mem_corner hp hb 2) (projection_mem_corner hp hq hqp)
      have hh := ih ((2:ℝ) • b-q) hmem h0 h1
      have he : F ((2:ℝ) • b-q)=(2:ℝ) • F b := by
        simp only [map_sub,← Complex.coe_smul,map_smul,hF q hq hqp,sub_zero]
      rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
      rw [pow_succ]
      nlinarith
  have hz (b : M) (hb : b ∈ corner p hp) (hb0 : 0 ≤ b) (hbp : b ≤ p) : F b=0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^n * ‖F‖) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
          (by norm_num : (1/2:ℝ)<1)).mul_const ‖F‖
    exact ge_of_tendsto ht (Eventually.of_forall fun n => hbound n b hb hb0 hbp)
  have hpos (b : M) (hb : b ∈ corner p hp) (hb0 : 0 ≤ b) : F b=0 := by
    let r : ℝ := ‖b‖+1
    have hr : 0 < r := by dsimp [r]; positivity
    let c : M := r⁻¹ • b
    have hc0 : 0 ≤ c := smul_nonneg (inv_nonneg.mpr hr.le) hb0
    have hcmem : c ∈ corner p hp := real_smul_mem_corner hp hb _
    have hcn : ‖c‖ ≤ 1 := by
      dsimp [c]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
    have hc1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hc0).mp hcn
    have hcp : c ≤ p := by
      have hh := star_left_conjugate_nonneg (sub_nonneg.mpr hc1) p
      rw [hp.isSelfAdjoint.star_eq,mul_sub,mul_one,sub_mul,hp.isIdempotentElem.eq,
        hcmem.1,hcmem.2] at hh
      exact sub_nonneg.mp hh
    have hh := hz c hcmem hc0 hcp
    dsimp [c] at hh
    simp only [← Complex.coe_smul,map_smul] at hh
    exact (smul_eq_zero.mp hh).resolve_left (by exact_mod_cast inv_ne_zero hr.ne')
  let C : M →L[ℂ] M := (ContinuousLinearMap.mul ℂ M p).comp
    ((ContinuousLinearMap.mul ℂ M).flip p)
  let G : StrongDual ℂ M := F.comp C
  have hG : G=0 := by
    have hker : (⊤ : Submodule ℂ M) ≤ G.ker := by
      rw [← CStarAlgebra.span_nonneg]
      apply Submodule.span_le.mpr
      intro b hb
      change F (p*(b*p))=0
      rw [← mul_assoc]
      apply hpos _ (compress_mem_corner hp b)
      simpa only [hp.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg hb p
    ext b
    exact hker Submodule.mem_top
  have hh := congrArg (fun K : StrongDual ℂ M => K a) hG
  change F (p*(a*p))=0 at hh
  rwa [ha.2,ha.1] at hh

include e in
lemma commute_corner_of_projections {p b : M} (hp : IsStarProjection p)
    (hb : ∀ q : M, IsStarProjection q → q ≤ p → Commute q b)
    {a : M} (ha : a ∈ corner p hp) : Commute a b := by
  change a*b=b*a
  apply sub_eq_zero.mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro F
  let D : M →L[ℂ] M := (ContinuousLinearMap.mul ℂ M).flip b-
    ContinuousLinearMap.mul ℂ M b
  have h := dual_zero_on_corner e (F.comp D) hp (fun q hq hqp => by
    change F (q*b-b*q)=0
    rw [(hb q hq hqp).eq,sub_self,map_zero]) ha
  exact h

end HochschildCorners

 

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild BoundedHochschild.WeakAlgebra HochschildRigidity HochschildSakai
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p)

abbrev Corner := corner p hp

instance cornerOne : One (Corner p hp) := ⟨⟨p,self_mem_corner hp⟩⟩
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_one : ((1 : Corner p hp):M)=p := rfl

instance cornerRing : Ring (Corner p hp) where
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2
  natCast := fun n => ⟨n • p,(corner p hp).nsmul_mem (self_mem_corner hp) n⟩
  natCast_zero := Subtype.ext (zero_nsmul _)
  natCast_succ n := Subtype.ext (succ_nsmul _ _)
  intCast := fun z => ⟨z • p,(corner p hp).toNonUnitalSubring.toAddSubgroup.zsmul_mem (self_mem_corner hp) z⟩
  intCast_ofNat n := Subtype.ext (natCast_zsmul _ _)
  intCast_negSucc n := Subtype.ext (negSucc_zsmul _ _)

instance cornerAlgebra : Algebra ℂ (Corner p hp) where
  algebraMap :=
    { toFun := fun c => c • (1 : Corner p hp)
      map_zero' := zero_smul _ _
      map_one' := one_smul _ _
      map_add' := fun _ _ => add_smul _ _ _
      map_mul' := fun c d => by
        ext
        change (c*d) • p=(c • p)*(d • p)
        rw [smul_mul_smul_comm,hp.isIdempotentElem.eq] }
  commutes' c a := by
    ext
    change (c • p)*(a:M)=(a:M)*(c • p)
    rw [smul_mul_assoc,mul_smul_comm,a.property.1,a.property.2]
  smul_def' c a := by
    ext
    change c • (a:M)=(c • p)*(a:M)
    rw [smul_mul_assoc,a.property.1]

instance cornerNormedRing : NormedRing (Corner p hp) where
  dist_eq a b := by
    change dist (a:M) (b:M)=‖-(a:M)+(b:M)‖
    rw [dist_comm,dist_eq_norm,sub_eq_add_neg,add_comm]
  norm_mul_le a b := norm_mul_le (a:M) (b:M)
instance cornerNormedAlgebra : NormedAlgebra ℂ (Corner p hp) where
  norm_smul_le c a := norm_smul_le c (a:M)
instance cornerCStarAlgebra : CStarAlgebra (Corner p hp) where

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_mul (a b : Corner p hp) : ((a*b : Corner p hp):M)=(a:M)*(b:M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_star (a : Corner p hp) : ((star a : Corner p hp):M)=star (a:M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_smul (c : ℂ) (a : Corner p hp) : ((c • a : Corner p hp):M)=c • (a:M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma corner_coe_zero : ((0 : Corner p hp):M)=0 := rfl

example : PartialOrder (Corner p hp) := inferInstance
instance cornerStarOrderedRing : StarOrderedRing (Corner p hp) :=
  StarOrderedRing.of_nonneg_iff' (fun {a b} h c => show (c:M)+(a:M) ≤ (c:M)+(b:M) from add_le_add le_rfl (show (a:M) ≤ (b:M) from h))
    (fun a => by
      constructor
      · intro ha
        have haM : (0:M) ≤ (a:M) := ha
        have hs : CFC.sqrt (a:M) ∈ corner p hp := by
          rw [CFC.sqrt_eq_real_sqrt (a:M) haM]
          exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
        refine ⟨⟨CFC.sqrt (a:M),hs⟩,Subtype.ext ?_⟩
        change (a:M)=star (CFC.sqrt (a:M))*CFC.sqrt (a:M)
        rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq,CFC.sqrt_mul_sqrt_self (a:M) haM]
      · rintro ⟨b,rfl⟩
        exact star_mul_self_nonneg (b:M))

section Predual
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def weakCorner : Submodule ℂ (WeakDual ℂ X) where
  carrier := {f | weakEquiv e f ∈ corner p hp}
  zero_mem' := by
    change weakEquiv e 0 ∈ corner p hp
    rw [map_zero]
    exact (corner p hp).zero_mem
  add_mem' := by
    intro a b ha hb
    change weakEquiv e (a+b) ∈ corner p hp
    rw [map_add]
    exact (corner p hp).add_mem ha hb
  smul_mem' := by
    intro c a ha
    change weakEquiv e (c • a) ∈ corner p hp
    rw [LinearEquiv.map_smulₛₗ]
    exact (corner p hp).smul_mem (star c) ha

lemma weakCorner_closed : IsClosed (weakCorner p hp e : Set (WeakDual ℂ X)) := by
  have hL := mul_hasPreadjoint e p
  have hR := mul_right_hasPreadjoint e p
  have hLeft := isClosed_eq (normal_continuous e _ hL) (continuous_id : Continuous (id : WeakDual ℂ X → _))
  have hRight := isClosed_eq (normal_continuous e _ hR) (continuous_id : Continuous (id : WeakDual ℂ X → _))
  change IsClosed {f | (weakEquiv e).symm (p*weakEquiv e f)=f} at hLeft
  change IsClosed {f | (weakEquiv e).symm (weakEquiv e f*p)=f} at hRight
  convert hLeft.inter hRight using 1
  ext f
  change (p*weakEquiv e f=weakEquiv e f ∧ weakEquiv e f*p=weakEquiv e f) ↔
    ((weakEquiv e).symm (p*weakEquiv e f)=f ∧ (weakEquiv e).symm (weakEquiv e f*p)=f)
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨by rw [h,LinearEquiv.symm_apply_apply],by rw [h',LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨h,h'⟩
    exact ⟨by simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e) h,
      by simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e) h'⟩

def CornerPredual := X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)
instance : NormedAddCommGroup (CornerPredual p hp e) := inferInstanceAs
  (NormedAddCommGroup (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))
instance : NormedSpace ℂ (CornerPredual p hp e) := inferInstanceAs
  (NormedSpace ℂ (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))
instance : CompleteSpace (CornerPredual p hp e) := inferInstanceAs
  (CompleteSpace (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))

def cornerStrongEquiv : WeakSubspace.strong (weakCorner p hp e) ≃ₗᵢ⋆[ℂ] Corner p hp where
  toFun f := ⟨e f.val,by
    have hf := (WeakSubspace.mem_strong (weakCorner p hp e) f.val).mp f.property
    exact hf⟩
  invFun a := ⟨e.symm a.val,by
    rw [WeakSubspace.mem_strong]
    change e (e.symm a.val) ∈ corner p hp
    simpa only [LinearIsometryEquiv.apply_symm_apply] using a.property⟩
  left_inv f := Subtype.ext (e.symm_apply_apply f.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)
  map_add' f g := Subtype.ext (map_add e f.val g.val)
  map_smul' c f := Subtype.ext (e.map_smulₛₗ c f.val)
  norm_map' f := e.norm_map f.val

def cornerPredualEquiv : StrongDual ℂ (CornerPredual p hp e) ≃ₗᵢ⋆[ℂ] Corner p hp :=
  (WeakSubspace.quotientDualEquiv (weakCorner p hp e) (weakCorner_closed p hp e)).trans
    (cornerStrongEquiv p hp e)

lemma cornerPredualEquiv_apply (F : StrongDual ℂ (CornerPredual p hp e)) (z : X) :
    e.symm ((cornerPredualEquiv p hp e F : Corner p hp):M) z=F (Submodule.Quotient.mk z) := by
  change e.symm (e (F.comp (WeakSubspace.preannihilator (weakCorner p hp e)).mkQL)) z=_
  rw [e.symm_apply_apply]
  rfl

lemma cornerPredualEquiv_symm_mk (a : Corner p hp) (z : X) :
    (cornerPredualEquiv p hp e).symm a (Submodule.Quotient.mk z)=e.symm (a:M) z := by
  have h := (cornerPredualEquiv p hp e).apply_symm_apply a
  have hh := congrArg (fun b : Corner p hp => e.symm (b:M) z) h
  rw [cornerPredualEquiv_apply] at hh
  exact hh

end Predual
end HochschildCorners

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_projection_coe {q : Corner p hp} (hq : IsStarProjection q) :
    IsStarProjection (q:M) := ⟨congrArg (fun a : Corner p hp => (a:M)) hq.isIdempotentElem.eq,
      congrArg (fun a : Corner p hp => (a:M)) hq.isSelfAdjoint.star_eq⟩

lemma corner_projection_le {q : Corner p hp} (hq : IsStarProjection q) : (q:M) ≤ p :=
  ((corner_projection_coe p hp hq).le_iff_mul_eq_left hp).mpr q.property.2

lemma corner_no_minimal (hdiff : HochschildDiffuse.NoMinimalProjections M) :
    HochschildDiffuse.NoMinimalProjections (Corner p hp) := by
  intro q hq hq0
  obtain ⟨r,hr,hrq,hr0,hrne⟩ := hdiff (q:M) (corner_projection_coe p hp hq)
    (fun h => hq0 (Subtype.ext h))
  have hrp := hrq.trans (corner_projection_le p hp hq)
  have hrc : r ∈ corner p hp := ⟨(hr.le_iff_mul_eq_right hp).mp hrp,
    (hr.le_iff_mul_eq_left hp).mp hrp⟩
  refine ⟨⟨r,hrc⟩,⟨Subtype.ext hr.isIdempotentElem.eq,Subtype.ext hr.isSelfAdjoint.star_eq⟩,
    hrq,?_,?_⟩
  · exact fun h => hr0 (congrArg (fun a : Corner p hp => (a:M)) h)
  · exact fun h => hrne (congrArg (fun a : Corner p hp => (a:M)) h)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

def cornerTrace : Corner p hp →ₚ[ℂ] ℂ where
  toLinearMap := ((τ p).re : ℂ)⁻¹ • (τ.toLinearMap.comp (corner p hp).subtype)
  monotone' := fun _ _ h => mul_le_mul_of_nonneg_left (τ.monotone h)
    (inv_nonneg.mpr (Complex.zero_le_real.mpr
      (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1))

@[simp] lemma cornerTrace_apply (a : Corner p hp) :
    cornerTrace p hp τ a = ((τ p).re : ℂ)⁻¹ * τ (a:M) := rfl

lemma cornerTrace_one (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hp0 : p ≠ 0) :
    cornerTrace p hp τ 1=1 := by
  rw [cornerTrace_apply,corner_coe_one,projection_trace_real τ p hp]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
    (HochschildDiffuse.projection_trace_pos τ hfaith hp hp0).ne')

lemma cornerTrace_tracial (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (a b : Corner p hp) : cornerTrace p hp τ (a*b)=cornerTrace p hp τ (b*a) := by
  simp only [cornerTrace_apply,corner_coe_mul,htr a.val b.val]

lemma cornerTrace_faithful (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hp0 : p ≠ 0)
    (a : Corner p hp) (ha : cornerTrace p hp τ (star a*a)=0) : a=0 := by
  have hne : ((τ p).re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (HochschildDiffuse.projection_trace_pos τ hfaith hp hp0).ne'
  have hh := (mul_eq_zero.mp ha).resolve_left (inv_ne_zero hne)
  exact Subtype.ext (hfaith a.val hh)

lemma cornerTrace_normal (hτ : TraceInPredual e τ) :
    TraceInPredual (cornerPredualEquiv p hp e) (cornerTrace p hp τ) := by
  obtain ⟨z,hz⟩ := hτ
  let zq : CornerPredual p hp e := Submodule.Quotient.mk z
  refine ⟨((τ p).re : ℂ)⁻¹ • zq,fun a => ?_⟩
  rw [map_smul]
  change _ = star (((τ p).re : ℂ)⁻¹ * (cornerPredualEquiv p hp e).symm a (Submodule.Quotient.mk z))
  rw [cornerPredualEquiv_symm_mk]
  rw [cornerTrace_apply,hz a.val,star_mul,star_inv₀]
  simp only [Complex.star_def,Complex.conj_ofReal]
  exact mul_comm _ _

end HochschildCorners

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)

lemma corner_factor_of_matrix_diagonal {n : ℕ} (E : MatrixSystem M n) (i : Fin n)
    (hip : E.entry i i ≤ p)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M)) :
    ∀ b : Corner p hp, (∀ x : Corner p hp, Commute b x) → ∃ c : ℂ, b=c • (1 : Corner p hp) := by
  intro b hb
  let r := E.entry i i
  have hr := E.diagonal_proj i
  have hpr : p*r=r := (hr.le_iff_mul_eq_right hp).mp hip
  have hrp : r*p=r := (hr.le_iff_mul_eq_left hp).mp hip
  have hrmem : r ∈ corner p hp := ⟨hpr,hrp⟩
  have hbr : Commute (b:M) r := congrArg (fun a : Corner p hp => (a:M)) (hb ⟨r,hrmem⟩).eq
  let d : E.commutant := ⟨E.coefficient i i (b:M),E.coefficient_mem i i b⟩
  have hd : ∀ c : E.commutant, Commute d c := by
    intro c
    have hrc : r*(c:M)=(c:M)*r := (c.property i i).eq.symm
    have hrrc : r*(r*(c:M))=r*(c:M) := by rw [← mul_assoc,hr.isIdempotentElem.eq]
    have hrcr : (r*(c:M))*r=r*(c:M) := by rw [hrc,mul_assoc,hr.isIdempotentElem.eq]
    have hcpm : r*(c:M) ∈ corner p hp := ⟨by rw [← mul_assoc,hpr],by
      rw [hrc,mul_assoc,hrp]⟩
    have hbc : (b:M)*(r*(c:M))=(r*(c:M))*(b:M) :=
      congrArg (fun a : Corner p hp => (a:M)) (hb ⟨_,hcpm⟩).eq
    apply Subtype.ext
    change E.coefficient i i (b:M)*(c:M)=(c:M)*E.coefficient i i (b:M)
    calc
      _ = E.coefficient i i (b:M)*E.coefficient i i (r*(c:M)) := by
        rw [E.coefficient_of_commutant i c.property]
      _ = E.coefficient i i ((b:M)*r*(r*(c:M))) := E.coefficient_mul i _ _
      _ = E.coefficient i i ((r*(c:M))*r*(b:M)) := by
        rw [mul_assoc (b:M) r,hrrc,hbc,hrcr]
      _ = E.coefficient i i (r*(c:M))*E.coefficient i i (b:M) := (E.coefficient_mul i _ _).symm
      _ = _ := by rw [E.coefficient_of_commutant i c.property]
  obtain ⟨c,hc⟩ := E.factor_of_commutant _ rfl hfactor d hd
  have hdc : E.coefficient i i (b:M)=c • (1:M) := congrArg (fun a : E.commutant => (a:M)) hc
  have hbrc : (b:M)*r=c • r := by
    have hh := E.coefficient_corner i (b:M)
    rw [hdc, mul_smul_comm,smul_mul_assoc,mul_one,hr.isIdempotentElem.eq] at hh
    rw [← hbr.eq,mul_assoc,hr.isIdempotentElem.eq] at hh
    exact hh.symm
  let a := (b:M)-c • p
  have hap : a*p=a := by dsimp [a]; rw [sub_mul,b.property.2,smul_mul_assoc,hp.isIdempotentElem.eq]
  have har : a*r=0 := by dsimp [a]; rw [sub_mul,hbrc,smul_mul_assoc,hpr,sub_self]
  have hra : r*a=0 := by dsimp [a]; rw [mul_sub,← hbr.eq,hbrc,mul_smul_comm,hrp,sub_self]
  have haxr (x : M) : a*x*r=0 := by
    have hmem : p*x*r ∈ corner p hp := ⟨by rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq],by
      rw [mul_assoc,hrp]⟩
    have hbX : (b:M)*(p*x*r)=(p*x*r)*(b:M) :=
      congrArg (fun y : Corner p hp => (y:M)) (hb ⟨_,hmem⟩).eq
    have hac : a*(p*x*r)=(p*x*r)*a := by
      dsimp [a]
      rw [sub_mul,mul_sub,hbX,smul_mul_assoc,mul_smul_comm,hmem.1,hmem.2]
    calc
      a*x*r = a*(p*x*r) := by rw [← mul_assoc,← mul_assoc,hap]
      _ = (p*x*r)*a := hac
      _ = 0 := by rw [mul_assoc,hra,mul_zero]
  have ha0 : a=0 := by
    calc
      a = ∑ j, a*E.entry j j := by rw [← Finset.mul_sum,E.sum_diagonal,mul_one]
      _ = ∑ j, (a*E.entry j i*r)*E.entry i j := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [r]
        rw [mul_assoc a (E.entry j i),E.entry_mul,ite_eq_left rfl,mul_assoc,E.entry_mul,ite_eq_left rfl]
      _ = 0 := by simp only [haxr,zero_mul,Finset.sum_const_zero]
  refine ⟨c,Subtype.ext (sub_eq_zero.mp ha0)⟩

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

include e hp in
lemma exists_matrix_diagonal_below
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M) (hp0 : p ≠ 0) :
    ∃ (n : ℕ) (E : MatrixSystem M n) (i : Fin n), E.entry i i ≤ p := by
  classical
  have hnorm : 0<‖τ.toPreGNS p‖ := lt_of_le_of_ne (norm_nonneg _)
    (fun h => hp0 ((preGNS_norm_eq_zero_iff τ hfaith p).mp h.symm))
  obtain ⟨n,E,s,hn,hs,hsp,herr⟩ := exists_matrix_projection_approx e τ hτ htr
    hfaith hdiff h1 hfactor hp hnorm
  have hsn : s.Nonempty := by
    by_contra h
    have hz : s=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hz,Finset.sum_empty,sub_zero] at herr
    exact lt_irrefl _ herr
  obtain ⟨i,hi⟩ := hsn
  refine ⟨n,E,i,le_trans ?_ hsp⟩
  exact Finset.single_le_sum (fun j hj => (E.diagonal_proj j).nonneg) hi

include e hp in
lemma corner_factor
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M) (hp0 : p ≠ 0) :
    ∀ b : Corner p hp, (∀ x : Corner p hp, Commute b x) → ∃ c : ℂ, b=c • (1 : Corner p hp) := by
  obtain ⟨n,E,i,hi⟩ := exists_matrix_diagonal_below p hp e τ hτ h1 htr hfaith hfactor hdiff hp0
  exact corner_factor_of_matrix_diagonal p hp E i hi hfactor

end HochschildCorners
end

end OAI
