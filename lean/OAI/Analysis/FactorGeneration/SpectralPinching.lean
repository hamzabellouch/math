import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import OAI.Analysis.FactorGeneration.Pinching
import OAI.Analysis.FactorGeneration.Supports

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerCutCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance cornerCutOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerCutPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerCutLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerCutStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

/-- Functional calculus positive parts retain a given right support. -/
theorem positivePart_right_support (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (p : AlgebraProjection M) (hp : x*p.val=x) : x⁺*p.val=x⁺ := by
  have he : x⁺*(1-p.val)=x⁻*(1-p.val) := by
    apply sub_eq_zero.mp
    rw [← sub_mul,CFC.posPart_sub_negPart x hx,mul_sub,mul_one,hp,sub_self]
  have hz : star (x⁺*(1-p.val))*(x⁺*(1-p.val))=0 := by
    nth_rw 2 [he]
    rw [star_mul,star_sub,star_one,p.property.isSelfAdjoint.star_eq,
      (CFC.posPart_nonneg x).isSelfAdjoint.star_eq]
    calc (1-p.val)*x⁺*(x⁻*(1-p.val)) = (1-p.val)*(x⁺*x⁻)*(1-p.val) := by
           simp only [mul_assoc]
      _ = 0 := by rw [CFC.posPart_mul_negPart,mul_zero,zero_mul]
  have h := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  rw [mul_sub,mul_one,sub_eq_zero] at h
  exact h.symm

theorem positiveSupport_le_corner (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (p : AlgebraProjection M) (hp : x*p.val=x) : positiveSupport x ≤ p := by
  apply (rangeProjection_le_iff _ p).mpr
  have h := congrArg star (positivePart_right_support x hx p hp)
  simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
    (CFC.posPart_nonneg x).isSelfAdjoint.star_eq] using h

def cornerSpectralShift (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    M.toStarSubalgebra := p.val*x*p.val-(t : ℂ) • p.val

theorem cornerSpectralShift_selfAdjoint (p : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (t : ℝ) :
    IsSelfAdjoint (cornerSpectralShift p x t) := by
  change star (p.val*x*p.val-(t : ℂ) • p.val) = _
  simp only [cornerSpectralShift,star_sub,star_mul,star_smul,p.property.isSelfAdjoint.star_eq,hx.star_eq,
    Complex.star_def,Complex.conj_ofReal,mul_assoc]

theorem cornerSpectralShift_support (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    cornerSpectralShift p x t*p.val=cornerSpectralShift p x t := by
  simp only [cornerSpectralShift,sub_mul,smul_mul_assoc,mul_assoc,p.property.isIdempotentElem.eq]

def cornerSpectralCut (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    AlgebraProjection M := positiveSupport (cornerSpectralShift p x t)

theorem cornerSpectralCut_le (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) : cornerSpectralCut p x t ≤ p :=
  positiveSupport_le_corner _ (cornerSpectralShift_selfAdjoint p x hx t) p
    (cornerSpectralShift_support p x t)

namespace CornerPartition
/-- Splitting p at an explicitly given subprojection q. -/
def binary (p q : AlgebraProjection M) (hq : q ≤ p) : CornerPartition p :=
  ofFamily (fun b : Bool => if b then q else
    ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property hq⟩)
    (by
      intro i j hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · change (p.val-q.val)*q.val=0
        rw [sub_mul,hq,q.property.isIdempotentElem.eq,sub_self]
      · change q.val*(p.val-q.val)=0
        rw [mul_sub,projection_mul_of_le hq,q.property.isIdempotentElem.eq,sub_self]
      · exact (hij rfl).elim)
    (by
      rw [Fintype.sum_bool]
      change q.val+(p.val-q.val)=p.val
      abel)

theorem binary_pinch (p q : AlgebraProjection M) (hq : q ≤ p) (x : M.toStarSubalgebra) :
    (binary p q hq).pinch x = q.val*x*q.val+(p.val-q.val)*x*(p.val-q.val) := by
  rw [binary,ofFamily_pinch,Fintype.sum_bool]
  rfl

end CornerPartition

/-- The finite corner partition constructed from the shifted positive part. -/
def cornerSpectralPartition (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) : CornerPartition p :=
  CornerPartition.binary p (cornerSpectralCut p x t) (cornerSpectralCut_le p x hx t)

/-- Its high block has the promised spectral lower bound. -/
theorem cornerSpectralCut_lower (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    0 ≤ (cornerSpectralCut p x t).val*x*(cornerSpectralCut p x t).val -
      (t : ℂ) • (cornerSpectralCut p x t).val := by
  have hc := positiveSupport_compression (cornerSpectralShift p x t)
    (cornerSpectralShift_selfAdjoint p x hx t)
  have hqp := cornerSpectralCut_le p x hx t
  have hleft : p.val*(cornerSpectralCut p x t).val=(cornerSpectralCut p x t).val := hqp
  have he : (cornerSpectralCut p x t).val * cornerSpectralShift p x t *
      (cornerSpectralCut p x t).val =
      (cornerSpectralCut p x t).val*x*(cornerSpectralCut p x t).val -
        (t : ℂ) • (cornerSpectralCut p x t).val := by
    simp only [cornerSpectralShift,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    simp only [← mul_assoc,projection_mul_of_le hqp]
    simp only [mul_assoc,hleft,(cornerSpectralCut p x t).property.isIdempotentElem.eq]
  rw [← he]
  exact hc.symm ▸ CFC.posPart_nonneg _

/-- The low block has the opposite shifted sign in the same corner. -/
theorem cornerSpectralCut_upper (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    let r := p.val-(cornerSpectralCut p x t).val
    r*x*r-(t : ℂ) • r ≤ 0 := by
  let q := cornerSpectralCut p x t
  let r : AlgebraProjection M := ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property
    (cornerSpectralCut_le p x hx t)⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-q.val)=p.val-q.val
    rw [mul_sub,p.property.isIdempotentElem.eq,cornerSpectralCut_le p x hx t]
  have hrleft : p.val*r.val=r.val := hrp
  have hs := cornerSpectralShift_support p x t
  have hsl : p.val*cornerSpectralShift p x t=cornerSpectralShift p x t := by
    have h := congrArg star hs
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
      (cornerSpectralShift_selfAdjoint p x hx t).star_eq] using h
  have hc : r.val*cornerSpectralShift p x t*r.val = -(cornerSpectralShift p x t)⁻ := by
    change (p.val-q.val)*cornerSpectralShift p x t*(p.val-q.val)=_
    have he : (p.val-q.val)*cornerSpectralShift p x t*(p.val-q.val) =
        (1-q.val)*cornerSpectralShift p x t*(1-q.val) := by
      simp only [sub_mul,mul_sub,one_mul,mul_one,hsl,hs,mul_assoc]
    rw [he]
    exact positiveSupport_complement_compression _ (cornerSpectralShift_selfAdjoint p x hx t)
  have he : r.val*cornerSpectralShift p x t*r.val=r.val*x*r.val-(t : ℂ) • r.val := by
    simp only [cornerSpectralShift,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    simp only [← mul_assoc,projection_mul_of_le hrp]
    simp only [mul_assoc,hrleft,r.property.isIdempotentElem.eq]
  change r.val*x*r.val-(t : ℂ) • r.val ≤ 0
  rw [← he,hc]
  exact neg_nonpos.mpr (CFC.negPart_nonneg _)

end

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition

theorem binary_pinch_of_commutes (p q : AlgebraProjection M) (hq : q ≤ p)
    (x : M.toStarSubalgebra) (hl : p.val*x=x) (hr : x*p.val=x)
    (hc : q.val*x=x*q.val) : (binary p q hq).pinch x=x := by
  have hqq : q.val*x*q.val=q.val*x := by
    rw [hc,mul_assoc,q.property.isIdempotentElem.eq]
  rw [binary_pinch]
  simp only [sub_mul,mul_sub,hl,hr,hqq]
  rw [hc]
  simp only [mul_assoc,projection_mul_of_le hq]
  abel

end CornerPartition

theorem cornerSpectralCut_commutes (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    (cornerSpectralCut p x t).val*(p.val*x*p.val)=
      (p.val*x*p.val)*(cornerSpectralCut p x t).val := by
  let q := cornerSpectralCut p x t
  have h := (positiveSupport_commutes (cornerSpectralShift p x t)
    (cornerSpectralShift_selfAdjoint p x hx t)).eq
  change q.val*(p.val*x*p.val-(t : ℂ) • p.val) =
    (p.val*x*p.val-(t : ℂ) • p.val)*q.val at h
  have hqp := cornerSpectralCut_le p x hx t
  have hleft : p.val*q.val=q.val := hqp
  have hright : q.val*p.val=q.val := projection_mul_of_le hqp
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,
    hright,hleft] at h
  exact sub_left_inj.mp h

theorem cornerSpectralPartition_pinch (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    (cornerSpectralPartition p x hx t).pinch x=p.val*x*p.val := by
  rw [← (cornerSpectralPartition p x hx t).pinch_corner_compression]
  apply CornerPartition.binary_pinch_of_commutes
  · simp only [← mul_assoc,p.property.isIdempotentElem.eq]
  · simp only [mul_assoc,p.property.isIdempotentElem.eq]
  · exact cornerSpectralCut_commutes p x hx t

end

/-! Interval bounds propagated through constructed spectral corner splits. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance intervalCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance intervalOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance intervalPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance intervalLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance intervalStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem compress_scalar_shift {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ) :
    q.val*(p.val*x*p.val-(t : ℂ) • p.val)*q.val =
      q.val*x*q.val-(t : ℂ) • q.val := by
  have hl : p.val*q.val=q.val := hqp
  have hr := projection_mul_of_le hqp
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  simp only [← mul_assoc,hr]
  simp only [mul_assoc,hl,q.property.isIdempotentElem.eq]

theorem lower_bound_compress {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ)
    (h : 0 ≤ p.val*x*p.val-(t : ℂ) • p.val) :
    0 ≤ q.val*x*q.val-(t : ℂ) • q.val := by
  have hh := star_left_conjugate_nonneg h q.val
  rw [q.property.isSelfAdjoint.star_eq,compress_scalar_shift hqp] at hh
  exact hh

theorem upper_bound_compress {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ)
    (h : p.val*x*p.val-(t : ℂ) • p.val ≤ 0) :
    q.val*x*q.val-(t : ℂ) • q.val ≤ 0 := by
  have hh := star_left_conjugate_nonneg (neg_nonneg.mpr h) q.val
  rw [q.property.isSelfAdjoint.star_eq,mul_neg,neg_mul,compress_scalar_shift hqp] at hh
  exact neg_nonneg.mp hh

structure SpectralInterval (x : M.toStarSubalgebra) where
  proj : AlgebraProjection M
  lo : ℝ
  hi : ℝ
  lower : 0 ≤ proj.val*x*proj.val-(lo : ℂ) • proj.val
  upper : proj.val*x*proj.val-(hi : ℂ) • proj.val ≤ 0

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

def midpoint : ℝ := (I.lo+I.hi)/2

def highProjection : AlgebraProjection M := cornerSpectralCut I.proj x I.midpoint

def lowProjection : AlgebraProjection M :=
  ⟨I.proj.val-(I.highProjection).val,
    (I.highProjection).property.sub_of_mul_eq_right I.proj.property
      (cornerSpectralCut_le I.proj x hx I.midpoint)⟩

theorem high_le (hx : IsSelfAdjoint x) : I.highProjection ≤ I.proj :=
  cornerSpectralCut_le I.proj x hx I.midpoint

theorem low_le : I.lowProjection hx ≤ I.proj := by
  change I.proj.val*(I.proj.val-(I.highProjection).val)=I.proj.val-I.highProjection.val
  rw [mul_sub,I.proj.property.isIdempotentElem.eq,I.high_le hx]

def high : SpectralInterval x where
  proj := I.highProjection
  lo := I.midpoint
  hi := I.hi
  lower := cornerSpectralCut_lower I.proj x hx I.midpoint
  upper := upper_bound_compress (I.high_le hx) x I.hi I.upper

def low : SpectralInterval x where
  proj := I.lowProjection hx
  lo := I.lo
  hi := I.midpoint
  lower := lower_bound_compress (I.low_le hx) x I.lo I.lower
  upper := cornerSpectralCut_upper I.proj x hx I.midpoint

def child (b : Bool) : SpectralInterval x := if b then I.high hx else I.low hx

theorem child_le (b : Bool) : (I.child hx b).proj ≤ I.proj := by
  cases b
  · exact I.low_le hx
  · exact I.high_le hx

theorem child_width (b : Bool) :
    (I.child hx b).hi-(I.child hx b).lo=(I.hi-I.lo)/2 := by
  cases b <;> dsimp [child,high,low,midpoint] <;> ring

theorem child_total : (I.child hx false).proj.val+(I.child hx true).proj.val=I.proj.val := by
  change (I.proj.val-(I.highProjection).val)+(I.highProjection).val=I.proj.val
  exact sub_add_cancel _ _

theorem child_orthogonal (b c : Bool) (h : b ≠ c) :
    (I.child hx b).proj.val*(I.child hx c).proj.val=0 := by
  have hl : I.proj.val*(I.highProjection).val=(I.highProjection).val := I.high_le hx
  have hr := projection_mul_of_le (I.high_le hx)
  cases b <;> cases c
  · exact (h rfl).elim
  · change (I.proj.val-(I.highProjection).val)*(I.highProjection).val=0
    rw [sub_mul,hl,(I.highProjection).property.isIdempotentElem.eq,sub_self]
  · change (I.highProjection).val*(I.proj.val-(I.highProjection).val)=0
    rw [mul_sub,hr,(I.highProjection).property.isIdempotentElem.eq,sub_self]
  · exact (h rfl).elim

theorem child_compression_total :
    (I.child hx false).proj.val*x*(I.child hx false).proj.val+
    (I.child hx true).proj.val*x*(I.child hx true).proj.val=I.proj.val*x*I.proj.val := by
  have h := cornerSpectralPartition_pinch I.proj x hx I.midpoint
  rw [cornerSpectralPartition,CornerPartition.binary_pinch] at h
  exact (add_comm _ _).trans h

end SpectralInterval

end

/-! Finite dyadic trees of actual spectral interval cuts. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

def level (I : SpectralInterval x) (hx : IsSelfAdjoint x) : (n : ℕ) → DyadicIndex n → SpectralInterval x
  | 0,_ => I
  | n+1,i => (level I hx n i.1).child hx i.2

theorem level_le : ∀ n i, (I.level hx n i).proj ≤ I.proj
  | 0,_ => le_refl _
  | n+1,i => ((I.level hx n i.1).child_le hx i.2).trans (level_le n i.1)

theorem level_width : ∀ n i,
    (I.level hx n i).hi-(I.level hx n i).lo = (I.hi-I.lo)/(2:ℝ)^n
  | 0,_ => by simp [level]
  | n+1,i => by
    change ((I.level hx n i.1).child hx i.2).hi-
      ((I.level hx n i.1).child hx i.2).lo=_
    rw [child_width,level_width n i.1,pow_succ,div_div]

theorem level_total : ∀ n, (∑ i : DyadicIndex n, (I.level hx n i).proj.val)=I.proj.val
  | 0 => by
    change (∑ _ : Unit, I.proj.val)=I.proj.val
    simp
  | n+1 => by
    change (∑ i : DyadicIndex n × Bool, ((I.level hx n i.1).child hx i.2).proj.val)=_
    rw [Fintype.sum_prod_type]
    have he (i : DyadicIndex n) :
        (∑ b : Bool, ((I.level hx n i).child hx b).proj.val)=(I.level hx n i).proj.val := by
      rw [Fintype.sum_bool,add_comm,child_total]
    simp only [he]
    exact level_total n

theorem level_orthogonal : ∀ n (i j : DyadicIndex n), i ≠ j →
    (I.level hx n i).proj.val*(I.level hx n j).proj.val=0
  | 0,i,j,h => (h (@Subsingleton.elim Unit _ i j)).elim
  | n+1,⟨i,b⟩,⟨j,c⟩,h => by
    change ((I.level hx n i).child hx b).proj.val*((I.level hx n j).child hx c).proj.val=0
    by_cases hij : i=j
    · subst j
      exact (I.level hx n i).child_orthogonal hx b c (fun hbc => h (by cases hbc; rfl))
    · exact orthogonal_subprojections (level_orthogonal n i j hij)
        ((I.level hx n i).child_le hx b) ((I.level hx n j).child_le hx c)

theorem level_compression_total : ∀ n,
    (∑ i : DyadicIndex n, (I.level hx n i).proj.val*x*(I.level hx n i).proj.val) =
      I.proj.val*x*I.proj.val
  | 0 => by
    change (∑ _ : Unit, I.proj.val*x*I.proj.val)=I.proj.val*x*I.proj.val
    simp
  | n+1 => by
    change (∑ i : DyadicIndex n × Bool, ((I.level hx n i.1).child hx i.2).proj.val*x*
      ((I.level hx n i.1).child hx i.2).proj.val)=_
    rw [Fintype.sum_prod_type]
    have he (i : DyadicIndex n) :
        (∑ b : Bool, ((I.level hx n i).child hx b).proj.val*x*
          ((I.level hx n i).child hx b).proj.val)=
        (I.level hx n i).proj.val*x*(I.level hx n i).proj.val := by
      rw [Fintype.sum_bool,add_comm,child_compression_total]
    simp only [he]
    exact level_compression_total n

def partition (n : ℕ) : CornerPartition I.proj :=
  CornerPartition.ofFamily (fun i : DyadicIndex n => (I.level hx n i).proj)
    (I.level_orthogonal hx n) (I.level_total hx n)

theorem partition_pinch (n : ℕ) : (I.partition hx n).pinch x=I.proj.val*x*I.proj.val := by
  rw [partition,CornerPartition.ofFamily_pinch]
  exact I.level_compression_total hx n

end SpectralInterval

/-! Finite spectral approximations constructed by successive sign cuts.
The approximation bound is proved from the leaf intervals. -/
local instance approximationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance approximationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance approximationPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance approximationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance approximationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

theorem error_upper : I.proj.val*x*I.proj.val-(I.lo : ℂ) • I.proj.val ≤
    ((I.hi-I.lo : ℝ) : ℂ) • I.proj.val := by
  calc I.proj.val*x*I.proj.val-(I.lo : ℂ) • I.proj.val ≤
      (I.hi : ℂ) • I.proj.val-(I.lo : ℂ) • I.proj.val :=
        sub_le_sub_right (sub_nonpos.mp I.upper) _
    _ = _ := by rw [← sub_smul,Complex.ofReal_sub]

def approximant (n : ℕ) : M.toStarSubalgebra :=
  ∑ i : DyadicIndex n, ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val

theorem approximant_error_sum (n : ℕ) :
    I.proj.val*x*I.proj.val-I.approximant hx n =
      ∑ i : DyadicIndex n, ((I.level hx n i).proj.val*x*(I.level hx n i).proj.val-
        ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val) := by
  rw [Finset.sum_sub_distrib,I.level_compression_total hx]
  rfl

theorem approximant_error_nonneg (n : ℕ) :
    0 ≤ I.proj.val*x*I.proj.val-I.approximant hx n := by
  rw [I.approximant_error_sum hx]
  exact Finset.sum_nonneg (fun i _ => (I.level hx n i).lower)

theorem approximant_error_upper (n : ℕ) :
    I.proj.val*x*I.proj.val-I.approximant hx n ≤
      (((I.hi-I.lo)/(2:ℝ)^n : ℝ) : ℂ) • I.proj.val := by
  rw [I.approximant_error_sum hx]
  have he := Finset.sum_le_sum (s := (Finset.univ : Finset (DyadicIndex n)))
    (fun i _ => (I.level hx n i).error_upper)
  simp only [I.level_width hx] at he
  rw [← Finset.smul_sum,I.level_total hx] at he
  exact he

/-- Actual operator norm approximation, not an assumed energy budget. -/
theorem approximant_norm_error (n : ℕ) (hab : I.lo ≤ I.hi) :
    ‖I.proj.val*x*I.proj.val-I.approximant hx n‖ ≤ (I.hi-I.lo)/(2:ℝ)^n := by
  have hw : 0 ≤ (I.hi-I.lo)/(2:ℝ)^n := div_nonneg (sub_nonneg.mpr hab) (by positivity)
  calc ‖I.proj.val*x*I.proj.val-I.approximant hx n‖ ≤
      ‖(((I.hi-I.lo)/(2:ℝ)^n : ℝ) : ℂ) • I.proj.val‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg (I.approximant_error_upper hx n)
          (I.approximant_error_nonneg hx n)
    _ = ((I.hi-I.lo)/(2:ℝ)^n)*‖I.proj.val‖ := by
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hw]
    _ ≤ (I.hi-I.lo)/(2:ℝ)^n := by
      nlinarith only [mul_le_mul_of_nonneg_left I.proj.property.norm_le hw]

theorem exists_approximant (hab : I.lo ≤ I.hi) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ‖I.proj.val*x*I.proj.val-I.approximant hx n‖ < ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((I.hi-I.lo)/ε)
  have hnp : (n : ℝ)<(2:ℝ)^n := by exact_mod_cast (show n < 2^n from Nat.lt_two_pow_self)
  have hbound : (I.hi-I.lo)/(2:ℝ)^n < ε := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ)<2^n)]
    have hh := (div_lt_iff₀ hε).mp hn
    nlinarith [mul_lt_mul_of_pos_left hnp hε]
  exact ⟨n,(I.approximant_norm_error hx n hab).trans_lt hbound⟩

end SpectralInterval

/-- Start the construction with the actual operator norm bounds in any corner. -/
def initialSpectralInterval (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) : SpectralInterval x := by
  let oneP : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  have hp : p ≤ oneP := one_mul _
  have hs (r : ℝ) : algebraMap ℝ M.toStarSubalgebra r=(r : ℂ) • (1 : M.toStarSubalgebra) := by
    rw [Algebra.algebraMap_eq_smul_one,Complex.coe_smul]
  refine ⟨p,-‖x‖,‖x‖,?_,?_⟩
  · apply lower_bound_compress hp x (-‖x‖)
    have h := hx.neg_algebraMap_norm_le_self
    rw [hs] at h
    change 0 ≤ 1*x*1-((-‖x‖ : ℝ) : ℂ) • (1 : M.toStarSubalgebra)
    simpa only [one_mul,mul_one,Complex.ofReal_neg,neg_smul] using sub_nonneg.mpr h
  · apply upper_bound_compress hp x ‖x‖
    have h := hx.le_algebraMap_norm_self
    rw [hs] at h
    change 1*x*1-(‖x‖ : ℂ) • (1 : M.toStarSubalgebra) ≤ 0
    simpa only [one_mul,mul_one] using sub_nonpos.mpr h

/-- An actual finite orthogonal spectral approximation of a compressed
self-adjoint operator. All projections and coefficients are constructed. -/
theorem exists_finite_spectral_approximation (p : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition p) (c : Fin Q.size → ℝ),
      Q.pinch x=p.val*x*p.val ∧
      ‖p.val*x*p.val-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I := initialSpectralInterval p x hx
  have hI : I.lo ≤ I.hi := neg_le_self (norm_nonneg _)
  obtain ⟨n,hn⟩ := I.exists_approximant hx hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx n,fun i => (I.level hx n (e i)).lo,I.partition_pinch hx n,?_⟩
  have he := Equiv.sum_comp e (fun i => ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val)
  change ‖p.val*x*p.val-∑ i, ((I.level hx n (e i)).lo : ℂ) •
    (I.level hx n (e i)).proj.val‖ < ε
  rw [he]
  exact hn

end

/-! Constructed cuts preserve commutation with other operators. -/
section
open scoped CStarAlgebra
open UltrapowerBridge ContinuousLinearMap LinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralCommutationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralCommutationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralCommutationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

omit [CompleteSpace H] in
theorem kernel_invariant_of_commutes (x y : H →L[ℂ] H) (h : x*y=y*x) :
    x.ker ∈ Module.End.invtSubmodule y.toLinearMap := by
  intro ξ hξ
  change x (y ξ)=0
  have he := congrArg (fun t : H →L[ℂ] H => t ξ) h
  change x (y ξ)=y (x ξ) at he
  rw [he,show x ξ=0 from hξ,map_zero]

theorem kernelProjection_commutes (x y : M.toStarSubalgebra)
    (hxy : Commute x y) (hxys : Commute x (star y)) :
    Commute (kernelProjection x).val y := by
  let k := x.val.ker.starProjection
  have hk : IsIdempotentElem k.toLinearMap :=
    (isStarProjection_starProjection (U := x.val.ker)).isIdempotentElem.toLinearMap
  have h₁ := kernel_invariant_of_commutes x.val y.val (congrArg Subtype.val hxy.eq)
  have h₂ : x.val.ker ∈ Module.End.invtSubmodule y.val.adjoint.toLinearMap := by
    exact kernel_invariant_of_commutes x.val (star y).val (congrArg Subtype.val hxys.eq)
  have hc : Commute k.toLinearMap y.val.toLinearMap := by
    apply (LinearMap.IsIdempotentElem.commute_iff hk).mpr
    change k.range ∈ Module.End.invtSubmodule y.val.toLinearMap ∧
      k.ker ∈ Module.End.invtSubmodule y.val.toLinearMap
    rw [Submodule.range_starProjection,Submodule.ker_starProjection]
    exact ⟨h₁,ContinuousLinearMap.orthogonal_mem_invtSubmodule h₂⟩
  apply Subtype.ext
  ext ξ
  exact congrArg (fun t : H →ₗ[ℂ] H => t ξ) hc.eq

theorem positiveSupport_commutes_of_commutes (x y : M.toStarSubalgebra)
    (hxy : Commute x y) (hxys : Commute x (star y)) :
    Commute (positiveSupport x).val y := by
  have hpos := hxy.cfcₙ_real (fun t : ℝ => t⁺)
  have hposs := hxys.cfcₙ_real (fun t : ℝ => t⁺)
  change Commute x⁺ y at hpos
  change Commute x⁺ (star y) at hposs
  have hs : IsSelfAdjoint x⁺ := (CFC.posPart_nonneg x).isSelfAdjoint
  have hk := kernelProjection_commutes x⁺ y hpos hposs
  change Commute (1-(kernelProjection (star x⁺)).val) y
  rw [hs.star_eq]
  exact (Commute.one_left y).sub_left hk

end

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem selfAdjoint_commutes_star_right {x y : M.toStarSubalgebra}
    (hx : IsSelfAdjoint x) (hxy : Commute x y) : Commute x (star y) := by
  have h := congrArg star hxy.eq
  simp only [star_mul,hx.star_eq] at h
  exact h.symm

theorem positiveSupport_commutes_of_selfAdjoint {x y : M.toStarSubalgebra}
    (hx : IsSelfAdjoint x) (hxy : Commute x y) :
    Commute (positiveSupport x).val y :=
  positiveSupport_commutes_of_commutes x y hxy (selfAdjoint_commutes_star_right hx hxy)

theorem cornerSpectralCut_commutes_with (p : AlgebraProjection M) (x y : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (hxy : Commute x y) (hp : Commute p.val y) (t : ℝ) :
    Commute (cornerSpectralCut p x t).val y := by
  apply positiveSupport_commutes_of_selfAdjoint (cornerSpectralShift_selfAdjoint p x hx t)
  have hscalar : Commute ((t : ℂ) • p.val) y := by
    show ((t : ℂ) • p.val)*y=y*((t : ℂ) • p.val)
    rw [smul_mul_assoc,mul_smul_comm,hp.eq]
  exact ((hp.mul_left hxy).mul_left hp).sub_left hscalar

namespace SpectralInterval
variable {x y : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

theorem child_commutes (hxy : Commute x y) (hp : Commute I.proj.val y) (b : Bool) :
    Commute (I.child hx b).proj.val y := by
  have hq := cornerSpectralCut_commutes_with I.proj x y hx hxy hp I.midpoint
  cases b
  · exact hp.sub_left hq
  · exact hq

theorem level_commutes (hxy : Commute x y) (hp : Commute I.proj.val y) :
    ∀ n i, Commute (I.level hx n i).proj.val y
  | 0,_ => hp
  | n+1,i => (I.level hx n i.1).child_commutes hx hxy (level_commutes hxy hp n i.1) i.2

theorem partition_commutes (hxy : Commute x y) (hp : Commute I.proj.val y)
    (n : ℕ) (i : Fin (I.partition hx n).size) :
    Commute ((I.partition hx n).piece i).val y :=
  I.level_commutes hx hxy hp n _

end SpectralInterval

/-- The finite construction retains a prescribed commutation relation. -/
theorem exists_finite_spectral_approximation_commuting (p : AlgebraProjection M)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hxy : Commute x y)
    (hp : Commute p.val y) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition p) (c : Fin Q.size → ℝ),
      Q.pinch x=p.val*x*p.val ∧ (∀ i, Commute (Q.piece i).val y) ∧
      ‖p.val*x*p.val-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I := initialSpectralInterval p x hx
  have hI : I.lo ≤ I.hi := neg_le_self (norm_nonneg _)
  obtain ⟨n,hn⟩ := I.exists_approximant hx hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx n,fun i => (I.level hx n (e i)).lo,I.partition_pinch hx n,
    I.partition_commutes hx hxy hp n,?_⟩
  have he := Equiv.sum_comp e (fun i => ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val)
  change ‖p.val*x*p.val-∑ i, ((I.level hx n (e i)).lo : ℂ) •
    (I.level hx n (e i)).proj.val‖ < ε
  rw [he]
  exact hn

/-- One constructed partition preserves the whole displayed commutant,
not a separately selected partition for each test operator. -/
theorem exists_finite_spectral_approximation_preserving_commutant (p : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition p) (c : Fin Q.size → ℝ),
      Q.pinch x=p.val*x*p.val ∧
      (∀ y : M.toStarSubalgebra, Commute x y → Commute p.val y →
        ∀ i, Commute (Q.piece i).val y) ∧
      ‖p.val*x*p.val-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I := initialSpectralInterval p x hx
  have hI : I.lo ≤ I.hi := neg_le_self (norm_nonneg _)
  obtain ⟨n,hn⟩ := I.exists_approximant hx hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx n,fun i => (I.level hx n (e i)).lo,I.partition_pinch hx n,
    fun y hxy hp => I.partition_commutes hx hxy hp n,?_⟩
  have he := Equiv.sum_comp e (fun i => ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val)
  change ‖p.val*x*p.val-∑ i, ((I.level hx n (e i)).lo : ℂ) •
    (I.level hx n (e i)).proj.val‖ < ε
  rw [he]
  exact hn

end Generator.Tracial

end

end OAI
