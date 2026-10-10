import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import OAI.Analysis.FactorGeneration.ProjectionLimits
import OAI.Analysis.FactorGeneration.TracialInclusion

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem cornerTrace_add (x y : M.toStarSubalgebra) :
    τ.trace (x+y) = τ.trace x + τ.trace y := inner_add_right _ _ _

theorem trace_sub (x y : M.toStarSubalgebra) :
    τ.trace (x-y) = τ.trace x - τ.trace y := inner_sub_right _ _ _

theorem cornerTrace_smul (c : ℂ) (x : M.toStarSubalgebra) :
    τ.trace (c • x) = c * τ.trace x := inner_smul_right _ _ _

theorem norm_trace_mul_le (x y : M.toStarSubalgebra) :
    ‖τ.trace (x*y)‖ ≤ τ.norm₂ x * τ.norm₂ y := by
  have he := norm_inner_le_norm (𝕜 := ℂ)
    (((star x : M.toStarSubalgebra) : H →L[ℂ] H) τ.vector)
    ((y : H →L[ℂ] H) τ.vector)
  have hi : inner ℂ (((star x : M.toStarSubalgebra) : H →L[ℂ] H) τ.vector)
      ((y : H →L[ℂ] H) τ.vector) = τ.trace (x*y) := by
    change inner ℂ (star (x : H →L[ℂ] H) τ.vector) ((y : H →L[ℂ] H) τ.vector) = _
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
    rfl
  rw [hi] at he
  change ‖τ.trace (x*y)‖ ≤ τ.norm₂ (star x)*τ.norm₂ y at he
  simpa only [τ.norm₂_star] using he

/-- The scalar conditional expectation in pMp, expressed in ambient coordinates. -/
def cornerScalar (p : AlgebraProjection M) (x : M.toStarSubalgebra) : ℂ :=
  τ.trace (p.val*x*p.val) / τ.trace p.val

def cornerCentered (p : AlgebraProjection M) (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  p.val*x*p.val - cornerScalar τ p x • p.val

theorem cornerCentered_support (p : AlgebraProjection M) (x : M.toStarSubalgebra) :
    p.val * cornerCentered τ p x = cornerCentered τ p x ∧
    cornerCentered τ p x * p.val = cornerCentered τ p x := by
  constructor
  · simp [cornerCentered,mul_sub,← mul_assoc,p.property.isIdempotentElem.eq]
  · simp [cornerCentered,sub_mul,mul_assoc,p.property.isIdempotentElem.eq]

theorem cornerCentered_trace (p : AlgebraProjection M) (hp : p.val ≠ 0)
    (x : M.toStarSubalgebra) : τ.trace (cornerCentered τ p x) = 0 := by
  have hn : τ.trace p.val ≠ 0 := by
    intro h
    have hh := projection_trace_pos τ p.val p.property hp
    rw [h,Complex.zero_re] at hh
    exact (lt_irrefl _ hh)
  rw [cornerCentered,trace_sub,cornerTrace_smul,cornerScalar,div_mul_cancel₀ _ hn,sub_self]

theorem compress_cornerCentered {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) :
    q.val*cornerCentered τ p x*q.val = q.val*x*q.val-cornerScalar τ p x • q.val := by
  simp only [cornerCentered,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  have hl : p.val*q.val=q.val := hqp
  have hr := projection_mul_of_le hqp
  simp only [← mul_assoc,hr]
  simp only [mul_assoc,hl,q.property.isIdempotentElem.eq]

/-- A supported compression has the trace scale sqrt(trace(q)), even against
an arbitrary bounded ambient test operator. -/
theorem supported_trace_test_le (q : AlgebraProjection M) (x y : M.toStarSubalgebra)
    (hx : x*q.val=x) :
    ‖τ.trace (x*y)‖ ≤ τ.norm₂ x * (τ.norm₂ q.val * ‖y‖) := by
  calc ‖τ.trace (x*y)‖ = ‖τ.trace (x*(q.val*y))‖ := by rw [← mul_assoc,hx]
       _ ≤ τ.norm₂ x * τ.norm₂ (q.val*y) := norm_trace_mul_le τ _ _
       _ ≤ τ.norm₂ x * (τ.norm₂ q.val * ‖y‖) :=
         mul_le_mul_of_nonneg_left (τ.norm₂_mul_le_right _ _) (norm_nonneg _)

theorem compression_trace_test_le (q : AlgebraProjection M) (x y : M.toStarSubalgebra)
    (hy : ‖y‖ ≤ 1) :
    ‖τ.trace ((q.val*x*q.val)*y)‖ ≤ τ.norm₂ (q.val*x*q.val) * τ.norm₂ q.val := by
  have hx : (q.val*x*q.val)*q.val=q.val*x*q.val := by
    rw [mul_assoc,q.property.isIdempotentElem.eq]
  exact (supported_trace_test_le τ q _ y hx).trans
    (mul_le_mul_of_nonneg_left (by nlinarith [show 0 ≤ τ.norm₂ q.val from norm_nonneg _])
      (norm_nonneg _))

end

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance : CStarAlgebra M.toStarSubalgebra := {}
local instance : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (τ : TracialRepresentation M)

def traceAbs (x : M.toStarSubalgebra) : M.toStarSubalgebra := CFC.sqrt (star x*x)
def norm₁ (x : M.toStarSubalgebra) : ℝ := (τ.trace (traceAbs x)).re

theorem traceAbs_selfAdjoint (x : M.toStarSubalgebra) : IsSelfAdjoint (traceAbs x) :=
  (CFC.sqrt_nonneg _).isSelfAdjoint

theorem traceAbs_sq (x : M.toStarSubalgebra) : traceAbs x * traceAbs x = star x*x :=
  CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg x)

theorem traceAbs_norm₂ (x : M.toStarSubalgebra) : τ.norm₂ (traceAbs x) = τ.norm₂ x := by
  have h := congrArg Complex.re (τ.trace_star_mul (traceAbs x))
  rw [(traceAbs_selfAdjoint x).star_eq,traceAbs_sq,τ.trace_star_mul] at h
  simp only [← Complex.ofReal_pow,Complex.ofReal_re] at h
  nlinarith [show 0 ≤ τ.norm₂ x from norm_nonneg _,
    show 0 ≤ τ.norm₂ (traceAbs x) from norm_nonneg _]

theorem trace_nonneg_of_nonneg (a : M.toStarSubalgebra) (ha : 0 ≤ a) :
    0 ≤ (τ.trace a).re := by
  have hs := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have h := congrArg Complex.re (τ.trace_star_mul (CFC.sqrt a))
  rw [hs,CFC.sqrt_mul_sqrt_self a ha] at h
  rw [h]
  simp only [← Complex.ofReal_pow,Complex.ofReal_re]
  positivity

theorem norm₁_nonneg (x : M.toStarSubalgebra) : 0 ≤ norm₁ τ x :=
  trace_nonneg_of_nonneg τ _ (CFC.sqrt_nonneg _)

theorem norm₁_le_norm₂ (x : M.toStarSubalgebra) : norm₁ τ x ≤ τ.norm₂ x := by
  exact (Complex.re_le_norm _).trans ((τ.norm_trace_le_norm₂ _).trans_eq (traceAbs_norm₂ τ x))

/-- Right support passes to the positive square root without a polar decomposition. -/
theorem traceAbs_support (q : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : x*q.val=x) : traceAbs x*q.val=traceAbs x := by
  have he : star (traceAbs x*(1-q.val))*(traceAbs x*(1-q.val))=0 := by
    rw [star_mul,star_sub,star_one,q.property.isSelfAdjoint.star_eq,
      (traceAbs_selfAdjoint x).star_eq]
    calc (1-q.val)*traceAbs x*(traceAbs x*(1-q.val)) =
        (1-q.val)*(traceAbs x*traceAbs x)*(1-q.val) := by simp only [mul_assoc]
         _ = 0 := by
           rw [traceAbs_sq]
           simp only [mul_assoc,mul_sub,mul_one,hx,sub_self]
  have hz := (CStarRing.star_mul_self_eq_zero_iff _).mp he
  rw [mul_sub,mul_one,sub_eq_zero] at hz
  exact hz.symm

/-- The trace scale needed in corner local quantization. -/
theorem norm₁_le_support_norm₂ (q : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : x*q.val=x) : norm₁ τ x ≤ τ.norm₂ x * τ.norm₂ q.val := by
  calc norm₁ τ x ≤ ‖τ.trace (traceAbs x)‖ := Complex.re_le_norm _
       _ = ‖τ.trace (traceAbs x*q.val)‖ := by rw [traceAbs_support q x hx]
       _ ≤ τ.norm₂ (traceAbs x) * τ.norm₂ q.val := norm_trace_mul_le τ _ _
       _ = τ.norm₂ x * τ.norm₂ q.val := by rw [traceAbs_norm₂]

theorem compression_norm₁_le (q : AlgebraProjection M) (x : M.toStarSubalgebra) :
    norm₁ τ (q.val*x*q.val) ≤ τ.norm₂ (q.val*x*q.val)*τ.norm₂ q.val := by
  apply norm₁_le_support_norm₂
  rw [mul_assoc,q.property.isIdempotentElem.eq]

/-- A strict corner L2 estimate supplies the manuscript's actual L1 estimate. -/
theorem compression_norm₁_lt_of_norm₂ (q : AlgebraProjection M) (hq : q.val ≠ 0)
    (x : M.toStarSubalgebra) (ε : ℝ)
    (h : τ.norm₂ (q.val*x*q.val) < ε*τ.norm₂ q.val) :
    norm₁ τ (q.val*x*q.val) < ε*(τ.trace q.val).re := by
  have hp : 0 < τ.norm₂ q.val := lt_of_le_of_ne (norm_nonneg _)
    (fun h => hq ((τ.norm₂_eq_zero_iff q.val).mp h.symm))
  have he := projection_trace_sq τ q.val q.property
  calc norm₁ τ (q.val*x*q.val) ≤ τ.norm₂ (q.val*x*q.val)*τ.norm₂ q.val :=
         compression_norm₁_le τ q x
       _ < (ε*τ.norm₂ q.val)*τ.norm₂ q.val := mul_lt_mul_of_pos_right h hp
       _ = ε*(τ.trace q.val).re := by rw [he]; ring

end

/-! A finite compression-energy estimate yields a nonzero corner projection with simultaneous L1 control. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_small_energy_piece {I J : Type*} (s : Finset I) (F : Finset J)
    (t : I → ℝ) (a : I → J → ℝ) (ε : ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (ha : ∀ i ∈ s, ∀ j ∈ F, 0 ≤ a i j)
    (h : ∑ i ∈ s, ∑ j ∈ F, a i j < ε * ∑ i ∈ s, t i) :
    ∃ i ∈ s, 0 < t i ∧ ∀ j ∈ F, a i j < ε*t i := by
  classical
  have hex : ∃ i ∈ s, (∑ j ∈ F, a i j) < ε*t i := by
    by_contra hn
    push Not at hn
    have he := Finset.sum_le_sum hn
    rw [← Finset.mul_sum] at he
    exact (not_lt_of_ge he) h
  obtain ⟨i,hi,he⟩ := hex
  have htpos : 0 < t i := by
    by_contra hn
    have hz : t i=0 := le_antisymm (le_of_not_gt hn) (ht i hi)
    rw [hz,mul_zero] at he
    exact (not_lt_of_ge (Finset.sum_nonneg (ha i hi))) he
  refine ⟨i,hi,htpos,fun j hj => ?_⟩
  exact (Finset.single_le_sum (ha i hi) hj).trans_lt he

/-- The aggregate squared L2 budget has exactly the trace weighting required
for simultaneous strict L1 estimates on a nonzero subprojection. -/
theorem exists_corner_L1_of_partition_energy {I : Type*}
    (s : Finset I) (p : AlgebraProjection M) (q : I → AlgebraProjection M)
    (hq : ∀ i ∈ s, q i ≤ p) (F : Finset M.toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε)
    (henergy : ∑ i ∈ s, ∑ x ∈ F,
      τ.norm₂ ((q i).val*cornerCentered τ p x*(q i).val)^2 <
      ε^2 * ∑ i ∈ s, (τ.trace (q i).val).re) :
    ∃ r : AlgebraProjection M, r ≤ p ∧ r.val ≠ 0 ∧ (∃ i ∈ s, r=q i) ∧ ∀ x ∈ F,
      norm₁ τ (r.val*cornerCentered τ p x*r.val) < ε*(τ.trace r.val).re := by
  obtain ⟨i,hi,ht,he⟩ := exists_small_energy_piece s F
    (fun i => (τ.trace (q i).val).re)
    (fun i x => τ.norm₂ ((q i).val*cornerCentered τ p x*(q i).val)^2) (ε^2)
    (fun i hi => by rw [projection_trace_sq τ _ (q i).property]; positivity)
    (fun i hi x hx => sq_nonneg _) henergy
  have hn : (q i).val ≠ 0 := by
    intro hz
    have hzero : τ.trace (q i).val=0 := by rw [hz]; exact inner_zero_right _
    rw [hzero,Complex.zero_re] at ht
    exact (lt_irrefl _ ht)
  refine ⟨q i,hq i hi,hn,⟨i,hi,rfl⟩,fun x hx => ?_⟩
  apply compression_norm₁_lt_of_norm₂ τ (q i) hn
  have h := he x hx
  rw [projection_trace_sq τ _ (q i).property] at h
  have hnq : 0 ≤ τ.norm₂ (q i).val := norm_nonneg _
  have hnx : 0 ≤ τ.norm₂ ((q i).val*cornerCentered τ p x*(q i).val) := norm_nonneg _
  nlinarith [mul_nonneg hε.le hnq]

end

/-! The scalar trace estimate for a term with two supported patch letters.
It reduces to the actual compressed middle coefficient and keeps trace(q),
not trace(p), as the scale of the error. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace CornerUnitary

theorem norm₂_eq_support {q : AlgebraProjection M} (v : CornerUnitary q) :
    τ.norm₂ v.val=τ.norm₂ q.val := by
  have he := v.trace_norm_sq τ
  rw [projection_trace_sq τ _ q.property] at he
  nlinarith [show 0 ≤ τ.norm₂ v.val from norm_nonneg _,show 0 ≤ τ.norm₂ q.val from norm_nonneg _]

end CornerUnitary

theorem two_patch_trace_le (q : AlgebraProjection M) (v w : CornerUnitary q)
    (a x b : M.toStarSubalgebra) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖τ.trace (a*v.val*x*w.val*b)‖ ≤ τ.norm₂ (q.val*x*q.val)*τ.norm₂ q.val := by
  have he : a*v.val*x*w.val*b = (a*v.val)*(q.val*x*q.val)*(w.val*b) := by
    simp only [← mul_assoc]
    rw [mul_assoc a v.val q.val,v.mul_support]
    simp only [mul_assoc]
    rw [← mul_assoc q.val w.val b,w.support_mul]
  have hr : τ.trace ((a*v.val)*(q.val*x*q.val)*(w.val*b)) =
      τ.trace ((q.val*x*q.val)*(w.val*b*a*v.val)) := by
    rw [mul_assoc (a*v.val) (q.val*x*q.val) (w.val*b),τ.trace_mul_comm (a*v.val)]
    simp only [mul_assoc]
  have hnorm : ‖w.val*b*a‖ ≤ 1 := by
    have hw : ‖w.val*b‖ ≤ 1 := (norm_mul_le _ _).trans
      (by nlinarith [w.norm_le_one,norm_nonneg w.val,norm_nonneg b])
    exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (w.val*b),norm_nonneg a])
  rw [he,hr]
  have hn : τ.norm₂ (w.val*b*a*v.val) ≤ τ.norm₂ q.val := by
    exact ((τ.norm₂_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hnorm)).trans_eq
      (v.norm₂_eq_support τ)
  exact (norm_trace_mul_le τ _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))

/-- The middle compression may be corner-centered with respect to a larger
residual support. This is the scalar version of the multiple-patch estimate. -/
theorem two_patch_centered_trace_lt (p q : AlgebraProjection M) (hq : q.val ≠ 0)
    (v w : CornerUnitary q) (a x b : M.toStarSubalgebra) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (ε : ℝ) (h : τ.norm₂ (q.val*cornerCentered τ p x*q.val) < ε*τ.norm₂ q.val) :
    ‖τ.trace (a*v.val*cornerCentered τ p x*w.val*b)‖ < ε*(τ.trace q.val).re := by
  have hpos : 0 < τ.norm₂ q.val := lt_of_le_of_ne (norm_nonneg _)
    (fun hz => hq ((τ.norm₂_eq_zero_iff _).mp hz.symm))
  calc _ ≤ τ.norm₂ (q.val*cornerCentered τ p x*q.val)*τ.norm₂ q.val :=
         two_patch_trace_le τ q v w a _ b ha hb
       _ < (ε*τ.norm₂ q.val)*τ.norm₂ q.val := mul_lt_mul_of_pos_right h hpos
       _ = ε*(τ.trace q.val).re := by rw [projection_trace_sq τ _ q.property]; ring

end Generator.Tracial

end

end OAI
