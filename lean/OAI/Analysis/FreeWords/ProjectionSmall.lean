import Mathlib
import OAI.Analysis.FreeWords.FactorCorners
import OAI.Analysis.FreeWords.TraceTransfer

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsDiffuse (M : VonNeumannAlgebra H) : Prop :=
  ∀ p : ConcreteAlgebra M, IsStarProjection p → p ≠ 0 →
    ∃ q : ConcreteAlgebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ q * p = q

end KKFreeLiftFrontier

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

open Filter Topology

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance projectionSmallPartialOrder (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance projectionSmallPreorder (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance projectionSmallLE (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance projectionSmallStarOrderedRing (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem trace_projection_nonneg {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    {p : ConcreteAlgebra M} (hp : IsStarProjection p) : 0 ≤ τ.map p := by
  have h := trace_square_nonneg τ p
  simpa only [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using h

theorem trace_projection_pos {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    {p : ConcreteAlgebra M} (hp : IsStarProjection p) (hp0 : p ≠ 0) : 0 < (τ.map p).re := by
  have hn := Complex.nonneg_iff.mp (trace_projection_nonneg τ hp)
  apply lt_of_le_of_ne hn.1
  intro he
  exact trace_projection_ne_zero τ hp hp0 (Complex.ext he.symm hn.2.symm)

theorem projection_half {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (hD : IsDiffuse M) {p : ConcreteAlgebra M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : ConcreteAlgebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≤ p ∧
      (τ.map q).re ≤ (τ.map p).re/2 := by
  obtain ⟨q,hq,hq0,hqp0,hqp⟩ := hD p hp hp0
  have hle : q ≤ p := (hq.le_iff_mul_eq_left hp).mpr hqp
  have hr : IsStarProjection (p-q) := (hq.le_iff_sub hp).mp hle
  have hr0 : p-q ≠ 0 := fun h => hqp0 (sub_eq_zero.mp h).symm
  by_cases hqsmall : (τ.map q).re ≤ (τ.map p).re/2
  · exact ⟨q,hq,hq0,hle,hqsmall⟩
  · refine ⟨p-q,hr,hr0,?_,?_⟩
    · exact sub_le_self _ hq.nonneg
    · simp only [map_sub,Complex.sub_re]
      linarith

theorem projection_trace_dyadic {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (hD : IsDiffuse M) {p : ConcreteAlgebra M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (n : ℕ) : ∃ q : ConcreteAlgebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≤ p ∧
      (τ.map q).re ≤ (τ.map p).re/(2:ℝ)^n := by
  induction n with
  | zero => exact ⟨p,hp,hp0,le_rfl,by simp⟩
  | succ n ih =>
    obtain ⟨q,hq,hq0,hqp,hτq⟩ := ih
    obtain ⟨r,hr,hr0,hrq,hτr⟩ := projection_half τ hD hq hq0
    refine ⟨r,hr,hr0,hrq.trans hqp,?_⟩
    calc
      (τ.map r).re ≤ (τ.map q).re/2 := hτr
      _ ≤ ((τ.map p).re/(2:ℝ)^n)/2 := div_le_div_of_nonneg_right hτq (by norm_num)
      _ = (τ.map p).re/(2:ℝ)^(n+1) := by rw [pow_succ,div_div]

theorem exists_small_projection {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (hD : IsDiffuse M) {p : ConcreteAlgebra M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ConcreteAlgebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≤ p ∧ (τ.map q).re < ε := by
  have ht : Tendsto (fun n : ℕ => (τ.map p).re/(2:ℝ)^n) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  obtain ⟨n,hn⟩ := (ht.eventually (eventually_lt_nhds hε)).exists
  obtain ⟨q,hq,hq0,hqp,hτq⟩ := projection_trace_dyadic τ hD hp hp0 n
  exact ⟨q,hq,hq0,hqp,hτq.trans_lt hn⟩

end

end KKProjectionSupport
end

end OAI
