import Mathlib
import OAI.Analysis.FreeWords.ProjectionChain
import OAI.Analysis.FreeWords.ProjectionSmall

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end KKFreeLiftFrontier

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

open Filter Topology

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance projectionSubdivisionPartialOrder₁ (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance projectionSubdivisionPreorder₁ (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance projectionSubdivisionLE₁ (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance projectionSubdivisionStarOrderedRing₁ (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport

open UniversalStrongKK Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance projectionSubdivisionPartialOrder₂ (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance projectionSubdivisionPreorder₂ (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance projectionSubdivisionLE₂ (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance projectionSubdivisionStarOrderedRing₂ (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

open UniversalStrongKK Filter Topology

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance projectionSubdivisionPartialOrder₃ (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance projectionSubdivisionPreorder₃ (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance projectionSubdivisionLE₃ (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance projectionSubdivisionStarOrderedRing₃ (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem exists_maximal_projection_trace (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (p : ConcreteAlgebra M) (hp : IsStarProjection p) (t : ℝ) (ht : 0 ≤ t) :
    ∃ q : {x : ConcreteAlgebra M // IsStarProjection x},
      Maximal (fun q : {x : ConcreteAlgebra M // IsStarProjection x} =>
        q.val ≤ p ∧ (τ.map q.val).re ≤ t) q := by
  let P := {x : ConcreteAlgebra M // IsStarProjection x}
  let S : Set P := {q | q.val ≤ p ∧ (τ.map q.val).re ≤ t}
  let z : P := ⟨0,IsStarProjection.zero _⟩
  have hz : z ∈ S := ⟨hp.nonneg,by simpa [z] using ht⟩
  obtain ⟨q,hzq,hq⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    let : Nonempty c := ⟨⟨y,hy⟩⟩
    let : IsDirectedOrder c := ⟨fun a b => by
      obtain ⟨k,hk,hak,hbk⟩ := hchain.directedOn a.val a.property b.val b.property
      exact ⟨⟨k,hk⟩,hak,hbk⟩⟩
    obtain ⟨v,hv,hfv,ω,hω,hlim⟩ := projection_directed_limit
      (fun i : c => i.val.val) (fun i => i.val.property) (fun _ _ hij => hij)
    have hvp : v ≤ p := by
      apply (hv.le_iff_mul_eq_left hp).mpr
      apply Subtype.ext
      have ht' := wot_mul_const hlim (p : H →L[ℂ] H)
      have he (i : c) : (i.val.val : H →L[ℂ] H)*(p : H →L[ℂ] H)=i.val.val :=
        congrArg Subtype.val ((i.val.property.le_iff_mul_eq_left hp).mp (hc i.property).1)
      simp only [he] at ht'
      exact congrArg ContinuousLinearMapWOT.toCLM (tendsto_nhds_unique ht' hlim)
    have htrace := trace_tendsto_bounded_wot τ (fun i : c => i.val.property.norm_le) hv.norm_le hlim
    have htr : (τ.map v).re ≤ t := le_of_tendsto
      (Complex.continuous_re.tendsto _ |>.comp htrace) (Eventually.of_forall fun i => (hc i.property).2)
    exact ⟨⟨v,hv⟩,⟨hvp,htr⟩,fun i hi => hfv ⟨i,hi⟩⟩) z hz
  exact ⟨q,hq⟩

theorem projection_with_trace (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hD : IsDiffuse M) (p : ConcreteAlgebra M) (hp : IsStarProjection p)
    (t : ℝ) (ht0 : 0 ≤ t) (htp : t ≤ (τ.map p).re) :
    ∃ q : ConcreteAlgebra M, IsStarProjection q ∧ q*p=q ∧ τ.map q=(t : ℂ) := by
  obtain ⟨Q,hQ⟩ := exists_maximal_projection_trace M τ p hp t ht0
  let q : ConcreteAlgebra M := Q.val
  have hq : IsStarProjection q := Q.property
  have hqp : q ≤ p := hQ.1.1
  have hqt : (τ.map q).re ≤ t := hQ.1.2
  have hτ : (τ.map q).re=t := by
    by_contra hne
    have hlt : (τ.map q).re<t := lt_of_le_of_ne hqt hne
    have hres : IsStarProjection (p-q) := (hq.le_iff_sub hp).mp hqp
    have hres0 : p-q ≠ 0 := by
      intro he
      have hpq := sub_eq_zero.mp he
      rw [hpq] at htp
      exact (not_lt_of_ge htp) hlt
    obtain ⟨r,hr,hr0,hrpq,htr⟩ := exists_small_projection τ hD hres hres0
      (t-(τ.map q).re) (sub_pos.mpr hlt)
    have hresq : (p-q)*q=0 := by
      rw [sub_mul,(hq.le_iff_mul_eq_right hp).mp hqp,hq.isIdempotentElem.eq,sub_self]
    have hrq : r*q=0 := by
      calc
        r*q = (r*(p-q))*q := by rw [(hr.le_iff_mul_eq_left hres).mp hrpq]
        _ = r*((p-q)*q) := mul_assoc _ _ _
        _ = 0 := by rw [hresq,mul_zero]
    have hqr : q*r=0 := by
      simpa only [star_mul,hr.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq,star_zero] using congrArg star hrq
    let Q' : {x : ConcreteAlgebra M // IsStarProjection x} := ⟨q+r,hq.add hr hqr⟩
    have hQ' : Q'.val ≤ p ∧ (τ.map Q'.val).re ≤ t := by
      constructor
      · change q+r ≤ p
        calc
          q+r ≤ q+(p-q) := by simpa only [add_comm] using add_le_add_left hrpq q
          _ = p := by abel
      · change (τ.map (q+r)).re ≤ t
        rw [map_add,Complex.add_re]
        linarith
    have hQQ' : Q ≤ Q' := le_add_of_nonneg_right hr.nonneg
    have heq := congrArg Subtype.val (hQ.eq_of_le hQ' hQQ')
    change q=q+r at heq
    exact hr0 (add_left_cancel (show q+r=q+0 by rw [← heq,add_zero]))
  refine ⟨q,hq,(hq.le_iff_mul_eq_left hp).mp hqp,?_⟩
  exact Complex.ext hτ (Complex.nonneg_iff.mp (trace_projection_nonneg τ hq)).2.symm

end

end KKProjectionSupport
end

end OAI
