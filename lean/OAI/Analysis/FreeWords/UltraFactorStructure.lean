import Mathlib
import OAI.Analysis.FreeWords.FactorVarianceStructure
import OAI.Analysis.FreeWords.UltraExpectation
import OAI.Analysis.FreeWords.UnitaryLift

namespace OAI

noncomputable section

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance ultraFactorStructureBoundedOrder : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _

local instance ultraFactorStructureBoundedSOR : StarOrderedRing (ℕ →ᵇ A) := CStarAlgebra.spectralOrderedRing _

theorem gnsUltra_center_scalar_of_witness (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y) = τ (y*x))
    (hw : ∀ x : A, ∃ u : unitary A,
      ‖gnsVector τ (x - τ x • 1)‖ ≤ 2*‖gnsVector τ (x*(u:A)-(u:A)*x)‖)
    (ω : Ultrafilter ℕ) (x : ℕ →ᵇ A)
    (hx : ∀ y : ℕ →ᵇ A,
      Commute ((ultraTrace τ ω).gnsStarAlgHom x) ((ultraTrace τ ω).gnsStarAlgHom y)) :
    (ultraTrace τ ω).gnsStarAlgHom x = (ultraTrace τ ω x) • 1 := by
  choose u hu using (fun j => hw (x j))
  let y : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun j => (u j : A)) continuous_of_discreteTopology ‖(1 : A)‖
    (fun j => by simpa only [mul_one] using (CStarRing.norm_coe_unitary_mul (u j) (1 : A)).le)
  let w := x*y-y*x
  have hzero : (ultraTrace τ ω).gnsStarAlgHom w = 0 := by
    dsimp [w]
    rw [map_sub, map_mul, map_mul, (hx y).eq, sub_self]
  have hwτ := (tracial_gns_zero _ (ultraTrace_tracial τ ω htr) w).mp hzero
  have hwlim : Tendsto (fun j => ‖gnsVector τ (w j)‖) (ω : Filter ℕ) (𝓝 0) := by
    simpa only [hwτ, Complex.zero_re, Real.sqrt_zero] using tendsto_gnsVector_norm τ ω w
  let c := ultraTrace τ ω x
  let v : ℕ →ᵇ A := x - c • 1
  have hbound (j : ℕ) : ‖gnsVector τ (v j)‖ ≤
      2*‖gnsVector τ (w j)‖ + ‖τ (x j)-c‖ * ‖gnsVector τ 1‖ := by
    have hid : v j = (x j - τ (x j) • 1) + (τ (x j)-c) • 1 := by
      change x j - c • 1 = _
      rw [sub_smul]
      abel
    rw [hid, map_add]
    apply (norm_add_le _ _).trans
    rw [map_smul, norm_smul]
    exact add_le_add (hu j) le_rfl
  have hlim : Tendsto (fun j => ‖gnsVector τ (v j)‖) (ω : Filter ℕ) (𝓝 0) := by
    have hc : Tendsto (fun j => ‖τ (x j)-c‖) (ω : Filter ℕ) (𝓝 0) := by
      have ht : Tendsto (fun j => τ (x j)) (ω : Filter ℕ) (𝓝 c) :=
        tendsto_ultraTraceValue τ ω x
      simpa only [sub_self, norm_zero] using (ht.sub_const c).norm
    have hr : Tendsto (fun j => 2*‖gnsVector τ (w j)‖ + ‖τ (x j)-c‖ * ‖gnsVector τ 1‖)
        (ω : Filter ℕ) (𝓝 0) := by
      simpa only [mul_zero, zero_mul, zero_add] using
        (hwlim.const_mul 2).add (hc.mul_const ‖gnsVector τ 1‖)
    exact squeeze_zero (fun j => norm_nonneg _) hbound hr
  have hv := gnsStarAlgHom_zero_of_gnsNorm_tendsto_zero τ htr ω v hlim
  change (ultraTrace τ ω).gnsStarAlgHom (x-c•1) = 0 at hv
  rw [map_sub, map_smul, map_one, sub_eq_zero] at hv
  exact hv

end

end KKFactorSupport

namespace KKFactorSupport

section

variable {A B C : Type*} [Ring A] [Ring B] [Ring C]
  [StarRing A] [StarRing B] [StarRing C]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]

theorem center_scalar_descend (f : A →⋆ₐ[ℂ] B) (g : B →⋆ₐ[ℂ] C)
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : ∀ a : A, (∀ b : A, Commute (g (f a)) (g (f b))) →
      ∃ c : ℂ, g (f a) = c • 1)
    (x : B) (hx : ∀ y : B, Commute x y) : ∃ c : ℂ, x = c • 1 := by
  obtain ⟨a, ha⟩ := hf x
  have hh : ∀ b, Commute (g (f a)) (g (f b)) := by
    intro b
    rw [ha]
    exact (hx (f b)).map g
  obtain ⟨c, hc⟩ := h a hh
  refine ⟨c, hg ?_⟩
  simpa only [ha, map_smul, map_one] using hc

end

end KKFactorSupport

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance ultraFactorStructureConcreteOrder (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance ultraFactorStructureConcretePreorder (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance ultraFactorStructureConcreteLE (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance ultraFactorStructureConcreteSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

local instance ultraFactorStructureSeqOrder (M : VonNeumannAlgebra H) : PartialOrder (ℕ →ᵇ ConcreteAlgebra M) := seqOrder M

local instance ultraFactorStructureSeqPreorder (M : VonNeumannAlgebra H) : Preorder (ℕ →ᵇ ConcreteAlgebra M) := (seqOrder M).toPreorder

local instance ultraFactorStructureSeqLE (M : VonNeumannAlgebra H) : LE (ℕ →ᵇ ConcreteAlgebra M) := (seqOrder M).toLE

local instance ultraFactorStructureSeqSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ℕ →ᵇ ConcreteAlgebra M) := seqSOR M

theorem ultraAlgebra_center_scalar {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (hM : KKFreeLiftFrontier.IsFactor M) (ω : Ultrafilter ℕ)
    (x : ultraAlgebra τ ω) (hx : ∀ y : ultraAlgebra τ ω, Commute x y) :
    ∃ c : ℂ, x = c • 1 := by
  apply center_scalar_descend (ultraProjection τ ω)
    (gnsQuotient (ultraTrace (tracePositive τ) ω)).subtype
    (ultraProjection_surjective τ ω) Subtype.val_injective _ x hx
  intro s hs
  have hw : ∀ a : ConcreteAlgebra M, ∃ u : unitary (ConcreteAlgebra M),
      ‖gnsVector (tracePositive τ) (a - (tracePositive τ) a • 1)‖ ≤
        2 * ‖gnsVector (tracePositive τ) (a * (u : ConcreteAlgebra M) - (u : ConcreteAlgebra M) * a)‖ := by
    intro a
    exact factor_commutator_witness τ hM a
  exact ⟨ultraTrace (tracePositive τ) ω s,
    gnsUltra_center_scalar_of_witness (tracePositive τ)
      (tracePositive_tracial τ) hw ω s hs⟩

end

end KKFactorSupport
end

end OAI
