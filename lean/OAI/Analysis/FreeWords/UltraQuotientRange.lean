import Mathlib
import OAI.Analysis.FreeWords.SpectralClip

namespace OAI

noncomputable section

namespace KKUltraTrace

open scoped ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] KKUltraTrace.seqOrder

attribute [local instance] KKUltraTrace.seqSOR

open scoped InnerProductSpace

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] KKUltraTrace._seqOrder

attribute [local instance] KKUltraTrace._seqSOR

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder BoundedContinuousFunction

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem starHom_controlled_lift (φ : A →⋆ₐ[ℂ] B) (x : A) {b : ℝ}
    (hb : 0 < b) (hx : ‖φ x‖ ≤ b) :
    ∃ y : A, φ y = φ x ∧ ‖y‖ ≤ b := by
  refine ⟨spectralClip b x, ?_, norm_spectralClip_le hb x⟩
  rw [map_spectralClip φ hb, spectralClip_eq_self hb _ hx]

theorem starHom_image_closed (φ : A →⋆ₐ[ℂ] B) : IsClosed (Set.range φ) := by
  let f : A →L[ℂ] B := ⟨φ.toAlgHom.toLinearMap, by change Continuous φ; fun_prop⟩
  let K : Submodule ℂ A := f.ker
  let : IsClosed (K : Set A) := f.isClosed_ker
  let q : A ⧸ K →L[ℂ] B := K.liftQL f le_rfl
  have hbound : ∀ a : A ⧸ K, ‖a‖ ≤ ‖q a‖ := by
    intro a
    induction a using Submodule.Quotient.induction_on K with
    | H x =>
      change ‖(Submodule.Quotient.mk x : A ⧸ K)‖ ≤ ‖φ x‖
      apply le_of_forall_pos_le_add
      intro ε hε
      have hb : 0 < ‖φ x‖ + ε := add_pos_of_nonneg_of_pos (norm_nonneg _) hε
      obtain ⟨y, hy, hyn⟩ := starHom_controlled_lift φ x hb (le_add_of_nonneg_right hε.le)
      have heq : (Submodule.Quotient.mk x : A ⧸ K) = Submodule.Quotient.mk y := by
        apply (Submodule.Quotient.eq K).mpr
        change φ (x - y) = 0
        rw [map_sub, hy, sub_self]
      rw [heq]
      exact (Submodule.Quotient.norm_mk_le K y).trans hyn
  have hanti : AntilipschitzWith 1 q :=
    q.antilipschitz_of_bound (by simpa only [NNReal.coe_one, one_mul] using hbound)
  have heq : Set.range q = Set.range φ := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      induction a using Submodule.Quotient.induction_on K with
      | H x => exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  rw [← heq]
  exact hanti.isClosed_range q.uniformContinuous

local instance : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (ℕ →ᵇ A) := CStarAlgebra.spectralOrderedRing _

theorem ultra_gns_image_closed (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) :
    IsClosed (Set.range (ultraTrace τ ω).gnsStarAlgHom) := by
  exact starHom_image_closed _

end

end KKUltraTrace
end

end OAI
