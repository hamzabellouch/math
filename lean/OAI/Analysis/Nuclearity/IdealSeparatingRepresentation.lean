import OAI.Analysis.Nuclearity.UnitalIdealQuotient
import OAI.Analysis.WeakInfiniteness.TensorFoundations
import OAI.Analysis.JiangSu.Excision.PureStateNorming
import OAI.Analysis.JiangSu.Excision.PureGNSCommutant

namespace OAI

/-! A closed ideal and an element outside it are separated by an actual
irreducible representation. This is the first representation step of
Tomiyama's product-state separation argument. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace

namespace WeakPureInfiniteness

universe u
variable {E : Type u} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

theorem exists_pure_state_gns_detecting (x : E) (hx : x ≠ 0) :
    ∃ (f : E →ₚ[ℂ] ℂ) (hf : f 1 = 1),
      PureStateExcision.ofPositiveState f hf ∈
        (PureStateExcision.realStateCarrier (A := E)).extremePoints ℝ ∧
      f.gnsStarAlgHom x ≠ 0 := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  obtain ⟨f, hf, hp, hfx⟩ := PureStateExcision.exists_pure_positive_state_norming
    (star x * x) (star_mul_self_nonneg x)
  refine ⟨f, hf, hp, ?_⟩
  intro hz
  have hzero : f (star x * x) = 0 := by
    rw [← Pureness.stateGNS_vector_value f (star x * x), map_mul, map_star, hz]
    simp only [star_zero, zero_mul, zero_apply, inner_zero_right]
  rw [hfx, Complex.ofReal_eq_zero, CStarRing.norm_star_mul_self] at hzero
  exact hx (norm_eq_zero.mp (mul_self_eq_zero.mp hzero))

omit [PartialOrder E] [StarOrderedRing E] in
theorem exists_ideal_separating_irreducible
    (J : NonunitalClosedIdeal.Ideal E) (x : E) (hx : x ∉ J.module) :
    ∃ H : ComplexHilbert.{u}, ∃ π : E →⋆ₐ[ℂ] (H →L[ℂ] H),
      (∀ a ∈ J.module, π a = 0) ∧ π x ≠ 0 ∧
      ∀ T : H →L[ℂ] H, (∀ a, Commute T (π a)) → ∃ c : ℂ, T = c • 1 := by
  let Q := NonunitalClosedIdeal.QuotientAlgebra J
  let _ : CStarAlgebra Q := unitalIdealQuotientStructure J
  let _ : PartialOrder Q := CStarAlgebra.spectralOrder Q
  let _ : StarOrderedRing Q := CStarAlgebra.spectralOrderedRing Q
  let q : E →⋆ₐ[ℂ] Q := UnitalIdealQuotient.quotientHom J
  have hqx : q x ≠ 0 := by
    exact fun h => hx ((UnitalIdealQuotient.quotientHom_eq_zero_iff J x).mp h)
  obtain ⟨f, hf, hp, hfx⟩ := exists_pure_state_gns_detecting (q x) hqx
  let H : ComplexHilbert.{u} := ⟨f.GNS⟩
  let π : E →⋆ₐ[ℂ] (H →L[ℂ] H) := f.gnsStarAlgHom.comp q
  refine ⟨H, π, ?_, hfx, ?_⟩
  · intro a ha
    change f.gnsStarAlgHom (q a) = 0
    rw [(UnitalIdealQuotient.quotientHom_eq_zero_iff J a).mpr ha, map_zero]
  · intro T hT
    apply PureStateExcision.pure_gns_scalar_commutant f hf hp T
    intro a
    obtain ⟨b, hb⟩ := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective J a
    exact hb ▸ hT b

end WeakPureInfiniteness

end

end OAI
