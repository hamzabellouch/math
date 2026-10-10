import OAI.Analysis.IrrationalRotation.Model.NormalAffiliation
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

namespace OAI

noncomputable section
open scoped InnerProductSpace NNReal

namespace Invariant233.PositivePartialResolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private def graphSum (H : E →ₗ.[ℂ] E) : H.graph →L[ℂ] E :=
  ((ContinuousLinearMap.fst ℂ E E) + (ContinuousLinearMap.snd ℂ E E)).comp
    H.graph.subtypeL

private theorem graphSum_apply (H : E →ₗ.[ℂ] E) (z : H.graph) :
    graphSum H z = z.val.1 + z.val.2 := rfl

theorem norm_le_norm_add (H : E →ₗ.[ℂ] E) (hpos : IsPositivePartial H)
    (x : H.domain) :
    ‖(x : E)‖ ≤ ‖(x : E) + H x‖ ∧ ‖H x‖ ≤ ‖(x : E) + H x‖ := by
  have hs := norm_add_sq (𝕜 := ℂ) (x : E) (H x)
  change ‖(x : E) + H x‖ ^ 2 = ‖(x : E)‖ ^ 2 +
    2 * (inner ℂ (x : E) (H x)).re + ‖H x‖ ^ 2 at hs
  have hp := hpos x
  constructor
  · nlinarith [sq_nonneg ‖H x‖, norm_nonneg ((x : E) + H x), norm_nonneg (x : E)]
  · nlinarith [sq_nonneg ‖(x : E)‖, norm_nonneg ((x : E) + H x), norm_nonneg (H x)]

private theorem graphSum_bound (H : E →ₗ.[ℂ] E) (hpos : IsPositivePartial H)
    (z : H.graph) : ‖z‖ ≤ (1 : ℝ≥0) * ‖graphSum H z‖ := by
  obtain ⟨x, hx, hHx⟩ := (LinearPMap.mem_graph_iff H).mp z.property
  have hb := norm_le_norm_add H hpos x
  change max ‖z.val.1‖ ‖z.val.2‖ ≤ 1 * ‖z.val.1 + z.val.2‖
  rw [one_mul, ← hx, ← hHx]
  exact max_le hb.1 hb.2

variable [CompleteSpace E]

private theorem graphSum_range_orthogonal (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) :
    (graphSum H).rangeᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro y hy
  have heq : ∀ x : H.domain, inner ℂ (-y) (x : E) = inner ℂ y (H x) := by
    intro x
    have hz : inner ℂ y ((x : E) + H x) = 0 := by
      apply Submodule.inner_left_of_mem_orthogonal (K := (graphSum H).range) _ hy
      exact ⟨⟨((x : E), H x), (LinearPMap.mem_graph_iff H).mpr ⟨x, rfl, rfl⟩⟩, rfl⟩
    rw [inner_add_right] at hz
    rw [inner_neg_left]
    exact (neg_eq_iff_add_eq_zero).mpr hz
  have hyD : y ∈ H.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨-y, heq⟩
  have hyH : H.adjoint ⟨y, hyD⟩ = -y :=
    LinearPMap.adjoint_apply_eq hH.dense_domain ⟨y, hyD⟩ heq
  have hself : H.adjoint = H := LinearPMap.isSelfAdjoint_def.mp hH
  have hyD' : y ∈ H.domain := by simpa only [hself] using hyD
  have hyH' : H ⟨y, hyD'⟩ = -y := by
    have hg : (y, -y) ∈ H.graph := by
      rw [← hself]
      exact (LinearPMap.mem_graph_iff H.adjoint).mpr ⟨⟨y, hyD⟩, rfl, hyH⟩
    obtain ⟨x, hx, hHx⟩ := (LinearPMap.mem_graph_iff H).mp hg
    have hxy : x = ⟨y, hyD'⟩ := Subtype.ext hx
    exact hxy ▸ hHx
  have hb := (norm_le_norm_add H hpos ⟨y, hyD'⟩).1
  rw [hyH', add_neg_cancel, norm_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg y))

theorem exists_add_apply_eq (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) (y : E) :
    ∃ x : H.domain, (x : E) + H x = y := by
  let : IsClosed (H.graph : Set (E × E)) := hH.isClosed
  let : CompleteSpace H.graph := inferInstance
  have ha := (graphSum H).antilipschitz_of_bound (graphSum_bound H hpos)
  have hc : IsClosed (Set.range (graphSum H)) :=
    ha.isClosed_range (graphSum H).uniformContinuous
  let : IsClosed ((graphSum H).range : Set E) := hc
  have hr : (graphSum H).range = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp (graphSum_range_orthogonal H hH hpos)
  have hy : y ∈ (graphSum H).range := by rw [hr]; trivial
  obtain ⟨z, hz⟩ := hy
  obtain ⟨x, hx, hHx⟩ := (LinearPMap.mem_graph_iff H).mp z.property
  change z.val.1 + z.val.2 = y at hz
  exact ⟨x, by rw [hx, hHx]; exact hz⟩

theorem exists_resolvent (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) :
    ∃ R : E →L[ℂ] E,
      ‖R‖ ≤ 1 ∧
      (∀ y, R y ∈ H.domain) ∧
      (∀ y, ∀ hy : R y ∈ H.domain, H ⟨R y, hy⟩ = y - R y) ∧
      (∀ x : H.domain, R ((x : E) + H x) = (x : E)) ∧
      R.range = H.domain := by
  let : IsClosed (H.graph : Set (E × E)) := hH.isClosed
  let : CompleteSpace H.graph := inferInstance
  have ha := (graphSum H).antilipschitz_of_bound (graphSum_bound H hpos)
  have hi : Function.Injective (graphSum H) := ha.injective
  have hs : Function.Surjective (graphSum H) := by
    intro y
    obtain ⟨x, hx⟩ := exists_add_apply_eq H hH hpos y
    exact ⟨⟨((x : E), H x), (LinearPMap.mem_graph_iff H).mpr ⟨x, rfl, rfl⟩⟩, hx⟩
  let e : H.graph ≃L[ℂ] E := ContinuousLinearEquiv.ofBijective (graphSum H)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  let R : E →L[ℂ] E := (ContinuousLinearMap.fst ℂ E E).comp
    (H.graph.subtypeL.comp e.symm.toContinuousLinearMap)
  have hR (y : E) : R y = (e.symm y).val.1 := rfl
  have hsum (y : E) : (e.symm y).val.1 + (e.symm y).val.2 = y :=
    e.apply_symm_apply y
  have hgraph (y : E) : ∃ x : H.domain,
      (x : E) = R y ∧ H x = (e.symm y).val.2 := by
    exact (LinearPMap.mem_graph_iff H).mp (e.symm y).property
  have hD (y : E) : R y ∈ H.domain := by
    obtain ⟨x, hx, _⟩ := hgraph y
    exact hx ▸ x.property
  have hHR (y : E) (hy : R y ∈ H.domain) : H ⟨R y, hy⟩ = y - R y := by
    obtain ⟨x, hx, hHx⟩ := hgraph y
    have hxeq : x = ⟨R y, hy⟩ := Subtype.ext hx
    rw [← hxeq, hHx]
    have hh := hsum y
    rw [← hR] at hh
    exact (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans hh)
  have hRH (x : H.domain) : R ((x : E) + H x) = (x : E) := by
    let z : H.graph := ⟨((x : E), H x), (LinearPMap.mem_graph_iff H).mpr ⟨x, rfl, rfl⟩⟩
    have hz : e z = (x : E) + H x := rfl
    rw [← hz, hR, e.symm_apply_apply]
  refine ⟨R, ?_, hD, hHR, hRH, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro y
    have hh := (norm_le_norm_add H hpos ⟨R y, hD y⟩).1
    rw [hHR, add_sub_cancel] at hh
    simpa only [one_mul] using hh
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact hD z
    · intro hy
      exact ⟨y + H ⟨y, hy⟩, hRH ⟨y, hy⟩⟩

end Invariant233.PositivePartialResolvent

end

end OAI
