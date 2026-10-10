import OAI.Analysis.IrrationalRotation.Model.NormalAffiliation
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

namespace OAI

noncomputable section
open scoped LinearPMap

namespace Invariant233.PositivePartialResolventAlternative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

def graphSum (H : E →ₗ.[ℂ] E) : H.graph →L[ℂ] E :=
  ((ContinuousLinearMap.fst ℂ E E) + (ContinuousLinearMap.snd ℂ E E)).comp
    H.graph.subtypeL

omit [CompleteSpace E] in
@[simp] theorem graphSum_apply (H : E →ₗ.[ℂ] E) (z : H.graph) :
    graphSum H z = z.val.1 + z.val.2 := rfl

omit [CompleteSpace E] in

theorem norm_coordinates_le (H : E →ₗ.[ℂ] E) (hpos : IsPositivePartial H)
    (x : H.domain) :
    ‖(x : E)‖ ≤ ‖(x : E) + H x‖ ∧ ‖H x‖ ≤ ‖(x : E) + H x‖ := by
  have heq := norm_add_sq (𝕜 := ℂ) (x : E) (H x)
  change ‖(x : E) + H x‖ ^ 2 = ‖(x : E)‖ ^ 2 +
    2 * (inner ℂ (x : E) (H x)).re + ‖H x‖ ^ 2 at heq
  have hp := hpos x
  constructor
  · nlinarith [sq_nonneg ‖H x‖, norm_nonneg (x : E), norm_nonneg ((x : E) + H x)]
  · nlinarith [sq_nonneg ‖(x : E)‖, norm_nonneg (H x), norm_nonneg ((x : E) + H x)]

omit [CompleteSpace E] in

theorem norm_le_graphSum (H : E →ₗ.[ℂ] E) (hpos : IsPositivePartial H)
    (z : H.graph) : ‖z‖ ≤ ‖graphSum H z‖ := by
  obtain ⟨x, hx, hHx⟩ := (H.mem_graph_iff).mp z.property
  have hz : z.val = ((x : E), H x) := Prod.ext hx.symm hHx.symm
  change ‖z.val‖ ≤ ‖z.val.1 + z.val.2‖
  rw [hz, Prod.norm_def]
  exact max_le (norm_coordinates_le H hpos x).1 (norm_coordinates_le H hpos x).2

theorem graphSum_injective_closedRange (H : E →ₗ.[ℂ] E)
    (hclosed : H.IsClosed) (hpos : IsPositivePartial H) :
    Function.Injective (graphSum H) ∧ IsClosed (Set.range (graphSum H)) := by
  let : CompleteSpace H.graph := hclosed.completeSpace_coe
  have ha : AntilipschitzWith 1 (graphSum H) :=
    (graphSum H).antilipschitz_of_bound (fun z => by
      simpa using norm_le_graphSum H hpos z)
  exact ⟨ha.injective, ha.isClosed_range (graphSum H).uniformContinuous⟩

theorem graphSum_orthogonal_eq_bot (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) :
    (graphSum H).rangeᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro y hy
  have hzero (x : H.domain) : inner ℂ y ((x : E) + H x) = 0 := by
    have hxy := Submodule.inner_left_of_mem_orthogonal
      (show (x : E) + H x ∈ (graphSum H).range from
        ⟨⟨((x : E), H x), H.mem_graph x⟩, rfl⟩) hy
    exact hxy
  have hid (x : H.domain) : inner ℂ (-y) (x : E) = inner ℂ y (H x) := by
    have hz := hzero x
    rw [inner_add_right] at hz
    rw [inner_neg_left]
    linear_combination -hz
  have hyAdj : y ∈ H.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨-y, hid⟩
  have hadj : H.adjoint ⟨y, hyAdj⟩ = -y :=
    LinearPMap.adjoint_apply_eq hH.dense_domain _ hid
  have heq : H.adjoint = H := LinearPMap.isSelfAdjoint_def.mp hH
  have hyD : y ∈ H.domain := by simpa only [heq] using hyAdj
  have hHy : H ⟨y, hyD⟩ = -y := by
    have hle : H.adjoint ≤ H := le_of_eq heq
    exact (hle.2 (show (⟨y, hyAdj⟩ : H.adjoint.domain).val =
      (⟨y, hyD⟩ : H.domain).val from rfl)).symm.trans hadj
  have hp := hpos ⟨y, hyD⟩
  rw [hHy, inner_neg_right] at hp
  have hnorm : (inner ℂ y y).re = ‖y‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) y
  simp only [Complex.neg_re, hnorm] at hp
  have hy0 : y = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg y])
  simpa only [hy0] using (Submodule.zero_mem (⊥ : Submodule ℂ E))

theorem graphSum_bijective (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) :
    Function.Bijective (graphSum H) := by
  obtain ⟨hinj, hc⟩ := graphSum_injective_closedRange H hH.isClosed hpos
  let : IsClosed ((graphSum H).range : Set E) := hc
  have ht : (graphSum H).range = ⊤ :=
    (Submodule.orthogonal_eq_bot_iff).mp (graphSum_orthogonal_eq_bot H hH hpos)
  exact ⟨hinj, LinearMap.range_eq_top.mp ht⟩

def graphInverse (H : E →ₗ.[ℂ] E) (hH : IsSelfAdjoint H)
    (hpos : IsPositivePartial H) : E →ₗ[ℂ] H.graph :=
  (LinearEquiv.ofBijective (graphSum H).toLinearMap
    (graphSum_bijective H hH hpos)).symm.toLinearMap

@[simp] theorem graphSum_graphInverse (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) (y : E) :
    graphSum H (graphInverse H hH hpos y) = y :=
  (LinearEquiv.ofBijective (graphSum H).toLinearMap
    (graphSum_bijective H hH hpos)).apply_symm_apply y

@[simp] theorem graphInverse_graphSum (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) (z : H.graph) :
    graphInverse H hH hpos (graphSum H z) = z :=
  (LinearEquiv.ofBijective (graphSum H).toLinearMap
    (graphSum_bijective H hH hpos)).symm_apply_apply z

def resolvent (H : E →ₗ.[ℂ] E) (hH : IsSelfAdjoint H)
    (hpos : IsPositivePartial H) : E →L[ℂ] E :=
  ((LinearMap.fst ℂ E E).comp (H.graph.subtype.comp (graphInverse H hH hpos))).mkContinuous 1
    (fun y => by
      change ‖(graphInverse H hH hpos y).val.1‖ ≤ 1 * ‖y‖
      rw [one_mul]
      exact (norm_fst_le _).trans ((norm_le_graphSum H hpos _).trans_eq
        (congrArg norm (graphSum_graphInverse H hH hpos y))))

@[simp] theorem resolvent_apply (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) (y : E) :
    resolvent H hH hpos y = (graphInverse H hH hpos y).val.1 := rfl

theorem resolvent_mem_domain (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) (y : E) :
    resolvent H hH hpos y ∈ H.domain :=
  LinearPMap.mem_domain_of_mem_graph (graphInverse H hH hpos y).property

theorem add_apply_resolvent (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) (y : E) :
    resolvent H hH hpos y + H ⟨resolvent H hH hpos y,
      resolvent_mem_domain H hH hpos y⟩ = y := by
  obtain ⟨x, hx, hHx⟩ := H.mem_graph_iff.mp (graphInverse H hH hpos y).property
  have hx' : x = ⟨resolvent H hH hpos y, resolvent_mem_domain H hH hpos y⟩ :=
    Subtype.ext hx
  have heq := graphSum_graphInverse H hH hpos y
  change (graphInverse H hH hpos y).val.1 + (graphInverse H hH hpos y).val.2 = y at heq
  rw [← hHx, hx'] at heq
  exact heq

theorem apply_resolvent (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) (y : E) :
    H ⟨resolvent H hH hpos y, resolvent_mem_domain H hH hpos y⟩ =
      y - resolvent H hH hpos y := by
  exact eq_sub_of_add_eq' (add_apply_resolvent H hH hpos y)

theorem resolvent_add_apply (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) (x : H.domain) :
    resolvent H hH hpos ((x : E) + H x) = (x : E) := by
  have h := graphInverse_graphSum H hH hpos ⟨((x : E), H x), H.mem_graph x⟩
  exact congrArg (fun z : H.graph => z.val.1) h

theorem norm_resolvent_le (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) :
    ‖resolvent H hH hpos‖ ≤ 1 := by
  apply (resolvent H hH hpos).opNorm_le_bound (by norm_num)
  intro y
  rw [one_mul]
  have hb := (norm_coordinates_le H hpos
    ⟨resolvent H hH hpos y, resolvent_mem_domain H hH hpos y⟩).1
  rwa [add_apply_resolvent] at hb

theorem range_resolvent (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) :
    (resolvent H hH hpos).range = H.domain := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact resolvent_mem_domain H hH hpos x
  · intro x hx
    exact ⟨x + H ⟨x, hx⟩, resolvent_add_apply H hH hpos ⟨x, hx⟩⟩

theorem resolvent_injective (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) :
    Function.Injective (resolvent H hH hpos) := by
  intro y z hyz
  have hd : (⟨resolvent H hH hpos y, resolvent_mem_domain H hH hpos y⟩ : H.domain) =
      ⟨resolvent H hH hpos z, resolvent_mem_domain H hH hpos z⟩ := Subtype.ext hyz
  calc
    y = resolvent H hH hpos y + H ⟨resolvent H hH hpos y,
      resolvent_mem_domain H hH hpos y⟩ := (add_apply_resolvent H hH hpos y).symm
    _ = resolvent H hH hpos z + H ⟨resolvent H hH hpos z,
      resolvent_mem_domain H hH hpos z⟩ := congrArg₂ (· + ·) hyz (congrArg H hd)
    _ = z := add_apply_resolvent H hH hpos z

theorem resolvent_denseRange (H : E →ₗ.[ℂ] E)
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) :
    DenseRange (resolvent H hH hpos) := by
  change Dense ((resolvent H hH hpos).range : Set E)
  rw [range_resolvent]
  exact hH.dense_domain

end Invariant233.PositivePartialResolventAlternative

end

end OAI
