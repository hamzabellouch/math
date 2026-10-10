import OAI.Analysis.KadisonSimilarity.Derivation.FiniteDerivationColumns
import Mathlib.Order.Filter.AtTopBot.Finset

namespace OAI

/-! Finite column implementers from an actual orthogonal decomposition into
reducing summands. The finite projections converge strongly by density. -/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology

variable {I : Type*} {K : I → Type*} {H : Type*}
  [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
  [∀ i, CompleteSpace (K i)]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Isometric summand inclusions with mutually orthogonal ranges and dense
linear span. The summands may have different Hilbert spaces. -/
structure OrthogonalSummandDecomposition (K : I → Type*)
    [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  inclusion : ∀ i, K i →ₗᵢ[ℂ] H
  orthogonal : ∀ i j, i ≠ j → ∀ x y,
    inner ℂ (inclusion i x) (inclusion j y) = 0
  dense_span : (Submodule.span ℂ (⋃ i, Set.range (inclusion i))).topologicalClosure = ⊤

namespace OrthogonalSummandDecomposition

/-- Construct the geometric decomposition from the operator form of
orthogonality of the inclusions. -/
def of_adjoint_orthogonal (U : ∀ i, K i →ₗᵢ[ℂ] H)
    (horth : ∀ i j, i ≠ j →
      (U i).toContinuousLinearMap.adjoint.comp (U j).toContinuousLinearMap = 0)
    (hdense : (Submodule.span ℂ (⋃ i, Set.range (U i))).topologicalClosure = ⊤) :
    OrthogonalSummandDecomposition K H where
  inclusion := U
  orthogonal i j hij x y := by
    change inner ℂ ((U i).toContinuousLinearMap x) ((U j).toContinuousLinearMap y) = 0
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have hz := congrArg (fun T : K j →L[ℂ] K i => T y) (horth i j hij)
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at hz
    rw [hz, inner_zero_right]
  dense_span := hdense

variable (U : OrthogonalSummandDecomposition K H)

def coordinate (i : I) : H →L[ℂ] K i := (U.inclusion i).toContinuousLinearMap.adjoint

/-- The projection onto any finite collection of summands. -/
def finiteProjection (F : Finset I) : H →L[ℂ] H :=
  ∑ i ∈ F, (U.inclusion i).toContinuousLinearMap.comp (U.coordinate i)

@[simp] theorem coordinate_inclusion_self (i : I) (x : K i) :
    U.coordinate i (U.inclusion i x) = x :=
  congrArg (fun T : K i →L[ℂ] K i => T x) (U.inclusion i).adjoint_comp_self

theorem coordinate_inclusion_ne {i j : I} (h : i ≠ j) (x : K j) :
    U.coordinate i (U.inclusion j x) = 0 := by
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((U.inclusion i).toContinuousLinearMap.adjoint (U.inclusion j x)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
  exact U.orthogonal i j h y x

@[simp] theorem finiteProjection_apply (F : Finset I) (x : H) :
    U.finiteProjection F x = ∑ i ∈ F, U.inclusion i (U.coordinate i x) := by
  simp [finiteProjection]

theorem coordinate_finiteProjection [DecidableEq I] (F : Finset I) (i : I) (x : H) :
    U.coordinate i (U.finiteProjection F x) =
      if i ∈ F then U.coordinate i x else 0 := by
  classical
  rw [finiteProjection_apply, map_sum]
  by_cases hi : i ∈ F
  · simp only [hi, ↓reduceIte]
    rw [Finset.sum_eq_single i]
    · exact U.coordinate_inclusion_self i _
    · intro j _ hji
      exact U.coordinate_inclusion_ne hji.symm _
    · exact fun hn => (hn hi).elim
  · simp only [hi, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro j hj
    apply U.coordinate_inclusion_ne
    exact fun hij => hi (hij ▸ hj)

theorem finiteProjection_idempotent (F : Finset I) :
    (U.finiteProjection F).comp (U.finiteProjection F) = U.finiteProjection F := by
  classical
  ext x
  simp only [ContinuousLinearMap.comp_apply, finiteProjection_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← finiteProjection_apply, coordinate_finiteProjection]
  simp only [hi, ↓reduceIte]

theorem finiteProjection_adjoint (F : Finset I) :
    (U.finiteProjection F).adjoint = U.finiteProjection F := by
  simp only [finiteProjection, map_sum, ContinuousLinearMap.adjoint_comp,
    coordinate, ContinuousLinearMap.adjoint_adjoint]

theorem norm_finiteProjection_le_one (F : Finset I) : ‖U.finiteProjection F‖ ≤ 1 := by
  apply IsStarProjection.norm_le
  constructor
  · change (U.finiteProjection F).comp (U.finiteProjection F) = U.finiteProjection F
    exact U.finiteProjection_idempotent F
  · change (U.finiteProjection F).adjoint = U.finiteProjection F
    exact U.finiteProjection_adjoint F

theorem finiteProjection_inclusion (F : Finset I) (i : I) (hi : i ∈ F) (x : K i) :
    U.finiteProjection F (U.inclusion i x) = U.inclusion i x := by
  classical
  rw [finiteProjection_apply, Finset.sum_eq_single i]
  · rw [coordinate_inclusion_self]
  · intro j _ hji
    rw [U.coordinate_inclusion_ne hji, map_zero]
  · exact fun hn => (hn hi).elim

/-- Every vector in the algebraic span is fixed by all sufficiently large
finite summand projections. -/
theorem finiteProjection_eventually_fixed (x : H)
    (hx : x ∈ Submodule.span ℂ (⋃ i, Set.range (U.inclusion i))) :
    ∃ F₀ : Finset I, ∀ F, F₀ ⊆ F → U.finiteProjection F x = x := by
  classical
  refine Submodule.span_induction (fun y hy => ?_) ?_
    (fun x y _ _ hx hy => ?_) (fun c x _ hx => ?_) hx
  · obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨{i}, fun F hF => U.finiteProjection_inclusion F i
      (hF (Finset.mem_singleton_self i)) x⟩
  · exact ⟨∅, fun _ _ => map_zero _⟩
  · obtain ⟨Fx, hx⟩ := hx
    obtain ⟨Fy, hy⟩ := hy
    exact ⟨Fx ∪ Fy, fun F hF => by
      rw [map_add, hx F ((Finset.subset_union_left).trans hF),
        hy F ((Finset.subset_union_right).trans hF)]⟩
  · obtain ⟨Fx, hx⟩ := hx
    exact ⟨Fx, fun F hF => by rw [map_smul, hx F hF]⟩

/-- Finite orthogonal sums converge strongly to the identity on the completed
space; only the dense linear span is used. -/
theorem finiteProjection_tendsto (x : H) :
    Tendsto (fun F : Finset I => U.finiteProjection F x) atTop (𝓝 x) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hx : x ∈ closure (Submodule.span ℂ (⋃ i, Set.range (U.inclusion i)) : Set H) := by
    change x ∈ (Submodule.span ℂ (⋃ i, Set.range (U.inclusion i))).topologicalClosure
    rw [U.dense_span]
    trivial
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨F₀, hF₀⟩ := U.finiteProjection_eventually_fixed y hy
  filter_upwards [eventually_ge_atTop F₀] with F hF
  have hfix := hF₀ F hF
  have hnorm : ‖U.finiteProjection F (x - y)‖ ≤ ‖x - y‖ := by
    calc
      _ ≤ ‖U.finiteProjection F‖ * ‖x - y‖ := (U.finiteProjection F).le_opNorm _
      _ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right (U.norm_finiteProjection_le_one F)
        (norm_nonneg _)
      _ = _ := one_mul _
  rw [dist_eq_norm]
  calc
    ‖U.finiteProjection F x - x‖ = ‖U.finiteProjection F (x - y) + (y - x)‖ := by
      rw [map_sub, hfix]
      congr 1
      abel
    _ ≤ ‖U.finiteProjection F (x - y)‖ + ‖y - x‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + ‖y - x‖ := add_le_add hnorm le_rfl
    _ < ε := by
      rw [norm_sub_rev y x]
      rw [dist_eq_norm] at hxy
      linarith

end OrthogonalSummandDecomposition

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Actual finite-column implementers obtained from implemented restrictions
to the summands. Cyclicity is used to obtain the local implementers, not in
their assembly. -/
def finiteColumnImplementers_of_summands
    (U : OrthogonalSummandDecomposition K H)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (σi : ∀ i, A →⋆ₐ[ℂ] (K i →L[ℂ] K i))
    (δ : A →L[ℂ] (H →L[ℂ] H)) (V : ∀ i, K i →L[ℂ] H)
    (hσ : ∀ i a, (σ a).comp (U.inclusion i).toContinuousLinearMap =
      (U.inclusion i).toContinuousLinearMap.comp (σi i a))
    (hV : ∀ i a, (δ a).comp (U.inclusion i).toContinuousLinearMap =
      (V i).comp (σi i a) - (σ a).comp (V i)) :
    FiniteColumnImplementers σ δ (atTop : Filter (Finset I)) where
  projection := U.finiteProjection
  implementer F := ∑ i ∈ F, (V i).comp (U.coordinate i)
  projection_norm := U.norm_finiteProjection_le_one
  projection_tendsto := U.finiteProjection_tendsto
  commutator_eq F a := by
    have hc (i : I) : (U.coordinate i).comp (σ a) = (σi i a).comp (U.coordinate i) := by
      have h := congrArg ContinuousLinearMap.adjoint (hσ i (star a))
      simpa only [ContinuousLinearMap.adjoint_comp, map_star,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint,
        OrthogonalSummandDecomposition.coordinate] using h
    apply ContinuousLinearMap.ext
    intro x
    simp only [commutator, sub_apply, mul_apply_eq_comp,
      ContinuousLinearMap.comp_apply, sum_apply, map_sum,
      OrthogonalSummandDecomposition.finiteProjection_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi := congrArg (fun T : K i →L[ℂ] H => T (U.coordinate i x)) (hV i a)
    have hci := congrArg (fun T : H →L[ℂ] K i => T x) (hc i)
    simp only [ContinuousLinearMap.comp_apply, sub_apply] at hi hci
    rw [hci]
    exact hi.symm

/-- The uniform commutator estimate bounds a derivation on a dense
orthogonal family of implemented reducing summands. -/
theorem derivation_completeBound_of_implemented_summands
    (U : OrthogonalSummandDecomposition K H)
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (σi : ∀ i, A →⋆ₐ[ℂ] (K i →L[ℂ] K i))
    (δ : A →L[ℂ] (H →L[ℂ] H)) (V : ∀ i, K i →L[ℂ] H)
    (hσ : ∀ i a, (σ a).comp (U.inclusion i).toContinuousLinearMap =
      (U.inclusion i).toContinuousLinearMap.comp (σi i a))
    (hV : ∀ i a, (δ a).comp (U.inclusion i).toContinuousLinearMap =
      (V i).comp (σi i a) - (σ a).comp (V i))
    (P : VonNeumannAlgebra H) (hP : ∀ a, σ a ∈ P)
    (kaplansky : ScalarKaplanskyClosure σ P)
    {C : ℝ} (hC : 0 ≤ C) (estimate : CommutatorEstimate P C) :
    CompleteBound δ (C * ‖δ‖) :=
  derivation_completeBound_of_finite_columns σ δ P hP kaplansky
    (finiteColumnImplementers_of_summands U σ σi δ V hσ hV) hC estimate

end KadisonSimilarity

end

end OAI
