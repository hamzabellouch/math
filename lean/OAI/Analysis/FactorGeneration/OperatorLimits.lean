import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Topology.Algebra.Algebra

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem base_norm_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

instance baseCompleteSpace (M : VonNeumannAlgebra H) : CompleteSpace M.toStarSubalgebra :=
  (base_norm_closed M).completeSpace_coe

instance baseNormedAlgebraRat (M : VonNeumannAlgebra H) : NormedAlgebra ℚ M.toStarSubalgebra :=
  .restrictScalars ℚ ℂ M.toStarSubalgebra

end

/-! Bounded operator families have weak operator ultralimits. This is proved
from Banach--Alaoglu and Riesz representation, not assumed as compactness. -/
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_weak_vector_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (v : ι → H) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) :
    ∃ z : H, ‖z‖ ≤ C ∧ ∀ y : H,
      Tendsto (fun i => inner ℂ y (v i)) (ω : Filter ι) (𝓝 (inner ℂ y z)) := by
  let f : ι → WeakDual ℂ H := fun i =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (v i))
  obtain ⟨d, hd, ht⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ H) C).ultrafilter_le_nhds
    (ω.map f) (by
      apply le_principal_iff.mpr
      change ∀ᶠ i in (ω : Filter ι), f i ∈ _
      exact Eventually.of_forall fun i => by
        simpa [f, Metric.mem_closedBall, dist_zero_right] using hv i)
  let z := (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual d)
  refine ⟨z, ?_, ?_⟩
  · have hd' : ‖WeakDual.toStrongDual d‖ ≤ C := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hd
    simpa only [z, LinearIsometryEquiv.norm_map] using hd'
  · intro y
    have he : Tendsto (fun i => inner ℂ (v i) y) (ω : Filter ι)
        (𝓝 (inner ℂ z y)) := by
      have h := (WeakBilin.eval_continuous _ y).continuousAt.tendsto.comp ht
      change Tendsto (fun i => inner ℂ (v i) y) (ω : Filter ι) (𝓝 (d y)) at h
      rw [show inner ℂ z y = d y from InnerProductSpace.toDual_symm_apply]
      exact h
    have hs := he.star
    change Tendsto (fun i => (starRingEnd ℂ) (inner ℂ (v i) y)) (ω : Filter ι)
      (𝓝 ((starRingEnd ℂ) (inner ℂ z y))) at hs
    simpa only [inner_conj_symm] using hs

theorem exists_weak_operator_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (a : ι → H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ C ∧ ∀ x y : H,
      Tendsto (fun i => inner ℂ y (a i x)) (ω : Filter ι) (𝓝 (inner ℂ y (T x))) := by
  have h (x : H) := exists_weak_vector_ultralimit ω (fun i => a i x) (C * ‖x‖)
    (fun i => (a i).le_of_opNorm_le (ha i) x)
  choose v hv ht using h
  have hadd (x z : H) : v (x+z) = v x + v z := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (x+z) y)
    simpa only [map_add, inner_add_right] using (ht x y).add (ht z y)
  have hsmul (c : ℂ) (x : H) : v (c • x) = c • v x := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (c • x) y)
    simpa only [map_smul, inner_smul_right] using (ht x y).const_mul c
  let T : H →L[ℂ] H := LinearMap.mkContinuous
    { toFun := v, map_add' := hadd, map_smul' := hsmul } C hv
  exact ⟨T, T.opNorm_le_bound hC hv, ht⟩

/-- The double-commutant property retains the weak limit in the actual algebra. -/
theorem weak_operator_limit_mem (M : VonNeumannAlgebra H)
    {ι : Type*} {l : Filter ι} [l.NeBot] (a : ι → M.toStarSubalgebra)
    (T : H →L[ℂ] H)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i : H →L[ℂ] H) x)) l
      (𝓝 (inner ℂ y (T x)))) : T ∈ M := by
  change T ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro S hS
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have he (i : ι) : inner ℂ y ((a i : H →L[ℂ] H) (S x)) =
      inner ℂ (star S y) ((a i : H →L[ℂ] H) x) := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (fun R : H →L[ℂ] H => inner ℂ y (R x)) (hS (a i) (a i).property)
  have hh := (ht (S x) y).congr he
  have heq := tendsto_nhds_unique hh (ht x (star S y))
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left, mul_apply_eq_comp] using heq.symm

/-! Operator-norm balls of an actual von Neumann algebra are compact for the
weak operator topology, using the previously constructed operator ultralimits. -/

def weakOperatorBall (M : VonNeumannAlgebra H) (C : ℝ) : Set (H →WOT[ℂ] H) :=
  {T | T.toCLM ∈ M ∧ ‖T.toCLM‖ ≤ C}

theorem weakOperatorBall_isCompact (M : VonNeumannAlgebra H) (C : ℝ) :
    IsCompact (weakOperatorBall M C) := by
  classical
  by_cases hC : 0 ≤ C
  · apply isCompact_iff_ultrafilter_le_nhds'.mpr
    intro ω hω
    let a : (H →WOT[ℂ] H) → M.toStarSubalgebra := fun T =>
      if h : T ∈ weakOperatorBall M C then ⟨T.toCLM,h.1⟩ else 0
    have ha (T : H →WOT[ℂ] H) : ‖a T‖ ≤ C := by
      dsimp [a]
      split_ifs with h
      · exact h.2
      · change ‖(0 : H →L[ℂ] H)‖ ≤ C
        simpa only [norm_zero] using hC
    obtain ⟨T,hT,ht⟩ := exists_weak_operator_ultralimit ω (fun U => (a U).val) C hC ha
    have hm := weak_operator_limit_mem M a T ht
    refine ⟨ContinuousLinearMapWOT.ofCLM T,⟨hm,hT⟩,?_⟩
    have hl : Tendsto (fun U => ContinuousLinearMapWOT.ofCLM (a U).val)
        (ω : Filter (H →WOT[ℂ] H)) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
      ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
    have he : (fun U => ContinuousLinearMapWOT.ofCLM (a U).val) =ᶠ[ω] id := by
      filter_upwards [show ∀ᶠ U in (ω : Filter (H →WOT[ℂ] H)),U ∈ weakOperatorBall M C from hω]
        with U hU
      simp only [a,dite_eq_left hU,ContinuousLinearMapWOT.ofCLM_toCLM,id_eq]
    exact hl.congr' he
  · have he : weakOperatorBall M C=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro T hT
      exact hC ((norm_nonneg _).trans hT.2)
    rw [he]
    exact isCompact_empty

theorem weakOperatorBall_isClosed (M : VonNeumannAlgebra H) (C : ℝ) :
    IsClosed (weakOperatorBall M C) := (weakOperatorBall_isCompact M C).isClosed

end Tracial

/-! Operator order bounds are closed in the weak operator topology. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem weakOperator_nonneg_isClosed :
    IsClosed {T : H →WOT[ℂ] H | 0 ≤ T.toCLM} := by
  have hi (x : H) : Continuous (fun T : H →WOT[ℂ] H => inner ℂ (T x) x) := by
    simpa only [Function.comp_def, id_eq, inner_conj_symm] using
      (Complex.continuous_conj.comp
        (ContinuousLinearMapWOT.continuous_inner_apply continuous_id x x))
  have he : {T : H →WOT[ℂ] H | 0 ≤ T.toCLM} =
      ⋂ x : H, {T : H →WOT[ℂ] H |
        ((inner ℂ (T x) x).re : ℂ) = inner ℂ (T x) x ∧ 0 ≤ (inner ℂ (T x) x).re} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, ContinuousLinearMap.nonneg_iff_isPositive,
      ContinuousLinearMap.isPositive_iff_complex]
    rfl
  rw [he]
  apply isClosed_iInter
  intro x
  exact (isClosed_eq (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (hi x)))
    (hi x)).inter (isClosed_le continuous_const (Complex.continuous_re.comp (hi x)))

theorem weakOperator_lowerBound_isClosed (a : H →L[ℂ] H) :
    IsClosed {T : H →WOT[ℂ] H | a ≤ T.toCLM} := by
  have h := (weakOperator_nonneg_isClosed (H := H)).preimage
    (continuous_id.sub (continuous_const (y := ContinuousLinearMapWOT.ofCLM a)))
  convert h using 1
  ext T
  change (a ≤ T.toCLM) ↔ 0 ≤ T.toCLM - a
  exact sub_nonneg.symm

theorem weakOperator_upperBound_isClosed (b : H →L[ℂ] H) :
    IsClosed {T : H →WOT[ℂ] H | T.toCLM ≤ b} := by
  have h := (weakOperator_nonneg_isClosed (H := H)).preimage
    ((continuous_const (y := ContinuousLinearMapWOT.ofCLM b)).sub continuous_id)
  convert h using 1
  ext T
  change (T.toCLM ≤ b) ↔ 0 ≤ b - T.toCLM
  exact sub_nonneg.symm

end Generator

end

end OAI
