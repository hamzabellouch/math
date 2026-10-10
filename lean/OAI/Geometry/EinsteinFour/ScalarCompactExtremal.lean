import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

namespace OAI

/-! The Hilbert-space extremal argument used for the scalar Sobolev
quotient. Compactness provides a convergent image sequence; the
parallelogram identity forces an extremizing sequence itself to converge. -/

namespace PositiveEinsteinFour.Geometry

open Filter Set
open scoped Topology

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_extremizing_sequence_cauchy (T : H →L[ℝ] E) (hT : 0 < ‖T‖)
    (u : ℕ → H) (hu : ∀ n, ‖u n‖ ≤ 1) (y : E)
    (hlim : Tendsto (fun n => T (u n)) atTop (𝓝 y)) (hy : ‖y‖ = ‖T‖) :
    CauchySeq u := by
  have hfst : Tendsto (fun nm : ℕ × ℕ => T (u nm.1)) atTop (𝓝 y) := by
    rw [← prod_atTop_atTop_eq]
    exact hlim.comp tendsto_fst
  have hsnd : Tendsto (fun nm : ℕ × ℕ => T (u nm.2)) atTop (𝓝 y) := by
    rw [← prod_atTop_atTop_eq]
    exact hlim.comp tendsto_snd
  have hsum : Tendsto (fun nm : ℕ × ℕ => ‖T (u nm.1 + u nm.2)‖ / ‖T‖)
      atTop (𝓝 2) := by
    have h := (hfst.add hsnd).norm.div_const ‖T‖
    have hv : ‖y + y‖ / ‖T‖ = 2 := by
      rw [← two_smul ℝ y, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hy]
      field_simp
    simpa only [map_add, hv] using h
  have hbound (nm : ℕ × ℕ) :
      ‖u nm.1 - u nm.2‖ ^ 2 ≤ 4 - (‖T (u nm.1 + u nm.2)‖ / ‖T‖) ^ 2 := by
    have hm : ‖T (u nm.1 + u nm.2)‖ / ‖T‖ ≤ ‖u nm.1 + u nm.2‖ :=
      (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using T.le_opNorm (u nm.1 + u nm.2))
    have hm2 := (sq_le_sq₀ (div_nonneg (norm_nonneg _) hT.le) (norm_nonneg _)).mpr hm
    have h1 := (sq_le_sq₀ (norm_nonneg (u nm.1)) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hu nm.1)
    have h2 := (sq_le_sq₀ (norm_nonneg (u nm.2)) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hu nm.2)
    have hpar := parallelogram_law_with_norm ℝ (u nm.1) (u nm.2)
    nlinarith
  have hzero : Tendsto (fun nm : ℕ × ℕ => ‖u nm.1 - u nm.2‖ ^ 2)
      atTop (𝓝 0) := by
    have hb := (tendsto_const_nhds (x := (4 : ℝ))).sub (hsum.pow 2)
    norm_num at hb
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun nm => sq_nonneg _) (fun nm => by simpa only [map_add] using hbound nm)
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hzero
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero, dist_eq_norm] using hnorm

/-- A nonzero compact scalar Sobolev operator from a complete Hilbert
space attains its norm on a unit vector. -/
theorem scalar_compact_operator_extremal [CompleteSpace H] (T : H →L[ℝ] E)
    (hcompact : IsCompactOperator T) (hT : 0 < ‖T‖) :
    ∃ u : H, ‖u‖ = 1 ∧ ‖T u‖ = ‖T‖ := by
  have hx (n : ℕ) : ∃ x : H, ‖x‖ < 1 ∧ ‖T‖ - 1 / ((n : ℝ) + 1) < ‖T x‖ :=
    T.exists_lt_apply_of_lt_opNorm (sub_lt_self _ (by positivity))
  choose u hu hTu using hx
  have hnorm : Tendsto (fun n => ‖T (u n)‖) atTop (𝓝 ‖T‖) := by
    have hlo : Tendsto (fun n : ℕ => ‖T‖ - 1 / ((n : ℝ) + 1)) atTop (𝓝 ‖T‖) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
      (fun n => (hTu n).le) (fun n => T.unit_le_opNorm _ (hu n).le)
  have hK := hcompact.isCompact_closure_image_of_isVonNBounded
    (NormedSpace.isVonNBounded_closedBall ℝ H 1)
  obtain ⟨y, _, φ, hφ, hlim⟩ := hK.tendsto_subseq (fun n =>
    subset_closure ⟨u n, by simpa only [Metric.mem_closedBall, dist_zero_right] using (hu n).le, rfl⟩)
  have hy : ‖y‖ = ‖T‖ := tendsto_nhds_unique hlim.norm (hnorm.comp hφ.tendsto_atTop)
  have hc := scalar_extremizing_sequence_cauchy T hT (u ∘ φ)
    (fun n => (hu (φ n)).le) y hlim hy
  obtain ⟨x, hxlim⟩ := cauchySeq_tendsto_of_complete hc
  have hxle : ‖x‖ ≤ 1 := le_of_tendsto hxlim.norm (Eventually.of_forall (fun n => (hu (φ n)).le))
  have hTx : T x = y := tendsto_nhds_unique (T.continuous.tendsto x |>.comp hxlim) hlim
  refine ⟨x, le_antisymm hxle ?_, by rw [hTx, hy]⟩
  have hbound := T.le_opNorm x
  rw [hTx, hy] at hbound
  nlinarith

end
end PositiveEinsteinFour.Geometry

end OAI
