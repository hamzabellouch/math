import Mathlib
import OAI.Analysis.HardSphere.Operators.FreeResolventDenseRange
import OAI.Analysis.HardSphere.Geometry.AvoidanceReflectionNorm
import OAI.Analysis.HardSphere.Comparison.LaplaceIntegrand

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology

lemma killedTransition_clamped_continuous (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    Continuous (fun t : ℝ ↦ killedTransition N L a (max 0 t) f) :=
  semigroup_clamped_continuous (killedTransition N L a) (killedTransition_add_nonneg N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) (killedTransition_tendsto_zero N L a) f

def killedLaplace (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) : ScalarL2 N L :=
  semigroupLaplace (killedTransition N L a) f

lemma killedLaplace_norm_le (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    ‖killedLaplace N L a f‖≤‖f‖ :=
  semigroupLaplace_norm_le (killedTransition N L a) (killedTransition_clamped_continuous N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) f

lemma killedLaplace_difference_tendsto (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    Tendsto (fun h : ℝ ↦ (h⁻¹:ℂ) • (killedLaplace N L a f-killedTransition N L a h (killedLaplace N L a f)))
      (𝓝[>] 0) (𝓝 (allowedProjection N L a f-killedLaplace N L a f)) := by
  simpa only [killedLaplace,killedTransition_zero] using semigroupLaplace_difference_tendsto_complex
    (killedTransition N L a) (killedTransition_add_nonneg N L a)
    (killedTransition_clamped_continuous N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) f

lemma killedLaplace_norm_sub_le (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    ‖killedLaplace N L a f-killedTransition N L a h (killedLaplace N L a f)‖≤
      (2*Real.exp 1)*h*‖f‖ :=
  semigroupLaplace_norm_sub_le (killedTransition N L a) (killedTransition_add_nonneg N L a)
    (killedTransition_clamped_continuous N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) f hh hh1

lemma killedLaplace_support (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    ∀ᵐ X ∂(volume : Measure (Configuration N L)), X∉allowed N L a → killedLaplace N L a f X=0 := by
  have he := semigroupLaplace_project (killedTransition N L a) (killedTransition_add_nonneg N L a)
    (killedTransition_clamped_continuous N L a)
    (fun t _ ↦ killedTransition_apply_contraction N L a t) f
  simpa only [killedLaplace,he] using killedTransition_support N L a 0 (killedLaplace N L a f)

lemma killedLaplace_free_energy_bound (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    h⁻¹ * (‖killedLaplace N L a f‖^2-(inner ℂ (killedLaplace N L a f)
      (freeTransition N L h (killedLaplace N L a f))).re)≤4*Real.exp 1*‖f‖^2 := by
  let u := killedLaplace N L a f
  have hb := free_deficit_le_twice_killed N L a h u
  have hi : ‖u‖^2-(inner ℂ u (killedTransition N L a h u)).re≤
      ‖u‖*‖u-killedTransition N L a h u‖ := by
    have hinner := re_inner_le_norm (𝕜 := ℂ) u (u-killedTransition N L a h u)
    change (inner ℂ u (u-killedTransition N L a h u)).re≤_ at hinner
    rw [inner_sub_right,Complex.sub_re] at hinner
    have he : (inner ℂ u u).re=‖u‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
    rw [he] at hinner
    exact hinner
  have hc := mul_le_mul (killedLaplace_norm_le N L a f)
    (killedLaplace_norm_sub_le N L a f hh.le hh1)
    (norm_nonneg _) (norm_nonneg _)
  have hd : ‖u‖^2-(inner ℂ u (freeTransition N L h u)).re≤
      4*Real.exp 1*h*‖f‖^2 := by
    nlinarith [hb,hi,hc]
  have hm := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hh.le)
  calc
    _ ≤ h⁻¹*(4*Real.exp 1*h*‖f‖^2) := hm
    _ = _ := by field_simp

lemma killedLaplace_free_graph (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    ∃ v : hilbertDomain N L (-1), scalarEmbedding N L (-1) v=killedLaplace N L a f ∧
      ‖v‖^2≤‖killedLaplace N L a f‖^2+4*Real.exp 1*‖f‖^2 := by
  apply free_graph_lift_of_heat_bound N L (-1) (by norm_num)
  intro n
  apply killedLaplace_free_energy_bound N L a f
  · positivity
  · apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]

end HardSphere

end

end OAI
