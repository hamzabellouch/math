import Mathlib
import OAI.Analysis.Conductivity.Walls.HadamardWall

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def wallPrimitive (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  p.2 * ∫ t in Icc (0:ℝ) 1, f (p.1,t*p.2)

lemma wallPrimitive_smooth {f : E × ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallPrimitive f) := by
  apply contDiff_snd.mul
  apply contDiff_compact_integral (μ := volume)
    (F := fun p : (E × ℝ) × ℝ => f (p.1.1,p.2*p.1.2))
    (K := Icc (0:ℝ) 1) _ isCompact_Icc
  exact hf.comp (contDiff_fst.fst.prodMk (contDiff_snd.mul contDiff_fst.snd))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] in
lemma wallPrimitive_eq_intervalIntegral (f : E × ℝ → ℝ) (x : E) (z : ℝ) :
    wallPrimitive f (x,z)=∫ t in (0:ℝ)..z, f (x,t) := by
  have he := intervalIntegral.smul_integral_comp_mul_right
    (fun t : ℝ => f (x,t)) z (a := 0) (b := 1)
  simpa only [smul_eq_mul,zero_mul,one_mul,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ←integral_Icc_eq_integral_Ioc,wallPrimitive] using he

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] in
lemma wallPrimitive_zero (f : E × ℝ → ℝ) (x : E) : wallPrimitive f (x,0)=0 := by
  simp [wallPrimitive]

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma wallPrimitive_hasDerivAt {f : E × ℝ → ℝ} (hf : Continuous f) (x : E) (z : ℝ) :
    HasDerivAt (fun t : ℝ => wallPrimitive f (x,t)) (f (x,z)) z := by
  simp_rw [wallPrimitive_eq_intervalIntegral]
  have hc : Continuous (fun t : ℝ => f (x,t)) :=
    hf.comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

lemma wallDerivative_primitive {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (p : E × ℝ) :
    wallDerivative (wallPrimitive f) p=f p := by
  have h := ((wallPrimitive_smooth hf).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact h.unique (wallPrimitive_hasDerivAt hf.continuous p.1 p.2)

end ScalarConductivity

end

end OAI
