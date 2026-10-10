import Mathlib
import OAI.Analysis.Conductivity.Fourier.RectangularTorusAtlas
import OAI.Analysis.Conductivity.Geometry.TorusLipschitzTrace
import OAI.Analysis.Conductivity.Fourier.RectangularRayTrace

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma rectangularRay_abs {w : ℝ} (hw : 0<w) (hw' : w≤1)
    (θ : UnitAddCircle) (i : Fin 2) : |rectangularRay w θ i|≤2 := by
  have hd := rayDenominator_lower hw hw' θ
  have hp : 0<rayDenominator w θ := by linarith
  rw [rectangularRay,abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  linarith [rayDirection_abs θ i]

lemma rectangularRay_coordinate_bound {w : ℝ} (hw : 0<w) (hw' : w≤1)
    (x : UnitAddTorus (Fin 2)) (j k i : Fin 2) (t : ℝ) :
    |rectangularRay w ((x+torusCoordinateShift j t) k) i-rectangularRay w (x k) i|≤
      ((2+4/w)*(2*Real.pi))*|t| := by
  by_cases h : k=j
  · subst k
    simpa [torusCoordinateShift,mul_assoc] using rectangularRay_difference hw hw' (x j) t i
  · simp only [Pi.add_apply,torusCoordinateShift,ite_eq_right h,add_zero,sub_self,abs_zero]
    positivity

def sourceRayCoordinates (x : UnitAddTorus (Fin 2)) : Fin 4 → ℝ :=
  ![rectangularRay 1 (x 0) 0,rectangularRay 1 (x 0) 1,
    rectangularRay sourceRadialWidth (x 1) 0,rectangularRay sourceRadialWidth (x 1) 1]

def sourceRayBox : Set (Fin 4 → ℝ) := Icc (fun _ => -2) (fun _ => 2)

lemma sourceRayCoordinates_mem (x : UnitAddTorus (Fin 2)) : sourceRayCoordinates x∈sourceRayBox := by
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hw' : sourceRadialWidth≤1 := by norm_num [sourceRadialWidth,sourceHole]
  have h (i : Fin 4) : |sourceRayCoordinates x i|≤2 := by
    fin_cases i
    · exact rectangularRay_abs (by norm_num) (by norm_num) _ _
    · exact rectangularRay_abs (by norm_num) (by norm_num) _ _
    · exact rectangularRay_abs hw hw' _ _
    · exact rectangularRay_abs hw hw' _ _
  exact ⟨fun i => (abs_le.mp (h i)).1,fun i => (abs_le.mp (h i)).2⟩

lemma continuous_sourceRayCoordinates : Continuous sourceRayCoordinates := by
  have hc1 := continuous_rectangularRay (w:=1) (by norm_num) (by norm_num)
  have hcw := continuous_rectangularRay (w:=sourceRadialWidth)
    (by norm_num [sourceRadialWidth,sourceHole]) (by norm_num [sourceRadialWidth,sourceHole])
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [sourceRayCoordinates]
  · exact (continuous_apply (0 : Fin 2)).comp (hc1.comp (continuous_apply (0 : Fin 2)))
  · exact (continuous_apply (1 : Fin 2)).comp (hc1.comp (continuous_apply (0 : Fin 2)))
  · exact (continuous_apply (0 : Fin 2)).comp (hcw.comp (continuous_apply (1 : Fin 2)))
  · exact (continuous_apply (1 : Fin 2)).comp (hcw.comp (continuous_apply (1 : Fin 2)))

def sourceRayConstant : ℝ := 6*(2*Real.pi)+(2+4/sourceRadialWidth)*(2*Real.pi)

lemma sourceRayConstant_nonneg : 0≤ sourceRayConstant := by
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  unfold sourceRayConstant
  positivity

lemma sourceRayCoordinates_difference (j : Fin 2) (t : ℝ) (x : UnitAddTorus (Fin 2)) :
    ‖sourceRayCoordinates (x+torusCoordinateShift j t)-sourceRayCoordinates x‖≤ sourceRayConstant*|t| := by
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hw' : sourceRadialWidth≤1 := by norm_num [sourceRadialWidth,sourceHole]
  have h1 : (2+4/(1:ℝ))*(2*Real.pi)≤ sourceRayConstant := by
    dsimp [sourceRayConstant]
    norm_num
    positivity
  have h2 : (2+4/sourceRadialWidth)*(2*Real.pi)≤ sourceRayConstant := by
    dsimp [sourceRayConstant]
    linarith [Real.pi_pos]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg sourceRayConstant_nonneg (abs_nonneg _))).mpr
  intro i
  change |sourceRayCoordinates (x+torusCoordinateShift j t) i-sourceRayCoordinates x i|≤_
  fin_cases i
  · exact (rectangularRay_coordinate_bound (w:=1) (by norm_num) (by norm_num) x j 0 0 t).trans
      (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
  · exact (rectangularRay_coordinate_bound (w:=1) (by norm_num) (by norm_num) x j 0 1 t).trans
      (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
  · exact (rectangularRay_coordinate_bound hw hw' x j 1 0 t).trans
      (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
  · exact (rectangularRay_coordinate_bound hw hw' x j 1 1 t).trans
      (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))

def sourceAngularPolynomial (t : ℝ) (z : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![sourceLength*(sourceRadialCenter+(1-t)*z 2)*z 0,
    (sourceRadialCenter+(1-t)*z 2)*z 1,(1-t)*z 3]

def sourceAngularCollar (t : ℝ) (x : UnitAddTorus (Fin 2)) : Fin 3 → ℝ :=
  sourceAngularPolynomial t (sourceRayCoordinates x)

lemma contDiff_sourceAngularPolynomial (t : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (sourceAngularPolynomial t) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [sourceAngularPolynomial] <;> fun_prop

lemma continuous_sourceAngularCollar (t : ℝ) : Continuous (sourceAngularCollar t) :=
  (contDiff_sourceAngularPolynomial t).continuous.comp continuous_sourceRayCoordinates

theorem sourceAngularTrace_summable (s : Fin 3 → ℝ) (t : ℝ) {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    Summable (fun h : Fin 2 → ℤ => torusRate s h*
      ‖mFourierCoeff (fun x => (f (sourceAngularCollar t x):ℂ)) h‖^2) := by
  let G : (Fin 4 → ℝ) → ℂ := fun z => (f (sourceAngularPolynomial t z):ℂ)
  have hG : ContDiff ℝ (↑(⊤ : ℕ∞)) G := by
    exact Complex.ofRealCLM.contDiff.comp (hf.comp (contDiff_sourceAngularPolynomial t))
  obtain ⟨K,hK⟩ := hG.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_Icc _ _) isCompact_Icc
  let F : C(UnitAddTorus (Fin 2),ℂ) :=
    ⟨fun x => G (sourceRayCoordinates x),hG.continuous.comp continuous_sourceRayCoordinates⟩
  have hdiff (j : Fin 2) (u : ℝ) (x : UnitAddTorus (Fin 2)) :
      ‖F (x+torusCoordinateShift j u)-F x‖≤((K:ℝ)*sourceRayConstant)*|u| := by
    have hh := hK.dist_le_mul _ (sourceRayCoordinates_mem (x+torusCoordinateShift j u))
      _ (sourceRayCoordinates_mem x)
    rw [dist_eq_norm,dist_eq_norm] at hh
    apply hh.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (sourceRayCoordinates_difference j u x) K.coe_nonneg
  exact torus_coordinate_trace_summable s F (fun _ => (K:ℝ)*sourceRayConstant)
    (fun _ => mul_nonneg K.coe_nonneg sourceRayConstant_nonneg) hdiff

end ScalarConductivity

end

end OAI
