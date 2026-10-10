import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.LogPhysicalMassJet

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal

def logRadiusChart (x : Point) : Point :=
  letI := pointDimension_neZero
  fun i => if i = 0 then Real.exp (x 0) else x i

lemma logRadiusChart_smooth : ContDiff ℝ ∞ logRadiusChart := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 0
  · simp only [logRadiusChart,hi,ite_eq_left]; fun_prop
  · simp only [logRadiusChart,hi,ite_false]; fun_prop

lemma radialFactor_smooth (a : I) : ContDiff ℝ ∞ (radialFactor a) := by
  unfold radialFactor
  by_cases ha : a = 0 <;> simp only [ha,ite_true,ite_false] <;> fun_prop

theorem coordinate_continuousConstSMul : ContinuousConstSMul ℝ ℝ := inferInstance

theorem coordinate_smulCommClass :
    @SMulCommClass ℝ ℝ ℝ Algebra.toSMul
      (@instSMulOfMul ℝ (@Distrib.toMul ℝ
        (@instDistribOfSemiring ℝ (@CommSemiring.toSemiring ℝ Real.instCommSemiring)))) :=
  inferInstance

def chartDerivative (x : Point) : Point →L[ℝ] Point :=
  letI := pointDimension_neZero
  letI := coordinate_smulCommClass
  letI := coordinate_continuousConstSMul
  ContinuousLinearMap.pi (fun i => if i = 0 then Real.exp (x 0) • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma logRadiusChart_hasFDerivAt (x : Point) : HasFDerivAt logRadiusChart (chartDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = 0
  · subst i
    simpa [logRadiusChart,chartDerivative,Function.comp_def] using
      (Real.hasDerivAt_exp (x 0)).comp_hasFDerivAt x (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).hasFDerivAt
  · simp only [logRadiusChart,hi,ite_false]
    change HasFDerivAt (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) (ContinuousLinearMap.proj i) x
    exact (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt

lemma chartDerivative_basis (a : I) (x : Point) :
    chartDerivative x (basis a) = radialFactor a (logRadiusChart x) • basis a := by
  ext i
  by_cases ha : a = 0 <;> by_cases hi : i = 0
  · subst a; subst i; simp [chartDerivative,radialFactor,logRadiusChart,basis]
  · subst a; simp [chartDerivative,radialFactor,logRadiusChart,basis,hi]
  · subst i; simp [chartDerivative,radialFactor,basis,ha,Ne.symm ha]
  · simp [chartDerivative,radialFactor,basis,ha,hi]

lemma D_pullback (a : I) {f : Point → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (logRadiusChart x)) :
    D (basis a) (fun y => f (logRadiusChart y)) x = scaledD a f (logRadiusChart x) := by
  unfold D
  change (fderiv ℝ (f ∘ logRadiusChart) x) (basis a) = _
  rw [fderiv_comp x hf (logRadiusChart_hasFDerivAt x).differentiableAt,
    (logRadiusChart_hasFDerivAt x).fderiv]
  simp only [ContinuousLinearMap.comp_apply,chartDerivative_basis,map_smul,smul_eq_mul,scaledD,D]

lemma scaledD_smooth_at (a : I) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (scaledD a f) x := by
  exact (radialFactor_smooth a).contDiffAt.mul (contDiffAt_D hf (m := ∞) (by simp) (basis a))

def coordinateIter : List I → (Point → ℝ) → Point → ℝ
  | [], f => f
  | a::l,f => D (basis a) (coordinateIter l f)

lemma scaledIter_contDiffAt (l : List I) (m : ℕ) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ (↑(m+l.length) : ℕ∞ω) f x) : ContDiffAt ℝ m (scaledIter l f) x := by
  induction l generalizing m with
  | nil => simpa only [List.length_nil,add_zero,scaledIter] using hf
  | cons a l ih =>
    have heq : m+(a::l).length = (m+1)+l.length := by simp; omega
    rw [heq] at hf
    exact ((radialFactor_smooth a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt.mul
      (contDiffAt_D (ih (m+1) hf) (m := m) (by simp) (basis a))

lemma coordinateIter_pullback (l : List I) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ l.length f (logRadiusChart x)) :
    coordinateIter l (fun y => f (logRadiusChart y)) x = scaledIter l f (logRadiusChart x) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    have heq : coordinateIter l (fun y => f (logRadiusChart y)) =ᶠ[𝓝 x]
        (fun y => scaledIter l f (logRadiusChart y)) := by
      have hf' : ContDiffAt ℝ l.length f (logRadiusChart x) := hf.of_le (by simp)
      have he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ l.length f (logRadiusChart y) :=
        (logRadiusChart_smooth.continuous.continuousAt.tendsto).eventually (hf'.eventually (by simp))
      filter_upwards [he] with y hy
      exact ih hy
    change D (basis a) (coordinateIter l (fun y => f (logRadiusChart y))) x = _
    rw [D_congr heq]
    have hf' : ContDiffAt ℝ (↑(1+l.length) : ℕ∞ω) f (logRadiusChart x) := by
      simpa only [List.length_cons,Nat.add_comm] using hf
    exact D_pullback a ((scaledIter_contDiffAt l 1 hf').differentiableAt (by norm_num))

end
end CKSMixedGeometry

end

end OAI
