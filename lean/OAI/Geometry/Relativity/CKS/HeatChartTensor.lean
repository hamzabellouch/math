import OAI.Geometry.Relativity.CKS.SphericalTensorIdentity
import OAI.Geometry.Relativity.CKS.HeatChart

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere
open scoped Topology ContDiff

lemma chartTensorA_first {T : ℝ → E → Mat} {t : ℝ → ℝ}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × E => T z.1 z.2 i j) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) {x : Point} (hx : x ∈ positiveChart)
    (i : Ix) (hi : i ≠ 0) : D (basis i) (chartTensorA T t) x =
      D (basis i) (tensorA (T (t (x 0)))) x := by
  apply angular_first_congr_leaf
    (((chartTensorA_smooth hT ht).contDiffAt (positiveChart_open.mem_nhds hx)).differentiableAt (by simp))
    ((tensorA_smooth (fun a b => joint_slice (F := fun s y => T s y a b) (hT a b) _)).differentiable (by simp) x) _ i hi
  intro y hy
  simp only [chartTensorA,hy]

lemma chartTensorPhi_first {T : ℝ → E → Mat} {t : ℝ → ℝ}
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × E => T z.1 z.2 i j) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) {x : Point} (hx : x ∈ positiveChart)
    (i : Ix) (hi : i ≠ 0) : D (basis i) (chartTensorPhi T t) x =
      D (basis i) (tensorPhi (T (t (x 0)))) x := by
  apply angular_first_congr_leaf
    (((chartTensorPhi_smooth hT ht).contDiffAt (positiveChart_open.mem_nhds hx)).differentiableAt (by simp))
    ((tensorPhi_smooth (fun a b => joint_slice (F := fun s y => T s y a b) (hT a b) _)).differentiable (by simp) x) _ i hi
  intro y hy
  simp only [chartTensorPhi,hy]

lemma varying_chart_divergence {F : ℝ → E → ℝ} {T : ℝ → E → Mat} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (hT : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × E => T z.1 z.2 i j) heatDomain)
    (hS : ∀ s, ∀ y ∈ U, ∀ i j, T s y i j = T s y j i)
    (hN : ∀ s, ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, ∑ i, y i * T s y i j = 0)
    (hTr : ∀ s, ∀ y : E, ‖y‖ = 1 → ∑ i : Ix, T s y i i = 0)
    (hDiv : ∀ s, ∀ y : E, ‖y‖ = 1 → ∀ j : Ix, tensorDivergence (T s) y j = sphereGradient (F s) y j)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : x ∈ positiveChart) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (chartTensorA T t) x + D (basis 2) (chartTensorPhi T t) x / Real.sin (x 1)^2 +
      2*Real.cos (x 1)*chartTensorA T t x / Real.sin (x 1) = D (basis 1) (chartMass F t c) x) ∧
    (D (basis 1) (chartTensorPhi T t) x - D (basis 2) (chartTensorA T t) x +
      Real.cos (x 1)*chartTensorPhi T t x / Real.sin (x 1) = D (basis 2) (chartMass F t c) x) := by
  rw [chartTensorA_first hT ht hx 1 (by decide),chartTensorA_first hT ht hx 2 (by decide),
    chartTensorPhi_first hT ht hx 1 (by decide),chartTensorPhi_first hT ht hx 2 (by decide),
    chartMass_first hF ht hc hx 1 (by decide),chartMass_first hF ht hc hx 2 (by decide)]
  exact tensor_chart_gradient (joint_slice hF _) (fun i j => joint_slice (F := fun s y => T s y i j) (hT i j) _)
    (hS _) (hN _) (hTr _) (hDiv _) x hs

lemma heatTensor_symmetric_U (p : ℕ → Poly) (hp : PolynomialRapid p)
    (t : ℝ) (x : E) (hx : x ∈ U) (i j : Ix) : heatTensor p t x i j = heatTensor p t x j i :=
  hessTF_symm _ _ (fun a b => partial_comm
    (spatialHeat_smooth _ (inversePolynomials_rapid p hp) _ t) hx a b) i j

def canonicalF (f₀ : C(Sphere,ℝ)) (m : ℝ) : ℝ → E → ℝ :=
  fun t y => m + spatialHeat (heatPolynomials f₀) (0,[]) t y
def canonicalT (f₀ : C(Sphere,ℝ)) : ℝ → E → Mat := heatTensor (heatPolynomials f₀)
lemma canonicalF_joint (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => canonicalF f₀ m z.1 z.2) heatDomain :=
  contDiffOn_const.add (jointHeatSeries_smooth _ (smoothDatum_rapid f₀ hf₀) (0,[]))
lemma canonicalT_joint (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (i j : Ix) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => canonicalT f₀ z.1 z.2 i j) heatDomain :=
  (heatTensor_generated _ (smoothDatum_rapid f₀ hf₀) i j).joint_smooth
    (inversePolynomials_rapid _ (smoothDatum_rapid f₀ hf₀))

theorem canonical_chart_divergence (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {t c : ℝ → ℝ} (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : x ∈ positiveChart) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (chartTensorA (canonicalT f₀) t) x + D (basis 2) (chartTensorPhi (canonicalT f₀) t) x / Real.sin (x 1)^2 +
      2*Real.cos (x 1)*chartTensorA (canonicalT f₀) t x / Real.sin (x 1) = D (basis 1) (chartMass (canonicalF f₀ m) t c) x) ∧
    (D (basis 1) (chartTensorPhi (canonicalT f₀) t) x - D (basis 2) (chartTensorA (canonicalT f₀) t) x +
      Real.cos (x 1)*chartTensorPhi (canonicalT f₀) t x / Real.sin (x 1) = D (basis 2) (chartMass (canonicalF f₀ m) t c) x) := by
  have hp := smoothDatum_rapid f₀ hf₀
  apply varying_chart_divergence (canonicalF_joint f₀ hf₀ m) (canonicalT_joint f₀ hf₀)
    (heatTensor_symmetric_U _ hp) (fun s y hy j => heatTensor_tangent _ s hy j)
    (fun s y hy => heatTensor_trace_zero _ s hy) _ ht hc hx hs
  intro s y hy j
  unfold canonicalF canonicalT
  rw [sphereGradient_const_add]
  exact heatTensor_divergence _ hp (heatPolynomials_harmonic f₀) s hy j

end
end CKSSphericalChart

end

end OAI
