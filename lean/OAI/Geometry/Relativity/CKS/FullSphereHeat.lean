import OAI.Geometry.Relativity.CKS.CovariantHeat

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

@[simp] lemma pd_const_add (m : ℝ) (F : E → ℝ) (k : Ix) (x : E) :
    pd k (fun y => m + F y) x = pd k F x := by
  simp only [pd, fderiv_const_add]

@[simp] lemma pd_const_add_fun (m : ℝ) (F : E → ℝ) (k : Ix) :
    pd k (fun y => m + F y) = pd k F := by
  funext x
  exact pd_const_add m F k x

@[simp] lemma roundLaplacian_const_add (m : ℝ) (F : E → ℝ) (x : E) :
    roundLaplacian (fun y => m + F y) x = roundLaplacian F x := by
  simp only [roundLaplacian, roundLap, tangentTrace, grad, hess, pd_const_add_fun, pd_const_add]

@[simp] lemma sphereGradient_const_add (m : ℝ) (F : E → ℝ) (x : E) (j : Ix) :
    sphereGradient (fun y => m + F y) x j = sphereGradient F x j := by
  simp only [sphereGradient, grad, pd_const_add]

lemma radial_restriction (f : C(Sphere,ℝ)) (hf : SmoothSphere f) :
    smoothRestriction (radialExtension f) (radialExtension_smooth hf) = f := by
  ext x
  exact radialExtension_on_sphere f x

lemma smoothDatum_rapid (f : C(Sphere,ℝ)) (hf : SmoothSphere f) :
    PolynomialRapid (heatPolynomials f) := by
  have h := heatPolynomials_rapid (radialExtension_smooth hf)
  rwa [radial_restriction f hf] at h

structure AngularHeatSolution (f₀ : Sphere → ℝ) (m : ℝ) where
  f : ℝ → E → ℝ
  T : ℝ → E → Mat
  f_joint : ContDiffOn ℝ ∞ (fun z : ℝ × E => f z.1 z.2) heatDomain
  T_joint : ∀ i j : Ix, ContDiffOn ℝ ∞ (fun z : ℝ × E => T z.1 z.2 i j) heatDomain
  initial : ∀ x : Sphere, f 0 x = f₀ x
  heat : ∀ t : ℝ, 0 ≤ t → ∀ x : E, ‖x‖ = 1 →
    deriv (fun s => f s x) t = roundLaplacian (f t) x
  mean : ∀ t : ℝ, (∫ x : Sphere, f t x ∂surfaceMeasure) = m * sphereArea
  symmetric : ∀ t : ℝ, ∀ x : E, ‖x‖ = 1 → ∀ i j : Ix, T t x i j = T t x j i
  tangent : ∀ t : ℝ, ∀ x : E, ‖x‖ = 1 → ∀ j : Ix, ∑ i, x i * T t x i j = 0
  trace_free : ∀ t : ℝ, ∀ x : E, ‖x‖ = 1 → ∑ i : Ix, T t x i i = 0
  divergence : ∀ t : ℝ, ∀ x : E, ‖x‖ = 1 → ∀ j : Ix,
    tensorDivergence (T t) x j = sphereGradient (f t) x j
  estimates : ∀ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x : E, ‖x‖ = 1 →
      tensorNorm (covariantTimeJet (scalarTensor (fun s y => f s y - m)) a b) t x +
      tensorNorm (covariantTimeJet (matrixTensor T) a b) t x ≤ C * Real.exp (-6*t)

theorem sphere_heat_full (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀)
    (m : ℝ) (hb : Balanced f₀ m) : Nonempty (AngularHeatSolution f₀ m) := by
  let p := heatPolynomials f₀
  have hp : PolynomialRapid p := smoothDatum_rapid f₀ hf₀
  have hh : HighHarmonic p := heatPolynomials_harmonic f₀
  let F : ℝ → E → ℝ := fun t x => m + spatialHeat p (0,[]) t x
  refine ⟨{
    f := F
    T := heatTensor p
    f_joint := contDiffOn_const.add (jointHeatSeries_smooth p hp (0,[]))
    T_joint := fun i j => (heatTensor_generated p hp i j).joint_smooth (inversePolynomials_rapid p hp)
    initial := ?_
    heat := ?_
    mean := ?_
    symmetric := fun t x hx i j => heatTensor_symmetric p hp t hx i j
    tangent := fun t x hx j => heatTensor_tangent p t hx j
    trace_free := fun t x hx => heatTensor_trace_zero p t hx
    divergence := ?_
    estimates := ?_
  }⟩
  · intro x
    have h := sphereHeatJet_initial (radialExtension_smooth hf₀)
      (m := m) (by rwa [radial_restriction f₀ hf₀])
    rw [radial_restriction f₀ hf₀] at h
    have he := congrArg (fun q : C(Sphere,ℝ) => q x) h
    change sphereEval (MvPolynomial.C m) x + sphereHeatJet p (0,[]) 0 x = f₀ x at he
    have hc : sphereEval (MvPolynomial.C m) x = m := by simp [sphereEval]
    rw [hc, sphereHeatJet_eq p hp] at he
    exact he
  · intro t ht x hx
    change deriv (fun s => m + spatialHeat p (0,[]) s x) t =
      roundLaplacian (fun y => m + spatialHeat p (0,[]) t y) x
    rw [deriv_const_add, roundLaplacian_const_add, roundLaplacian_eq_Casimir (spatialHeat_smooth p hp _ t) hx]
    exact spatialHeat_equation p hp hh _ ht (by intro h; simp [h] at hx)
  · intro t
    let q : C(Sphere,ℝ) := sphereEval (MvPolynomial.C m) + sphereHeatJet p (0,[]) t
    have he : (fun x : Sphere => F t x) = fun x => q x := by
      funext x
      change m + jointHeatSeries p (0,[]) (t,x) = sphereEval (MvPolynomial.C m) x + sphereHeatJet p (0,[]) t x
      rw [sphereHeatJet_eq p hp]
      simp [sphereEval]
    rw [he, ← sphereIntegral_apply]
    change sphereIntegral (sphereEval (MvPolynomial.C m) + sphereHeatJet p (0,[]) t) = _
    rw [map_add, sphereIntegral_constant, sphereHeatJet_mean_zero p hp hh, add_zero]
  · intro t x hx j
    change tensorDivergence (heatTensor p t) x j = sphereGradient (fun y => m + spatialHeat p (0,[]) t y) x j
    rw [sphereGradient_const_add]
    exact heatTensor_divergence p hp hh t hx j
  · intro a b
    have hF : (fun s y => F s y - m) = spatialHeat p (0,[]) := by
      funext s y
      dsimp only [F]
      ring
    rw [hF]
    exact heat_covariant_estimates p hp a b

theorem sphere_heat_every_smooth (f₀ : Sphere → ℝ) (hf₀ : SmoothSphere f₀)
    (m : ℝ)
    (hmean : (∫ x : Sphere, f₀ x ∂surfaceMeasure) = m * sphereArea)
    (hfirst : ∀ i : Ix, (∫ x : Sphere, f₀ x * (x : E) i ∂surfaceMeasure) = 0) :
    Nonempty (AngularHeatSolution f₀ m) := by
  let f : C(Sphere,ℝ) := ⟨f₀, hf₀.continuous⟩
  apply sphere_heat_full f hf₀ m
  constructor
  · rwa [sphereIntegral_apply]
  · intro i
    rw [sphereIntegral_apply]
    exact hfirst i

end
end CKSInducedSphere

end

end OAI
