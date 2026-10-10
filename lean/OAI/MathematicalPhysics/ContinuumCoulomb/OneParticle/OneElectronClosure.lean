import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronCoordinates

namespace OAI

/-! Transfer of the physical one-electron estimate to the full spinful weak-H1
form domain. The only approximation input is the published H=W density result. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def oneElectronOrbitalLp (φ : Position → ℝ) (hφ : MemLp φ 2) :
    Lp ℂ 2 (volume : Measure (Configuration 1)) :=
  (hφ.ofReal.comp_measurePreserving oneElectronCoordinates.measurePreserving).toLp
    (fun x => (φ (oneElectronCoordinates x) : ℂ))

theorem h1_inner_real_orbital {n : ℕ} (u : Coulomb.H1Vector n)
    (s : SpinConfiguration n) (φ : Configuration n → ℝ) (hφ : MemLp φ 2) :
    inner ℂ (hφ.ofReal.toLp (fun x => (φ x : ℂ))) (h1Coordinates u (Sum.inl s)) =
      ∫ x, u.value s x*(φ x : ℂ) := by
  have hcφ : MemLp (fun x => (φ x : ℂ)) 2 := hφ.ofReal
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hcφ.coeFn_toLp,(h1Coordinate_memLp u (Sum.inl s)).coeFn_toLp]
    with x hφx hux
  change inner ℂ (hφ.ofReal.toLp (fun x => (φ x : ℂ)) x)
    (h1Coordinates u (Sum.inl s) x) = _
  change h1Coordinates u (Sum.inl s) x = u.value s x at hux
  rw [hφx,hux,RCLike.inner_apply]
  simp only [Complex.conj_ofReal]

theorem oneElectron_inner_real_orbital (u : Coulomb.H1Vector 1)
    (s : SpinConfiguration 1) (φ : Position → ℝ) (hφ : MemLp φ 2) :
    inner ℂ (oneElectronOrbitalLp φ hφ) (h1Coordinates u (Sum.inl s)) =
      ∫ x, u.value s x*(φ (oneElectronCoordinates x) : ℂ) :=
  h1_inner_real_orbital u s (fun x => φ (oneElectronCoordinates x))
    (hφ.comp_measurePreserving oneElectronCoordinates.measurePreserving)

theorem oneElectron_graphOrbitalMass {ι : Type*} [Fintype ι]
    (φ : ι → Position → ℝ) (hφ : ∀ i, MemLp (φ i) 2) (u : Coulomb.H1Vector 1) :
    graphOrbitalMass (fun i => oneElectronOrbitalLp (φ i) (hφ i)) (h1Coordinates u) =
      ∑ s, ∑ i, ‖∫ x, u.value s x*(φ i (oneElectronCoordinates x) : ℂ)‖^2 := by
  unfold graphOrbitalMass
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z : ℂ => ‖z‖^2)
    (h1_inner_real_orbital u s (fun x => φ i (oneElectronCoordinates x))
      ((hφ i).comp_measurePreserving oneElectronCoordinates.measurePreserving))

theorem oneElectron_weakH1_lower
    (hdensity : PublishedSobolevSmoothDensity)
    {ι : Type*} [Fintype ι] (V : Position → ℝ) (hV : Continuous V)
    (B : ℝ) (hB : ∀ x, |V x| ≤ B) (φ : ι → Position → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2) (E κ : ℝ)
    (hphysical : ∀ f : Position → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
      E*(∫ x, ‖f x‖^2)-κ*(∑ i, ‖∫ x, f x*(φ i x : ℂ)‖^2) ≤ positionComplexForm V f)
    (u : Coulomb.H1Vector 1) :
    E*Coulomb.mass u-κ*graphOrbitalMass (fun i => oneElectronOrbitalLp (φ i) (hφ i))
      (h1Coordinates u) ≤ boundedPotentialForm (fun x => V (oneElectronCoordinates x)) u := by
  apply boundedPotential_projection_lower_of_compact hdensity _
    (hV.comp oneElectronCoordinates.continuous) B (fun x => hB _) _ E κ ?_ u
  intro v hv hd
  have hs (s : SpinConfiguration 1) := hphysical (oneElectronPullback (v.value s))
    (oneElectronPullback_contDiff (hv s).1) (oneElectronPullback_compact (hv s).2)
  have hm (s : SpinConfiguration 1) : (∫ x, ‖oneElectronPullback (v.value s) x‖^2) =
      ∫ x, ‖v.value s x‖^2 := oneElectronPullback_integral (fun x => ‖v.value s x‖^2)
  have ho (s : SpinConfiguration 1) (i : ι) :
      (∫ x, oneElectronPullback (v.value s) x*(φ i x : ℂ)) =
        ∫ x, v.value s x*(φ i (oneElectronCoordinates x) : ℂ) := by
    have h := oneElectronPullback_integral_complex
      (fun x => v.value s x*(φ i (oneElectronCoordinates x) : ℂ))
    simpa only [oneElectronPullback,LinearIsometryEquiv.apply_symm_apply] using h
  have hs' (s : SpinConfiguration 1) :
      E*(∫ x, ‖v.value s x‖^2)-κ*(∑ i, ‖∫ x, v.value s x*(φ i (oneElectronCoordinates x) : ℂ)‖^2) ≤
      (1/2:ℝ)*(∑ a : Fin 3, ∫ x, ‖fderiv ℝ (v.value s) x (EuclideanSpace.single (0,a) 1)‖^2)+
      ∫ x, V (oneElectronCoordinates x)*‖v.value s x‖^2 := by
    simpa only [hm,ho,oneElectronPullback_form V (hv s).1] using hs s
  have h := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hs' s)
  rw [oneElectron_graphOrbitalMass]
  unfold Coulomb.mass boundedPotentialForm Coulomb.kinetic
  simp_rw [hd,Fintype.sum_prod_type,Fin.sum_univ_one]
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Function.comp_apply] using h

end ContinuumCoulomb

end

end OAI
