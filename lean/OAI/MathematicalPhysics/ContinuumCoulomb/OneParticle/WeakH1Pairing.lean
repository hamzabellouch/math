import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronClosure
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalH1

namespace OAI

/-! Integration by parts against a noncompact square-integrable C1 function
on the actual weak-H1 graph. Compact approximation is used only through the
explicit published Sobolev density input. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem complex_C1_compact_test_ibp {n : ℕ} (f g : Configuration n → ℂ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (a : Configuration n) :
    (∫ x, f x*fderiv ℝ g x a) = -(∫ x, fderiv ℝ f x a*g x) := by
  have hf' : Continuous (fun x => fderiv ℝ f x a) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hg' : Continuous (fun x => fderiv ℝ g x a) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hf'.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left)
    ((hf.continuous.mul hg').integrable_of_hasCompactSupport (hc.fderiv_apply ℝ a).mul_left)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left)
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => hg.differentiable (by norm_num) x)

theorem h1_inner_real_coordinate {n : ℕ} (u : Coulomb.H1Vector n)
    (a : H1Index n) (φ : Configuration n → ℝ) (hφ : MemLp φ 2) :
    inner ℂ (hφ.ofReal.toLp (fun x => (φ x : ℂ))) (h1Coordinates u a) =
      ∫ x, h1CoordinateFunction u a x*(φ x : ℂ) := by
  have hmem : MemLp (fun x => (φ x : ℂ)) 2 := hφ.ofReal
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hmem.coeFn_toLp,(h1Coordinate_memLp u a).coeFn_toLp] with x hp hu
  change h1Coordinates u a x = h1CoordinateFunction u a x at hu
  change inner ℂ (hmem.toLp _ x) (h1Coordinates u a x) = _
  rw [hp,hu,RCLike.inner_apply]
  simp only [Complex.conj_ofReal]

theorem weakH1_real_test_ibp (hdensity : PublishedSobolevSmoothDensity)
    {n : ℕ} (g : Configuration n → ℝ) (hg : ContDiff ℝ 1 g) (hL2 : MemLp g 2)
    (a : Fin n × Fin 3)
    (hpartial : MemLp (fun x => fderiv ℝ g x (EuclideanSpace.single a 1)) 2)
    (v : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    (∫ x, v.gradient s a x*(g x : ℂ)) =
      -(∫ x, v.value s x*(fderiv ℝ g x (EuclideanSpace.single a 1) : ℂ)) := by
  let d : Configuration n → ℝ := fun x => fderiv ℝ g x (EuclideanSpace.single a 1)
  let G : Lp ℂ 2 (volume : Measure (Configuration n)) := hL2.ofReal.toLp (fun x => (g x : ℂ))
  let D : Lp ℂ 2 (volume : Measure (Configuration n)) := hpartial.ofReal.toLp (fun x => (d x : ℂ))
  have hcompact (w : Coulomb.H1Vector n)
      (hw : ∀ t, ContDiff ℝ 1 (w.value t) ∧ HasCompactSupport (w.value t))
      (hd : ∀ t b x, w.gradient t b x =
        fderiv ℝ (w.value t) x (EuclideanSpace.single b 1)) :
      inner ℂ G (h1Coordinates w (Sum.inr (s,a))) =
        -inner ℂ D (h1Coordinates w (Sum.inl s)) := by
    rw [h1_inner_real_coordinate w (Sum.inr (s,a)) g hL2,
      h1_inner_real_coordinate w (Sum.inl s) d hpartial]
    have he (x : Configuration n) : fderiv ℝ (fun y => (g y : ℂ)) x
        (EuclideanSpace.single a 1) = (d x : ℂ) := by
      exact congrArg (fun L : Configuration n →L[ℝ] ℂ => L (EuclideanSpace.single a 1))
        (Complex.ofRealCLM.hasFDerivAt.comp x (hg.differentiable (by norm_num) x).hasFDerivAt).fderiv
    have hi := complex_C1_compact_test_ibp (fun x => (g x : ℂ)) (w.value s)
      (Complex.ofRealCLM.contDiff.comp hg) (hw s).1 (hw s).2 (EuclideanSpace.single a 1)
    simpa only [h1CoordinateFunction, hd, he, mul_comm] using hi
  obtain ⟨w,hw,hd,ht⟩ := exists_compact_h1_graph_sequence hdensity v
  have hcG : Continuous (fun f : H1Coordinates n => inner ℂ G (f (Sum.inr (s,a)))) :=
    continuous_const.inner (continuous_apply _)
  have hcD : Continuous (fun f : H1Coordinates n => -inner ℂ D (f (Sum.inl s))) :=
    (continuous_const.inner (continuous_apply _)).neg
  have hl := hcG.continuousAt.tendsto.comp ht
  have hr := hcD.continuousAt.tendsto.comp ht
  have heq : inner ℂ G (h1Coordinates v (Sum.inr (s,a))) =
      -inner ℂ D (h1Coordinates v (Sum.inl s)) :=
    tendsto_nhds_unique hl (hr.congr' (Filter.Eventually.of_forall (fun k =>
      (hcompact (w k) (hw k) (hd k)).symm)))
  change inner ℂ (hL2.ofReal.toLp (fun x => (g x : ℂ)))
      (h1Coordinates v (Sum.inr (s,a))) =
    -inner ℂ (hpartial.ofReal.toLp (fun x => (d x : ℂ)))
      (h1Coordinates v (Sum.inl s)) at heq
  rw [h1_inner_real_coordinate v (Sum.inr (s,a)) g hL2,
    h1_inner_real_coordinate v (Sum.inl s) d hpartial] at heq
  exact heq

end ContinuumCoulomb

end

end OAI
