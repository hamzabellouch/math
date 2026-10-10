import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WeakH1Laplacian

namespace OAI

/-! Integration by parts for a complex C2 orbital against the full weak-H1
space. Only the sum of its second derivatives is required to lie in L2. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

def configurationComplexPartial {n : ℕ} (φ : Configuration n → ℂ)
    (a : Fin n × Fin 3) (x : Configuration n) : ℂ :=
  fderiv ℝ φ x (EuclideanSpace.single a 1)

def configurationComplexLaplacian {n : ℕ} (φ : Configuration n → ℂ)
    (x : Configuration n) : ℂ :=
  ∑ a, configurationComplexPartial (configurationComplexPartial φ a) a x

theorem configurationComplexPartial_C1 {n : ℕ} {φ : Configuration n → ℂ}
    (hφ : ContDiff ℝ 2 φ) (a : Fin n × Fin 3) :
    ContDiff ℝ 1 (configurationComplexPartial φ a) :=
  (hφ.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const

theorem h1_inner_complex_coordinate {n : ℕ} (u : Coulomb.H1Vector n)
    (a : H1Index n) (φ : Configuration n → ℂ) (hφ : MemLp φ 2) :
    inner ℂ (hφ.toLp φ) (h1Coordinates u a) =
      ∫ x, star (φ x)*h1CoordinateFunction u a x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp,(h1Coordinate_memLp u a).coeFn_toLp] with x hp hu
  change h1Coordinates u a x = h1CoordinateFunction u a x at hu
  rw [hp,hu,RCLike.inner_apply]
  exact mul_comm _ _

theorem weakH1_complex_laplacian_pairing (hdensity : PublishedSobolevSmoothDensity)
    {n : ℕ} (φ : Configuration n → ℂ) (hφ : ContDiff ℝ 2 φ)
    (hpartial : ∀ a, MemLp (configurationComplexPartial φ a) 2)
    (hlap : MemLp (configurationComplexLaplacian φ) 2)
    (v : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    (∑ a, ∫ x, star (configurationComplexPartial φ a x)*v.gradient s a x) =
      -(∫ x, star (configurationComplexLaplacian φ x)*v.value s x) := by
  let G (a : Fin n × Fin 3) : Lp ℂ 2 (volume : Measure (Configuration n)) :=
    (hpartial a).toLp (configurationComplexPartial φ a)
  let L : Lp ℂ 2 (volume : Measure (Configuration n)) :=
    hlap.toLp (configurationComplexLaplacian φ)
  have hpair (w : Coulomb.H1Vector n) (a : Fin n × Fin 3) :
      inner ℂ (G a) (h1Coordinates w (Sum.inr (s,a))) =
        ∫ x, star (configurationComplexPartial φ a x)*w.gradient s a x :=
    h1_inner_complex_coordinate w (Sum.inr (s,a)) _ (hpartial a)
  have hlpair (w : Coulomb.H1Vector n) :
      inner ℂ L (h1Coordinates w (Sum.inl s)) =
        ∫ x, star (configurationComplexLaplacian φ x)*w.value s x :=
    h1_inner_complex_coordinate w (Sum.inl s) _ hlap
  have hcompact (w : Coulomb.H1Vector n)
      (hw : ∀ t, ContDiff ℝ 1 (w.value t) ∧ HasCompactSupport (w.value t))
      (hd : ∀ t a x, w.gradient t a x =
        fderiv ℝ (w.value t) x (EuclideanSpace.single a 1)) :
      (∑ a, inner ℂ (G a) (h1Coordinates w (Sum.inr (s,a)))) =
        -inner ℂ L (h1Coordinates w (Sum.inl s)) := by
    have hi (a : Fin n × Fin 3) : Integrable (fun x =>
        star (configurationComplexPartial (configurationComplexPartial φ a) a x)*w.value s x) :=
      (((configurationComplexPartial_C1 hφ a).continuous_fderiv (by norm_num)).clm_apply
        continuous_const).star.mul (hw s).1.continuous |>.integrable_of_hasCompactSupport (hw s).2.mul_left
    have he (a : Fin n × Fin 3) :
        (∫ x, star (configurationComplexPartial φ a x)*w.gradient s a x) =
          -(∫ x, star (configurationComplexPartial (configurationComplexPartial φ a) a x)*w.value s x) := by
      have hc := configurationComplexPartial_C1 hφ a
      have hstar (x : Configuration n) :
          fderiv ℝ (fun y => star (configurationComplexPartial φ a y)) x
            (EuclideanSpace.single a 1) =
          star (configurationComplexPartial (configurationComplexPartial φ a) a x) := by
        exact congrArg (fun B : Configuration n →L[ℝ] ℂ => B (EuclideanSpace.single a 1))
          (Complex.conjCLE.hasFDerivAt.comp x (hc.differentiable (by norm_num) x).hasFDerivAt).fderiv
      have hh := complex_C1_compact_test_ibp (fun x => star (configurationComplexPartial φ a x))
        (w.value s) (Complex.conjCLE.contDiff.comp hc) (hw s).1 (hw s).2
          (EuclideanSpace.single a 1)
      simpa only [hd,hstar] using hh
    simp only [hpair,hlpair]
    simp_rw [he]
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [← integral_finsetSum Finset.univ (fun a _ => hi a)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [configurationComplexLaplacian,star_sum,Finset.sum_mul]
  obtain ⟨w,hw,hd,ht⟩ := exists_compact_h1_graph_sequence hdensity v
  have hcG : Continuous (fun f : H1Coordinates n =>
      ∑ a, inner ℂ (G a) (f (Sum.inr (s,a)))) :=
    continuous_finsetSum _ (fun a _ => continuous_const.inner (continuous_apply _))
  have hcL : Continuous (fun f : H1Coordinates n => -inner ℂ L (f (Sum.inl s))) :=
    (continuous_const.inner (continuous_apply _)).neg
  have heq := tendsto_nhds_unique (hcG.continuousAt.tendsto.comp ht)
    ((hcL.continuousAt.tendsto.comp ht).congr' (Filter.Eventually.of_forall
      (fun k => (hcompact (w k) (hw k) (hd k)).symm)))
  simpa only [hpair,hlpair] using heq

end ContinuumCoulomb

end

end OAI
