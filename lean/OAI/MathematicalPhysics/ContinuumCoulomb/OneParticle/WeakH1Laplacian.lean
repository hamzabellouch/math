import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WeakH1Pairing

namespace OAI

/-! The weak kinetic pairing with a C2 orbital only requires its Laplacian,
not each second partial separately, to belong to L2. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

def configurationRealPartial {n : ℕ} (φ : Configuration n → ℝ)
    (a : Fin n × Fin 3) (x : Configuration n) : ℝ :=
  fderiv ℝ φ x (EuclideanSpace.single a 1)

def configurationRealLaplacian {n : ℕ} (φ : Configuration n → ℝ)
    (x : Configuration n) : ℝ :=
  ∑ a, configurationRealPartial (configurationRealPartial φ a) a x

theorem configurationRealPartial_C1 {n : ℕ} {φ : Configuration n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (a : Fin n × Fin 3) :
    ContDiff ℝ 1 (configurationRealPartial φ a) :=
  (hφ.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const

theorem weakH1_laplacian_pairing (hdensity : PublishedSobolevSmoothDensity)
    {n : ℕ} (φ : Configuration n → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hpartial : ∀ a, MemLp (configurationRealPartial φ a) 2)
    (hlap : MemLp (configurationRealLaplacian φ) 2)
    (v : Coulomb.H1Vector n) (s : SpinConfiguration n) :
    (∑ a, ∫ x, v.gradient s a x*(configurationRealPartial φ a x : ℂ)) =
      -(∫ x, v.value s x*(configurationRealLaplacian φ x : ℂ)) := by
  let G (a : Fin n × Fin 3) : Lp ℂ 2 (volume : Measure (Configuration n)) :=
    (hpartial a).ofReal.toLp (fun x => (configurationRealPartial φ a x : ℂ))
  let L : Lp ℂ 2 (volume : Measure (Configuration n)) :=
    hlap.ofReal.toLp (fun x => (configurationRealLaplacian φ x : ℂ))
  have hpair (w : Coulomb.H1Vector n) (a : Fin n × Fin 3) :
      inner ℂ (G a) (h1Coordinates w (Sum.inr (s,a))) =
        ∫ x, w.gradient s a x*(configurationRealPartial φ a x : ℂ) :=
    h1_inner_real_coordinate w (Sum.inr (s,a)) _ (hpartial a)
  have hlpair (w : Coulomb.H1Vector n) :
      inner ℂ L (h1Coordinates w (Sum.inl s)) =
        ∫ x, w.value s x*(configurationRealLaplacian φ x : ℂ) :=
    h1_inner_real_coordinate w (Sum.inl s) _ hlap
  have hcompact (w : Coulomb.H1Vector n)
      (hw : ∀ t, ContDiff ℝ 1 (w.value t) ∧ HasCompactSupport (w.value t))
      (hd : ∀ t a x, w.gradient t a x =
        fderiv ℝ (w.value t) x (EuclideanSpace.single a 1)) :
      (∑ a, inner ℂ (G a) (h1Coordinates w (Sum.inr (s,a)))) =
        -inner ℂ L (h1Coordinates w (Sum.inl s)) := by
    have hi (a : Fin n × Fin 3) : Integrable (fun x => w.value s x*
        (configurationRealPartial (configurationRealPartial φ a) a x : ℂ)) :=
      ((hw s).1.continuous.mul (Complex.continuous_ofReal.comp
        (((configurationRealPartial_C1 hφ a).continuous_fderiv (by norm_num)).clm_apply
          continuous_const))).integrable_of_hasCompactSupport (hw s).2.mul_right
    have he (a : Fin n × Fin 3) :
        (∫ x, w.gradient s a x*(configurationRealPartial φ a x : ℂ)) =
          -(∫ x, w.value s x*
            (configurationRealPartial (configurationRealPartial φ a) a x : ℂ)) := by
      have hc := configurationRealPartial_C1 hφ a
      have hdcast (x : Configuration n) :
          fderiv ℝ (fun y => (configurationRealPartial φ a y : ℂ)) x
            (EuclideanSpace.single a 1) =
          (configurationRealPartial (configurationRealPartial φ a) a x : ℂ) := by
        exact congrArg (fun B : Configuration n →L[ℝ] ℂ => B (EuclideanSpace.single a 1))
          (Complex.ofRealCLM.hasFDerivAt.comp x (hc.differentiable (by norm_num) x).hasFDerivAt).fderiv
      have hh := complex_C1_compact_test_ibp (fun x => (configurationRealPartial φ a x : ℂ))
        (w.value s) (Complex.ofRealCLM.contDiff.comp hc) (hw s).1 (hw s).2
          (EuclideanSpace.single a 1)
      simpa only [hd,hdcast,mul_comm] using hh
    simp only [hpair,hlpair]
    simp_rw [he]
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [← integral_finsetSum Finset.univ (fun a _ => hi a)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [configurationRealLaplacian,Complex.ofReal_sum,Finset.mul_sum]
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
