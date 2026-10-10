import OAI.Probability.PosteriorReplicas.Gaussian.MatrixNoise
import OAI.Probability.PosteriorReplicas.Measures.EqualBaseMeasures

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def equalApprox {d k m : ℕ} (base : BaseLaw) (n : ℕ)
    (H : EqualSpace d k m → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ A, ∫⁻ u : Tuple d m,
    matrixNoiseDensity m k n (fun i => labels A (u i.succ) - labels A (u 0)) *
      H (A, labels A (u 0), u) ∂Measure.pi (fun _ => base.measure d) ∂gaussianRows d k

def smoothedTail {d k m : ℕ} (base : BaseLaw) (n : ℕ)
    (H : EqualSpace d k m → ℝ≥0∞) (A : Rows d k) (p : Vec d) : ℝ≥0∞ :=
  ∫⁻ v : Fin m → Vec d, matrixNoiseDensity m k n (fun i => labels A (v i) - labels A p) *
    H (A, labels A p, Fin.cons p v) ∂Measure.pi (fun _ => base.measure d)

lemma equalApprox_cons {d k m : ℕ} [NeZero d] (base : BaseLaw) (n : ℕ)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    equalApprox base n H = ∫⁻ A, ∫⁻ p, smoothedTail base n H A p
      ∂base.measure d ∂gaussianRows d k := by
  unfold equalApprox smoothedTail
  apply lintegral_congr
  intro A
  rw [lintegral_pi_cons (base.measure d) (by fun_prop)]
  simp only [Fin.cons_succ, Fin.cons_zero]

lemma smoothedTail_representation {d k m : ℕ} {A : Rows d k}
    (hA : LinearIndependent ℝ A) (hk : k < d) (base : BaseLaw) (n : ℕ)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) (p : Vec d) :
    smoothedTail base n H A p =
      ∫⁻ z, ∫⁻ R, (∏ i, baseDensity base A (labels A p + noiseScale n • z i)) *
        H (A, labels A p, Fin.cons p
          (fun i => basePoint base A (labels A p + noiseScale n • z i) (R i)))
        ∂gaussianRows d m ∂matrixNormal m k := by
  unfold smoothedTail
  rw [base_pi_lintegral hA hk base (by fun_prop)]
  simp_rw [labels_basePoint hA]
  have hrw (y : Fin m → Labels k) :
      (∏ i, baseDensity base A (y i)) *
        (∫⁻ R, matrixNoiseDensity m k n (fun i => y i - labels A p) *
          H (A, labels A p, Fin.cons p (fun i => basePoint base A (y i) (R i)))
          ∂gaussianRows d m) =
      matrixNoiseDensity m k n (y - fun _ => labels A p) *
        ((∏ i, baseDensity base A (y i)) *
          ∫⁻ R, H (A, labels A p, Fin.cons p (fun i => basePoint base A (y i) (R i)))
          ∂gaussianRows d m) := by
    rw [lintegral_const_mul _ (by fun_prop)]
    ac_rfl
  simp_rw [hrw]
  rw [matrixNoise_convolution (fun _ => labels A p) (by fun_prop)]
  apply lintegral_congr
  intro z
  rw [lintegral_const_mul _ (by fun_prop)]
  rfl

lemma smoothedTail_bound {d k m : ℕ} {A : Rows d k}
    (hA : LinearIndependent ℝ A) (hk : k + 2 < d) (base : BaseLaw) (n : ℕ)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H)
    (b : ℝ≥0∞) (hHb : ∀ x, H x ≤ b) (p : Vec d) :
    smoothedTail base n H A p ≤
      ENNReal.ofReal (baseProjectionConstant base d k / Real.sqrt (rowGram A).det)^m * b := by
  rw [smoothedTail_representation hA (by omega) base n hH p]
  calc
    _ ≤ ∫⁻ z, ∫⁻ R, ENNReal.ofReal
        (baseProjectionConstant base d k / Real.sqrt (rowGram A).det)^m * b
        ∂gaussianRows d m ∂matrixNormal m k := by
      apply lintegral_mono
      intro z
      apply lintegral_mono
      intro R
      apply mul_le_mul' _ (hHb _)
      simpa using Finset.prod_le_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
        baseDensity_le_sup (by omega) base A (labels A p + noiseScale n • z i))
    _ = _ := by simp

lemma smoothedTail_limit {d k m : ℕ} {A : Rows d k}
    (hA : LinearIndependent ℝ A) (hk : k + 2 < d) (base : BaseLaw)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Continuous H)
    (b : ℝ≥0∞) (hb : b ≠ ∞) (hHb : ∀ x, H x ≤ b) (p : Vec d) :
    Tendsto (fun n => smoothedTail base n H A p) atTop
      (nhds (baseDensity base A (labels A p)^m *
        ∫⁻ R, H (A, labels A p, Fin.cons p
          (fun i => basePoint base A (labels A p) (R i))) ∂gaussianRows d m)) := by
  let B := ENNReal.ofReal (baseProjectionConstant base d k / Real.sqrt (rowGram A).det)^m * b
  have hfin : B ≠ ∞ := ENNReal.mul_ne_top (by finiteness) hb
  have hbound (n) (z : (Fin m → Labels k) × Rows d m) :
      (∏ i, baseDensity base A (labels A p + noiseScale n • z.1 i)) *
        H (A, labels A p, Fin.cons p
          (fun i => basePoint base A (labels A p + noiseScale n • z.1 i) (z.2 i))) ≤ B := by
    apply mul_le_mul' _ (hHb _)
    simpa using Finset.prod_le_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
      baseDensity_le_sup (by omega) base A (labels A p + noiseScale n • z.1 i))
  have hlim := tendsto_lintegral_of_dominated_convergence
    (μ := (matrixNormal m k).prod (gaussianRows d m)) (fun _ => B)
    (F := fun n z => (∏ i, baseDensity base A (labels A p + noiseScale n • z.1 i)) *
        H (A, labels A p, Fin.cons p
          (fun i => basePoint base A (labels A p + noiseScale n • z.1 i) (z.2 i))))
    (f := fun z => baseDensity base A (labels A p)^m *
        H (A, labels A p, Fin.cons p (fun i => basePoint base A (labels A p) (z.2 i))))
    (fun _ => by fun_prop)
    (fun n => Filter.Eventually.of_forall (hbound n))
    (by simpa using hfin)
    (by
      apply Filter.Eventually.of_forall
      intro z
      have hy (i : Fin m) : Tendsto (fun n => labels A p + noiseScale n • z.1 i) atTop
          (nhds (labels A p)) := by
        simpa using tendsto_const_nhds.add (tendsto_noiseScale.smul_const (z.1 i))
      have hprod : Tendsto (fun n => ∏ i, baseDensity base A (labels A p + noiseScale n • z.1 i)) atTop
          (nhds (baseDensity base A (labels A p)^m)) := by
        simpa using ENNReal.tendsto_finsetProd_of_ne_top Finset.univ
          (fun i _ => (continuous_baseDensity hk base hA).tendsto (labels A p) |>.comp (hy i))
          (fun i _ => (baseDensity_lt_top base A (labels A p)).ne)
      apply ENNReal.Tendsto.mul hprod (Or.inr (ne_top_of_le_ne_top hb (hHb _)))
      · apply hH.tendsto _ |>.comp
        apply tendsto_const_nhds.prodMk_nhds
        apply tendsto_const_nhds.prodMk_nhds
        apply tendsto_const_nhds.finCons
        apply tendsto_pi_nhds.mpr
        intro i
        exact (continuous_basePoint_label base A (z.2 i)).tendsto (labels A p) |>.comp (hy i)
      · exact Or.inr (by finiteness [baseDensity_lt_top base A (labels A p)]))
  have he (n) : smoothedTail base n H A p =
      ∫⁻ z : (Fin m → Labels k) × Rows d m,
        (∏ i, baseDensity base A (labels A p + noiseScale n • z.1 i)) *
          H (A, labels A p, Fin.cons p
            (fun i => basePoint base A (labels A p + noiseScale n • z.1 i) (z.2 i)))
        ∂(matrixNormal m k).prod (gaussianRows d m) := by
    rw [smoothedTail_representation hA (by omega) base n hH.measurable p,
      lintegral_prod _ (by fun_prop)]
  simp_rw [he]
  convert hlim using 1
  rw [lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [lintegral_const_mul _ (show Measurable (fun R : Rows d m =>
    H (A, labels A p, Fin.cons p (fun i => basePoint base A (labels A p) (R i)))) by fun_prop)]

lemma equalApprox_left_limit {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Continuous H)
    (b : ℝ≥0∞) (hb : b ≠ ∞) (hHb : ∀ x, H x ≤ b) :
    Tendsto (fun n => equalApprox base n H) atTop
      (nhds (∫⁻ z, H z ∂leftBaseMeasure d k m base)) := by
  have : NeZero d := ⟨by omega⟩
  have hAe : ∀ᵐ z ∂(gaussianRows d k).prod (base.measure d), LinearIndependent ℝ z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_gaussian_rows_full_rank (by omega) (by omega))
  have he (n) : equalApprox base n H =
      ∫⁻ z : Rows d k × Vec d, smoothedTail base n H z.1 z.2
        ∂(gaussianRows d k).prod (base.measure d) := by
    rw [equalApprox_cons base n hH.measurable, lintegral_prod _ (by unfold smoothedTail; fun_prop)]
  simp_rw [he]
  rw [leftBaseMeasure_lintegral base hH.measurable]
  have hf_meas : Measurable (fun z : Rows d k × Vec d =>
      baseDensity base z.1 (labels z.1 z.2)^m *
        ∫⁻ R, H (z.1, labels z.1 z.2,
          Fin.cons z.2 (fun i => basePoint base z.1 (labels z.1 z.2) (R i)))
          ∂gaussianRows d m) := by fun_prop
  rw [← lintegral_prod _ hf_meas.aemeasurable]
  apply tendsto_lintegral_of_dominated_convergence
    (fun z : Rows d k × Vec d =>
      ENNReal.ofReal (baseProjectionConstant base d k / Real.sqrt (rowGram z.1).det)^m * b)
  · intro n
    unfold smoothedTail
    fun_prop
  · intro n
    filter_upwards [hAe] with z hz
    exact smoothedTail_bound hz (by omega) base n hH.measurable b hHb z.2
  · rw [lintegral_prod _ (by fun_prop)]
    simp only [lintegral_const, measure_univ, mul_one]
    rw [lintegral_mul_const _ (by fun_prop)]
    exact ENNReal.mul_ne_top (base_density_sup_moment_finite hd hk base).ne hb
  · filter_upwards [hAe] with z hz
    exact smoothedTail_limit hz (by omega) base hH b hb hHb z.2

end PosteriorReplicas
end

end OAI
