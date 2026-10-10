import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphDual
import OAI.Analysis.PlanarEndpoint.GraphScaling
import OAI.Analysis.PlanarEndpoint.SpatialGrid
import OAI.Analysis.PlanarEndpoint.SpatialOrthogonal
import OAI.Analysis.PlanarEndpoint.TimeSeparation

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace PlanarEndpoint
attribute [local instance] Classical.propDecidable

lemma scaled_cutoff_annular {χ : Plane → ℂ} {c₀ C₀ N : ℝ} (hN : 0 < N)
    (hs : ∀ ξ ∈ tsupport χ, c₀ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀) :
    ∀ ξ : Plane, ξ ∉ {ξ | c₀*N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀*N} → χ (N⁻¹ • ξ) = 0 := by
  intro ξ hξ
  by_contra hne
  have hh := hs (N⁻¹ • ξ) (subset_tsupport χ (by exact hne))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)] at hh
  have he : N⁻¹*‖ξ‖*N=‖ξ‖ := by field_simp
  apply hξ
  constructor
  · have := mul_le_mul_of_nonneg_right hh.1 hN.le
    simpa only [he] using this
  · have := mul_le_mul_of_nonneg_right hh.2 hN.le
    simpa only [he] using this

lemma real_univ_finsetSum {ι : Type*} [Fintype ι] (μ : ι → Measure Plane)
    [∀ i, IsFiniteMeasure (μ i)] : (∑ i, μ i).real univ = ∑ i, (μ i).real univ := by
  simp only [measureReal_def, ← Measure.sum_fintype, Measure.sum_apply _ MeasurableSet.univ,
    tsum_fintype]
  exact ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)

lemma graphLp_congr_measure (χ : Plane → ℂ) (hχ : MemLp χ 2 volume)
    {μ ν : Measure Plane} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ = ν)
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) :
    graphLp χ hχ μ T w hT hw hb = graphLp χ hχ ν T w hT hw hb := by
  subst ν
  rfl

lemma graph_spatial_bound_of_shortTime {c₀ C₀ p : ℝ} (hp : 2 < p) (hC₀ : 0 < C₀)
    (hshort : ShortTimeWeakEstimate c₀ C₀ p)
    (χ : Plane → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hann : ∀ ξ ∈ tsupport χ, c₀ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀)
    (B : ℝ) (hB : 0 ≤ B) (hχB : ∀ ξ, ‖χ ξ‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ l : ℕ, ∀ (N r : ℝ) (hN : 0 < N), 0 < r → N*r=(2:ℝ)^l →
      ∀ (x₀ : Plane) (t₀ s : ℝ), 0 ≤ s → s ≤ r/N →
      ∀ (E : Set Plane), MeasurableSet E → E ⊆ Metric.ball x₀ 1 →
      ∀ (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
      (hb : ∀ x, ‖w x‖ ≤ 1), (∀ x ∈ E, T x ∈ Icc t₀ (t₀+s)) →
      ∀ [IsFiniteMeasure (volume.restrict E)],
      ‖graphLp (fun ξ => χ (N⁻¹ • ξ)) (scaled_cutoff_memLp χ hχ.continuous hc hN)
        (volume.restrict E) T w hT hw hb‖^2 ≤
        C*((2:ℝ)^l)^(2/3:ℝ)*volume.real E := by
  obtain ⟨Cb,hCb,hball⟩ := graph_ball_bound_of_shortTime hp hshort
  obtain ⟨Cf,hCf,hker⟩ := frequencyKernel_spatial_decay hC₀ hχ hc (fun ξ hξ => (hann ξ hξ).2) 4
  obtain ⟨K,hK⟩ := exists_nat_ge (4*C₀)
  let D : ℝ := Fintype.card (GridBox K)
  let A : ℝ := ∫ z, spatialDecay 1 z
  have hA : 0 ≤ A := integral_nonneg (spatialDecay_nonneg (N:=1))
  have hD : 0 ≤ D := Nat.cast_nonneg _
  refine ⟨D*Cb*B^2+Cf*A+1, by positivity, ?_⟩
  intro l N r hN hr hNr x₀ t₀ s hs hs' E hE hEB T w hT hw hb hTs inst
  let χN : Plane → ℂ := fun ξ => χ (N⁻¹ • ξ)
  have hχN := scaled_cutoff_memLp χ hχ.continuous hc hN
  have hχNm : Measurable χN := (hχ.continuous.comp (continuous_const_smul _)).measurable
  obtain ⟨M,hM⟩ := exists_nat_ge (1/r+1)
  let F : GridBox M → Set Plane := fun a => E ∩ gridCell x₀ r (fun i => (a i:ℤ))
  let μ : GridBox M → Measure Plane := fun a => volume.restrict (F a)
  have hFm (a : GridBox M) : MeasurableSet (F a) := hE.inter (measurableSet_gridCell _ _ _)
  have hfin : volume E ≠ ⊤ := isFiniteMeasure_restrict.mp inst
  let (a : GridBox M) : IsFiniteMeasure (μ a) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left))
  have hsum : ∑ a, μ a = volume.restrict E := (grid_restrict_eq_sum hr hM hE hEB).symm
  have hμ : (∑ a, μ a) ≤ volume := by rw [hsum]; exact Measure.restrict_le_self
  have hwindow : s ≤ r^2/((2:ℝ)^l) := by
    have he : r^2/((2:ℝ)^l) = r/N := by rw [← hNr]; field_simp
    rwa [he]
  have hbnd (a : GridBox M) : ‖graphLp χN hχN (μ a) T w hT hw hb‖^2 ≤
      Cb*B^2*((2:ℝ)^l)^(2/3:ℝ)*volume.real (F a) :=
    hball l N r hr hNr χN hχNm hχN B hB (fun ξ => hχB (N⁻¹ • ξ))
      (ae_of_all _ (scaled_cutoff_annular hN hann)) (gridCenter x₀ r (fun i => (a i:ℤ)))
      t₀ s hs hwindow (F a) (hFm a)
      (Set.inter_subset_right.trans (gridCell_in_ball hr _))
      T w hT hw hb (fun x hx => hTs x hx.1)
  have hgood (a : GridBox M) : ∀ᵐ x ∂μ a, x ∈ E ∧ x ∈ gridCell x₀ r (fun i => (a i:ℤ)) :=
    ae_restrict_mem (hFm a)
  have hfar (a b : GridBox M) (hab : ¬gridNear K a b) :
      ∀ᵐ z : Plane × Plane ∂(μ b).prod (μ a),
      ‖frequencyKernel χN (z.1-z.2) (T z.1-T z.2)‖ ≤ Cf*spatialDecay N (z.1-z.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hgood b),
      Measure.quasiMeasurePreserving_snd.ae (hgood a)] with z hz hy
    have hab' : ¬gridNear K b a := by
      intro h
      exact hab (fun i => by simpa only [abs_sub_comm] using h i)
    have hdist := grid_far_distance hr hab' hz.2 hy.2
    have ht1 := hTs z.1 hz.1
    have ht2 := hTs z.2 hy.1
    have htd : |T z.1-T z.2| ≤ r/N := (abs_le.mpr ⟨by linarith [ht1.1, ht2.2],by linarith [ht1.2, ht2.1]⟩).trans hs'
    have hg : 4*C₀*N*|T z.1-T z.2| ≤ ‖z.1-z.2‖ := by
      have hmul := mul_le_mul_of_nonneg_left htd (show 0 ≤ 4*C₀*N by positivity)
      have he : 4*C₀*N*(r/N)=4*C₀*r := by field_simp
      rw [he] at hmul
      exact hmul.trans ((mul_le_mul_of_nonneg_right hK hr.le).trans hdist)
    simpa only [spatialDecay, ← mul_div_assoc] using hker N hN (z.1-z.2) (T z.1-T z.2) hg
  have hh := graphPartition_near_far χN hχNm hχN μ hμ T w hT hw hb
    (D:=D) (gridNear K) (fun a b h i => by simpa only [abs_sub_comm] using h i)
    hCf hN (fun a => by dsimp only [D]; exact_mod_cast gridNear_degree K a) hfar
  rw [graphLp_congr_measure χN hχN hsum T w hT hw hb] at hh
  have hreal : (∑ a, μ a).real univ = volume.real E := by
    rw [hsum, measureReal_restrict_apply_univ]
  rw [hreal] at hh
  have hmass : ∑ a, volume.real (F a) = volume.real E := by
    calc
      _ = ∑ a, (μ a).real univ := by simp only [μ, measureReal_restrict_apply_univ]
      _ = (∑ a, μ a).real univ := (real_univ_finsetSum μ).symm
      _ = volume.real E := by rw [hsum, measureReal_restrict_apply_univ]
  have hsumB : (∑ a, ‖graphLp χN hχN (μ a) T w hT hw hb‖^2) ≤
      Cb*B^2*((2:ℝ)^l)^(2/3:ℝ)*volume.real E := by
    calc
      _ ≤ ∑ a, Cb*B^2*((2:ℝ)^l)^(2/3:ℝ)*volume.real (F a) :=
        Finset.sum_le_sum (fun a _ => hbnd a)
      _ = _ := by rw [← Finset.mul_sum, hmass]
  have hf : 1 ≤ ((2:ℝ)^l)^(2/3:ℝ) := Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by norm_num)
  have hm : 0 ≤ volume.real E := measureReal_nonneg
  have hbound := hh.trans (add_le_add (mul_le_mul_of_nonneg_left hsumB hD) le_rfl)
  change _ ≤ D*(Cb*B^2*((2:ℝ)^l)^(2/3:ℝ)*volume.real E)+Cf*A*volume.real E at hbound
  apply hbound.trans
  nlinarith [mul_le_mul_of_nonneg_right hf (mul_nonneg (mul_nonneg hCf hA) hm),
    mul_nonneg (Real.rpow_nonneg (by positivity) (2/3:ℝ)) hm]

end PlanarEndpoint
end

end OAI
