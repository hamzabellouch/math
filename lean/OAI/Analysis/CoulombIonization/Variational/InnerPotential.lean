import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoulombTestCharge
import OAI.Analysis.CoulombIonization.Variational.BoundedDensityPotential

namespace OAI

open MeasureTheory Set Metric Laplacian
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

 def sourcePotential (mu : Measure Space) (y : Space) : ℝ :=
    ∫ a, (‖y-a‖)⁻¹ ∂mu

 lemma inner_source_separation {h d : ℝ} {a y : Space}
    (ha : ‖a‖ ≤ h) (hy : h+d ≤ ‖y‖) : d ≤ ‖y-a‖ := by
  have := norm_le_norm_sub_add y a
  linarith

 lemma source_kernel_integrable (mu : Measure Space) [IsFiniteMeasure mu]
    {h d : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) (hd : 0 < d) {y : Space}
    (hy : h+d ≤ ‖y‖) : Integrable (fun a => (‖y-a‖)⁻¹) mu := by
  apply (integrable_const (d⁻¹)).mono' (by fun_prop)
  filter_upwards [hs] with a ha
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_anti₀ hd (inner_source_separation ha hy)

 lemma sourcePotential_nonneg (mu : Measure Space) (y : Space) :
    0 ≤ sourcePotential mu y := integral_nonneg (fun _ => inv_nonneg.mpr (norm_nonneg _))

 lemma sourcePotential_le (mu : Measure Space) [IsFiniteMeasure mu]
    {h d : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) (hd : 0 < d) {y : Space}
    (hy : h+d ≤ ‖y‖) : sourcePotential mu y ≤ (mu Set.univ).toReal/d := by
  calc
    _ ≤ ∫ _a, d⁻¹ ∂mu := integral_mono_ae (source_kernel_integrable mu hs hd hy)
          (integrable_const _) (hs.mono (fun a ha => inv_anti₀ hd (inner_source_separation ha hy)))
    _ = _ := by simp only [integral_const,smul_eq_mul,Measure.real,div_eq_mul_inv]

 lemma sourcePotential_difference (mu : Measure Space) [IsFiniteMeasure mu]
    {h d : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) (hd : 0 < d) {y z : Space}
    (hy : h+d ≤ ‖y‖) (hz : h+d ≤ ‖z‖) :
    |sourcePotential mu y-sourcePotential mu z| ≤
      ((mu Set.univ).toReal/d^2)*‖y-z‖ := by
  have hi := source_kernel_integrable mu hs hd hy
  have hj := source_kernel_integrable mu hs hd hz
  have hb : ∀ᵐ a ∂mu, ‖(‖y-a‖)⁻¹-(‖z-a‖)⁻¹‖ ≤ ‖y-z‖/d^2 := by
    filter_upwards [hs] with a ha
    have hya := inner_source_separation ha hy
    have hza := inner_source_separation ha hz
    have hn1 : a ≠ y := by intro he; subst a; simp only [sub_self,norm_zero] at hya; linarith
    have hn2 : a ≠ z := by intro he; subst a; simp only [sub_self,norm_zero] at hza; linarith
    have hiy := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg (y-a))) (inv_anti₀ hd hya) 2
    have hiz := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg (z-a))) (inv_anti₀ hd hza) 2
    rw [Real.norm_eq_abs]
    calc _ ≤ ‖y-z‖*((‖y-a‖)⁻¹^2+(‖z-a‖)⁻¹^2)/2 := coulomb_inv_difference hn1 hn2
         _ ≤ ‖y-z‖*(d⁻¹^2+d⁻¹^2)/2 := by gcongr
         _ = _ := by ring
  have hh := norm_integral_le_of_norm_le (integrable_const (‖y-z‖/d^2) :
    Integrable (fun _ : Space => ‖y-z‖/d^2) mu) hb
  rw [integral_sub hi hj,Real.norm_eq_abs] at hh
  calc
    _ ≤ ∫ _a : Space, ‖y-z‖/d^2 ∂mu := hh
    _ = _ := by simp only [integral_const,Measure.real,smul_eq_mul]; ring

 lemma sourcePotential_lipschitzOn (mu : Measure Space) [IsFiniteMeasure mu]
    {h d : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) (hd : 0 < d) :
    LipschitzOnWith ⟨(mu Set.univ).toReal/d^2,by positivity⟩ (sourcePotential mu)
      {y | h+d ≤ ‖y‖} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  change dist (sourcePotential mu y) (sourcePotential mu z) ≤
    ((mu univ).toReal/d^2)*dist y z
  simpa only [dist_eq_norm,Real.norm_eq_abs] using
    sourcePotential_difference mu hs hd hy hz

 lemma sourcePotential_continuousOn_exterior (mu : Measure Space) [IsFiniteMeasure mu]
    {h : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) :
    ContinuousOn (sourcePotential mu) {y | h < ‖y‖} := by
  intro y hy
  change h < ‖y‖ at hy
  have hd : 0 < (‖y‖-h)/2 := by linarith [hy]
  have hnb : {z : Space | h+(‖y‖-h)/2 ≤ ‖z‖} ∈ 𝓝 y :=
    Filter.mem_of_superset
      (continuous_norm.continuousAt.preimage_mem_nhds
        (Ioi_mem_nhds (show h+(‖y‖-h)/2 < ‖y‖ by linarith [hy])))
      (fun z hz => show h+(‖y‖-h)/2 ≤ ‖z‖ from hz.le)
  exact ((sourcePotential_lipschitzOn mu hs hd).continuousOn.continuousAt hnb).continuousWithinAt

 lemma sourcePotential_pairing_integrable (mu : Measure Space) [IsFiniteMeasure mu]
    {h d : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) (hd : 0 < d)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ {y | h+d ≤ ‖y‖}) :
    Integrable (fun p : Space × Space => (‖p.2-p.1‖)⁻¹*Δ g p.2)
      (mu.prod volume) := by
  have hi : Integrable (Δ g) := (tfLaplacian_continuous hg).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg)
  apply ((integrable_const (d⁻¹) : Integrable (fun _ : Space => d⁻¹) mu).mul_prod hi.norm).mono'
    (by have hc := tfLaplacian_continuous hg; fun_prop)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (by have hc := tfLaplacian_continuous hg; fun_prop)
    (by have hc := tfLaplacian_continuous hg; fun_prop))).mpr
  filter_upwards [hs] with a ha
  apply ae_of_all
  intro y
  rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  by_cases hz : Δ g y = 0
  · simp only [hz,norm_zero,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right
      (inv_anti₀ hd (inner_source_separation ha (hsg (tfLaplacian_support hg hz)))) (norm_nonneg _)

 lemma sourcePotential_weak_harmonic_separated (mu : Measure Space) [IsFiniteMeasure mu]
    {h d : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) (hd : 0 < d)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ {y | h+d ≤ ‖y‖}) :
    (∫ y, sourcePotential mu y*Δ g y) = 0 := by
  have hf := sourcePotential_pairing_integrable mu hs hd hg hcg hsg
  have he : (∫ y, sourcePotential mu y*Δ g y) =
      ∫ a, ∫ y, (‖y-a‖)⁻¹*Δ g y ∂volume ∂mu := by
    simp only [sourcePotential,← integral_mul_const]
    exact (integral_integral_swap hf).symm
  rw [he]
  apply integral_eq_zero_of_ae
  filter_upwards [hs] with a ha
  have hga : g a = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hh : h+d ≤ ‖a‖ := hsg hm
    linarith
  have hh := tfPotential_laplacian hg hcg a
  change (∫ y, Δ g y/‖a-y‖) = _ at hh
  simpa [norm_sub_rev,div_eq_mul_inv,mul_comm,hga] using hh

 lemma compact_exterior_separated {K : Set Space} (hK : IsCompact K) {h : ℝ}
    (hs : K ⊆ {y | h < ‖y‖}) : ∃ d > 0, K ⊆ {y | h+d ≤ ‖y‖} := by
  rcases K.eq_empty_or_nonempty with he | hn
  · exact ⟨1,by norm_num,by simp [he]⟩
  obtain ⟨y,hy,hmin⟩ := hK.exists_isMinOn hn continuous_norm.continuousOn
  refine ⟨‖y‖-h,sub_pos.mpr (hs hy),?_⟩
  intro z hz
  change h+(‖y‖-h) ≤ ‖z‖
  simp only [add_sub_cancel]
  exact hmin hz

 theorem sourcePotential_weak_harmonic_exterior (mu : Measure Space) [IsFiniteMeasure mu]
    {h : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ {y | h < ‖y‖}) :
    (∫ y, sourcePotential mu y*Δ g y) = 0 := by
  obtain ⟨d,hd,hdg⟩ := compact_exterior_separated hcg hsg
  exact sourcePotential_weak_harmonic_separated mu hs hd hg hcg hdg

end CoulombAtom

end

end OAI
