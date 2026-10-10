import Mathlib
import OAI.Probability.GaussianInformation.Kernel.Entropy

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Coercivity
open _root_.OAI.KernelPotential.Geometry Sphere

lemma inverse_kernel_bound {d n q : ℕ} (μ : Measure (Ambient d)) [IsProbabilityMeasure μ]
    {C : ℝ} (hC : 0 ≤ C) (hq : 0 < q) (hqn : q+1 ≤ n)
    (hball : ∀ s r, 0 < r → μ (ball s r) ≤ ENNReal.ofReal (C*r^n)) (s : Ambient d) :
    (∫⁻ u, (ENNReal.ofReal ‖u-s‖)⁻¹^q ∂μ) ≤ ENNReal.ofReal (1+C*2^(n+q+1)) := by
  have ht : ∀ j : ℕ, μ {u | ‖u-s‖ ≤ (1/2:ℝ)^j} ≤
      ENNReal.ofReal (C*2^n)*ENNReal.ofReal ((1/2:ℝ)^((q+1)*j)) := by
    intro j
    calc
      _ ≤ μ (ball s (2*(1/2:ℝ)^j)) := measure_mono (by
        intro u hu
        change dist u s < _
        rw [dist_eq_norm]
        have hp : 0 < (1/2:ℝ)^j := by positivity
        change ‖u-s‖ ≤ (1/2:ℝ)^j at hu
        linarith)
      _ ≤ ENNReal.ofReal (C*(2*(1/2:ℝ)^j)^n) := hball _ _ (by positivity)
      _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow, ← mul_assoc, Nat.mul_comm (q+1) j, pow_mul]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_of_le_one (by positivity : 0 ≤ (1/2:ℝ)^j) (pow_le_one₀ (by norm_num) (by norm_num)) hqn
  have h := inverseMoment_extended_of_tails μ (fun u => ‖u-s‖)
    (measurable_id.sub_const s).norm (fun u => norm_nonneg _) q hq
    (ENNReal.ofReal (C*2^n)) ENNReal.ofReal_ne_top ht
  apply h.trans_eq
  rw [measure_univ, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  congr 1
  rw [mul_assoc, ← pow_add]
  congr 3

lemma integral_square_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x,f x ∂μ)^2 ≤ ∫⁻ x,(f x)^2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (p := (2:ℝ)) (q := (2:ℝ)) (Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩)
    hf.aemeasurable (measurable_const (a := (1:ℝ≥0∞))).aemeasurable
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_one,measure_univ] at h
  have H := pow_le_pow_left₀ zero_le h 2
  simpa only [← ENNReal.rpow_natCast, Nat.cast_ofNat, ← ENNReal.rpow_mul,
    show (1/(2:ℝ))*(2:ℝ)=1 by norm_num,ENNReal.rpow_one] using H

lemma measurable_kernel {d q : ℕ} :
    Measurable (fun x : Ambient d × Ambient d => (ENNReal.ofReal ‖x.1-x.2‖)⁻¹^q) :=
  ((measurable_fst.sub measurable_snd).norm.ennreal_ofReal.inv).pow_const q

lemma measurable_J {d : ℕ} (ν : Measure (Ambient d)) [SFinite ν] : Measurable (J ν) := by
  unfold J
  apply Measurable.lintegral_prod_right
  exact ((measurable_snd.sub measurable_fst).norm.ennreal_ofReal.inv).pow_const _

lemma J_square_integral {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] :
    (∫⁻ s,(J ν s)^2 ∂sphereProbability d) ≤
      ENNReal.ofReal (1+(9*3^d:ℝ)*2^((d-1)+4*(d/16)+1)) := by
  have hk : 0 < d/16 := Nat.div_pos (by omega) (by norm_num)
  calc
    _ ≤ ∫⁻ s,∫⁻ u, ((ENNReal.ofReal ‖u-s‖)⁻¹^(2*(d/16)))^2 ∂ν ∂sphereProbability d := by
      apply lintegral_mono
      intro s
      exact integral_square_le ν _ (((measurable_id.sub_const s).norm.ennreal_ofReal.inv).pow_const _)
    _ = ∫⁻ u,∫⁻ s, (ENNReal.ofReal ‖u-s‖)⁻¹^(4*(d/16)) ∂sphereProbability d ∂ν := by
      simp_rw [← pow_mul, show 2*(d/16)*2=4*(d/16) by omega]
      exact lintegral_lintegral_swap (measurable_kernel.comp measurable_swap).aemeasurable
    _ ≤ ∫⁻ u, ENNReal.ofReal (1+(9*3^d:ℝ)*2^((d-1)+4*(d/16)+1)) ∂ν := by
      apply lintegral_mono
      intro u
      simp_rw [norm_sub_rev u]
      exact inverse_kernel_bound (sphereProbability d) (by positivity) (by omega)
        (by omega) (fun s r hr => cap_bound (by omega) s hr) u
    _ = _ := by simp

lemma bounded_density_representation {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • μ) :
    ∃ f : α → ℝ, Measurable f ∧ (∀ x,0 ≤ f x) ∧ (∀ x,f x ≤ H) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (f x)) := by
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
  have hr : ν.rnDeriv μ ≤ᵐ[μ] fun _ => ENNReal.ofReal H := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν μ)
    intro s hs _
    calc
      _ ≤ ν s := Measure.setLIntegral_rnDeriv_le s
      _ ≤ (ENNReal.ofReal H • μ) s := hν s
      _ = _ := by simp [Measure.smul_apply]
  let f : α → ℝ := fun x => min H (ν.rnDeriv μ x).toReal
  refine ⟨f,measurable_const.min (Measure.measurable_rnDeriv ν μ).ennreal_toReal,
    fun x => le_min hH.le ENNReal.toReal_nonneg,fun x => min_le_left _ _,?_⟩
  rw [← Measure.withDensity_rnDeriv_eq ν μ hac]
  apply withDensity_congr_ae
  filter_upwards [hr] with x hx
  dsimp [f]
  have hxt : ν.rnDeriv μ x ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  have hxH : (ν.rnDeriv μ x).toReal ≤ H := by
    exact (ENNReal.toReal_le_toReal hxt ENNReal.ofReal_ne_top).mpr hx |>.trans_eq (ENNReal.toReal_ofReal hH.le)
  rw [min_eq_right hxH, ENNReal.ofReal_toReal hxt]

lemma bounded_J {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) :
    J ν s ≤ ENNReal.ofReal (H*(1+(9*3^d:ℝ)*2^((d-1)+2*(d/16)+1))) := by
  have hk : 0 < d/16 := Nat.div_pos (by omega) (by norm_num)
  calc
    J ν s ≤ ∫⁻ u,(ENNReal.ofReal ‖u-s‖)⁻¹^(2*(d/16)) ∂(ENNReal.ofReal H • sphereProbability d) :=
      lintegral_mono' hν (le_refl _)
    _ = ENNReal.ofReal H * J (sphereProbability d) s := by rw [J,lintegral_smul_measure,smul_eq_mul]
    _ ≤ ENNReal.ofReal H * ENNReal.ofReal (1+(9*3^d:ℝ)*2^((d-1)+2*(d/16)+1)) := by
      gcongr
      exact inverse_kernel_bound (sphereProbability d) (by positivity) (by omega)
        (by omega) (fun s r hr => cap_bound (by omega) s hr) s
    _ = _ := (ENNReal.ofReal_mul hH.le).symm

lemma lower_J_on_sphere {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν, ‖u‖=1) (s : Ambient d) (hs : ‖s‖=1) :
    ENNReal.ofReal ((1/2:ℝ)^(2*(d/16))) ≤ J ν s := by
  calc
    _ = ∫⁻ u, ENNReal.ofReal ((1/2:ℝ)^(2*(d/16))) ∂ν := by simp
    _ ≤ J ν s := by
      apply lintegral_mono_ae
      filter_upwards [hν] with u hu
      have hn : ‖u-s‖ ≤ 2 := by calc
        ‖u-s‖ ≤ ‖u‖+‖s‖ := norm_sub_le _ _
        _ = 2 := by rw [hu,hs]; norm_num
      rw [ENNReal.ofReal_pow (by norm_num),show ENNReal.ofReal (1/2:ℝ)=(ENNReal.ofReal (2:ℝ))⁻¹ by rw [one_div,ENNReal.ofReal_inv_of_pos (by norm_num)]]
      exact pow_le_pow_left₀ zero_le (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hn)) _

lemma integrable_log_of_bounds {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {a b : ℝ} (ha : 0 < a)
    (hbound : ∀ᵐ x ∂μ, a ≤ f x ∧ f x ≤ b) : Integrable (fun x => Real.log (f x)) μ := by
  apply Integrable.mono' (integrable_const (|Real.log a|+|Real.log b|)) hf.log.aestronglyMeasurable
  filter_upwards [hbound] with x hx
  have hl := Real.log_le_log ha hx.1
  have hu := Real.log_le_log (ha.trans_le hx.1) hx.2
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hh := neg_abs_le (Real.log a)
    have hb0 := abs_nonneg (Real.log b)
    linarith
  · have hh := le_abs_self (Real.log b)
    have ha0 := abs_nonneg (Real.log a)
    linarith

lemma J_real_bounds {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1) :
    (1/2:ℝ)^(2*(d/16)) ≤ (J ν s).toReal ∧
      (J ν s).toReal ≤ H*(1+(9*3^d:ℝ)*2^((d-1)+2*(d/16)+1)) := by
  have hu := bounded_J hd ν hH hν s
  have ht := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hnorm : ∀ᵐ u ∂ν, ‖u‖=1 := (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega))
  have hl := lower_J_on_sphere ν hnorm s hs
  constructor
  · convert ENNReal.toReal_mono ht hl using 1
    rw [ENNReal.toReal_ofReal (by positivity)]
  · convert ENNReal.toReal_mono ENNReal.ofReal_ne_top hu using 1
    rw [ENNReal.toReal_ofReal (by positivity)]

lemma integrable_log_J {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (hν : BoundedDensity ν) (μ : Measure (Ambient d))
    [IsFiniteMeasure μ] (hμ : ∀ᵐ s ∂μ, ‖s‖=1) :
    Integrable (fun s => Real.log (J ν s).toReal) μ := by
  obtain ⟨H,hH,hνH⟩ := hν
  apply integrable_log_of_bounds μ _ (measurable_J ν).ennreal_toReal (by positivity : 0 < (1/2:ℝ)^(2*(d/16)))
  filter_upwards [hμ] with s hs
  exact J_real_bounds hd ν hH hνH s hs

open EntropySupport

lemma density_integral_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {H : ℝ} (hfH : ∀ x,f x ≤ H)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    ∫ x,f x ∂μ = 1 := by
  have hif := integrable_bounded_measurable μ f hf (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfH x)
  have h := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (f x)))
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hif (ae_of_all _ hf0)] at h
  exact ENNReal.ofReal_eq_one.mp h

lemma density_entropy_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {H : ℝ} (hfH : ∀ x,f x ≤ H)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    0 ≤ ∫ x,xlog (f x) ∂μ := by
  have hif := integrable_bounded_measurable μ f hf (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfH x)
  have hix := integrable_xlog_bounded μ f hf hf0 hfH
  have h := integral_mono (hif.sub (integrable_const 1)) hix
    (fun x => Real.self_sub_one_le_mul_log (hf0 x))
  change (∫ x,f x-1 ∂μ) ≤ _ at h
  rw [integral_sub hif (integrable_const 1),density_integral_one μ f hf hf0 hfH] at h
  simpa using h

lemma entropy_young {f j M : ℝ} (hf : 0 ≤ f) (hj : 0 < j) (hM : 0 < M) :
    2*f*Real.log j ≤ xlog f+f*(Real.log M-1)+j^2/M := by
  have h := xlog_lower_tangent hf (div_pos (sq_pos_of_pos hj) hM)
  have hl : Real.log (j^2/M) = 2*Real.log j-Real.log M := by
    rw [Real.log_div (pow_ne_zero _ hj.ne') hM.ne',Real.log_pow]; norm_num
  dsimp [xlog] at h ⊢
  rw [hl] at h
  nlinarith

noncomputable def sphereMoment (d : ℕ) : ℝ := 1+(9*3^d:ℝ)*2^((d-1)+4*(d/16)+1)
lemma sphereMoment_pos (d : ℕ) : 0 < sphereMoment d := by dsimp [sphereMoment]; positivity

lemma square_integrable_bound {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (hν : BoundedDensity ν) :
    Integrable (fun s => (J ν s).toReal^2) (sphereProbability d) ∧
      (∫ s,(J ν s).toReal^2 ∂sphereProbability d) ≤ sphereMoment d := by
  have hb := J_square_integral hd ν
  have ht : (∫⁻ s,(J ν s)^2 ∂sphereProbability d) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hm := (measurable_J ν).pow_const 2
  obtain ⟨H,hH,hνH⟩ := hν
  have hp : ∀ s,(J ν s)^2 < ∞ := fun s =>
    ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (bounded_J hd ν hH hνH s)))
  constructor
  · simpa only [ENNReal.toReal_pow] using integrable_toReal_of_lintegral_ne_top hm.aemeasurable ht
  · have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    change _ ≤ (ENNReal.ofReal (sphereMoment d)).toReal at hh
    rw [ENNReal.toReal_ofReal (sphereMoment_pos d).le] at hh
    simpa only [← ENNReal.toReal_pow, integral_toReal hm.aemeasurable (ae_of_all _ hp)] using hh

lemma Phi_density_formula {d : ℕ} (hd : 16 ≤ d) (f : Ambient d → ℝ)
    (hf : Measurable f) (hf0 : ∀ x,0 ≤ f x) {H : ℝ} (hfH : ∀ x,f x ≤ H)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (hν : BoundedDensity ν)
    (heq : ν = (sphereProbability d).withDensity (fun x => ENNReal.ofReal (f x))) :
    Phi ν = ∫ s, xlog (f s)-f s*Real.log (J ν s).toReal ∂sphereProbability d := by
  have : IsProbabilityMeasure ((sphereProbability d).withDensity (fun x => ENNReal.ofReal (f x))) := heq ▸ inferInstance
  have hix := integrable_xlog_bounded (sphereProbability d) f hf hf0 hfH
  have hil := integrable_log_J hd ν hν (sphereProbability d) (ae_unit_norm (by omega))
  have hib := hil.bdd_mul hf.aestronglyMeasurable (ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 x)]; exact hfH x))
  have hD : (InformationTheory.klDiv ν (sphereProbability d)).toReal = ∫ s,xlog (f s) ∂sphereProbability d := by
    rw [heq,klDiv_withDensity_bounded _ f hf hf0 hfH,
      ENNReal.toReal_ofReal (density_entropy_nonneg _ f hf hf0 hfH)]
  have hB : B ν = ∫ s,f s*Real.log (J ν s).toReal ∂sphereProbability d := by
    unfold B
    nth_rw 1 [heq]
    rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hf0 _),smul_eq_mul]
  rw [Phi,hD,hB,integral_sub hix hib]

lemma B_entropy_bound {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (hν : BoundedDensity ν) :
    2*B ν ≤ (InformationTheory.klDiv ν (sphereProbability d)).toReal+Real.log (sphereMoment d) := by
  obtain ⟨H,hH,hνH⟩ := hν
  obtain ⟨f,hf,hf0,hfH,heq⟩ := bounded_density_representation (sphereProbability d) ν hH hνH
  have : IsProbabilityMeasure ((sphereProbability d).withDensity (fun x => ENNReal.ofReal (f x))) := heq ▸ inferInstance
  have hif := integrable_bounded_measurable (sphereProbability d) f hf
    (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfH x)
  have hix := integrable_xlog_bounded (sphereProbability d) f hf hf0 hfH
  have hil := integrable_log_J hd ν ⟨H,hH,hνH⟩ (sphereProbability d) (ae_unit_norm (by omega))
  have hib := hil.bdd_mul hf.aestronglyMeasurable (ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 x)]; exact hfH x))
  obtain ⟨hij,hijbound⟩ := square_integrable_bound hd ν ⟨H,hH,hνH⟩
  have hpoint : ∀ᵐ s ∂sphereProbability d,
      2*(f s*Real.log (J ν s).toReal) ≤
        xlog (f s)+f s*(Real.log (sphereMoment d)-1)+(J ν s).toReal^2/sphereMoment d := by
    filter_upwards [ae_unit_norm (by omega : 0 < d)] with s hs
    have hj := (J_real_bounds hd ν hH hνH s hs).1
    have hjpos : 0 < (J ν s).toReal := lt_of_lt_of_le (by positivity) hj
    simpa only [mul_assoc] using entropy_young (hf0 s) hjpos (sphereMoment_pos d)
  have h := integral_mono_ae (hib.const_mul 2)
    ((hix.add (hif.mul_const _)).add (hij.div_const _)) hpoint
  change (∫ s,2*(f s*Real.log (J ν s).toReal) ∂sphereProbability d) ≤
    (∫ s,xlog (f s)+f s*(Real.log (sphereMoment d)-1)+(J ν s).toReal^2/sphereMoment d ∂sphereProbability d) at h
  rw [integral_const_mul,integral_add (f := fun s => xlog (f s)+f s*(Real.log (sphereMoment d)-1))
      (g := fun s => (J ν s).toReal^2/sphereMoment d) (hix.add (hif.mul_const _)) (hij.div_const _),
    integral_add hix (hif.mul_const (Real.log (sphereMoment d)-1)),integral_mul_const,integral_div,
    density_integral_one _ f hf hf0 hfH,one_mul] at h
  have hrat : (∫ s,(J ν s).toReal^2 ∂sphereProbability d)/sphereMoment d ≤ 1 :=
    (div_le_one (sphereMoment_pos d)).mpr hijbound
  have hD : (InformationTheory.klDiv ν (sphereProbability d)).toReal = ∫ s,xlog (f s) ∂sphereProbability d := by
    rw [heq,klDiv_withDensity_bounded _ f hf hf0 hfH,
      ENNReal.toReal_ofReal (density_entropy_nonneg _ f hf hf0 hfH)]
  have hB : B ν = ∫ s,f s*Real.log (J ν s).toReal ∂sphereProbability d := by
    unfold B
    nth_rw 1 [heq]
    rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hf0 _),smul_eq_mul]
  rw [hD,hB]
  linarith

lemma log_sphereMoment_le {d : ℕ} (hd : 16 ≤ d) : Real.log (sphereMoment d) ≤ 20*d := by
  let e := (d-1)+4*(d/16)+1
  have he : e ≤ 2*d := by dsimp [e]; omega
  have heR : (e:ℝ) ≤ 2*d := by exact_mod_cast he
  have hdR : (16:ℝ) ≤ d := by exact_mod_cast hd
  have h3 : (1:ℝ) ≤ 3^d := one_le_pow₀ (by norm_num)
  have h2 : (1:ℝ) ≤ 2^e := one_le_pow₀ (by norm_num)
  have hQ : (1:ℝ) ≤ 9*3^d*2^e := by nlinarith
  have hM : sphereMoment d ≤ 18*3^d*2^e := by dsimp [sphereMoment,e] at *; nlinarith
  have hl := Real.log_le_log (sphereMoment_pos d) hM
  have heq : Real.log (18*3^d*2^e:ℝ) = Real.log 18+(d:ℝ)*Real.log 3+(e:ℝ)*Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow]
  rw [heq] at hl
  have hl18 : Real.log (18:ℝ) ≤ 17 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 18)]
  have hl3 : Real.log (3:ℝ) ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)]
  have hl2 : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have he0 : (0:ℝ) ≤ e := Nat.cast_nonneg e
  nlinarith [mul_le_mul_of_nonneg_left hl3 (Nat.cast_nonneg d),mul_le_mul_of_nonneg_left hl2 he0]

lemma coercivity {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (hν : BoundedDensity ν) :
    (1/2:ℝ)*(InformationTheory.klDiv ν (sphereProbability d)).toReal-10*d ≤ Phi ν := by
  have h := B_entropy_bound hd ν hν
  have hl := log_sphereMoment_le hd
  unfold Phi
  linarith

lemma Phi_uniform_le {d : ℕ} (hd : 16 ≤ d) :
    Phi (sphereProbability d) ≤ (2*(d/16):ℕ)*Real.log 2 := by
  have hσ : BoundedDensity (sphereProbability d) := ⟨1,by norm_num,by simp⟩
  have hil := integrable_log_J hd (sphereProbability d) hσ (sphereProbability d) (ae_unit_norm (by omega))
  have hl : ∀ᵐ s ∂sphereProbability d,
      -((2*(d/16):ℕ):ℝ)*Real.log 2 ≤ Real.log (J (sphereProbability d) s).toReal := by
    filter_upwards [ae_unit_norm (by omega : 0 < d)] with s hs
    have hlow := (J_real_bounds hd (sphereProbability d) (by norm_num : (0:ℝ) < 1) (by simp) s hs).1
    have h := Real.log_le_log (by positivity : 0 < (1/2:ℝ)^(2*(d/16))) hlow
    rw [Real.log_pow,Real.log_div one_ne_zero (by norm_num),Real.log_one,zero_sub] at h
    simpa only [mul_neg,neg_mul] using h
  have h := integral_mono_ae (integrable_const (-((2*(d/16):ℕ):ℝ)*Real.log 2)) hil hl
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at h
  rw [Phi,InformationTheory.klDiv_self,ENNReal.toReal_zero,zero_sub]
  change -B (sphereProbability d) ≤ _
  change _ ≤ B (sphereProbability d) at h
  linarith

end Coercivity
end KernelPotential

end OAI
