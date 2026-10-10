import OAI.MathematicalPhysics.Boltzmann.Branching.TruncatedExponential
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # Measurable local majorants pass to weak L1 limits -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.le_measurable {μ : Measure X} [SigmaFinite μ]
    {f : ℕ → X → ℝ} {g u : X → ℝ}
    (h : WeakL1Converges μ f g) (hfi : ∀ n, Integrable (f n) μ)
    (hum : Measurable u) (hle : ∀ n, f n ≤ᵐ[μ] u) : g ≤ᵐ[μ] u := by
  let D (n : ℕ) := spanningSets μ n ∩ {x | |u x| ≤ (n:ℝ)}
  have hD (n) : MeasurableSet (D n) :=
    (measurableSet_spanningSets μ n).inter (measurableSet_le hum.abs measurable_const)
  have hui (n) : IntegrableOn u (D n) μ := by
    have hf : μ (D n) < ⊤ := (measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ n)
    let : IsFiniteMeasure (μ.restrict (D n)) := isFiniteMeasure_restrict.mpr hf.ne
    apply (integrable_const (n:ℝ)).mono' hum.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (hD n)] with x hx
    simpa only [Real.norm_eq_abs] using (show |u x| ≤ (n:ℝ) from hx.2)
  have hh (n) : ∀ᵐ x ∂μ, x ∈ D n → g x ≤ u x :=
    h.le_on hfi (hD n) hum (hui n) (fun j => (hle j).mono (fun _ hx _ => hx))
  filter_upwards [ae_all_iff.mpr hh] with x hx
  have hmem : x ∈ ⋃ n : ℕ, spanningSets μ n := by rw [iUnion_spanningSets]; trivial
  obtain ⟨m,hm⟩ := mem_iUnion.mp hmem
  obtain ⟨k,hk⟩ := exists_nat_gt |u x|
  apply hx (max m k)
  exact ⟨spanningSets_mono (le_max_left _ _) hm,
    hk.le.trans (Nat.cast_le.mpr (le_max_right m k))⟩

theorem WeakL1Converges.le_on_measurable {μ : Measure X} [SigmaFinite μ]
    {f : ℕ → X → ℝ} {g u : X → ℝ}
    (h : WeakL1Converges μ f g) (hfi : ∀ n, Integrable (f n) μ)
    {s : Set X} (hs : MeasurableSet s) (hum : Measurable u)
    (hle : ∀ n, ∀ᵐ x ∂μ, x ∈ s → f n x ≤ u x) :
    ∀ᵐ x ∂μ, x ∈ s → g x ≤ u x := by
  apply (ae_restrict_iff' hs).mp
  exact (h.restrict hs).le_measurable (fun n => (hfi n).restrict) hum
    (fun n => (ae_restrict_iff' hs).mpr (hle n))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Pulling a weak L¹ limit back through a measure-preserving equivalence -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.comp_measurableEquiv {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) {f : ℕ → Y → ℝ} {g : Y → ℝ}
    (hf : ∀ n, Measurable (f n)) (h : WeakL1Converges ν f g) :
    WeakL1Converges μ (fun n => f n ∘ e) (g ∘ e) := by
  apply WeakL1Converges.of_comp_measurePreserving (MeasurePreserving.symm e he)
    (fun n => (hf n).comp e.measurable) (h.1.comp e.measurable)
  simpa only [Function.comp_def,MeasurableEquiv.apply_symm_apply] using h

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A convergent scalar coefficient in an integrable weak majorant -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem weakL1_affine {a b : X → ℝ} (ham : Measurable a) (hbm : Measurable b)
    (hai : Integrable a μ) (hbi : Integrable b μ) {c : ℕ → ℝ} {l : ℝ}
    (hc : Tendsto c atTop (𝓝 l)) :
    WeakL1Converges μ (fun n x => a x+c n*b x) (fun x => a x+l*b x) := by
  refine ⟨ham.add (hbm.const_mul l),hai.add (hbi.const_mul l),?_⟩
  intro ψ hψ hψb
  obtain ⟨C,hC⟩ := hψb
  have haψ : Integrable (fun x => ψ x*a x) μ :=
    hai.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have hbψ : Integrable (fun x => ψ x*b x) μ :=
    hbi.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have he (k : ℝ) : (∫ x, ψ x*(a x+k*b x) ∂μ) =
      (∫ x, ψ x*a x ∂μ)+k*(∫ x, ψ x*b x ∂μ) := by
    simp_rw [mul_add,show ∀ x, ψ x*(k*b x) = k*(ψ x*b x) by intro x; ring]
    rw [integral_add haψ (hbψ.const_mul k),integral_const_mul]
  simp_rw [he]
  exact tendsto_const_nhds.add (hc.mul_const _)

theorem WeakL1Converges.le_affine {f : ℕ → X → ℝ} {g a b : X → ℝ}
    (hg : WeakL1Converges μ f g) (hfi : ∀ n, Integrable (f n) μ)
    (ham : Measurable a) (hbm : Measurable b) (hai : Integrable a μ) (hbi : Integrable b μ)
    {c : ℕ → ℝ} {l : ℝ} (hc : Tendsto c atTop (𝓝 l))
    (hb : ∀ n, ∀ᵐ x ∂μ, f n x ≤ a x+c n*b x) :
    ∀ᵐ x ∂μ, g x ≤ a x+l*b x := by
  have h := ((weakL1_affine ham hbm hai hbi hc).sub hg
    (fun n => hai.add (hbi.const_mul (c n))) hfi).nonneg
    (fun n => (hb n).mono (fun x hx => sub_nonneg.mpr hx))
  exact h.mono (fun x hx => sub_nonneg.mp hx)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The half-Gaussian velocity moment bound passes to a weak density limit -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.velocity_moment {μ : Measure X} [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (h : WeakL1Converges (μ.prod volume) f g)
    (hfm : ∀ n, Measurable (f n)) (hfn : ∀ n p, 0 ≤ f n p) (hgn : ∀ p, 0 ≤ g p)
    (hfi : ∀ n, Integrable (f n) (μ.prod volume))
    {M : X → ℝ} (hMm : Measurable M) (hMi : Integrable M μ) (hMn : ∀ x, 0 ≤ M x)
    (hb : ∀ n, ∀ᵐ x ∂μ, VelocityMoment.moment (fun v => f n (x,v)) ≤ ENNReal.ofReal (M x)) :
    ∀ᵐ x ∂μ, VelocityMoment.moment (fun v => g (x,v)) ≤ ENNReal.ofReal (M x) := by
  have htrunc (k : ℕ) : ∀ᵐ x ∂μ,
      (∫ v, VelocityMoment.truncatedWeight k v*g (x,v)) ≤ M x := by
    let w : X × Velocity → ℝ := fun p => VelocityMoment.truncatedWeight k p.2
    have hwm : Measurable w := (VelocityMoment.truncatedWeight_measurable k).comp measurable_snd
    have hwb p : |w p| ≤ k := VelocityMoment.truncatedWeight_abs_le k p.2
    have hw := h.marginal hfi hwm k hwb
    apply hw.le
    · intro n
      exact ((hfi n).bdd_mul hwm.aestronglyMeasurable (ae_of_all _ hwb)).integral_prod_left
    · exact hMm
    · exact hMi
    · intro n
      filter_upwards [hb n] with x hx
      exact VelocityMoment.truncatedMoment_le
        ((hfm n).comp (measurable_const.prodMk measurable_id))
        (fun v => hfn n (x,v)) (hMn x) hx k
  filter_upwards [ae_all_iff.mpr htrunc,h.2.1.prod_right_ae] with x hx hi
  exact VelocityMoment.moment_le_of_truncated
    (h.1.comp (measurable_const.prodMk measurable_id)) hi (fun v => hgn (x,v)) hx

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Survival from a positive measure source and a bounded loss density -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem ae_survival_of_weak_balance {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C)
    {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hbound : ∀ᵐ t ∂volume, t ∈ Ioo a b → g t ≤ C*f t)
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ t, deriv ψ t*f t)+(∫ t, ψ t ∂μ)-(∫ t, ψ t*g t) = 0) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      Real.exp (C*(s-t))*f s ≤ f t := by
  let W := slabExponential a b C
  have hW := slabExponential_measurable a b C
  have hWb : ∀ t, |W t| ≤ Real.exp (C*b) := slabExponential_bound a b hC
  have hWn : ∀ t, 0 ≤ W t := slabExponential_nonneg a b C
  let F : ℝ → ℝ := fun t => W t*f t
  let r : ℝ → ℝ := fun t => W t*(C*f t-g t)
  have hF : Integrable F := hf.bdd_mul hW.aestronglyMeasurable (ae_of_all _ hWb)
  have hr : Integrable r := ((hf.const_mul C).sub hg).bdd_mul hW.aestronglyMeasurable
    (ae_of_all _ hWb)
  have hrn : ∀ᵐ t ∂volume, 0 ≤ r t := by
    filter_upwards [hbound] with t ht
    by_cases hmem : t ∈ Ioo a b
    · exact mul_nonneg (hWn t) (sub_nonneg.mpr (ht hmem))
    · simp only [r,W,slabExponential,indicator_of_notMem hmem,zero_mul,le_refl]
  let μw := positiveDensityMeasure μ W
  let ρ := positiveDensityMeasure volume r
  have hiW : Integrable W μ := (integrable_const (Real.exp (C*b))).mono'
    hW.aestronglyMeasurable (ae_of_all _ hWb)
  let _ : IsFiniteMeasure μw := positiveDensityMeasure_finite hiW (ae_of_all _ hWn)
  let _ : IsFiniteMeasure ρ := positiveDensityMeasure_finite hr hrn
  let ν := μw+ρ
  have hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ t, deriv ψ t*F t)+(∫ t, ψ t ∂ν) = 0 := by
    intro ψ hψ hψc hψs
    let θ : ℝ → ℝ := fun t => Real.exp (C*t)*ψ t
    have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := by dsimp only [θ]; fun_prop
    have hθc : HasCompactSupport θ := hψc.mul_left
    have hθs : tsupport θ ⊆ Ioo a b := tsupport_mul_subset_right.trans hψs
    have hθeq (t : ℝ) : θ t = ψ t*W t := slabExponential_test hψs t
    have hdθ (t : ℝ) : deriv θ t = deriv ψ t*W t+C*(ψ t*W t) :=
      slabExponential_test_derivative hψ hψs t
    obtain ⟨B,hB⟩ := hψ.continuous.bounded_above_of_compact_support hψc
    have hψμ : Integrable ψ μw := (integrable_const B).mono' hψ.continuous.aestronglyMeasurable
      (ae_of_all _ hB)
    have hψρ : Integrable ψ ρ := (integrable_const B).mono' hψ.continuous.aestronglyMeasurable
      (ae_of_all _ hB)
    have hd : Integrable (fun t => deriv θ t*f t) :=
      hf.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        (hθ.continuous_deriv (by simp)) hθc.deriv
    have hθg : Integrable (fun t => θ t*g t) :=
      hg.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hθ.continuous hθc
    have hDF : Integrable (fun t => deriv ψ t*F t) :=
      hF.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        (hψ.continuous_deriv (by simp)) hψc.deriv
    have hψr : Integrable (fun t => ψ t*r t) := hr.bdd_mul hψ.continuous.aestronglyMeasurable
      (ae_of_all _ hB)
    have he : (∫ t, deriv θ t*f t)-(∫ t, θ t*g t) =
        (∫ t, deriv ψ t*F t)+(∫ t, ψ t*r t) := by
      rw [← integral_sub hd hθg,← integral_add hDF hψr]
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by
        dsimp only
        rw [hdθ,hθeq]
        dsimp only [F,r]
        ring)
    have hμeq : (∫ t, θ t ∂μ) = ∫ t, ψ t*W t ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ hθeq
    have hh := hw θ hθ hθc hθs
    rw [hμeq] at hh
    change (∫ t, deriv ψ t*F t)+(∫ t, ψ t ∂(μw+ρ)) = 0
    rw [integral_add_measure hψμ hψρ]
    change (∫ t, deriv ψ t*F t)+
      ((∫ t, ψ t ∂positiveDensityMeasure μ W)+
        (∫ t, ψ t ∂positiveDensityMeasure volume r)) = 0
    rw [positiveDensityMeasure_integral hW.aemeasurable (ae_of_all _ hWn),
      positiveDensityMeasure_integral hr.aestronglyMeasurable.aemeasurable hrn]
    linarith only [he,hh]
  obtain ⟨c,htrace⟩ := ae_cumulative_balance hab hF.locallyIntegrable ν 0 (by
    intro ψ hψ hc hs
    simpa using hweak ψ hψ hc hs)
  filter_upwards [htrace] with s hs
  filter_upwards [htrace] with t ht
  intro hsa hta hst
  have hs' := hs hsa
  have ht' := ht hta
  simp only [cumulative,Measure.real,Measure.coe_zero,Pi.zero_apply,ENNReal.toReal_zero,sub_zero]
    at hs' ht'
  have hmono := cumulative_monotone ν hst
  have hst' : Real.exp (C*s)*f s ≤ Real.exp (C*t)*f t := by
    change W s*f s = _ at hs'
    change W t*f t = _ at ht'
    rw [show W s = Real.exp (C*s) from indicator_of_mem hsa _] at hs'
    rw [show W t = Real.exp (C*t) from indicator_of_mem hta _] at ht'
    change (ν (Iic s)).toReal ≤ (ν (Iic t)).toReal at hmono
    linarith only [hs',ht',hmono]
  calc
    _ = Real.exp (-C*t)*(Real.exp (C*s)*f s) := by
      rw [← mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-C*t)*(Real.exp (C*t)*f t) :=
      mul_le_mul_of_nonneg_left hst' (Real.exp_pos _).le
    _ = f t := by rw [← mul_assoc,← Real.exp_add]; simp

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
