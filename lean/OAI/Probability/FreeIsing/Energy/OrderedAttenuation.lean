import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367
namespace OrderedAttenuation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω}

theorem integral_mul_le_of_condExp_le [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {z g : Ω → ℝ} {r : ℝ}
    (hz : Integrable z μ) (hg : Integrable g μ)
    (hzg : Integrable (fun ω => z ω * g ω) μ)
    (hzm : AEStronglyMeasurable[m] z μ)
    (hz0 : ∀ᵐ ω ∂μ, 0 ≤ z ω)
    (hcond : ∀ᵐ ω ∂μ, (μ[g | m]) ω ≤ r) :
    (∫ ω, z ω * g ω ∂μ) ≤ r * (∫ ω, z ω ∂μ) := by
  have hpull := condExp_mul_of_aestronglyMeasurable_left hzm hzg hg
  have hprod : Integrable (fun ω => z ω * (μ[g | m]) ω) μ :=
    integrable_condExp.congr hpull
  calc
    (∫ ω, z ω * g ω ∂μ) = ∫ ω, (μ[z * g | m]) ω ∂μ :=
      (integral_condExp hm).symm
    _ = ∫ ω, z ω * (μ[g | m]) ω ∂μ := integral_congr_ae hpull
    _ ≤ ∫ ω, r * z ω ∂μ := by
      apply integral_mono_ae hprod (hz.const_mul r)
      filter_upwards [hz0, hcond] with ω hzω hcondω
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcondω hzω
    _ = r * (∫ ω, z ω ∂μ) := integral_const_mul _ _

theorem condExp_mul_le_of_condExp_le [IsFiniteMeasure μ]
    {mBase m : MeasurableSpace Ω} (hbase : mBase ≤ m) (hm : m ≤ mΩ)
    {z g : Ω → ℝ} {r : ℝ}
    (hz : Integrable z μ) (hg : Integrable g μ)
    (hzg : Integrable (fun ω => z ω * g ω) μ)
    (hzm : AEStronglyMeasurable[m] z μ)
    (hz0 : ∀ᵐ ω ∂μ, 0 ≤ z ω)
    (hcond : ∀ᵐ ω ∂μ, (μ[g | m]) ω ≤ r) :
    ∀ᵐ ω ∂μ, (μ[z * g | mBase]) ω ≤ r * (μ[z | mBase]) ω := by
  have hpull := condExp_mul_of_aestronglyMeasurable_left hzm hzg hg
  have hbound : (μ[z * g | m]) ≤ᵐ[μ] (fun ω => r * z ω) := by
    filter_upwards [hpull, hz0, hcond] with ω hp hzω hc
    rw [hp]
    simpa only [Pi.mul_apply, mul_comm] using mul_le_mul_of_nonneg_left hc hzω
  have hmono := condExp_mono (m := mBase) integrable_condExp (hz.const_mul r) hbound
  have htower := condExp_condExp_of_le (μ := μ) (f := z * g) hbase hm
  have hscale : (μ[(fun ω => r * z ω) | mBase]) =ᵐ[μ]
      (fun ω => r * (μ[z | mBase]) ω) := by
    change (μ[r • z | mBase]) =ᵐ[μ] r • (μ[z | mBase])
    exact condExp_smul r z mBase
  filter_upwards [hmono, htower, hscale] with ω hle heq hmul
  simpa only [heq, hmul] using hle

theorem product_integrable_and_bounds [IsFiniteMeasure μ]
    {g : ℕ → Ω → ℝ}
    (hg : ∀ i, AEMeasurable (g i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, g i ω ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    Integrable (fun ω => ∏ i ∈ Finset.range n, g i ω) μ ∧
      (∀ᵐ ω ∂μ, (∏ i ∈ Finset.range n, g i ω) ∈ Set.Icc (0 : ℝ) 1) := by
  have hbounds : ∀ᵐ ω ∂μ, (∏ i ∈ Finset.range n, g i ω) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [ae_all_iff.mpr hb] with ω hω
    exact ⟨Finset.prod_nonneg (fun i _hi => (hω i).1),
      Finset.prod_le_one₀ (fun i _hi => (hω i).1) (fun i _hi => (hω i).2)⟩
  have hmeas := Finset.aemeasurable_fun_prod (Finset.range n) (fun i _hi => hg i)
  exact ⟨Integrable.of_mem_Icc 0 1 hmeas hbounds, hbounds⟩

theorem integral_prod_le_prod [IsProbabilityMeasure μ]
    {g : ℕ → Ω → ℝ} {r : ℕ → ℝ}
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ i, m i ≤ mΩ)
    (hg : ∀ i, AEMeasurable (g i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, g i ω ∈ Set.Icc (0 : ℝ) 1)
    (hr : ∀ i, 0 ≤ r i)
    (hprev : ∀ n, AEStronglyMeasurable[m n]
      (fun ω => ∏ i ∈ Finset.range n, g i ω) μ)
    (hcond : ∀ n, ∀ᵐ ω ∂μ, (μ[g n | m n]) ω ≤ r n) (n : ℕ) :
    (∫ ω, ∏ i ∈ Finset.range n, g i ω ∂μ) ≤ ∏ i ∈ Finset.range n, r i := by
  have hprod := product_integrable_and_bounds hg hb
  induction n with
  | zero => simp
  | succ n ih =>
    have hn_nonneg : ∀ᵐ ω ∂μ, 0 ≤ ∏ i ∈ Finset.range n, g i ω :=
      (hprod n).2.mono fun _ h => h.1
    have hgn : Integrable (g n) μ := Integrable.of_mem_Icc 0 1 (hg n) (hb n)
    have hmul : Integrable (fun ω => (∏ i ∈ Finset.range n, g i ω) * g n ω) μ := by
      simpa only [Finset.prod_range_succ] using (hprod (n + 1)).1
    calc
      (∫ ω, ∏ i ∈ Finset.range (n + 1), g i ω ∂μ) =
          ∫ ω, (∏ i ∈ Finset.range n, g i ω) * g n ω ∂μ := by
        simp only [Finset.prod_range_succ]
      _ ≤ r n * (∫ ω, ∏ i ∈ Finset.range n, g i ω ∂μ) :=
        integral_mul_le_of_condExp_le (hm n) (hprod n).1 hgn hmul
          (hprev n) hn_nonneg (hcond n)
      _ ≤ r n * (∏ i ∈ Finset.range n, r i) := mul_le_mul_of_nonneg_left ih (hr n)
      _ = ∏ i ∈ Finset.range (n + 1), r i := by
        rw [Finset.prod_range_succ, mul_comm]

theorem integral_prod_le_pow [IsProbabilityMeasure μ]
    {g : ℕ → Ω → ℝ} {r : ℝ}
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ i, m i ≤ mΩ)
    (hg : ∀ i, AEMeasurable (g i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, g i ω ∈ Set.Icc (0 : ℝ) 1)
    (hr : 0 ≤ r)
    (hprev : ∀ n, AEStronglyMeasurable[m n]
      (fun ω => ∏ i ∈ Finset.range n, g i ω) μ)
    (hcond : ∀ n, ∀ᵐ ω ∂μ, (μ[g n | m n]) ω ≤ r) (n : ℕ) :
    (∫ ω, ∏ i ∈ Finset.range n, g i ω ∂μ) ≤ r ^ n := by
  simpa using integral_prod_le_prod m hm hg hb (fun _ => hr) hprev hcond n

theorem condExp_prod_le_prod [IsFiniteMeasure μ]
    {g : ℕ → Ω → ℝ} {r : ℕ → ℝ} {mBase : MeasurableSpace Ω}
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ i, m i ≤ mΩ)
    (hbase : ∀ i, mBase ≤ m i)
    (hg : ∀ i, AEMeasurable (g i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, g i ω ∈ Set.Icc (0 : ℝ) 1)
    (hr : ∀ i, 0 ≤ r i)
    (hprev : ∀ n, AEStronglyMeasurable[m n]
      (fun ω => ∏ i ∈ Finset.range n, g i ω) μ)
    (hcond : ∀ n, ∀ᵐ ω ∂μ, (μ[g n | m n]) ω ≤ r n) (n : ℕ) :
    ∀ᵐ ω ∂μ, (μ[(fun ω => ∏ i ∈ Finset.range n, g i ω) | mBase]) ω ≤
      ∏ i ∈ Finset.range n, r i := by
  have hprod := product_integrable_and_bounds hg hb
  induction n with
  | zero => simp [condExp_const ((hbase 0).trans (hm 0))]
  | succ n ih =>
    have hn_nonneg : ∀ᵐ ω ∂μ, 0 ≤ ∏ i ∈ Finset.range n, g i ω :=
      (hprod n).2.mono fun _ h => h.1
    have hgn : Integrable (g n) μ := Integrable.of_mem_Icc 0 1 (hg n) (hb n)
    have hmul : Integrable (fun ω => (∏ i ∈ Finset.range n, g i ω) * g n ω) μ := by
      simpa only [Finset.prod_range_succ] using (hprod (n + 1)).1
    have hstep := condExp_mul_le_of_condExp_le (hbase n) (hm n)
      (hprod n).1 hgn hmul (hprev n) hn_nonneg (hcond n)
    filter_upwards [hstep, ih] with ω hstepω hihω
    simp only [Finset.prod_range_succ]
    exact hstepω.trans (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hihω (hr n))

theorem one_sub_pow_le_exp {a : ℝ} (ha : a ≤ 1) (n : ℕ) :
    (1 - a) ^ n ≤ Real.exp (-a * (n : ℝ)) := by
  have he : 1 - a ≤ Real.exp (-a) := by
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-a)
  calc
    (1 - a) ^ n ≤ (Real.exp (-a)) ^ n := pow_le_pow_left₀ (sub_nonneg.mpr ha) he n
    _ = Real.exp (-a * (n : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem integral_prod_le_exp [IsProbabilityMeasure μ]
    {g : ℕ → Ω → ℝ} {a : ℝ} (ha : a ≤ 1)
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ i, m i ≤ mΩ)
    (hg : ∀ i, AEMeasurable (g i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, g i ω ∈ Set.Icc (0 : ℝ) 1)
    (hprev : ∀ n, AEStronglyMeasurable[m n]
      (fun ω => ∏ i ∈ Finset.range n, g i ω) μ)
    (hcond : ∀ n, ∀ᵐ ω ∂μ, (μ[g n | m n]) ω ≤ 1 - a) (n : ℕ) :
    (∫ ω, ∏ i ∈ Finset.range n, g i ω ∂μ) ≤ Real.exp (-a * (n : ℝ)) := by
  exact (integral_prod_le_pow m hm hg hb (sub_nonneg.mpr ha) hprev hcond n).trans
    (one_sub_pow_le_exp ha n)

theorem condExp_prod_le_exp [IsFiniteMeasure μ]
    {g : ℕ → Ω → ℝ} {a : ℝ} {mBase : MeasurableSpace Ω} (ha : a ≤ 1)
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ i, m i ≤ mΩ)
    (hbase : ∀ i, mBase ≤ m i)
    (hg : ∀ i, AEMeasurable (g i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, g i ω ∈ Set.Icc (0 : ℝ) 1)
    (hprev : ∀ n, AEStronglyMeasurable[m n]
      (fun ω => ∏ i ∈ Finset.range n, g i ω) μ)
    (hcond : ∀ n, ∀ᵐ ω ∂μ, (μ[g n | m n]) ω ≤ 1 - a) (n : ℕ) :
    ∀ᵐ ω ∂μ, (μ[(fun ω => ∏ i ∈ Finset.range n, g i ω) | mBase]) ω ≤
      Real.exp (-a * (n : ℝ)) := by
  have hp := condExp_prod_le_prod m hm hbase hg hb
    (fun _ => sub_nonneg.mpr ha) hprev hcond n
  filter_upwards [hp] with ω hω
  exact hω.trans (by simpa using one_sub_pow_le_exp ha n)

end OrderedAttenuation
end Problem367

end

end OAI
