import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367
namespace ContinuousModification

variable {T Ω : Type*}

def sampledLimit (q : T → ℕ → T) (F : T → Ω → ℝ) (t : T) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => F (q t n) ω)

theorem sampledLimit_congr {q : T → ℕ → T} {F G : T → Ω → ℝ}
    {t : T} {ω ω' : Ω} (h : ∀ n, F (q t n) ω = G (q t n) ω') :
    sampledLimit q F t ω = sampledLimit q G t ω' := by
  unfold sampledLimit
  congr 1
  exact funext h

theorem measurable_sampledLimit [MeasurableSpace T] [MeasurableSpace Ω]
    {q : T → ℕ → T} {F : T → Ω → ℝ}
    (hF : ∀ n, Measurable (fun z : T × Ω => F (q z.1 n) z.2)) :
    Measurable (fun z : T × Ω => sampledLimit q F z.1 z.2) := by
  exact (StronglyMeasurable.limUnder (fun n => (hF n).stronglyMeasurable)).measurable

theorem measurable_sampledLimit_at [MeasurableSpace Ω]
    {q : T → ℕ → T} {F : T → Ω → ℝ} (t : T)
    (hF : ∀ n, Measurable (F (q t n))) : Measurable (sampledLimit q F t) := by
  exact (StronglyMeasurable.limUnder (fun n => (hF n).stronglyMeasurable)).measurable

theorem ae_all_eq_of_continuous_modification [TopologicalSpace T] [MeasurableSpace Ω]
    {μ : Measure Ω} {q : T → ℕ → T} {F G : T → Ω → ℝ}
    {S : Set T} (hS : S.Countable)
    (hqS : ∀ t n, q t n ∈ S)
    (hq : ∀ t, Tendsto (q t) atTop (𝓝 t))
    (hFG : ∀ s ∈ S, F s =ᵐ[μ] G s)
    (hG : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω)) :
    ∀ᵐ ω ∂μ, ∀ t, sampledLimit q F t ω = G t ω := by
  let : Countable S := hS.to_subtype
  have hEq : ∀ᵐ ω ∂μ, ∀ s : S, F s ω = G s ω :=
    ae_all_iff.mpr (fun s => hFG s s.property)
  filter_upwards [hEq, hG] with ω hEqω hGω
  intro t
  have hseq : (fun n => F (q t n) ω) = (fun n => G (q t n) ω) :=
    funext (fun n => hEqω ⟨q t n, hqS t n⟩)
  unfold sampledLimit
  rw [hseq]
  exact ((hGω.tendsto t).comp (hq t)).limUnder_eq

theorem ae_continuous_sampledLimit [TopologicalSpace T] [MeasurableSpace Ω]
    {μ : Measure Ω} {q : T → ℕ → T} {F G : T → Ω → ℝ}
    {S : Set T} (hS : S.Countable)
    (hqS : ∀ t n, q t n ∈ S)
    (hq : ∀ t, Tendsto (q t) atTop (𝓝 t))
    (hFG : ∀ s ∈ S, F s =ᵐ[μ] G s)
    (hG : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω)) :
    ∀ᵐ ω ∂μ, Continuous (fun t => sampledLimit q F t ω) := by
  filter_upwards [ae_all_eq_of_continuous_modification hS hqS hq hFG hG, hG]
    with ω hEq hGω
  simpa only [hEq] using hGω

theorem sampledLimit_equivariant {I : Type*} {q : T → ℕ → T}
    (F : I → T → Ω → ℝ) (a : Ω → Ω) (e : I → I)
    (hF : ∀ i t n ω, F i (q t n) (a ω) = F (e i) (q t n) ω) :
    ∀ i t ω, sampledLimit q (F i) t (a ω) = sampledLimit q (F (e i)) t ω := by
  intro i t ω
  exact sampledLimit_congr (fun n => hF i t n ω)

theorem ae_all_eq_family [TopologicalSpace T] [MeasurableSpace Ω]
    {I : Type*} [Countable I] {μ : Measure Ω} {q : T → ℕ → T}
    {F G : I → T → Ω → ℝ} {S : Set T} (hS : S.Countable)
    (hqS : ∀ t n, q t n ∈ S)
    (hq : ∀ t, Tendsto (q t) atTop (𝓝 t))
    (hFG : ∀ i s, s ∈ S → F i s =ᵐ[μ] G i s)
    (hG : ∀ i, ∀ᵐ ω ∂μ, Continuous (fun t => G i t ω)) :
    ∀ᵐ ω ∂μ, ∀ i t, sampledLimit q (F i) t ω = G i t ω := by
  apply ae_all_iff.mpr
  intro i
  exact ae_all_eq_of_continuous_modification hS hqS hq (hFG i) (hG i)

theorem isStronglyProgressive_sampledLimit [Preorder T] [MeasurableSpace T]
    [mΩ : MeasurableSpace Ω] (ℱ : Filtration T mΩ)
    {q : T → ℕ → T} {F : T → Ω → ℝ}
    (hF : ∀ n, IsStronglyProgressive ℱ (fun t ω => F (q t n) ω)) :
    IsStronglyProgressive ℱ (sampledLimit q F) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  exact StronglyMeasurable.limUnder (fun n => hF n t)

def dyadicLeft (t : ℝ) (n : ℕ) : ℝ := (⌊(2 : ℝ)^n * t⌋ : ℤ) / (2 : ℝ)^n

theorem dyadicLeft_le (t : ℝ) (n : ℕ) : dyadicLeft t n ≤ t := by
  unfold dyadicLeft
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^n)).2
  simpa only [mul_comm] using Int.floor_le ((2 : ℝ)^n * t)

theorem sub_inv_pow_le_dyadicLeft (t : ℝ) (n : ℕ) :
    t - ((2 : ℝ)^n)⁻¹ ≤ dyadicLeft t n := by
  have hp : (0 : ℝ) < 2^n := by positivity
  unfold dyadicLeft
  apply (le_div_iff₀ hp).2
  have hfloor := Int.lt_floor_add_one ((2 : ℝ)^n * t)
  have hinv : ((2 : ℝ)^n)⁻¹ * (2 : ℝ)^n = 1 := inv_mul_cancel₀ hp.ne'
  nlinarith

theorem dyadicLeft_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ dyadicLeft t n := by
  unfold dyadicLeft
  exact div_nonneg (Int.cast_nonneg (Int.floor_nonneg.mpr (by positivity))) (by positivity)

theorem tendsto_dyadicLeft (t : ℝ) : Tendsto (dyadicLeft t) atTop (𝓝 t) := by
  have hinv : Tendsto (fun n : ℕ => ((2 : ℝ)^n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlow : Tendsto (fun n : ℕ => t - ((2 : ℝ)^n)⁻¹) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (sub_inv_pow_le_dyadicLeft t) (dyadicLeft_le t)

theorem dyadicLeft_mem_rationals (t : ℝ) (n : ℕ) :
    dyadicLeft t n ∈ Set.range (fun r : ℚ => (r : ℝ)) := by
  refine ⟨(⌊(2 : ℝ)^n * t⌋ : ℚ) / (2 : ℚ)^n, ?_⟩
  simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat, dyadicLeft]

theorem measurable_dyadic_sample [MeasurableSpace Ω] {F : ℝ → Ω → ℝ}
    (hF : ∀ t, Measurable (F t)) (n : ℕ) :
    Measurable (fun z : ℝ × Ω => F (dyadicLeft z.1 n) z.2) := by
  have hstep : Measurable (fun z : ℤ × Ω => F ((z.1 : ℝ) / (2 : ℝ)^n) z.2) :=
    measurable_from_prod_countable_right (fun k => hF ((k : ℝ) / (2 : ℝ)^n))
  exact hstep.comp (((measurable_const.mul measurable_fst).floor).prodMk measurable_snd)

theorem isProgressive_dyadic_sample [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ mΩ) {F : ℝ → Ω → ℝ}
    (hF : Adapted ℱ F) (n : ℕ) :
    IsProgressive ℱ (fun t ω => F (dyadicLeft t n) ω) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  have hstep : Measurable
      (fun z : ℤ × Ω => F (min ((z.1 : ℝ) / (2 : ℝ)^n) t) z.2) :=
    measurable_from_prod_countable_right (fun k => by
      exact (hF (min ((k : ℝ) / (2 : ℝ)^n) t)).mono
        (ℱ.mono (min_le_right _ _)) le_rfl)
  have hfloor : Measurable
      (fun z : Set.Iic t × Ω => (⌊(2 : ℝ)^n * (z.1 : ℝ)⌋, z.2)) :=
    ((measurable_const.mul (measurable_subtype_coe.comp measurable_fst)).floor).prodMk
      measurable_snd
  have heq : (fun z : Set.Iic t × Ω => F (dyadicLeft (z.1 : ℝ) n) z.2) =
      (fun z : Set.Iic t × Ω => F (min (dyadicLeft (z.1 : ℝ) n) t) z.2) := by
    funext z
    rw [min_eq_left ((dyadicLeft_le (z.1 : ℝ) n).trans z.1.property)]
  rw [heq]
  exact hstep.comp hfloor

theorem isStronglyProgressive_dyadicLimit [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ mΩ) {F : ℝ → Ω → ℝ} (hF : Adapted ℱ F) :
    IsStronglyProgressive ℱ (sampledLimit dyadicLeft F) :=
  isStronglyProgressive_sampledLimit ℱ
    (fun n => (isProgressive_dyadic_sample ℱ hF n).isStronglyProgressive)

theorem measurable_dyadicLimit [MeasurableSpace Ω] {F : ℝ → Ω → ℝ}
    (hF : ∀ t, Measurable (F t)) :
    Measurable (fun z : ℝ × Ω => sampledLimit dyadicLeft F z.1 z.2) :=
  measurable_sampledLimit (measurable_dyadic_sample hF)

theorem ae_all_dyadicLimit_eq [MeasurableSpace Ω] {μ : Measure Ω}
    {F G : ℝ → Ω → ℝ}
    (hFG : ∀ r : ℚ, F (r : ℝ) =ᵐ[μ] G (r : ℝ))
    (hG : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω)) :
    ∀ᵐ ω ∂μ, ∀ t, sampledLimit dyadicLeft F t ω = G t ω := by
  apply ae_all_eq_of_continuous_modification
    (Set.countable_range (fun r : ℚ => (r : ℝ))) dyadicLeft_mem_rationals tendsto_dyadicLeft
    ?_ hG
  rintro s ⟨r, rfl⟩
  exact hFG r

end ContinuousModification
end Problem367

end

end OAI
