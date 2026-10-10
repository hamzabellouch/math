import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ProductFrequencyTop

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma tsupport_intrinsicCorrectionF (g : SmoothMetric E M) (n Λ : ℝ) (u : M → ℝ) :
    tsupport (intrinsicCorrectionF g n Λ u) ⊆
      tsupport (fun x => laplaceBeltrami g u x+Λ*u x) := by
  apply closure_mono
  intro x hx hzero
  apply hx
  simp only [intrinsicCorrectionF,hzero,zero_div]

lemma intrinsic_corrections_eq_one_off_residual
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (g : SmoothMetric E M) (n Λ : ℝ)
    (hD : ∀ x, intrinsicCorrectionD g n u x ≠ 0) {x : M}
    (hx : x ∉ tsupport (fun x => laplaceBeltrami g u x+Λ*u x)) :
    intrinsicCorrectionB g n Λ u x=1 ∧ intrinsicCorrectionS g n Λ u x=1 := by
  have hxF : x ∉ tsupport (intrinsicCorrectionF g n Λ u) :=
    fun h => hx (tsupport_intrinsicCorrectionF g n Λ u h)
  have hF := image_eq_zero_of_notMem_tsupport hxF
  have hgrad := coordinateGradientPair_zero_off_support g (intrinsicCorrectionF g n Λ u) u hxF
  have hf := contMDiff_intrinsicCorrectionF hu g n Λ hD
  have hw := weightedLaplacian_expansion
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) g x
  simp only [hF,hgrad,zero_mul,zero_add] at hw
  simp only [intrinsicCorrectionB,intrinsicCorrectionS,hF,hw,zero_mul,mul_zero,
    sub_zero,and_self]

lemma tsupport_intrinsic_corrections_sub_one
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (g : SmoothMetric E M) (n Λ : ℝ)
    (hD : ∀ x, intrinsicCorrectionD g n u x ≠ 0) :
    tsupport (fun x => intrinsicCorrectionB g n Λ u x-1) ⊆
      tsupport (fun x => laplaceBeltrami g u x+Λ*u x) ∧
    tsupport (fun x => intrinsicCorrectionS g n Λ u x-1) ⊆
      tsupport (fun x => laplaceBeltrami g u x+Λ*u x) := by
  constructor <;> apply closure_minimal _ isClosed_closure <;> intro x hx <;> by_contra hn
  · exact hx (sub_eq_zero.mpr (intrinsic_corrections_eq_one_off_residual hu g n Λ hD hn).1)
  · exact hx (sub_eq_zero.mpr (intrinsic_corrections_eq_one_off_residual hu g n Λ hD hn).2)

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology

lemma eventual_scalar_correction_rate (L : ℝ) (P Q D : ℕ)
    (hD : P+Q+2 ≤ D) :
    ∀ᶠ n : ℕ in atTop,
      L*(n:ℝ)^Q/(n:ℝ)^D ≤ ((n:ℝ)⁻¹)^P := by
  have hb : ∀ᶠ n : ℕ in atTop, max 1 L ≤ (n:ℝ) :=
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop (max 1 L))
  filter_upwards [hb] with n hn
  have hn1 : 1 ≤ (n:ℝ) := (le_max_left 1 L).trans hn
  have hn0 : 0 < (n:ℝ) := zero_lt_one.trans_le hn1
  have hLn : L ≤ (n:ℝ) := (le_max_right 1 L).trans hn
  rw [inv_pow,← one_div,div_le_div_iff₀ (pow_pos hn0 D) (pow_pos hn0 P),one_mul]
  calc
    (L*(n:ℝ)^Q)*(n:ℝ)^P = L*(n:ℝ)^(P+Q) := by rw [pow_add]; ring
    _ ≤ (n:ℝ)*(n:ℝ)^(P+Q) := mul_le_mul_of_nonneg_right hLn (pow_nonneg hn0.le _)
    _ = (n:ℝ)^(P+Q+1) := by rw [pow_succ]; ring
    _ ≤ (n:ℝ)^D := pow_le_pow_right₀ hn1 (by omega)

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
theorem eventually_scalar_exactification
    (h B P D : ℕ) (hP : 0 < P) (hD : P+((2*B+21)*(h+2)+10)+2 ≤ D)
    {C : ℝ} (hC : 0 < C) (U W : ℕ → M → ℝ)
    (hU : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (U n))
    (hW : ∀ n x, 0 < W n x)
    (hdata : ∀ᶠ n : ℕ in atTop,
      (∀ x, W n x/(n:ℝ)^B ≤ |U n x|+
        Real.sqrt (coordinateGradientPair g (U n) (U n) x)/(n:ℝ)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h+2,
        ‖iteratedFDeriv ℝ j (U n ∘ (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*W n ((chartAt E (A.p i)).symm y)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h+1,
        ‖iteratedFDeriv ℝ j
          ((fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x) ∘
            (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*W n ((chartAt E (A.p i)).symm y))) :
    ∀ᶠ n : ℕ in atTop,
      let b := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n)
      let s := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n)
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s ∧
      (∀ x, 0 < b x ∧ 0 < s x) ∧
      (∀ x, weightedLaplacian g b (U n) x+sphereFrequency n*s x*U n x=0) ∧
      A.ChartJetBound h (fun x => ((b x-1:ℝ):ℂ)) (inverseFrequency n^P) ∧
      A.ChartJetBound h (fun x => ((s x-1:ℝ):ℂ)) (inverseFrequency n^P) ∧
      (∀ x, |b x-1|+|s x-1| ≤ inverseFrequency n^P) ∧
      (tsupport (fun x => b x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) ∧
      (tsupport (fun x => s x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) := by
  obtain ⟨L,hL,hbound⟩ := A.quantitative_intrinsic_correction_jets h B hC
  have hrate := eventual_scalar_correction_rate L P ((2*B+21)*(h+2)+10) D hD
  have hsmall := (inverseFrequency_pow_zero P (Nat.ne_of_gt hP)).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hdata,hrate,hsmall,eventually_ge_atTop 1] with n hn hr hsmall hn1
  have hn1' : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  have hn0 : 0 < (n:ℝ) := zero_lt_one.trans_le hn1'
  have hΛ : sphereFrequency n ≠ 0 := by unfold sphereFrequency; positivity
  have hden (x : M) : intrinsicCorrectionD g (n:ℝ) (U n) x ≠ 0 :=
    (intrinsicCorrectionD_pos g (U n) x hn0 (hW n x) (hn.1 x)).ne'
  obtain ⟨hb,hsmooth,heq⟩ := intrinsic_scalar_correction (hU n) g (n:ℝ)
    (sphereFrequency n) hΛ hden
  obtain ⟨hbj,hsj,habs⟩ := hbound (n:ℝ) hn1' D (U n) (hU n) (W n) (hW n)
    hn.1 hn.2.1 hn.2.2
  have hsupp := tsupport_intrinsic_corrections_sub_one (hU n) g (n:ℝ)
    (sphereFrequency n) hden
  refine ⟨hb,hsmooth,?_,heq,
    fun chart order horder point => (hbj chart order horder point).trans hr,
    fun chart order horder point => (hsj chart order horder point).trans hr,?_,hsupp⟩
  · intro x
    have hx := (habs x).trans hr
    have hbx : |intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n) x-1| < 1 := by
      have h := abs_nonneg (intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n) x-1)
      exact (le_add_of_nonneg_right h).trans_lt (hx.trans_lt hsmall)
    have hsx : |intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n) x-1| < 1 := by
      have h := abs_nonneg (intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n) x-1)
      exact (le_add_of_nonneg_left h).trans_lt (hx.trans_lt hsmall)
    constructor <;> linarith [(abs_lt.mp hbx).1,(abs_lt.mp hsx).1]
  · intro x
    exact (habs x).trans hr
end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff
lemma eventual_product_scalar_correction_rate (L : ℝ) (P Q D : ℕ)
    (hD : P+Q+2 ≤ D) :
    ∀ᶠ n : ℕ in atTop, L*productWaveFrequency n^Q/productWaveFrequency n^D ≤  inverseFrequency n^P := by
  have hb := productWaveFrequency_tendsto.eventually (eventually_ge_atTop (max 1 L))
  filter_upwards [hb,eventually_ge_atTop (1:ℕ)] with n hn hn1
  have hν1 : 1 ≤ productWaveFrequency n := (le_max_left _ _).trans hn
  have hν0 : 0<productWaveFrequency n := zero_lt_one.trans_le hν1
  have hLν : L ≤ productWaveFrequency n := (le_max_right _ _).trans hn
  have hratio : L*productWaveFrequency n^Q/productWaveFrequency n^D ≤ (productWaveFrequency n)⁻¹^P := by
    rw [inv_pow,←one_div,div_le_div_iff₀ (pow_pos hν0 D) (pow_pos hν0 P),one_mul]
    calc
      _ = L*productWaveFrequency n^(P+Q) := by rw [pow_add]; ring
      _  ≤  productWaveFrequency n*productWaveFrequency n^(P+Q) :=
        mul_le_mul_of_nonneg_right hLν (pow_nonneg hν0.le _)
      _ = productWaveFrequency n^(P+Q+1) := by rw [pow_succ]; ring
      _  ≤  _ := pow_le_pow_right₀ hν1 (by omega)
  exact hratio.trans (pow_le_pow_left₀ (inv_nonneg.mpr hν0.le)
    (inv_anti₀ (by exact_mod_cast (show 0<n by omega)) (productWaveFrequency_bounds hn1).1) P)
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E<2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)
omit [T2Space M] in
theorem eventually_product_scalar_exactification
    (h B P D : ℕ) (hP : 0 < P) (hD : P+((2*B+21)*(h+2)+10)+2  ≤  D)
    {C : ℝ} (hC : 0 < C) (U W : ℕ → M → ℝ)
    (hU : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (U n))
    (hW : ∀ n x, 0 < W n x)
    (hdata : ∀ᶠ n : ℕ in atTop,
      (∀ x, W n x/(productWaveFrequency n)^B  ≤  |U n x|+
        Real.sqrt (coordinateGradientPair g (U n) (U n) x)/(productWaveFrequency n)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j  ≤  h+2,
        ‖iteratedFDeriv ℝ j (U n ∘ (chartAt E (A.p i)).symm) y‖  ≤
          C*(productWaveFrequency n)^(j+4)*W n ((chartAt E (A.p i)).symm y)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j  ≤  h+1,
        ‖iteratedFDeriv ℝ j
          ((fun x => laplaceBeltrami g (U n) x+productFrequency n*U n x) ∘
            (chartAt E (A.p i)).symm) y‖  ≤
          C*(productWaveFrequency n)^4/(productWaveFrequency n)^D*W n ((chartAt E (A.p i)).symm y))) :
    ∀ᶠ n : ℕ in atTop,
      let b := intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) (U n)
      let s := intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) (U n)
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s ∧
      (∀ x, 0 < b x ∧ 0 < s x) ∧
      (∀ x, weightedLaplacian g b (U n) x+productFrequency n*s x*U n x=0) ∧
      A.ChartJetBound h (fun x => ((b x-1:ℝ):ℂ)) (inverseFrequency n^P) ∧
      A.ChartJetBound h (fun x => ((s x-1:ℝ):ℂ)) (inverseFrequency n^P) ∧
      (∀ x, |b x-1|+|s x-1|  ≤  inverseFrequency n^P) ∧
      (tsupport (fun x => b x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+productFrequency n*U n x)) ∧
      (tsupport (fun x => s x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+productFrequency n*U n x)) := by
  obtain ⟨L,hL,hbound⟩ := A.quantitative_intrinsic_correction_jets h B hC
  have hrate := eventual_product_scalar_correction_rate L P ((2*B+21)*(h+2)+10) D hD
  have hsmall := (inverseFrequency_pow_zero P (Nat.ne_of_gt hP)).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hdata,hrate,hsmall,eventually_ge_atTop 1] with n hn hr hsmall hn1
  have hn1' : 1  ≤  productWaveFrequency n :=
    (show (1:ℝ) ≤ n by exact_mod_cast hn1).trans (productWaveFrequency_bounds hn1).1
  have hn0 : 0 < (productWaveFrequency n) := zero_lt_one.trans_le hn1'
  have hΛ : productFrequency n ≠ 0 := by unfold productFrequency; positivity
  have hden (x : M) : intrinsicCorrectionD g (productWaveFrequency n) (U n) x ≠ 0 :=
    (intrinsicCorrectionD_pos g (U n) x hn0 (hW n x) (hn.1 x)).ne'
  obtain ⟨hb,hsmooth,heq⟩ := intrinsic_scalar_correction (hU n) g (productWaveFrequency n)
    (productFrequency n) hΛ hden
  have hrj := hn.2.2
  rw [←productWaveFrequency_equation n] at hrj
  have hbounds := hbound (productWaveFrequency n) hn1' D (U n) (hU n) (W n) (hW n)
    hn.1 hn.2.1 hrj
  rw [productWaveFrequency_equation] at hbounds
  obtain ⟨hbj,hsj,habs⟩ := hbounds
  have hsupp := tsupport_intrinsic_corrections_sub_one (hU n) g (productWaveFrequency n)
    (productFrequency n) hden
  refine ⟨hb,hsmooth,?_,heq,
    fun chart order horder point => (hbj chart order horder point).trans hr,
    fun chart order horder point => (hsj chart order horder point).trans hr,?_,hsupp⟩
  · intro x
    have hx := (habs x).trans hr
    have hbx : |intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) (U n) x-1| < 1 := by
      have h := abs_nonneg (intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) (U n) x-1)
      exact (le_add_of_nonneg_right h).trans_lt (hx.trans_lt hsmall)
    have hsx : |intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) (U n) x-1| < 1 := by
      have h := abs_nonneg (intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) (U n) x-1)
      exact (le_add_of_nonneg_left h).trans_lt (hx.trans_lt hsmall)
    constructor <;> linarith [(abs_lt.mp hbx).1,(abs_lt.mp hsx).1]
  · intro x
    exact (habs x).trans hr

end CompactMetricAtlas

end YauCounterexamples
end

end OAI
