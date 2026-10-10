import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ComplexGramTraceSecondMul
import OAI.Geometry.SmoothYau.Limits.CubicConstantNonneg
import OAI.Geometry.SmoothYau.SphereMetric.FourThree

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
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Filter
open scoped Topology

def sphereFrequency (n : ℕ) : ℝ := (n : ℝ) * (n + 2)
def inverseFrequency (n : ℕ) : ℝ := (n : ℝ)⁻¹

lemma sphereFrequency_atTop : Tendsto sphereFrequency atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
lemma inverseFrequency_zero : Tendsto inverseFrequency atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
lemma inverseFrequency_pow_zero (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun n => inverseFrequency n ^ m) atTop (𝓝 0) := by
  simpa only [zero_pow hm] using inverseFrequency_zero.pow m
lemma sphereFrequency_mul_pow (n m : ℕ) (hn : n ≠ 0) :
    sphereFrequency n * inverseFrequency n ^ (m + 2) =
      inverseFrequency n ^ m + 2 * inverseFrequency n ^ (m + 1) := by
  have hx : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [sphereFrequency, inverseFrequency, pow_add, pow_one, inv_pow]
  field_simp
lemma sphereFrequency_mul_pow_zero (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun n => sphereFrequency n * inverseFrequency n ^ (m + 2))
      atTop (𝓝 0) := by
  have he : (fun n => inverseFrequency n ^ m + 2 * inverseFrequency n ^ (m + 1)) =ᶠ[atTop]
      (fun n => sphereFrequency n * inverseFrequency n ^ (m + 2)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (sphereFrequency_mul_pow n m (by omega)).symm
  apply Tendsto.congr' he
  convert (inverseFrequency_pow_zero m hm).add
    ((inverseFrequency_pow_zero (m + 1) (by omega)).const_mul 2) using 1
  norm_num
lemma sphereFrequency_ratio (n P : ℕ) (D : ℝ) (hn : n ≠ 0) :
    sphereFrequency n * (D * inverseFrequency n ^ (P + 8)) /
      inverseFrequency n ^ (P + 4) = D * (inverseFrequency n ^ 2 + 2 * inverseFrequency n ^ 3) := by
  have hx : inverseFrequency n ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hn)
  have hp : P + 8 = (P + 4) + 4 := by omega
  rw [hp, pow_add]
  have he : sphereFrequency n * (D * (inverseFrequency n ^ (P + 4) * inverseFrequency n ^ 4)) /
      inverseFrequency n ^ (P + 4) = D * (sphereFrequency n * inverseFrequency n ^ 4) := by
    field_simp
  rw [he, sphereFrequency_mul_pow n 2 hn]

theorem positive_factor_rates (P : ℕ) (D : ℝ) (hD : 0 < D) :
    Tendsto (fun n => D * inverseFrequency n ^ (P + 8)) atTop (𝓝 0) ∧
    Tendsto (fun n => inverseFrequency n ^ (P + 4)) atTop (𝓝 0) ∧
    Tendsto (fun n => sphereFrequency n * (D * inverseFrequency n ^ (P + 8))) atTop (𝓝 0) ∧
    Tendsto (fun n => sphereFrequency n * inverseFrequency n ^ (P + 4)) atTop (𝓝 0) ∧
    Tendsto (fun n => sphereFrequency n * (D * inverseFrequency n ^ (P + 8)) /
      inverseFrequency n ^ (P + 4)) atTop (𝓝 0) ∧
    ∀ᶠ n in atTop, 0 ≤ D * inverseFrequency n ^ (P + 8) ∧
      0 < inverseFrequency n ^ (P + 4) := by
  have hε : Tendsto (fun n => D * inverseFrequency n ^ (P + 8)) atTop (𝓝 0) := by
    simpa using (inverseFrequency_pow_zero (P + 8) (by omega)).const_mul D
  have hδ := inverseFrequency_pow_zero (P + 4) (by omega)
  have hΛε : Tendsto (fun n => sphereFrequency n * (D * inverseFrequency n ^ (P + 8)))
      atTop (𝓝 0) := by
    convert (sphereFrequency_mul_pow_zero (P + 6) (by omega)).const_mul D using 1
    · ext n; ring
    · simp
  have hΛδ : Tendsto (fun n => sphereFrequency n * inverseFrequency n ^ (P + 4))
      atTop (𝓝 0) := by
    convert sphereFrequency_mul_pow_zero (P + 2) (by omega) using 1
  have hratio : Tendsto (fun n => sphereFrequency n * (D * inverseFrequency n ^ (P + 8)) /
      inverseFrequency n ^ (P + 4)) atTop (𝓝 0) := by
    have he := ((inverseFrequency_pow_zero 2 (by omega)).add
      ((inverseFrequency_pow_zero 3 (by omega)).const_mul 2)).const_mul D
    have he' : Tendsto (fun n => D * (inverseFrequency n ^ 2 + 2 * inverseFrequency n ^ 3))
        atTop (𝓝 0) := by simpa using he
    apply he'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (sphereFrequency_ratio n P D (by omega)).symm
  refine ⟨hε, hδ, hΛε, hΛδ, hratio, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : 0 < inverseFrequency n := inv_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  exact ⟨mul_nonneg hD.le (pow_nonneg hp.le _), pow_pos hp _⟩

lemma eventual_output_rate (P : ℕ) (C : ℝ) :
    ∀ᶠ n in atTop, C * inverseFrequency n ^ (P + 4) ≤ inverseFrequency n ^ P := by
  have ht : Tendsto (fun n => C * inverseFrequency n ^ 4) atTop (𝓝 0) := by
    simpa using (inverseFrequency_pow_zero 4 (by omega)).const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  calc
    C * inverseFrequency n ^ (P + 4) = (C * inverseFrequency n ^ 4) * inverseFrequency n ^ P := by rw [pow_add]; ring
    _ ≤ 1 * inverseFrequency n ^ P := mul_le_mul_of_nonneg_right hn.le (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) _)
    _ = inverseFrequency n ^ P := one_mul _

end

section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
local instance threeModelNormedSpace' : NormedSpace ℝ ThreeModel := inferInstance
local instance threeModelContinuousSMul' : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul

local instance threeAmbientNormedSpace' : NormedSpace ℝ ThreeAmbient := inferInstance
local instance threeAmbientContinuousSMul' : ContinuousSMul ℝ ThreeAmbient := inferInstance
local instance sphereN_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1)) = n+1) := ⟨by simp [Euclidean]⟩


def threeComplexPower (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) : ℂ :=
  (planarLinear a b (p.1:Euclidean 3))^k*(p.2:ℂ)^k
def threePower (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) : ℝ :=
  (threeComplexPower a b k p).re
lemma threeComplexPower_smooth (a b : Euclidean 3) (k : ℕ) :
    ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℂ) ∞ (threeComplexPower a b k) := by
  let L : ThreeAmbient →L[ℝ] ℂ := (planarLinear a b).comp (WithLp.fstL 2 ℝ (Euclidean 3) ℂ)
  let R : ThreeAmbient →L[ℝ] ℂ := WithLp.sndL 2 ℝ (Euclidean 3) ℂ
  have hh : ContDiff ℝ ∞ (fun x : ThreeAmbient => (L x)^k*(R x)^k) :=
    (L.contDiff.pow k).mul (R.contDiff.pow k)
  have hc := hh.contMDiff.comp (I:=𝓘(ℝ,ThreeModel)) threeImmersion_smooth
  exact hc
lemma threePower_smooth (a b : Euclidean 3) (k : ℕ) :
    ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (threePower a b k) :=
  Complex.reCLM.contMDiff.comp (threeComplexPower_smooth a b k)
lemma threeComplexPower_chart (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    threeComplexPower a b k ∘ (chartAt ThreeModel p).symm =
      fun z => productSphere_fstPower (n:=2) (m:=1) p.1 (planarLinear a b) k z*
        productSphere_sndPower (n:=2) (m:=1) p.2 (planarLinear (1:ℂ) Complex.I) k z := by
  funext y
  have hh := congrFun (three_chart_symm p) y
  have h₁ := congrArg (fun q : ThreeAmbient => q.fst) hh
  have h₂ := congrArg (fun q : ThreeAmbient => q.snd) hh
  change (((chartAt ThreeModel p).symm y).1:Euclidean 3) =
    roundChart (p.1:Euclidean 3) (sphereFrame p.1) y.fst at h₁
  change (((chartAt ThreeModel p).symm y).2:ℂ) =
    roundChart (p.2:ℂ) (unitSphereFrame (n:=1) p.2) y.snd at h₂
  simp only [Function.comp_apply,threeComplexPower,h₁,h₂]
  simp only [productSphere_fstPower,productSphere_sndPower,Function.comp_apply]
  rw [complexIdentityPlanar]
  rfl
lemma threePower_chart (a b : Euclidean 3) (k : ℕ) (p : ThreeManifold) :
    threePower a b k ∘ (chartAt ThreeModel p).symm =
      fun z => (productSphere_fstPower (n:=2) (m:=1) p.1 (planarLinear a b) k z*
        productSphere_sndPower (n:=2) (m:=1) p.2 (planarLinear (1:ℂ) Complex.I) k z).re := by
  have hh := congrArg (fun f : ThreeModel → ℂ => fun x => (f x).re)
    (threeComplexPower_chart a b k p)
  exact hh

def productFrequency (k : ℕ) : ℝ := 2*(k:ℝ)^2+(k:ℝ)
lemma productFrequency_pos {k : ℕ} (hk : 1 ≤ k) : 0 < productFrequency k := by
  have hk' : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  unfold productFrequency
  positivity

theorem threePower_eigen (a b : Euclidean 3) (k : ℕ) (hk : 2 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (p : ThreeManifold) :
    -laplaceBeltrami threeBackgroundMetric (threePower a b k) p =
      productFrequency k*threePower a b k p := by
  have hc : inner ℝ (1:ℂ) 1 = 1 := by simp
  have hd : inner ℝ Complex.I Complex.I = 1 := by simp
  have hcd : inner ℝ (1:ℂ) Complex.I = 0 := by simp [Complex.inner]
  have ht := productSphere_power_trace (Module.finBasis ℝ ThreeModel) p.1 p.2 a b
    (1:ℂ) Complex.I k k hk hk ha hb hab hc hd hcd
  have hfull : ContDiff ℝ ∞ (fun z : ThreeModel =>
      productSphere_fstPower (n:=2) (m:=1) p.1 (planarLinear a b) k z*
      productSphere_sndPower (n:=2) (m:=1) p.2 (planarLinear (1:ℂ) Complex.I) k z) :=
    (productSphere_fstPower_smooth _ _ _).mul (productSphere_sndPower_smooth _ _ _)
  rw [three_laplace_at_center _ (threePower_smooth _ _ _),threePower_chart]
  simp_rw [second_real_part hfull]
  have hr := congrArg Complex.re ht
  simp only [complexGramTrace,Complex.re_sum,Complex.re_ofReal_mul] at hr
  rw [hr,complexIdentityPlanar]
  have hf : -((k:ℂ)*((k:ℂ)+(2:ℂ)-1)+(k:ℂ)*((k:ℂ)+(1:ℂ)-1)) =
      (-(productFrequency k):ℂ) := by
    unfold productFrequency
    push_cast
    ring
  norm_num only [Nat.cast_ofNat]
  rw [hf, mul_assoc]
  simp only [neg_mul,Complex.neg_re,neg_neg,Complex.re_ofReal_mul]
  rfl
end


section
open Set Filter
open scoped Topology

def productWaveFrequency (k : ℕ) : ℝ := Real.sqrt (productFrequency k+1)-1
lemma productFrequency_nonneg (k : ℕ) : 0 ≤ productFrequency k := by
  unfold productFrequency
  positivity
lemma productWaveFrequency_equation (k : ℕ) :
    productWaveFrequency k*(productWaveFrequency k+2)=productFrequency k := by
  have h := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
  unfold productWaveFrequency
  nlinarith
lemma productWaveFrequency_bounds {k : ℕ} (hk : 1≤k) :
    (k:ℝ) ≤ productWaveFrequency k ∧ productWaveFrequency k ≤ 2*(k:ℝ) := by
  have hp : (1:ℝ)≤k := by exact_mod_cast hk
  have hs := Real.sq_sqrt (add_nonneg (productFrequency_nonneg k) zero_le_one)
  have hs0 := Real.sqrt_nonneg (productFrequency k+1)
  dsimp [productFrequency] at hs hs0 ⊢
  unfold productWaveFrequency productFrequency
  constructor <;> nlinarith [sq_nonneg ((k:ℝ)-1)]
lemma productWaveFrequency_tendsto : Tendsto productWaveFrequency atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) _ _)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
  exact (productWaveFrequency_bounds hk).1
lemma productWaveFrequency_ratio_formula {k : ℕ} (hk : 1≤k) :
    productWaveFrequency k/(k:ℝ)=Real.sqrt (2+(k:ℝ)⁻¹+((k:ℝ)⁻¹)^2)-(k:ℝ)⁻¹ := by
  have hp : (0:ℝ)<k := by exact_mod_cast (zero_lt_one.trans_le hk)
  have hs : productFrequency k+1 = (k:ℝ)^2*(2+(k:ℝ)⁻¹+((k:ℝ)⁻¹)^2) := by
    unfold productFrequency
    field_simp
  rw [productWaveFrequency,hs,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hp.le]
  field_simp
lemma productWaveFrequency_ratio_tendsto :
    Tendsto (fun k : ℕ => productWaveFrequency k/(k:ℝ)) atTop (𝓝 (Real.sqrt 2)) := by
  have hi : Tendsto (fun k : ℕ => (k:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (((tendsto_const_nhds (x:=(2:ℝ))).add hi |>.add (hi.pow 2)).sqrt).sub hi
  simp only [add_zero,zero_pow (by decide : (2:ℕ)≠0),sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
  exact (productWaveFrequency_ratio_formula hk).symm
end


open Set Filter Function Manifold
open scoped Topology ContDiff
lemma productFrequency_atTop : Tendsto productFrequency atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) _ _)
  exact Eventually.of_forall (fun k => by dsimp [productFrequency]; nlinarith [sq_nonneg (k:ℝ)])
lemma productFrequency_mul_pow (n m : ℕ) (hn : n ≠ 0) :
    productFrequency n * inverseFrequency n ^ (m + 2) =
      2 * inverseFrequency n ^ m + inverseFrequency n ^ (m + 1) := by
  have hx : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [productFrequency, inverseFrequency, pow_add, pow_one, inv_pow]
  field_simp

lemma productFrequency_mul_pow_zero (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun n => productFrequency n * inverseFrequency n ^ (m + 2))
      atTop (𝓝 0) := by
  have he : (fun n => 2 * inverseFrequency n ^ m + inverseFrequency n ^ (m + 1)) =ᶠ[atTop]
      (fun n => productFrequency n * inverseFrequency n ^ (m + 2)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (productFrequency_mul_pow n m (by omega)).symm
  apply Tendsto.congr' he
  convert ((inverseFrequency_pow_zero m hm).const_mul 2).add
    (inverseFrequency_pow_zero (m + 1) (by omega)) using 1
  norm_num

lemma productFrequency_ratio (n P : ℕ) (D : ℝ) (hn : n ≠ 0) :
    productFrequency n * (D * inverseFrequency n ^ (P + 8)) /
      inverseFrequency n ^ (P + 4) = D * (2 * inverseFrequency n ^ 2 + inverseFrequency n ^ 3) := by
  have hx : inverseFrequency n ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hn)
  have hp : P + 8 = (P + 4) + 4 := by omega
  rw [hp, pow_add]
  have he : productFrequency n * (D * (inverseFrequency n ^ (P + 4) * inverseFrequency n ^ 4)) /
      inverseFrequency n ^ (P + 4) = D * (productFrequency n * inverseFrequency n ^ 4) := by
    field_simp
  rw [he, productFrequency_mul_pow n 2 hn]

theorem product_positive_factor_rates (P : ℕ) (D : ℝ) (hD : 0 < D) :
    Tendsto (fun n => D * inverseFrequency n ^ (P + 8)) atTop (𝓝 0) ∧
    Tendsto (fun n => inverseFrequency n ^ (P + 4)) atTop (𝓝 0) ∧
    Tendsto (fun n => productFrequency n * (D * inverseFrequency n ^ (P + 8))) atTop (𝓝 0) ∧
    Tendsto (fun n => productFrequency n * inverseFrequency n ^ (P + 4)) atTop (𝓝 0) ∧
    Tendsto (fun n => productFrequency n * (D * inverseFrequency n ^ (P + 8)) /
      inverseFrequency n ^ (P + 4)) atTop (𝓝 0) ∧
    ∀ᶠ n in atTop, 0 ≤ D * inverseFrequency n ^ (P + 8) ∧
      0 < inverseFrequency n ^ (P + 4) := by
  have hε : Tendsto (fun n => D * inverseFrequency n ^ (P + 8)) atTop (𝓝 0) := by
    simpa using (inverseFrequency_pow_zero (P + 8) (by omega)).const_mul D
  have hδ := inverseFrequency_pow_zero (P + 4) (by omega)
  have hΛε : Tendsto (fun n => productFrequency n * (D * inverseFrequency n ^ (P + 8)))
      atTop (𝓝 0) := by
    convert (productFrequency_mul_pow_zero (P + 6) (by omega)).const_mul D using 1
    · ext n; ring
    · simp
  have hΛδ : Tendsto (fun n => productFrequency n * inverseFrequency n ^ (P + 4))
      atTop (𝓝 0) := by
    convert productFrequency_mul_pow_zero (P + 2) (by omega) using 1
  have hratio : Tendsto (fun n => productFrequency n * (D * inverseFrequency n ^ (P + 8)) /
      inverseFrequency n ^ (P + 4)) atTop (𝓝 0) := by
    have he := (((inverseFrequency_pow_zero 2 (by omega)).const_mul 2).add
      (inverseFrequency_pow_zero 3 (by omega))).const_mul D
    have he' : Tendsto (fun n => D * (2 * inverseFrequency n ^ 2 + inverseFrequency n ^ 3))
        atTop (𝓝 0) := by simpa using he
    apply he'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (productFrequency_ratio n P D (by omega)).symm
  refine ⟨hε, hδ, hΛε, hΛδ, hratio, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : 0 < inverseFrequency n := inv_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  exact ⟨mul_nonneg hD.le (pow_nonneg hp.le _), pow_pos hp _⟩

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)
theorem eventually_product_positive_factor_of_jets
    (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
    (N P : ℕ) (hN : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ) - N))
    (b s : ℕ → M → ℝ)
    (hb : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (b n))
    (hsmooth : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (s n))
    (hdata : ∀ᶠ n in atTop,
      A.ChartJetBound (2 * (k + 1)) (fun x => ((b n x - 1 : ℝ) : ℂ))
        (inverseFrequency n ^ (P + 8)) ∧
      A.ChartJetBound (2 * (k + 1)) (fun x => ((s n x - 1 : ℝ) : ℂ))
        (inverseFrequency n ^ (P + 8))) :
    ∀ᶠ n in atTop, ∃ u : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
      (∀ x, weightedLaplacian g (b n) u x =
        productFrequency n * b n x ^ 3 * u x ^ 5 - productFrequency n * s n x * u x) ∧
      A.ChartJetBound N (fun x => ((u x - 1 : ℝ) : ℂ)) (inverseFrequency n ^ P) := by
  have ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  obtain ⟨D, hD, hDbound⟩ := A.exists_jet_sobolev_constant (k + 1)
  obtain ⟨C, hC, hCbound⟩ := A.exists_chart_jet_constant N hN
  obtain ⟨he, hδ, hΛe, hΛδ, hratio, hpos⟩ := product_positive_factor_rates P D hD
  have hnorms : ∀ᶠ n in atTop,
      ‖A.realOfSmooth _ ht (fun x => b n x - 1) ((hb n).sub contMDiff_const)‖ ≤
        D * inverseFrequency n ^ (P + 8) ∧
      ‖A.realOfSmooth _ ht (fun x => s n x - 1) ((hsmooth n).sub contMDiff_const)‖ ≤
        D * inverseFrequency n ^ (P + 8) := by
    filter_upwards [hdata] with n hn
    have hpow : 0 ≤ inverseFrequency n ^ (P + 8) :=
      pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) _
    constructor
    · exact hDbound ⟨_, Complex.ofRealCLM.contMDiff.comp ((hb n).sub contMDiff_const)⟩ _ hpow hn.1
    · exact hDbound ⟨_, Complex.ofRealCLM.contMDiff.comp ((hsmooth n).sub contMDiff_const)⟩ _ hpow hn.2
  have hex := A.eventually_positive_factor hd B ht b s hb hsmooth productFrequency
    (fun n => D * inverseFrequency n ^ (P + 8)) (fun n => inverseFrequency n ^ (P + 4))
    productFrequency_atTop he hδ hΛe hΛδ hratio hpos hnorms
  filter_upwards [hex, eventual_output_rate P C] with n hn hr
  obtain ⟨u, hu, hup, hueq, h, hnorm, hv⟩ := hn
  refine ⟨u, hu, hup, hueq, ?_⟩
  have heq : A.representative (2 * ((k + 1 : ℕ) : ℝ)) h.val =
      fun x => ((u x - 1 : ℝ) : ℂ) := by
    ext x
    rw [← A.ofReal_realValue, hv]
  rw [← heq]
  intro patch order horder point
  exact (hCbound h.val patch order horder point).trans
    ((mul_le_mul_of_nonneg_left hnorm hC.le).trans hr)

theorem eventually_product_positive_factor_of_eventual_jets
    (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
    (N P : ℕ) (hN : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ)-N))
    (b s : ℕ → M → ℝ)
    (hsmooth : ∀ᶠ n in atTop,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b n) ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s n))
    (hdata : ∀ᶠ n in atTop,
      A.ChartJetBound (2*(k+1)) (fun x => ((b n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) ∧
      A.ChartJetBound (2*(k+1)) (fun x => ((s n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8))) :
    ∀ᶠ n in atTop, ∃ v : M → ℝ,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
      (∀ x, weightedLaplacian g (b n) v x =
        productFrequency n*b n x^3*v x^5-productFrequency n*s n x*v x) ∧
      A.ChartJetBound N (fun x => ((v x-1:ℝ):ℂ)) (inverseFrequency n^P) := by
  classical
  let Good (n : ℕ) := ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b n) ∧
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s n)
  let b' (n : ℕ) : M → ℝ := if Good n then b n else fun _ => 1
  let s' (n : ℕ) : M → ℝ := if Good n then s n else fun _ => 1
  have hb' (n : ℕ) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b' n) := by
    by_cases hn : Good n
    · simpa [b', hn] using hn.1
    · simp only [b', ite_eq_right hn]
      exact contMDiff_const
  have hs' (n : ℕ) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s' n) := by
    by_cases hn : Good n
    · simpa [s', hn] using hn.2
    · simp only [s', ite_eq_right hn]
      exact contMDiff_const
  have hdata' : ∀ᶠ n in atTop,
      A.ChartJetBound (2*(k+1)) (fun x => ((b' n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) ∧
      A.ChartJetBound (2*(k+1)) (fun x => ((s' n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) := by
    filter_upwards [hsmooth,hdata] with n hn hj
    change Good n at hn
    simpa only [b',s',ite_eq_left hn] using hj
  have h := A.eventually_product_positive_factor_of_jets hd B N P hN b' s' hb' hs' hdata'
  filter_upwards [hsmooth,h] with n hn hv
  change Good n at hn
  simpa only [b',s',ite_eq_left hn] using hv

end CompactMetricAtlas

end YauCounterexamples
end

end OAI
