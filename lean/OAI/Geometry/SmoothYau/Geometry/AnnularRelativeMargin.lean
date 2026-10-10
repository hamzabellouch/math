import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ChartGradientProjectionSmooth

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma roundPower_ne_zero (a b : Euclidean (d+1)) (k : ℕ)
    (ha : inner ℝ a a = 1) (hab : inner ℝ a b = 0) : roundPower a b k ≠ 0 := by
  have hn : ‖a‖ = 1 := by rw [real_inner_self_eq_norm_sq] at ha; nlinarith [norm_nonneg a]
  let p : Sphere d := ⟨a,by simpa only [Metric.mem_sphere,dist_zero_right] using hn⟩
  intro he
  have hh := congrFun he p
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  simp [roundPower,p,planarLinear_apply,hn,hba] at hh

def ambientPowerGradient (a b : Euclidean (d+1)) (k : ℕ) (x : Euclidean (d+1)) : Euclidean (d+1) :=
  (k:ℝ) • (((planarLinear a b x)^(k-1)).re • a - ((planarLinear a b x)^(k-1)).im • b)

lemma ambientPowerGradient_pair (a b : Euclidean (d+1)) (k : ℕ) (x v : Euclidean (d+1)) :
    inner ℝ v (ambientPowerGradient a b k x) =
      ((k:ℂ) * (planarLinear a b x)^(k-1) * planarLinear a b v).re := by
  simp only [ambientPowerGradient,inner_smul_right,inner_sub_right,
    planarLinear_apply,Complex.mul_re,Complex.mul_im,Complex.natCast_re,
    Complex.natCast_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,
    zero_add,add_zero,one_mul]
  rw [real_inner_comm a v,real_inner_comm b v]
  ring

lemma roundPower_chart_directional (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d) (v : Euclidean d) :
    fderiv ℝ (roundPower a b k ∘ (chartAt (Euclidean d) p).symm) 0 v =
      inner ℝ (sphereFrame p v) (ambientPowerGradient a b k p) := by
  have hc : roundPower a b k ∘ (chartAt (Euclidean d) p).symm =
      fun z => ((planarLinear a b (roundChart (p : Euclidean (d+1)) (sphereFrame p) z))^k).re := by
    funext z
    simp only [roundPower,Function.comp_apply]
    rw [← sphere_chart_symm]
  have hf : ContDiff ℝ ∞ (fun z => (planarLinear a b (roundChart (p : Euclidean (d+1)) (sphereFrame p) z))^k) :=
    ((planarLinear a b).contDiff.comp (roundChart_smooth _ _)).pow k
  rw [hc,fderiv_real_part (hf.differentiable (by simp) _),roundLinearPower_directional,
    roundChart_zero,(roundChart_first _ _).fderiv,ambientPowerGradient_pair]
  rfl

lemma ambientPowerGradient_norm_sq (a b : Euclidean (d+1)) (k : ℕ) (x : Euclidean (d+1))
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    inner ℝ (ambientPowerGradient a b k x) (ambientPowerGradient a b k x) =
      (k:ℝ)^2 * (Complex.normSq (planarLinear a b x))^(k-1) := by
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  simp only [ambientPowerGradient,inner_smul_left,inner_smul_right,inner_sub_left,
    inner_sub_right,ha,hb,hab,hba,conj_trivial,mul_one,mul_zero,sub_zero,zero_sub]
  rw [← map_pow Complex.normSq]
  simp only [Complex.normSq_apply]
  ring

lemma ambientPowerGradient_radial (a b : Euclidean (d+1)) (k : ℕ) (hk : 1 ≤ k) (x : Euclidean (d+1)) :
    inner ℝ x (ambientPowerGradient a b k x) = (k:ℝ) * ((planarLinear a b x)^k).re := by
  rw [ambientPowerGradient_pair,mul_assoc,← pow_succ,Nat.sub_add_cancel hk]
  simp [Complex.mul_re]

theorem roundPower_gradient_square (a b : Euclidean (d+1)) (k : ℕ) (hk : 1 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) (p : Sphere d) :
    ∑ i, ∑ j, (Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)))⁻¹ i j *
      fderiv ℝ (roundPower a b k ∘ (chartAt (Euclidean d) p).symm) 0 (Module.finBasis ℝ (Euclidean d) j) *
      fderiv ℝ (roundPower a b k ∘ (chartAt (Euclidean d) p).symm) 0 (Module.finBasis ℝ (Euclidean d) i) =
      (k:ℝ)^2 * ((Complex.normSq (planarLinear a b p))^(k-1) - (roundPower a b k p)^2) := by
  simp_rw [roundPower_chart_directional]
  rw [sphere_inverse_gram_contraction,ambientPowerGradient_norm_sq _ _ _ _ ha hb hab,
    ambientPowerGradient_radial _ _ _ hk]
  dsimp [roundPower]
  ring

lemma complex_power_real_sq_bound (z : ℂ) (k : ℕ) :
    (z^k).re^2 ≤ (Complex.normSq z)^k := by
  rw [← map_pow Complex.normSq,Complex.normSq_apply]
  nlinarith [sq_nonneg (z^k).im]

theorem roundPower_annulus_noncritical (a b : Euclidean (d+1)) (k : ℕ) (hk : 1 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) (p : Sphere d)
    (hpos : 0 < Complex.normSq (planarLinear a b p)) (hlt : Complex.normSq (planarLinear a b p) < 1) :
    fderiv ℝ (roundPower a b k ∘ (chartAt (Euclidean d) p).symm) 0 ≠ 0 := by
  have hlow : 0 < (Complex.normSq (planarLinear a b p))^(k-1) - (roundPower a b k p)^2 := by
    have hbnd := complex_power_real_sq_bound (planarLinear a b p) k
    have he : (Complex.normSq (planarLinear a b p))^k =
        (Complex.normSq (planarLinear a b p))^(k-1) * Complex.normSq (planarLinear a b p) := by
      rw [← pow_succ,Nat.sub_add_cancel hk]
    rw [he] at hbnd
    have hh := mul_pos (pow_pos hpos (k-1)) (sub_pos.mpr hlt)
    dsimp [roundPower]
    nlinarith
  have hh := roundPower_gradient_square a b k hk ha hb hab p
  intro hz
  simp only [hz,_root_.zero_apply,mul_zero,Finset.sum_const_zero] at hh
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp := mul_pos (sq_pos_of_pos hkpos) hlow
  linarith


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
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩
lemma round_metricCoefficients_at (g : SmoothMetric (Euclidean d) (Sphere d)) (p : Sphere d)
    (hg : ∀ (v w : TangentSpace 𝓘(ℝ,Euclidean d) p),
      g.inner p v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p w)) :
    metricCoefficients g p 0 = Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)) := by
  have hp : (chartAt (Euclidean d) p).symm 0 = p := by
    simpa only [sphere_chart_center] using (chartAt (Euclidean d) p).left_inv (mem_chart_source _ p)
  have hg' : ∀ (v w : TangentSpace 𝓘(ℝ,Euclidean d) ((chartAt (Euclidean d) p).symm 0)),
      g.inner ((chartAt (Euclidean d) p).symm 0) v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) ((chartAt (Euclidean d) p).symm 0) v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) ((chartAt (Euclidean d) p).symm 0) w) := by
    change (fun q : Sphere d => ∀ v w : TangentSpace 𝓘(ℝ,Euclidean d) q,
      g.inner q v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) q v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) q w))
      ((chartAt (Euclidean d) p).symm 0)
    rw [hp]
    exact hg
  let : ContinuousSMul ℝ (Euclidean d) := IsBoundedSMul.continuousSMul
  let : ContinuousSMul ℝ (Euclidean (d+1)) := IsBoundedSMul.continuousSMul
  have hround : fderiv ℝ (roundChart (p : Euclidean (d+1)) (sphereFrame p)) 0 =
      (sphereFrame p).toContinuousLinearMap :=
    (roundChart_first (p : Euclidean (d+1)) (sphereFrame p)).fderiv
  ext i j
  rw [metricCoefficients,hg']
  rw [coordinateVector,coordinateVector,sphere_coordinate_embedding p 0,
    sphere_coordinate_embedding p 0,hround]
  exact (sphereFrame p).inner_map_map _ _
lemma roundPower_coordinateGradientPair (g : SmoothMetric (Euclidean d) (Sphere d)) (p : Sphere d)
    (hg : ∀ (v w : TangentSpace 𝓘(ℝ,Euclidean d) p),
      g.inner p v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p w))
    (a b : Euclidean (d+1)) (n : ℕ) (hn : 1 ≤ n)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    coordinateGradientPair g (roundPower a b n) (roundPower a b n) p =
      (n:ℝ)^2 * ((Complex.normSq (planarLinear a b p))^(n-1) - (roundPower a b n p)^2) := by
  rw [coordinateGradientPair,sphere_chart_center,round_metricCoefficients_at g p hg]
  convert roundPower_gradient_square a b n hn ha hb hab p using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring



end

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
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff

lemma annular_relative_margin (n : ℕ) (hn : 1 ≤ n) {R t U w G : ℝ}
    (hR : 0 < R) (hRt : R ≤ t) (ht : t < 1)
    (hU : U^2 ≤ R^n) (hw : 1/2 ≤ w) (hG0 : 0 ≤ G) (hG : G ≤ (1-t)/8) :
    U^2*G < w^2*((n:ℝ)^2*(R^(n-1)-U^2)) := by
  have hRn : R^n=R^(n-1)*R := by rw [←pow_succ,Nat.sub_add_cancel hn]
  have hRp : 0 < R^(n-1) := pow_pos hR _
  have ht0 : 0 < t := hR.trans_le hRt
  have hR1 : R ≤ 1 := hRt.trans ht.le
  have hN : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hN2 : 1 ≤ (n:ℝ)^2 := by nlinarith
  have hw2 : 1/4 ≤ w^2 := by nlinarith
  have hdiff : R^(n-1)*(1-t) ≤ R^(n-1)-U^2 := by
    rw [hRn] at hU
    have h := mul_le_mul_of_nonneg_left hRt hRp.le
    nlinarith
  have hdiffpos : 0 < R^(n-1)-U^2 := (mul_pos hRp (sub_pos.mpr ht)).trans_le hdiff
  have hleft : U^2*G ≤ R^(n-1)*(1-t)/8 := by
    calc
      U^2*G ≤ R^n*((1-t)/8) := mul_le_mul hU hG hG0 (pow_nonneg hR.le _)
      _ ≤ R^(n-1)*((1-t)/8) := by
        rw [hRn]
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        simpa using mul_le_mul_of_nonneg_left hR1 hRp.le
      _ = _ := by ring
  have hright : (R^(n-1)*(1-t))/4 ≤ w^2*((n:ℝ)^2*(R^(n-1)-U^2)) := by
    calc
      _ ≤ (1/4)*(R^(n-1)-U^2) := by linarith [hdiff]
      _ ≤ w^2*((n:ℝ)^2*(R^(n-1)-U^2)) := by
        have h₁ := mul_le_mul_of_nonneg_right hN2 hdiffpos.le
        have h₂ := mul_le_mul hw2 (by simpa using h₁) hdiffpos.le (sq_nonneg w)
        exact h₂
  have hp := mul_pos hRp (sub_pos.mpr ht)
  linarith

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma roundPower_conjugating_margin
    (g : SmoothMetric (Euclidean d) (Sphere d)) (p : Sphere d)
    (hg : ∀ v z : TangentSpace 𝓘(ℝ,Euclidean d) p,
      g.inner p v z = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p z))
    (a b : Euclidean (d+1)) (n : ℕ) (hn : 1 ≤ n)
    (ha : inner ℝ a a=1) (hb : inner ℝ b b=1) (hab : inner ℝ a b=0)
    {t : ℝ} (hR : 0 < Complex.normSq (planarLinear a b p))
    (hRt : Complex.normSq (planarLinear a b p) ≤ t) (ht : t < 1)
    (w : Sphere d → ℝ) (hw : 1/2 ≤ w p)
    (hG : coordinateGradientPair g w w p ≤ (1-t)/8) :
    (roundPower a b n p)^2*coordinateGradientPair g w w p <
      (w p)^2*coordinateGradientPair g (roundPower a b n) (roundPower a b n) p := by
  rw [roundPower_coordinateGradientPair g p hg a b n hn ha hb hab]
  exact annular_relative_margin n hn hR hRt ht
    (complex_power_real_sq_bound (planarLinear a b p) n) hw
    (coordinateGradientPair_nonneg g w p) hG

lemma coordinateGradientPair_congr_nhds_cutoff {E M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] (g : SmoothMetric E M)
    {f h : M → ℝ} {p : M} (he : f =ᶠ[𝓝 p] h) :
    coordinateGradientPair g f f p=coordinateGradientPair g h h p := by
  let c := chartAt E p
  have hp := c.map_source (mem_chart_source E p)
  have ht : Tendsto c.symm (𝓝 (c p)) (𝓝 p) := by
    simpa only [c.left_inv (mem_chart_source E p)] using (c.continuousAt_symm hp).tendsto
  have hd := (he.comp_tendsto ht).fderiv_eq (𝕜:=ℝ)
  unfold coordinateGradientPair
  change (∑ i, ∑ j, _ * fderiv ℝ (f ∘ c.symm) (c p) _ *
    fderiv ℝ (f ∘ c.symm) (c p) _) = _
  rw [hd]


end YauCounterexamples
end

end OAI
