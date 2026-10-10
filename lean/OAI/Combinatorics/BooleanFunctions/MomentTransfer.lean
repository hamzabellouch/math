import OAI.Combinatorics.BooleanFunctions.GaussianGain

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace MomentTransfer
open SmoothGaussian SmoothSelector GaussianGain
/-- Only compact continuous test functions are passed through weak convergence. -/
theorem compact_test_tendsto {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ω n → ℝ) (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1))
    (f : ℝ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun n => ∫ x, f (T n x) ∂P n) atTop (𝓝 (∫ x, f x ∂gaussianReal 0 1)) := by
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hT.tendsto)
    (ofCompactSupport f hf hc)
  change Tendsto (fun n => ∫ x, f x ∂(P n).map (T n)) atTop
    (𝓝 (∫ x, f x ∂(gaussianReal 0 1).map (fun x => x))) at h
  rw [Measure.map_id'] at h
  have he (n : ℕ) : (∫ x, f x ∂(P n).map (T n)) =
      ∫ x, f (T n x) ∂P n := by
    rw [integral_map (hT.forall_aemeasurable n) hf.aestronglyMeasurable]
  simpa only [he] using h

def moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Ω → ℝ)
    {ι : Type*} (w : ι → ℝ → ℝ) (k : Fin 3) (i : ι) : ℝ :=
  ∫ x, w i (T x)*(T x)^(k:ℕ) ∂P

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def means (l : Fin 3 → ι → ℝ) (i : ι) : ℝ := l 1 i / l 0 i
def vars (l : Fin 3 → ι → ℝ) (i : ι) : ℝ := l 2 i / l 0 i - (means l i)^2

def gain (l s : Fin 3 → ι → ℝ) : ℝ :=
  (∏ i, l 0 i) * (1 + ∑ i, vars l i -
    ∑ i, (s 2 i + 2*(1-means l i)*s 1 i +
      ((1-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j)*s 0 i) / l 0 i)

theorem gain_tendsto (l s : ℕ → Fin 3 → ι → ℝ) (l₀ s₀ : Fin 3 → ι → ℝ)
    (hl : ∀ k i, Tendsto (fun n => l n k i) atTop (𝓝 (l₀ k i)))
    (hs : ∀ k i, Tendsto (fun n => s n k i) atTop (𝓝 (s₀ k i)))
    (hb : ∀ i, l₀ 0 i ≠ 0) :
    Tendsto (fun n => gain (l n) (s n)) atTop (𝓝 (gain l₀ s₀)) := by
  have hm (i : ι) : Tendsto (fun n => means (l n) i) atTop (𝓝 (means l₀ i)) :=
    (hl 1 i).div (hl 0 i) (hb i)
  have hv (i : ι) : Tendsto (fun n => vars (l n) i) atTop (𝓝 (vars l₀ i)) :=
    ((hl 2 i).div (hl 0 i) (hb i)).sub ((hm i).pow 2)
  have hvsum := tendsto_finsetSum Finset.univ (fun i _ => hv i)
  have hother (i : ι) := tendsto_finsetSum (Finset.univ.erase i) (fun j _ => hv j)
  have hj (i : ι) : Tendsto (fun n => (s n 2 i + 2*(1-means (l n) i)*s n 1 i +
      ((1-means (l n) i)^2+∑ j ∈ Finset.univ.erase i, vars (l n) j)*s n 0 i) / l n 0 i)
      atTop (𝓝 ((s₀ 2 i + 2*(1-means l₀ i)*s₀ 1 i +
      ((1-means l₀ i)^2+∑ j ∈ Finset.univ.erase i, vars l₀ j)*s₀ 0 i) / l₀ 0 i)) := by
    exact (((hs 2 i).add ((tendsto_const_nhds.mul (tendsto_const_nhds.sub (hm i))).mul (hs 1 i))).add
      ((((tendsto_const_nhds.sub (hm i)).pow 2).add (hother i)).mul (hs 0 i))).div (hl 0 i) (hb i)
  exact (tendsto_finsetProd Finset.univ (fun i _ => hl 0 i)).mul
    ((tendsto_const_nhds.add hvsum).sub (tendsto_finsetSum Finset.univ (fun i _ => hj i)))

theorem hat_le_one (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    hat N δ i t ≤ 1 := by
  exact (Finset.single_le_sum (fun j _ => hat_nonneg N δ j t) (Finset.mem_univ i)).trans
    (hats_sum_le_one N δ t)

theorem hat_moment_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (T : Ω → ℝ) (hT : Measurable T) (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (k : ℕ)
    (hi : Integrable (fun x => (T x)^k) P) :
    Integrable (fun x => hat N δ i (T x)*(T x)^k) P := by
  apply hi.norm.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hat_nonneg ..)]
  exact mul_le_of_le_one_left (abs_nonneg _) (hat_le_one ..)

theorem weight_moment_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (T : Ω → ℝ) (hT : Measurable T) (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (k : ℕ)
    (hi : Integrable (fun x => (T x)^k) P) :
    (∫ x, weight N δ i (T x)*(T x)^k ∂P) =
      (∫ x, hat N δ i (T x)*(T x)^k ∂P) +
        if i = middle N then (∫ x, (T x)^k ∂P) -
          ∑ j, ∫ x, hat N δ j (T x)*(T x)^k ∂P else 0 := by
  have hh (j) := hat_moment_integrable T hT N δ j k hi
  by_cases he : i = middle N
  · subst i
    simp only [weight,ite_true,add_mul,sub_mul,one_mul,Finset.sum_mul]
    rw [integral_add (f := fun x => hat N δ (middle N) (T x)*(T x)^k)
      (g := fun x => (T x)^k-∑ j, hat N δ j (T x)*(T x)^k)
      (hh (middle N)) (hi.sub (integrable_finsetSum Finset.univ (fun j _ => hh j))),
      integral_sub hi (integrable_finsetSum Finset.univ (fun j _ => hh j)),
      integral_finsetSum Finset.univ (fun j _ => hh j)]
  · simp only [weight,he,ite_false,add_zero]

theorem gaussian_pow_integrable (k : Fin 3) :
    Integrable (fun x : ℝ => x^(k:ℕ)) (gaussianReal 0 1) := by
  fin_cases k
  · simp only [pow_zero]; exact integrable_const _
  · change Integrable (fun x : ℝ => x^1) (gaussianReal 0 1)
    simp only [pow_one]
    exact (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  · exact gaussian_sq_integrable 1

theorem leaf_moments_tendsto {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ω n → ℝ) (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1))
    (k : Fin 3) (i : Leaves) :
    Tendsto (fun n => moments (P n) (T n) leafTest k i) atTop
      (𝓝 (moments (gaussianReal 0 1) id leafTest k i)) := by
  apply compact_test_tendsto P T hT
  · exact (continuous_tent _ _).mul (continuous_id.pow _)
  · exact (tent_compactSupport width_pos).mul_right

theorem selector_moments_tendsto {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ω n → ℝ) (hm : ∀ n, Measurable (T n))
    (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1))
    (hi : ∀ n (k : Fin 3), Integrable (fun x => (T n x)^(k:ℕ)) (P n))
    (hM : ∀ k : Fin 3, Tendsto (fun n => ∫ x, (T n x)^(k:ℕ) ∂P n) atTop
      (𝓝 (∫ x : ℝ, x^(k:ℕ) ∂gaussianReal 0 1))) (k : Fin 3) (i : Leaves) :
    Tendsto (fun n => moments (P n) (T n) selectorTest k i) atTop
      (𝓝 (moments (gaussianReal 0 1) id selectorTest k i)) := by
  have hh (j : Leaves) := compact_test_tendsto P T hT
    (fun x => hat gridN step j x*x^(k:ℕ))
    ((hat_continuous ..).mul (continuous_id.pow _)) ((hat_compactSupport step_pos j).mul_right)
  simp only [moments,selectorTest]
  simp_rw [weight_moment_eq (T _) (hm _) _ _ _ _ (hi _ k),
    weight_moment_eq id measurable_id _ _ _ _ (gaussian_pow_integrable k)]
  by_cases he : i = middle gridN
  · simp only [he,ite_true]
    exact (hh (middle gridN)).add ((hM k).sub (tendsto_finsetSum Finset.univ (fun j _ => hh j)))
  · simp only [he,ite_false,add_zero]
    exact hh i

theorem weight_le_one (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    weight N δ i t ≤ 1 := by
  calc weight N δ i t ≤ ∑ j, weight N δ j t :=
      Finset.single_le_sum (fun j _ => weight_nonneg N δ j t) (Finset.mem_univ i)
    _ = 1 := weight_sum ..

theorem gaussian_selector_integrable (k : Fin 3) (i : Leaves) :
    Integrable (fun x : ℝ => selectorTest i x*x^(k:ℕ)) (gaussianReal 0 1) := by
  apply (gaussian_pow_integrable k).norm.mono' (by dsimp [selectorTest]; fun_prop)
  filter_upwards [] with x
  change |weight gridN step i x*x^(k:ℕ)| ≤ |x^(k:ℕ)|
  rw [abs_mul,abs_of_nonneg (weight_nonneg ..)]
  exact mul_le_of_le_one_left (abs_nonneg _) (weight_le_one ..)

theorem quadratic_moment_formula {P : Measure ℝ} (w : ℝ → ℝ)
    (h0 : Integrable w P) (h1 : Integrable (fun x => w x*x) P)
    (h2 : Integrable (fun x => w x*x^2) P) (a v : ℝ) :
    (∫ x, w x*((1+x-a)^2+v) ∂P) = (∫ x, w x*x^2 ∂P) +
      2*(1-a)*(∫ x, w x*x ∂P) + ((1-a)^2+v)*(∫ x, w x ∂P) := by
  have he : (fun x => w x*((1+x-a)^2+v)) = fun x =>
      w x*x^2 + (2*(1-a))*(w x*x) + ((1-a)^2+v)*w x := by funext x; ring
  rw [he,integral_add (f := fun x => w x*x^2+(2*(1-a))*(w x*x))
    (g := fun x => ((1-a)^2+v)*w x) (h2.add (h1.const_mul _)) (h0.const_mul _),
    integral_add h2 (h1.const_mul _), integral_const_mul,integral_const_mul]

def gaussianLeafMoments : Fin 3 → Leaves → ℝ := moments (gaussianReal 0 1) id leafTest
def gaussianSelectorMoments : Fin 3 → Leaves → ℝ := moments (gaussianReal 0 1) id selectorTest

@[simp] theorem gaussianLeaf_zero (i : Leaves) : gaussianLeafMoments 0 i = GaussianGain.beta i := by
  simp only [gaussianLeafMoments,moments,Fin.val_zero,pow_zero,mul_one,GaussianGain.beta,mass,id_eq]
@[simp] theorem gaussianLeaf_mean (i : Leaves) : means gaussianLeafMoments i = mu i := by
  simp only [means,gaussianLeafMoments,moments,Fin.val_zero,Fin.val_one,pow_zero,pow_one,mul_one,
    mu,mean,mass,id_eq]
@[simp] theorem gaussianLeaf_var (i : Leaves) : vars gaussianLeafMoments i = sigma i := by
  rw [vars,gaussianLeaf_mean]
  simp only [gaussianLeafMoments,moments,Fin.val_zero,pow_zero,mul_one,
    sigma,SmoothGaussian.variance,mass,id_eq,mu]
  rfl

theorem gaussianGain_eq : gain gaussianLeafMoments gaussianSelectorMoments =
    (∏ i : Leaves, GaussianGain.beta i) * (1+totalVariance-J) := by
  have hi0 (i) : Integrable (selectorTest i) (gaussianReal 0 1) := by
    simpa only [Fin.val_zero,pow_zero,mul_one] using gaussian_selector_integrable 0 i
  have hi1 (i) : Integrable (fun x => selectorTest i x*x) (gaussianReal 0 1) := by
    simpa only [Fin.val_one,pow_one] using gaussian_selector_integrable 1 i
  have hi2 (i) : Integrable (fun x => selectorTest i x*x^2) (gaussianReal 0 1) :=
    gaussian_selector_integrable 2 i
  have hik (i) : Integrable (fun x => selectorTest i x*((1+x-mu i)^2+otherVariance i)/GaussianGain.beta i)
      (gaussianReal 0 1) := by
    have he : (fun x => selectorTest i x*((1+x-mu i)^2+otherVariance i)) = fun x =>
        selectorTest i x*x^2 + (2*(1-mu i))*(selectorTest i x*x) +
          ((1-mu i)^2+otherVariance i)*selectorTest i x := by funext x; ring
    apply Integrable.div_const
    rw [he]
    exact ((hi2 i).add ((hi1 i).const_mul _)).add ((hi0 i).const_mul _)
  have hJ : J = ∑ i, (gaussianSelectorMoments 2 i + 2*(1-mu i)*gaussianSelectorMoments 1 i +
      ((1-mu i)^2+otherVariance i)*gaussianSelectorMoments 0 i) / GaussianGain.beta i := by
    change (∫ t, ∑ i, selectorTest i t*((1+t-mu i)^2+otherVariance i)/GaussianGain.beta i
      ∂gaussianReal 0 1) = _
    rw [integral_finsetSum Finset.univ (fun i _ => hik i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_div,quadratic_moment_formula _ (hi0 i) (hi1 i) (hi2 i)]
    simp only [gaussianSelectorMoments,moments,Fin.val_zero,Fin.val_one,pow_zero,pow_one,mul_one,id_eq]
    rfl
  simp only [gain,gaussianLeaf_zero,gaussianLeaf_mean,gaussianLeaf_var,totalVariance,hJ,otherVariance]

theorem gaussianGain_pos : 0 < gain gaussianLeafMoments gaussianSelectorMoments := by
  rw [gaussianGain_eq]
  exact positive_gaussian_deficit

def eta : ℝ := gain gaussianLeafMoments gaussianSelectorMoments / 2

theorem eta_pos : 0 < eta := div_pos gaussianGain_pos (by norm_num)

theorem eventually_positive_gain {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ω n → ℝ) (hm : ∀ n, Measurable (T n))
    (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1))
    (hi : ∀ n (k : Fin 3), Integrable (fun x => (T n x)^(k:ℕ)) (P n))
    (hM : ∀ k : Fin 3, Tendsto (fun n => ∫ x, (T n x)^(k:ℕ) ∂P n) atTop
      (𝓝 (∫ x : ℝ, x^(k:ℕ) ∂gaussianReal 0 1))) :
    ∀ᶠ n in atTop, (∀ i : Leaves, 0 < moments (P n) (T n) leafTest 0 i) ∧
      eta < gain (moments (P n) (T n) leafTest) (moments (P n) (T n) selectorTest) := by
  have hl := leaf_moments_tendsto P T hT
  have hs := selector_moments_tendsto P T hm hT hi hM
  have hg := gain_tendsto (fun n => moments (P n) (T n) leafTest)
    (fun n => moments (P n) (T n) selectorTest) gaussianLeafMoments gaussianSelectorMoments
    hl hs (fun i => by rw [gaussianLeaf_zero]; exact (beta_pos i).ne')
  have he : eta < gain gaussianLeafMoments gaussianSelectorMoments := by
    dsimp [eta]; linarith [gaussianGain_pos]
  have hge := (tendsto_order.mp hg).1 eta he
  have hp : ∀ᶠ n in atTop, ∀ i : Leaves, 0 < moments (P n) (T n) leafTest 0 i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hl 0 i).eventually (lt_mem_nhds (by
      change 0 < gaussianLeafMoments 0 i
      rw [gaussianLeaf_zero]; exact beta_pos i))
  exact hp.and hge

end MomentTransfer
end SquareRootDegree

end

end OAI
