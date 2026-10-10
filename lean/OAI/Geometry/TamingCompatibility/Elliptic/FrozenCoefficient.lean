import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.PerturbationNeg

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution Filter Function EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Topology ContDiff BoundedContinuousFunction
section CoefficientBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in

lemma continuous_bounded_family {A : Type*} [TopologicalSpace A]
    (f : A → E →ᵇ ℂ) {K : Set E} (hK : IsCompact K)
    (hf : Continuous (fun p : A × E => f p.1 p.2))
    (hs : ∀ t, Function.support (f t) ⊆ K) : Continuous f := by
  let g : A → C(E,ℂ) := fun t => (f t).toContinuousMap
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g hf
  rw [continuous_iff_continuousAt]
  intro t
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
  have h := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
    (hg.continuousAt (x := t))) K hK
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h ε hε] with s hs'
  intro x
  by_cases hx : x ∈ K
  · exact hs' x hx
  · have ht : f t x = 0 := by_contra fun hh => hx (hs t hh)
    have hst : f s x = 0 := by_contra fun hh => hx (hs s hh)
    simp only [ht, hst, dist_self]
    exact hε

omit [FiniteDimensional ℝ E] in
lemma family_derivative_smooth (f : ℝ → 𝓢(E,ℂ))
    (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2)) (v : E) :
    ContDiff ℝ ∞ (fun p : ℝ × E => (∂_{v} (f p.1) : 𝓢(E,ℂ)) p.2) := by
  have hf' : ContDiff ℝ ∞ (fun p : (ℝ × E) × E => f p.1.1 p.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hf'.fderiv_apply (𝕜 := ℝ)
    (f := fun q : ℝ × E => fun x : E => f q.1 x) (g := fun p : ℝ × E => p.2)
    (k := fun _ : ℝ × E => v) contDiff_snd contDiff_const (show (∞ : WithTop ℕ∞)+1 ≤ (∞ : WithTop ℕ∞) by simp)
  simpa only [Function.uncurry, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hd

lemma coefficientSize_continuous_family (n : ℕ) (f : ℝ → 𝓢(E,ℂ))
    {K : Set E} (hK : IsCompact K) (hs : ∀ t, tsupport (f t) ⊆ K)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2)) :
    Continuous (fun t => coefficientSize n (f t)) := by
  induction n generalizing f with
  | zero =>
    apply (continuous_bounded_family (fun t => (f t).toBoundedContinuousFunction)
      hK hf.continuous (fun t => (subset_tsupport _).trans (hs t))).norm
  | succ n ih =>
    apply (ih f hs hf).add
    apply continuous_finsetSum
    intro i _
    exact ih (fun t => ∂_{stdOrthonormalBasis ℝ E i} (f t))
      (fun t => (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans (hs t))
      (family_derivative_smooth f hf _)

def frozenCoefficient (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p : E) (r : ℝ) : 𝓢(E,ℂ) :=
  (hχ.mul_right (f' := fun x => f (p + r • x) - f p)).toSchwartzMap
    ((χ.smooth ⊤).mul ((hf.comp (contDiff_const.add (contDiff_const.smul contDiff_id))).sub
      contDiff_const))

omit [FiniteDimensional ℝ E] in
lemma frozenCoefficient_apply (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p : E) (r : ℝ) (x : E) :
    frozenCoefficient χ hχ f hf p r x = χ x * (f (p + r • x) - f p) := rfl

omit [FiniteDimensional ℝ E] in
lemma frozenCoefficient_zero (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p : E) :
    frozenCoefficient χ hχ f hf p 0 = 0 := by
  ext x
  simp [frozenCoefficient_apply]

lemma coefficientSize_zero (n : ℕ) : coefficientSize (E := E) n 0 = 0 := by
  induction n with
  | zero =>
    have h : (0 : 𝓢(E,ℂ)).toBoundedContinuousFunction = 0 := by ext x; rfl
    simp only [coefficientSize, h, norm_zero]
  | succ n ih => simp only [coefficientSize, LineDeriv.lineDerivOp_zero, ih,
      Finset.sum_const_zero, add_zero]

theorem frozenCoefficient_size_tendsto_zero (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (p : E) :
    Tendsto (fun r => coefficientSize n (frozenCoefficient χ hχ f hf p r))
      (𝓝 0) (𝓝 0) := by
  have hs (r : ℝ) : tsupport (frozenCoefficient χ hχ f hf p r) ⊆ tsupport χ :=
    tsupport_mul_subset_left
  have hfamily : ContDiff ℝ ∞ (fun q : ℝ × E =>
      frozenCoefficient χ hχ f hf p q.1 q.2) :=
    ((χ.smooth ⊤).comp contDiff_snd).mul
      ((hf.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))).sub contDiff_const)
  have hh := (coefficientSize_continuous_family n _ hχ hs hfamily).continuousAt (x := 0)
  simpa only [ContinuousAt, frozenCoefficient_zero, coefficientSize_zero] using hh

end CoefficientBounds

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def frozenPrincipal (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p : E) (r : ℝ) :
    basisIndex E → basisIndex E → 𝓢(E,ℂ) :=
  fun i j => frozenCoefficient χ hχ (a i j) (ha i j) p r

lemma frozen_principal_size_tendsto (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p : E) :
    Tendsto (fun r => principalCoefficientSize (F := F) n (frozenPrincipal χ hχ a ha p r))
      (𝓝 0) (𝓝 0) := by
  unfold principalCoefficientSize frozenPrincipal
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      (frozenCoefficient_size_tendsto_zero n χ hχ (a i j) (ha i j) p).mul_const
        ‖secondDerivative (F := F) (n:ℝ) (stdOrthonormalBasis ℝ E i)
          (stdOrthonormalBasis ℝ E j)‖))
  simpa only [zero_mul, Finset.sum_const_zero] using hh

lemma frozen_weak_size_tendsto
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p : E) :
    Tendsto (fun r => weakPrincipalCoefficientSize (F := F) (frozenPrincipal χ hχ a ha p r))
      (𝓝 0) (𝓝 0) := by
  unfold weakPrincipalCoefficientSize frozenPrincipal
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      (frozenCoefficient_size_tendsto_zero 1 χ hχ (a i j) (ha i j) p).mul_const
        ‖secondDerivative (F := F) (-1) (stdOrthonormalBasis ℝ E i)
          (stdOrthonormalBasis ℝ E j)‖))
  simpa only [zero_mul, Finset.sum_const_zero] using hh

theorem frozen_perturbation_norm_tendsto (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p : E) :
    Tendsto (fun r => ‖perturbation (F := F) n (frozenPrincipal χ hχ a ha p r)‖)
      (𝓝 0) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := product_operator_estimate (E := E) (F := F) n
  apply squeeze_zero (fun _ => norm_nonneg _) (fun r => perturbation_norm_le n hC _)
  simpa only [mul_zero] using (frozen_principal_size_tendsto (F := F) n χ hχ a ha p).const_mul C

theorem frozen_weak_norm_tendsto
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p : E) :
    Tendsto (fun r => ‖perturbationNegOne (F := F) (frozenPrincipal χ hχ a ha p r)‖)
      (𝓝 0) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := productNegOne_operator_estimate (E := E) (F := F)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun r => perturbationNegOne_norm_le hC _)
  simpa only [mul_zero] using (frozen_weak_size_tendsto (F := F) χ hχ a ha p).const_mul C

theorem frozen_eventually_H1_regular
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p : E) :
    ∀ᶠ r in 𝓝 (0:ℝ), ∀ (b : basisIndex E → 𝓢(E,ℂ)) (c g : 𝓢(E,ℂ))
      (u : 𝓢'(E,F)), MemSobolev 1 2 u →
      MemSobolev 0 2 (smulLeftCLM F g
        (perturbedHelmholtz (frozenPrincipal χ hχ a ha p r) u + lowerOrder b c u)) →
      MemSobolev 2 2 (smulLeftCLM F g u) := by
  have hw := (frozen_weak_norm_tendsto (F := F) χ hχ a ha p).eventually
    (gt_mem_nhds (show (0:ℝ)<1 by norm_num))
  have hs := (frozen_perturbation_norm_tendsto (F := F) 0 χ hχ a ha p).eventually
    (gt_mem_nhds (show (0:ℝ)<1 by norm_num))
  filter_upwards [hw, hs] with r hrw hrs
  intro b c g u hu hf
  apply cutoff_H1_regular _ hrw hrs g hu
  have hu' : MemSobolev ((0:ℕ)+1:ℝ) 2 u := by simpa using hu
  have hl : MemSobolev 0 2 (lowerOrder b c u) := by
    simpa only [Nat.cast_zero] using lowerOrder_memSobolev 0 b c hu'
  have hl₀ : MemSobolev (0:ℕ) 2 (lowerOrder b c u) := by
    simpa only [Nat.cast_zero] using hl
  have hg : MemSobolev 0 2 (smulLeftCLM F g (lowerOrder b c u)) := by
    simpa only [Nat.cast_zero] using memSobolev_nat_product (E := E) (F := F) 0 g hl₀
  rw [map_add] at hf
  simpa only [add_sub_cancel_right] using hf.sub hg

end TamingCompatibility.HilbertSobolev

end

end OAI
