import Mathlib
import OAI.Probability.ParisiFinite.ParisiConjugateTransport
import OAI.Probability.ParisiFinite.ParisiCanonicalTransport

namespace OAI

/-! Parisi Reflection. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Set Real Matrix Filter InnerProductSpace
open scoped Topology NNReal RealInnerProductSpace
namespace ParisiSpectral

lemma posSemidef_kernel_variable_average {A B Ω : Type*} [MeasurableSpace Ω]
    (K : Matrix A A ℝ) [Fact K.PosSemidef]
    (μ : B → Measure Ω) (T : B → Ω → A)
    (hi : ∀ b, Integrable (fun z => kernelFeature K (T b z)) (μ b)) :
    Matrix.PosSemidef (fun b c => ∫ z, ∫ w, K (T b z) (T c w) ∂(μ c) ∂(μ b)) := by
  have he (b c : B) : (∫ z, ∫ w, K (T b z) (T c w) ∂(μ c) ∂(μ b)) =
      ⟪∫ z, kernelFeature K (T b z) ∂(μ b), ∫ w, kernelFeature K (T c w) ∂(μ c)⟫_ℝ := by
    simp_rw [← inner_kernelFeature K, integral_inner (hi c)]
    simp_rw [real_inner_comm (∫ w, kernelFeature K (T c w) ∂(μ c))]
    rw [integral_inner (hi b), real_inner_comm]
  simpa only [he] using posSemidef_inner (fun b => ∫ z, kernelFeature K (T b z) ∂(μ b))

lemma gaussian_double_difference_general {f : ℝ → ℝ} (hc : Continuous f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (s t : ℝ≥0) (x : ℝ) :
    (∫ z, ∫ w, f (x+z-w) ∂gaussianReal 0 t ∂gaussianReal 0 s) = heat (s+t) f x := by
  have he (z : ℝ) : (∫ w, f (x+z-w) ∂gaussianReal 0 t) =
      (∫ w, f (x+z+w) ∂gaussianReal 0 t) := by
    have hh := integral_map (μ := gaussianReal 0 t) (f := fun w => f (x+z+w)) measurable_neg.aemeasurable
      ((hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    rw [gaussianReal_map_neg, neg_zero] at hh
    simpa only [sub_eq_add_neg] using hh.symm
  simp_rw [he]
  have hi : Integrable (fun z => f (x+z)) (gaussianReal 0 s ∗ gaussianReal 0 t) := by
    rw [gaussianReal_conv_gaussianReal]
    exact Integrable.of_bound (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable C
      (ae_of_all _ fun z => hC _)
  have hh := integral_conv hi
  rw [gaussianReal_conv_gaussianReal, zero_add] at hh
  simpa only [heat, add_assoc] using hh.symm

 

lemma PositiveDefinite.heat_reflection {f : ℝ → ℝ} (hf : PositiveDefinite f)
    (hc : Continuous f) :
    Matrix.PosSemidef (fun p q : ℝ≥0 × ℝ => ParisiSpectral.heat (p.1+q.1) f (p.2-q.2)) := by
  let K : Matrix ℝ ℝ ℝ := fun x y => f (x-y)
  let : Fact K.PosSemidef := ⟨hf⟩
  have hcont : Continuous (kernelFeature K) := hf.continuous_feature hc
  have hi (p : ℝ≥0 × ℝ) : Integrable (fun z => kernelFeature K (p.2+z)) (gaussianReal 0 p.1) := by
    apply Integrable.of_bound (hcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (sqrt (f 0))
    filter_upwards [] with z
    have hn := norm_kernelFeature_sq K (p.2+z)
    simp only [K, sub_self] at hn
    exact (le_sqrt (norm_nonneg _) hf.at_zero).mpr hn.le
  have hp := posSemidef_kernel_variable_average K (fun p : ℝ≥0 × ℝ => gaussianReal 0 p.1)
    (fun p z => p.2+z) hi
  have he : (fun p q : ℝ≥0 × ℝ => ∫ z, ∫ w, K (p.2+z) (q.2+w)
      ∂gaussianReal 0 q.1 ∂gaussianReal 0 p.1) =
      (fun p q : ℝ≥0 × ℝ => ParisiSpectral.heat (p.1+q.1) f (p.2-q.2)) := by
    funext p q
    rw [← gaussian_double_difference_general hc hf.norm_le p.1 q.1 (p.2-q.2)]
    apply integral_congr_ae
    filter_upwards [] with z
    apply integral_congr_ae
    filter_upwards [] with w
    change f ((p.2+z)-(q.2+w)) = f (p.2-q.2+z-w)
    congr 1
    ring
  exact (congrArg Matrix.PosSemidef he).mp hp

lemma PositiveDefinite.heat_abs_le {g : ℝ → ℝ} (hg : PositiveDefinite g)
    (hc : Continuous g) (t : ℝ≥0) (x : ℝ) : |ParisiSpectral.heat t g x| ≤ g 0 := by
  apply abs_integral_le_integral_abs.trans
  have hi : Integrable (fun z => |g (x+z)|) (gaussianReal 0 t) :=
    Integrable.of_bound (hc.comp (continuous_const.add continuous_id)).abs.aestronglyMeasurable
      (g 0) (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs, abs_abs] using hg.norm_le (x+z))
  have hh := integral_mono hi (integrable_const (g 0))
    (fun z => by simpa only [Real.norm_eq_abs] using hg.norm_le (x+z))
  simpa only [integral_const, probReal_univ, one_smul] using hh

end ParisiSpectral

open MeasureTheory ProbabilityTheory Set Real Matrix Filter InnerProductSpace
open scoped Topology NNReal RealInnerProductSpace BigOperators
namespace ParisiSpectral

lemma hasSum_entropy_remainder {u : ℝ} (hu : |u| < 1) :
    HasSum (fun n : ℕ => u^(n+2)/((n+1:ℝ)*(n+2))) ((1-u)*log (1-u)+u) := by
  have h := hasSum_pow_div_log_of_abs_lt_one hu
  have hs : HasSum (fun n : ℕ => u^(n+2)/(n+2)) (-log (1-u)-u) := by
    have ht := (hasSum_nat_add_iff' (f := fun n : ℕ => u^(n+1)/(n+1)) 1).mpr h
    simpa only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_one, div_one,
      Nat.cast_zero, Nat.cast_add, add_assoc, one_add_one_eq_two] using ht
  have hm := (h.mul_left u).sub hs
  convert! hm using 1
  · funext n
    have hn : (n+1:ℝ) ≠ 0 := by positivity
    have hn2 : (n+2:ℝ) ≠ 0 := by positivity
    rw [pow_succ, pow_succ]
    field_simp
    ring
  · ring

lemma posSemidef_hadamard_pow {A : Type*} {K : Matrix A A ℝ}
    (hK : K.PosSemidef) (n : ℕ) : Matrix.PosSemidef (fun a b => (K a b)^n) := by
  induction n with
  | zero =>
    simpa only [pow_zero, RCLike.inner_apply, map_one, star_trivial, mul_one] using
      (posSemidef_inner (fun _ : A => (1:ℝ)))
  | succ n ih =>
    have hh : Matrix.PosSemidef (fun a b => (K a b)^n * K a b) := ih.hadamard hK
    simpa only [pow_succ] using hh

 

lemma posSemidef_entropy_remainder {A : Type*} (c g : Matrix A A ℝ)
    (hc : ∀ a b, 0 < c a b) (hg : g.PosSemidef)
    (hgc : ∀ a b, |g a b| < c a b)
    (hinv : ∀ n : ℕ, Matrix.PosSemidef (fun a b => (c a b)^(-(n+1:ℝ)))) :
    Matrix.PosSemidef (fun a b =>
      (c a b-g a b)*log (c a b-g a b)-c a b*log (c a b)+
        (1+log (c a b))*g a b) := by
  classical
  let F (n : ℕ) : Matrix A A ℝ := fun a b =>
    (g a b)^(n+2)*(c a b)^(-(n+1:ℝ))/((n+1:ℝ)*(n+2))
  have hF (n : ℕ) : (F n).PosSemidef := by
    have hh := ((posSemidef_hadamard_pow hg (n+2)).hadamard (hinv n)).smul
      (show (0:ℝ) ≤ ((n+1:ℝ)*(n+2))⁻¹ by positivity)
    convert! hh using 1
    funext a b
    dsimp only [F]
    change _ = ((n+1:ℝ)*(n+2))⁻¹*((g a b)^(n+2)*(c a b)^(-(n+1:ℝ)))
    rw [div_eq_mul_inv]
    ring
  have hs (a b : A) : HasSum (fun n => F n a b)
      ((c a b-g a b)*log (c a b-g a b)-c a b*log (c a b)+
        (1+log (c a b))*g a b) := by
    have hu : |g a b/c a b| < 1 := by
      rw [abs_div, abs_of_pos (hc a b), div_lt_one (hc a b)]
      exact hgc a b
    have hh := (hasSum_entropy_remainder hu).mul_left (c a b)
    have hdiff : 0 < c a b-g a b := by have := le_abs_self (g a b); linarith [hgc a b]
    have he : 1-g a b/c a b = (c a b-g a b)/c a b := by field_simp [(hc a b).ne']
    convert! hh using 1
    · funext n
      dsimp only [F]
      have hr : (c a b)^(-(n+1:ℝ)) = ((c a b)^(n+1))⁻¹ := by
        rw [rpow_neg (hc a b).le]
        norm_cast
      rw [hr, div_pow]
      field_simp [(hc a b).ne']
      ring
    · rw [he, log_div hdiff.ne' (hc a b).ne']
      field_simp [(hc a b).ne']
      ring
  apply PositiveDefinite.posSemidef_limit (l := atTop)
    (K := fun N : ℕ => ∑ n ∈ Finset.range N, F n)
  · intro N
    exact Matrix.posSemidef_sum (Finset.range N) (fun n _ => hF n)
  · intro a b
    have he : (fun i : ℕ => (∑ n ∈ Finset.range i, F n) a b) =
        (fun i : ℕ => ∑ n ∈ Finset.range i, F n a b) := by
      funext i
      exact Matrix.sum_apply a b (Finset.range i) F
    rw [he]
    exact (hs a b).tendsto_sum_nat

end ParisiSpectral

 

open MeasureTheory ProbabilityTheory Set Real Matrix Filter InnerProductSpace
open scoped Topology NNReal RealInnerProductSpace BigOperators
namespace ParisiSpectral

lemma posSemidef_kernel_finite_combination {A B I : Type*} [Fintype I]
    (K : Matrix A A ℝ) [Fact K.PosSemidef] (T : B → I → A) (c : B → I → ℝ) :
    Matrix.PosSemidef (fun b d => ∑ i, ∑ j, c b i*c d j*K (T b i) (T d j)) := by
  have he b d : (∑ i, ∑ j, c b i*c d j*K (T b i) (T d j)) =
      ⟪∑ i, c b i • kernelFeature K (T b i),∑ j, c d j • kernelFeature K (T d j)⟫_ℝ := by
    simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,inner_kernelFeature]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simpa only [he] using posSemidef_inner (fun b => ∑ i, c b i • kernelFeature K (T b i))

lemma scaled_taylor_tendsto {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f)
    (x k : ℝ) :
    Tendsto (fun e => (f (x+k*e)-taylorWithinEval f n univ x (x+k*e))/e^n)
      (𝓝 (0:ℝ)) (𝓝 0) := by
  have ht := Real.taylor_tendsto (f := f) (n := n) convex_univ (mem_univ x) hf.contDiffOn
  simp only [nhdsWithin_univ] at ht
  have hc : Tendsto (fun e : ℝ => x+k*e) (𝓝 0) (𝓝 x) := by
    simpa only [mul_zero,add_zero] using
      ((show Continuous (fun e : ℝ => x+k*e) from by fun_prop).tendsto (0:ℝ))
  have hh := (ht.comp hc).const_mul (k^n)
  simp only [mul_zero] at hh
  apply hh.congr
  intro e
  dsimp only [Function.comp_def]
  rw [add_sub_cancel_left,mul_pow]
  by_cases hk : k=0
  · simp [hk,taylorWithinEval_self]
  · field_simp

def jetWeight (n i : Fin 3) : ℝ :=
  match n.val,i.val with
  | 0,0 => 1
  | 0,_ => 0
  | 1,0 => -1
  | 1,1 => 1
  | 1,_ => 0
  | _,0 => 1
  | _,1 => -2
  | _,_ => 1

def differenceJet (f : ℝ → ℝ) (n m : Fin 3) (x e : ℝ) : ℝ :=
  (∑ i : Fin 3,∑ j : Fin 3,
    (jetWeight n i)*(jetWeight m j)*f (x+((i:ℝ)-(j:ℝ))*e))/e^((n:ℕ)+(m:ℕ))

lemma differenceJet_tendsto {f : ℝ → ℝ} (n m : Fin 3)
    (hf : ContDiff ℝ ((n:ℕ)+(m:ℕ)) f) (x : ℝ) :
    Tendsto (differenceJet f n m x) (𝓝[≠] (0:ℝ))
      (𝓝 ((-1:ℝ)^(m:ℕ)*iteratedDeriv ((n:ℕ)+(m:ℕ)) f x)) := by
  have hs (i j : Fin 3) := (scaled_taylor_tendsto hf x ((i:ℝ)-(j:ℝ))).const_mul
    (jetWeight n i*jetWeight m j)
  have ht := tendsto_finsetSum Finset.univ (fun i hi =>
    tendsto_finsetSum Finset.univ (fun j hj => hs i j))
  simp only [mul_zero,Finset.sum_const_zero] at ht
  have ht' := ht.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 (0:ℝ))
  have he : (fun e : ℝ => ∑ i : Fin 3,∑ j : Fin 3,
      jetWeight n i*jetWeight m j*((f (x+((i:ℝ)-(j:ℝ))*e)-
        taylorWithinEval f ((n:ℕ)+(m:ℕ)) univ x (x+((i:ℝ)-(j:ℝ))*e))/e^((n:ℕ)+(m:ℕ))))
      =ᶠ[𝓝[≠] (0:ℝ)] (fun e => differenceJet f n m x e-
        (-1:ℝ)^(m:ℕ)*iteratedDeriv ((n:ℕ)+(m:ℕ)) f x) := by
    filter_upwards [self_mem_nhdsWithin] with e he
    have hne : e≠0 := he
    fin_cases n <;> fin_cases m <;>
      norm_num [differenceJet,jetWeight,Fin.sum_univ_three,taylorWithinEval_succ,
        taylor_within_zero_eval,iteratedDerivWithin_univ,smul_eq_mul,Nat.factorial] <;>
      field_simp [hne] <;> norm_num <;> ring
  have hh := ht'.congr' he
  exact (tendsto_sub_nhds_zero_iff).mp hh

 

lemma posSemidef_spatial_jets {T I : Type*} (F : T → T → ℝ → ℝ)
    (hF : Matrix.PosSemidef (fun p q : T×ℝ => F p.1 q.1 (p.2-q.2)))
    (ord : I → Fin 3)
    (hc : ∀ t u i j,ContDiff ℝ ((ord i:ℕ)+(ord j:ℕ)) (F t u)) :
    Matrix.PosSemidef (fun p q : T×I×ℝ =>
      (-1:ℝ)^(ord q.2.1:ℕ)*iteratedDeriv ((ord p.2.1:ℕ)+(ord q.2.1:ℕ))
        (F p.1 q.1) (p.2.2-q.2.2)) := by
  let K : Matrix (T×ℝ) (T×ℝ) ℝ := fun p q => F p.1 q.1 (p.2-q.2)
  let : Fact K.PosSemidef := ⟨hF⟩
  let B (e : ℝ) : Matrix (T×I×ℝ) (T×I×ℝ) ℝ := fun p q =>
    ∑ k : Fin 3,∑ l : Fin 3,
      (jetWeight (ord p.2.1) k/e^(ord p.2.1:ℕ))*
      (jetWeight (ord q.2.1) l/e^(ord q.2.1:ℕ))*
      F p.1 q.1 ((p.2.2+(k:ℝ)*e)-(q.2.2+(l:ℝ)*e))
  have hp (e : ℝ) : (B e).PosSemidef :=
    posSemidef_kernel_finite_combination K
      (fun (p : T×I×ℝ) (k : Fin 3) => (p.1,p.2.2+(k:ℝ)*e))
      (fun (p : T×I×ℝ) (k : Fin 3) => jetWeight (ord p.2.1) k/e^(ord p.2.1:ℕ))
  apply PositiveDefinite.posSemidef_limit (l := 𝓝[≠] (0:ℝ)) hp
  intro p q
  have he (e : ℝ) : B e p q = differenceJet (F p.1 q.1) (ord p.2.1) (ord q.2.1)
      (p.2.2-q.2.2) e := by
    dsimp only [B,differenceJet]
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    rw [show (p.2.2+(k:ℝ)*e)-(q.2.2+(l:ℝ)*e)=
      (p.2.2-q.2.2)+((k:ℝ)-(l:ℝ))*e by ring]
    rw [pow_add]
    ring
  simpa only [he] using differenceJet_tendsto (ord p.2.1) (ord q.2.1)
    (hc p.1 q.1 p.2.1 q.2.1) (p.2.2-q.2.2)

end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Set Real Matrix Filter InnerProductSpace
open scoped Topology NNReal RealInnerProductSpace BigOperators
namespace ParisiSpectral

def PositiveOnPD (μ : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → PositiveDefinite f → 0≤∫ x,f x ∂μ

lemma stationary_kernel_finsupp {A : Type*} (κ : A → A → ℝ → ℝ)
    (hκ : Matrix.PosSemidef (fun p q : A × ℝ => κ p.1 q.1 (p.2-q.2)))
    (c : A →₀ ℝ) : PositiveDefinite (fun x => ∑ a∈c.support,∑ b∈c.support,c a*c b*κ a b x) := by
  classical
  let K : Matrix (A × ℝ) (A × ℝ) ℝ := fun p q => κ p.1 q.1 (p.2-q.2)
  let : Fact K.PosSemidef := ⟨hκ⟩
  have he (x y : ℝ) : (∑ a∈c.support,∑ b∈c.support,c a*c b*κ a b (x-y)) =
      ⟪∑ a∈c.support,c a • kernelFeature K (a,x),∑ b∈c.support,c b • kernelFeature K (b,y)⟫_ℝ := by
    simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,inner_kernelFeature]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [K]
    ring
  simpa only [PositiveDefinite,he] using
    posSemidef_inner (fun x => ∑ a∈c.support,c a • kernelFeature K (a,x))

lemma PositiveOnPD.kernel_integral {A : Type*} {μ : Measure ℝ} (hμ : PositiveOnPD μ)
    (κ : A → A → ℝ → ℝ)
    (hκ : Matrix.PosSemidef (fun p q : A × ℝ => κ p.1 q.1 (p.2-q.2)))
    (hc : ∀ a b,Continuous (κ a b)) (hi : ∀ a b,Integrable (κ a b) μ)
    (hsym : ∀ a b,κ a b=κ b a) :
    Matrix.PosSemidef (fun a b => ∫ x,κ a b x ∂μ) := by
  classical
  refine ⟨?_,?_⟩
  · apply Matrix.IsHermitian.ext
    intro a b
    simp only [star_trivial]
    rw [hsym b a]
  · intro c
    have hs := stationary_kernel_finsupp κ hκ c
    have hp := hμ _ (by
      apply continuous_finsetSum
      intro a ha
      apply continuous_finsetSum
      intro b hb
      exact continuous_const.mul (hc a b)) hs
    have hi' (a b : A) : Integrable (fun x => c a*c b*κ a b x) μ := (hi a b).const_mul _
    rw [integral_finsetSum c.support (fun a ha =>
      integrable_finsetSum _ (fun b hb => hi' a b))] at hp
    simp_rw [integral_finsetSum c.support (fun b hb => hi' _ b),integral_const_mul] at hp
    simpa only [Finsupp.sum,star_trivial,mul_assoc,mul_left_comm,mul_comm] using hp

lemma continuous_kernelFeature_comp {A B : Type*} [TopologicalSpace B]
    (K : Matrix A A ℝ) [Fact K.PosSemidef] (T : B → A)
    (hc : Continuous (fun p : B × B => K (T p.1) (T p.2))) :
    Continuous (fun x => kernelFeature K (T x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  change Filter.Tendsto _ _ _
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ht : Tendsto (fun y => K (T y) (T y)+K (T x) (T x)-2*K (T y) (T x)) (𝓝 x) (𝓝 0) := by
    have h1 : Continuous (fun y => K (T y) (T y)) := hc.comp (continuous_id.prodMk continuous_id)
    have h2 : Continuous (fun y => K (T y) (T x)) := hc.comp (continuous_id.prodMk (continuous_const (y := x)))
    have hh := (h1.add (continuous_const (y := K (T x) (T x))) |>.sub (h2.const_mul 2)).tendsto x
    change Tendsto _ (𝓝 x) (𝓝 (K (T x) (T x)+K (T x) (T x)-2*K (T x) (T x))) at hh
    rwa [show K (T x) (T x)+K (T x) (T x)-2*K (T x) (T x)=0 by ring] at hh
  filter_upwards [ht.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with y hy
  rw [dist_eq_norm]
  have hn := norm_kernelFeature_sub_sq K (T y) (T x)
  nlinarith [norm_nonneg (kernelFeature K (T y)-kernelFeature K (T x))]

lemma stationary_kernel_bounded {A : Type*} (κ : A → A → ℝ → ℝ)
    (hκ : Matrix.PosSemidef (fun p q : A × ℝ => κ p.1 q.1 (p.2-q.2))) (a b : A) :
    ∀ x,‖κ a b x‖ ≤ sqrt (κ a a 0)*sqrt (κ b b 0) := by
  let K : Matrix (A × ℝ) (A × ℝ) ℝ := fun p q => κ p.1 q.1 (p.2-q.2)
  let : Fact K.PosSemidef := ⟨hκ⟩
  have hn (d : A) (x : ℝ) : ‖kernelFeature K (d,x)‖=sqrt (κ d d 0) := by
    have hh := norm_kernelFeature_sq K (d,x)
    simp only [K,sub_self] at hh
    rw [←hh,sqrt_sq (norm_nonneg _)]
  intro x
  have hh := abs_real_inner_le_norm (kernelFeature K (a,x)) (kernelFeature K (b,0))
  rwa [inner_kernelFeature,hn,hn,show K (a,x) (b,0)=κ a b x from by simp [K],←Real.norm_eq_abs] at hh

lemma stationary_kernel_heat {A : Type*} (κ : A → A → ℝ → ℝ)
    (hκ : Matrix.PosSemidef (fun p q : A × ℝ => κ p.1 q.1 (p.2-q.2)))
    (hc : ∀ a b,Continuous (κ a b)) (s : A → ℝ≥0) :
    Matrix.PosSemidef (fun p q : A × ℝ => heat (s p.1+s q.1) (κ p.1 q.1) (p.2-q.2)) := by
  let K : Matrix (A × ℝ) (A × ℝ) ℝ := fun p q => κ p.1 q.1 (p.2-q.2)
  let : Fact K.PosSemidef := ⟨hκ⟩
  have hi (p : A × ℝ) : Integrable (fun z => kernelFeature K (p.1,p.2+z)) (gaussianReal 0 (s p.1)) := by
    have hct : Continuous (fun z => kernelFeature K (p.1,p.2+z)) := by
      apply continuous_kernelFeature_comp
      change Continuous (fun z : ℝ × ℝ => κ p.1 p.1 ((p.2+z.1)-(p.2+z.2)))
      exact (hc _ _).comp (by fun_prop)
    apply Integrable.of_bound hct.aestronglyMeasurable (sqrt (κ p.1 p.1 0))
    filter_upwards [] with z
    have hn := norm_kernelFeature_sq K (p.1,p.2+z)
    simp only [K,sub_self] at hn
    have hp : 0≤κ p.1 p.1 0 := by simpa only [sub_self] using hκ.diag_nonneg (i := p)
    exact (le_sqrt (norm_nonneg _) hp).mpr hn.le
  have hh := posSemidef_kernel_variable_average K (fun p : A × ℝ => gaussianReal 0 (s p.1))
    (fun p z => (p.1,p.2+z)) hi
  apply (congrArg Matrix.PosSemidef (show (fun p q : A × ℝ =>
    ∫ z,∫ w,K (p.1,p.2+z) (q.1,q.2+w) ∂gaussianReal 0 (s q.1) ∂gaussianReal 0 (s p.1))=
    (fun p q : A × ℝ => heat (s p.1+s q.1) (κ p.1 q.1) (p.2-q.2)) from ?_)).mp hh
  funext p q
  rw [←gaussian_double_difference_general (hc _ _) (stationary_kernel_bounded κ hκ _ _) (s p.1) (s q.1)]
  congr 1
  funext z
  congr 1
  funext w
  dsimp only [K]
  congr 1
  ring

end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Filter Function Set Real
open scoped Topology NNReal
namespace ParisiFinite.BoundedCoefficient
open ParisiPath ParisiSpectral
variable {β : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

def conjugateMeasure (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (c : BoundedCoefficient β)
    (hβ : 0<β) (t : Time) : Measure ℝ :=
  (P.map (fun ω => solution (c.driftData hβ) (brownianPath W ω) t)).withDensity
    (fun x => ENNReal.ofReal (exp (-(c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩ x)))

lemma integral_conjugateMeasure (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) (t : Time) {f : ℝ → ℝ} (hf : StronglyMeasurable f) :
    (∫ x,f x ∂conjugateMeasure P W c hβ t)=
      ∫ ω,exp (-(c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩
        (solution (c.driftData hβ) (brownianPath W ω) t))*
        f (solution (c.driftData hβ) (brownianPath W ω) t) ∂P := by
  have he : Continuous (fun x => exp (-(c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩ x)) :=
    (continuous_const.mul (field_lipschitz β hβ c.mono c.bound _).continuous).rexp
  rw [conjugateMeasure,integral_withDensity_eq_integral_toReal_smul he.measurable.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (exp_pos _).le,smul_eq_mul]
  exact integral_map (aemeasurable_solution_eval _ _ (brownianPath_aemeasurable_eval hW) t)
    (he.stronglyMeasurable.mul hf).aestronglyMeasurable

lemma conjugateMeasure_finite (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) (t : Time) (ha : 0<c.val ⟨t,t.property.1⟩) :
    IsFiniteMeasure (conjugateMeasure P W c hβ t) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hp := (field_coshCone β hβ c.mono c.bound ⟨t,t.property.1⟩ (by exact_mod_cast ha) le_rfl).neg_exp_positiveDefinite
    (by exact_mod_cast ha) (c.val ⟨t,t.property.1⟩).coe_nonneg
  have hc : Continuous (fun x => exp (-(c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩ x)) :=
    (continuous_const.mul (field_lipschitz β hβ c.mono c.bound _).continuous).rexp
  exact isFiniteMeasure_withDensity_ofReal (Integrable.of_bound hc.aestronglyMeasurable _
    (ae_of_all _ hp.norm_le)).hasFiniteIntegral

lemma conjugateMeasure_positive (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) (t : Time) (ht0 : 0<(t:ℝ))
    (ha : 0<c.val ⟨t,t.property.1⟩) : PositiveOnPD (conjugateMeasure P W c hβ t) := by
  intro ψ hψc hψ
  rw [c.integral_conjugateMeasure hβ hW t hψc.stronglyMeasurable]
  exact c.conjugate_expectation_nonneg hβ hW ⟨t,t.property.1⟩ (by intro he; have hv := congrArg (fun r : ℝ≥0 => (r : ℝ)) he; exact ht0.ne' hv)
    (by exact_mod_cast t.property.2) ha hψ hψc

lemma conjugateMeasure_firstMoment (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) (t : Time) (ha : 0<c.val ⟨t,t.property.1⟩) :
    Integrable (fun x : ℝ => |x|) (conjugateMeasure P W c hβ t) := by
  have he : Continuous (fun x => exp (-(c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩ x)) :=
    (continuous_const.mul (field_lipschitz β hβ c.mono c.bound _).continuous).rexp
  have hp := (field_coshCone β hβ c.mono c.bound ⟨t,t.property.1⟩ (by exact_mod_cast ha) le_rfl).neg_exp_positiveDefinite
    (by exact_mod_cast ha) (c.val ⟨t,t.property.1⟩).coe_nonneg
  rw [conjugateMeasure,integrable_withDensity_iff_integrable_smul' he.measurable.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (exp_pos _).le,smul_eq_mul]
  have hi : Integrable (fun x : ℝ => |x|)
      (P.map (fun ω => solution (c.driftData hβ) (brownianPath W ω) t)) :=
    (integrable_map_measure continuous_abs.aestronglyMeasurable
      (aemeasurable_solution_eval _ _ (brownianPath_aemeasurable_eval hW) t)).mpr
      (brownian_solution_integrable hW _ t).abs
  exact hi.bdd_mul he.aestronglyMeasurable (ae_of_all _ hp.norm_le)

end ParisiFinite.BoundedCoefficient

 

 

open MeasureTheory ProbabilityTheory Set Real Matrix Filter InnerProductSpace
open scoped Topology NNReal RealInnerProductSpace BigOperators
namespace ParisiSpectral
lemma continuous_heat {f : ℝ → ℝ} (hc : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖≤C) (t : ℝ≥0) : Continuous (heat t f) := by
  apply continuous_of_dominated (bound := fun _ => C)
    (fun x => (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (fun x => ae_of_all _ fun z => hC _) (integrable_const _)
    (ae_of_all _ fun z => hc.comp (continuous_id.add continuous_const))

lemma heat_heat {f : ℝ → ℝ} (hc : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖≤C) (s t : ℝ≥0) : heat s (heat t f)=heat (s+t) f := by
  funext x
  have hh := gaussian_double_difference_general hc hC s t x
  have he (z : ℝ) : (∫ w,f (x+z-w) ∂gaussianReal 0 t)=heat t f (x+z) := by
    have hh := integral_map (μ := gaussianReal 0 t) (f := fun w => f (x+z+w)) measurable_neg.aemeasurable
      ((hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    rw [gaussianReal_map_neg,neg_zero] at hh
    simpa only [heat,sub_eq_add_neg] using hh.symm
  simpa only [he,heat] using hh

lemma PositiveDefinite.sub_heat {f : ℝ → ℝ} (hf : PositiveDefinite f)
    (hc : Continuous f) (t : ℝ≥0) : PositiveDefinite (fun x => f x-ParisiSpectral.heat t f x) := by
  let K : Matrix ℝ ℝ ℝ := fun x y => f (x-y)
  let : Fact K.PosSemidef := ⟨hf⟩
  have hp (z : ℝ) : Matrix.PosSemidef (fun x y : ℝ =>
      2*f (x-y)-f (x-y+z)-f (x-y-z)) := by
    have hh := posSemidef_inner (fun x => kernelFeature K x-kernelFeature K (x+z))
    have he : (fun x y : ℝ => 2*f (x-y)-f (x-y+z)-f (x-y-z)) =
        (fun x y : ℝ => ⟪kernelFeature K x-kernelFeature K (x+z),kernelFeature K y-kernelFeature K (y+z)⟫_ℝ) := by
      funext x y
      simp only [inner_sub_left,inner_sub_right,inner_kernelFeature]
      dsimp only [K]
      rw [show x-(y+z)=x-y-z by ring,show x+z-y=x-y+z by ring,
        show x+z-(y+z)=x-y by ring]
      ring
    rw [he]
    exact hh
  have hi (x y : ℝ) : Integrable (fun z => 2*f (x-y)-f (x-y+z)-f (x-y-z)) (gaussianReal 0 t) := by
    exact ((integrable_const _).sub (Integrable.of_bound
      (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable _ (ae_of_all _ fun z => hf.norm_le _))).sub
      (Integrable.of_bound (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable _
        (ae_of_all _ fun z => hf.norm_le _))
  have hh := posSemidef_integral (gaussianReal 0 t) (fun z x y => 2*f (x-y)-f (x-y+z)-f (x-y-z))
    (ae_of_all _ hp) hi
  have hv (x : ℝ) : (∫ z,f (x-z) ∂gaussianReal 0 t) = ParisiSpectral.heat t f x := by
    have h := integral_map (μ := gaussianReal 0 t) (f := fun z => f (x+z)) measurable_neg.aemeasurable
      (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    rw [gaussianReal_map_neg,neg_zero] at h
    simpa only [ParisiSpectral.heat,sub_eq_add_neg] using h.symm
  have he (x y : ℝ) : (∫ z,2*f (x-y)-f (x-y+z)-f (x-y-z) ∂gaussianReal 0 t)=
      2*(f (x-y)-ParisiSpectral.heat t f (x-y)) := by
    have hi1 : Integrable (fun z => f (x-y+z)) (gaussianReal 0 t) :=
      Integrable.of_bound (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable _
        (ae_of_all _ fun z => hf.norm_le _)
    have hi2 : Integrable (fun z => f (x-y-z)) (gaussianReal 0 t) :=
      Integrable.of_bound (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable _
        (ae_of_all _ fun z => hf.norm_le _)
    rw [integral_sub (f := fun z => 2*f (x-y)-f (x-y+z))
      (g := fun z => f (x-y-z)) ((integrable_const (2*f (x-y))).sub hi1) hi2,
      integral_sub (integrable_const (2*f (x-y))) hi1,hv]
    simp only [integral_const,probReal_univ,one_smul,ParisiSpectral.heat]
    ring
  simp_rw [he] at hh
  have hh' := hh.smul (show (0:ℝ)≤(1/2:ℝ) by norm_num)
  have heq : Matrix.of (fun x y : ℝ => f (x-y)-ParisiSpectral.heat t f (x-y)) =
      (1/2:ℝ) • Matrix.of (fun x y : ℝ => 2*(f (x-y)-ParisiSpectral.heat t f (x-y))) := by
    ext x y
    simp only [Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]
    ring
  change (Matrix.of (fun x y : ℝ => f (x-y)-ParisiSpectral.heat t f (x-y))).PosSemidef
  rw [heq]
  exact hh'

lemma PositiveOnPD.heat_le {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : PositiveOnPD μ)
    {f : ℝ → ℝ} (hf : PositiveDefinite f) (hc : Continuous f) (t : ℝ≥0) :
    (∫ x,heat t f x ∂μ)≤∫ x,f x ∂μ := by
  have hp := hμ _ (hc.sub (continuous_heat hc hf.norm_le t)) (hf.sub_heat hc t)
  have hi : Integrable f μ := Integrable.of_bound hc.aestronglyMeasurable _ (ae_of_all _ hf.norm_le)
  have hi' : Integrable (heat t f) μ := Integrable.of_bound (continuous_heat hc hf.norm_le t).aestronglyMeasurable _
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hf.heat_abs_le hc t x)
  change 0≤∫ x,f x-heat t f x ∂μ at hp
  rw [integral_sub hi hi'] at hp
  linarith
end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Filter Function Set Real
open scoped Topology NNReal
namespace ParisiFinite.BoundedCoefficient
open ParisiPath ParisiSpectral
variable {β : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma conjugateMeasure_plateau_integral (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) {a d α : ℝ≥0} (ha0 : a≠0) (had : a<d) (hd1 : d≤1)
    (ha : 0<α) (hg : ∀ t∈Ico a d,c.val t=α) (hgd : c.val d=α)
    {f : ℝ → ℝ} (hfc : Continuous f) (R : ℝ≥0) (hR : ∀ x,|f x|≤R) :
    (∫ x,f x ∂c.conjugateMeasure P W hβ ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩)=
    ∫ x,heat (d-a) f x ∂c.conjugateMeasure P W hβ
      ⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩ := by
  have hga : c.val a=α := hg a ⟨le_rfl,had⟩
  have hpd := field_negative_exp_positiveDefinite β hβ c.mono c.bound d (hgd ▸ ha) (by exact_mod_cast ha)
  have he : Continuous (fun x => exp (-(α:ℝ)*field β c.val d x)) :=
    (continuous_const.mul (field_lipschitz β hβ c.mono c.bound d).continuous).rexp
  let g : ℝ → ℝ := fun x => exp (-(α:ℝ)*field β c.val d x)*f x
  have hgc : Continuous g := he.mul hfc
  have hb (x : ℝ) : |g x|≤(‖exp (-(α:ℝ)*field β c.val d 0)‖₊*R:ℝ≥0) := by
    have hh : |exp (-(α:ℝ)*field β c.val d x)|≤exp (-(α:ℝ)*field β c.val d 0) := hpd.norm_le x
    have hm := mul_le_mul hh (hR x) (abs_nonneg (f x)) (exp_pos (-(α:ℝ)*field β c.val d 0)).le
    simpa only [g,abs_mul,NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs,abs_of_pos (exp_pos _)] using hm
  have ht := c.actual_plateau_transport hβ hW ha0 had hd1 hg hgc
    (‖exp (-(α:ℝ)*field β c.val d 0)‖₊*R) hb
  rw [c.integral_conjugateMeasure hβ hW _ hfc.stronglyMeasurable,
    c.integral_conjugateMeasure hβ hW _
      (continuous_heat hfc (fun x => by simpa only [Real.norm_eq_abs] using hR x) (d-a)).stronglyMeasurable]
  have heD : (⟨(⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩:Time),d.coe_nonneg⟩:ℝ≥0)=d := rfl
  have heA : (⟨(⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩:Time),a.coe_nonneg⟩:ℝ≥0)=a := rfl
  simp only [heD,heA,hgd,hga]
  rw [show (fun ω => exp (-(α:ℝ)*field β c.val d
      (solution (c.driftData hβ) (brownianPath W ω) ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩))*
      f (solution (c.driftData hβ) (brownianPath W ω) ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩))=
      (fun ω => g (solution (c.driftData hβ) (brownianPath W ω) ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩)) from rfl,ht]
  apply integral_congr_ae
  filter_upwards [] with ω
  let x : ℝ := solution (c.driftData hβ) (brownianPath W ω)
    ⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩
  have hh := conjugate_tiltedMean (field_lipschitz β hβ c.mono c.bound d) hgc 0 α (d-a) x
  simp only [zero_mul,exp_zero,one_mul,sub_zero] at hh
  rw [NNReal.coe_sub had.le] at hh
  change tiltedMean (α:ℝ) (sqrt ((d:ℝ)-a)) (field β c.val d) g x = _
  rw [hh]
  rw [field_on_plateau β hβ c.mono c.bound hd1 hg ⟨le_rfl,had⟩ x]
  congr 1
  congr 1
  funext y
  dsimp only [g]
  rw [←mul_assoc,←exp_add]
  simp only [show (α:ℝ)*field β c.val d y+ -(α:ℝ)*field β c.val d y=0 by ring,exp_zero,one_mul]

lemma conjugateMeasure_plateau (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) {a d α : ℝ≥0} (ha0 : a≠0) (had : a<d) (hd1 : d≤1)
    (ha : 0<α) (hg : ∀ t∈Ico a d,c.val t=α) (hgd : c.val d=α) :
    c.conjugateMeasure P W hβ ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩=
    c.conjugateMeasure P W hβ ⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩ ∗ gaussianReal 0 (d-a) := by
  have := c.conjugateMeasure_finite hβ hW ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩ (by change 0<c.val d; simpa only [hgd] using ha)
  have := c.conjugateMeasure_finite hβ hW ⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩
    (by change 0<c.val a; simpa only [hg a ⟨le_rfl,had⟩] using ha)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_conv (μ := c.conjugateMeasure P W hβ ⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩)
    (ν := gaussianReal 0 (d-a)) (f.integrable (μ := c.conjugateMeasure P W hβ ⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩ ∗ gaussianReal 0 (d-a)))]
  exact c.conjugateMeasure_plateau_integral hβ hW ha0 had hd1 ha hg hgd f.continuous ‖f‖₊
    (fun x => by simpa only [Real.norm_eq_abs,coe_nnnorm] using f.norm_coe_le_norm x)
end ParisiFinite.BoundedCoefficient

end

end OAI
