import Mathlib
import OAI.Probability.JammingConcavity.PolynomialHeat

namespace OAI

/-! Uniform Polynomial Growth. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set

namespace MicroscopicJamming
namespace Higher

 
def UniformPolynomialGrowth {ι : Type*} (s : Set ι) (f : ι → ℝ → ℝ) : Prop :=
  ∃ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ s, ∀ x, |f t x| ≤ C*(1+|x|)^n

lemma UniformPolynomialGrowth.at {ι : Type*} {s : Set ι} {f : ι → ℝ → ℝ}
    (hf : UniformPolynomialGrowth s f) {t : ι} (ht : t ∈ s) : PolynomialGrowth (f t) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  exact ⟨n,C,hC,hf t ht⟩

lemma PolynomialGrowth.uniform {ι : Type*} {f : ℝ → ℝ} (hf : PolynomialGrowth f) (s : Set ι) :
    UniformPolynomialGrowth s (fun _ => f) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  exact ⟨n,C,hC,fun _ _ => hf⟩

lemma UniformPolynomialGrowth.comp {ι ι' : Type*} {s : Set ι} {s' : Set ι'} {f : ι → ℝ → ℝ}
    (hf : UniformPolynomialGrowth s f) {v : ι' → ι} (hv : MapsTo v s' s) :
    UniformPolynomialGrowth s' (fun t => f (v t)) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  exact ⟨n,C,hC,fun t ht => hf (v t) (hv ht)⟩

lemma UniformPolynomialGrowth.const {ι : Type*} (s : Set ι) (c : ℝ) :
    UniformPolynomialGrowth s (fun _ _ => c) := (PolynomialGrowth.const c).uniform _

lemma UniformPolynomialGrowth.add {ι : Type*} {s : Set ι} {f g : ι → ℝ → ℝ}
    (hf : UniformPolynomialGrowth s f) (hg : UniformPolynomialGrowth s g) :
    UniformPolynomialGrowth s (fun t x => f t x+g t x) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  obtain ⟨m,D,hD,hg⟩ := hg
  refine ⟨max n m,C+D,add_nonneg hC hD,fun t ht x => ?_⟩
  calc
    |f t x+g t x| ≤ |f t x|+|g t x| := abs_add_le _ _
    _ ≤ C*(1+|x|)^n+D*(1+|x|)^m := add_le_add (hf t ht x) (hg t ht x)
    _ ≤ C*(1+|x|)^(max n m)+D*(1+|x|)^(max n m) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (le_max_left ..)) hC)
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (le_max_right ..)) hD)
    _ = _ := by ring

lemma UniformPolynomialGrowth.mul {ι : Type*} {s : Set ι} {f g : ι → ℝ → ℝ}
    (hf : UniformPolynomialGrowth s f) (hg : UniformPolynomialGrowth s g) :
    UniformPolynomialGrowth s (fun t x => f t x*g t x) := by
  obtain ⟨n,C,hC,hf⟩ := hf
  obtain ⟨m,D,hD,hg⟩ := hg
  refine ⟨n+m,C*D,mul_nonneg hC hD,fun t ht x => ?_⟩
  rw [abs_mul]
  calc
    |f t x| * |g t x| ≤ (C*(1+|x|)^n)*(D*(1+|x|)^m) :=
      mul_le_mul (hf t ht x) (hg t ht x) (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

lemma UniformPolynomialGrowth.const_mul {ι : Type*} {s : Set ι} {f : ι → ℝ → ℝ}
    (hf : UniformPolynomialGrowth s f) (a : ℝ) :
    UniformPolynomialGrowth s (fun t x => a*f t x) := (UniformPolynomialGrowth.const s a).mul hf

lemma UniformPolynomialGrowth.sub {ι : Type*} {s : Set ι} {f g : ι → ℝ → ℝ}
    (hf : UniformPolynomialGrowth s f) (hg : UniformPolynomialGrowth s g) :
    UniformPolynomialGrowth s (fun t x => f t x-g t x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.const_mul (-1))

lemma UniformPolynomialGrowth.pow {ι : Type*} {s : Set ι} {f : ι → ℝ → ℝ}
    (hf : UniformPolynomialGrowth s f) (n : ℕ) :
    UniformPolynomialGrowth s (fun t x => (f t x)^n) := by
  induction n with
  | zero => simpa using UniformPolynomialGrowth.const s 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma UniformPolynomialGrowth.finset_sum {ι α : Type*} {s : Set ι} (S : Finset α)
    {f : α → ι → ℝ → ℝ} (hf : ∀ i ∈ S, UniformPolynomialGrowth s (f i)) :
    UniformPolynomialGrowth s (fun t x => ∑ i ∈ S, f i t x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using UniformPolynomialGrowth.const s 0
  | @insert a S ha ih =>
      simpa [Finset.sum_insert,ha] using (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))

end Higher
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming
namespace Higher

lemma affine_continuousAt {E : Type*} [TopologicalSpace E] [FirstCountableTopology E]
    {v : ℝ → ℝ} (hv : Continuous v)
    (hg : PolynomialGrowth v) {a b : E → ℝ} {t₀ : E}
    (ha : ContinuousAt a t₀) (hb : ContinuousAt b t₀) :
    ContinuousAt (fun t => ∫ z : ℝ, v (a t+b t*z) ∂gaussianReal 0 1) t₀ := by
  let K := 1+|a t₀|+|b t₀|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hea : ∀ᶠ t in 𝓝 t₀, |a t| ≤ K :=
    (ha.abs.tendsto.eventually (eventually_lt_nhds (show |a t₀| < K by
      dsimp [K]; linarith [abs_nonneg (b t₀)]))).mono fun _ h => h.le
  have heb : ∀ᶠ t in 𝓝 t₀, |b t| ≤ K :=
    (hb.abs.tendsto.eventually (eventually_lt_nhds (show |b t₀| < K by
      dsimp [K]; linarith [abs_nonneg (a t₀)]))).mono fun _ h => h.le
  obtain ⟨n,C,hC,hgrow⟩ := hg
  refine continuousAt_of_dominated
    (μ := gaussianReal 0 1) (bound := fun z => C*(1+2*K)^n*(1+|z|)^n)
    (Eventually.of_forall fun t => (hv.measurable.comp (by fun_prop)).aestronglyMeasurable)
    ?_ ((gaussian_abs_one_pow_integrable n).const_mul _) ?_
  · filter_upwards [hea,heb] with t hat hbt
    filter_upwards [] with z
    have hab : 1+|a t+b t*z| ≤ (1+2*K)*(1+|z|) :=
      (heat_affine_bound (a t) (b t) z).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    rw [Real.norm_eq_abs]
    calc
      |v (a t+b t*z)| ≤ C*(1+|a t+b t*z|)^n := hgrow _
      _ ≤ C*((1+2*K)*(1+|z|))^n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hab n) hC
      _ = _ := by rw [mul_pow]; ring
  · filter_upwards [] with z
    exact hv.continuousAt.comp (ha.add (hb.mul_const z))

lemma heat_jointly_continuous {v : ℝ → ℝ} (hv : Continuous v)
    (hg : PolynomialGrowth v) :
    Continuous (fun p : ℝ × ℝ => gaussianHeat v p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact affine_continuousAt hv hg continuous_snd.continuousAt
    (Real.continuous_sqrt.comp continuous_fst).continuousAt

end Higher
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming
namespace Higher

def normalizedHeatJet (u : ℝ → ℝ) (a T : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  gaussianHeat (iteratedDeriv n (fun y => Real.exp (a*u y))) T x /
    gaussianHeat (fun y => Real.exp (a*u y)) T x

lemma exp_heat_pos {u : ℝ → ℝ} {B a T x : ℝ} (hu : Continuous u)
    (hB : ∀ y, u y ≤ B) (ha : 0 ≤ a) :
    0 < gaussianHeat (fun y => Real.exp (a*u y)) T x := by
  apply integral_exp_pos
  simpa using weighted_poly_integrable (x:=x) (b:=Real.sqrt T) hu hB ha
    (measurable_const (a:=1)) (PolynomialGrowth.const 1)

lemma tilted_heat_polynomial {u f : ℝ → ℝ} {A B C κ Q a L : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hsub : a*κ*L < 1) (hf : Measurable f) (hg : PolynomialGrowth f) :
    UniformPolynomialGrowth (Icc 0 L) (fun T x =>
      gaussianHeat (fun y => f y*Real.exp (a*u y)) T x /
      gaussianHeat (fun y => Real.exp (a*u y)) T x) := by
  have hδ : 0 < 1-a*κ*L := sub_pos.mpr hsub
  obtain ⟨n,H,hH,hbnd⟩ := tilted_polynomial_bound (R:=Real.sqrt L) (δ:=1-a*κ*L)
    hu ha (Real.sqrt_nonneg _) hδ (by rw [Real.sq_sqrt hL]) hf hg
  refine ⟨n,H,hH,fun T hT x => ?_⟩
  have hZ := exp_heat_pos (T:=T) (x:=x) hu.differentiable.continuous
    (fun y => (hu.bounds y).2.1) ha
  rw [abs_div,abs_of_pos hZ]
  apply (div_le_iff₀ hZ).mpr
  exact hbnd (Real.sqrt T) (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hT.2) x

lemma heat_uniform_growth {u f : ℝ → ℝ} {A B C κ Q L : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (hL : 0 ≤ L)
    (hf : Measurable f) (hg : PolynomialGrowth f) :
    UniformPolynomialGrowth (Icc 0 L) (fun T x => gaussianHeat f T x) := by
  have hh := tilted_heat_polynomial (a:=0) hu (by norm_num) hL (by norm_num) hf hg
  simpa [gaussianHeat] using hh

lemma normalizedHeatJet_growth {u : ℝ → ℝ} {A B C κ Q a L : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (hs : SmoothPolynomial u)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hsub : a*κ*L < 1) (n : ℕ) :
    UniformPolynomialGrowth (Icc 0 L) (fun T x => normalizedHeatJet u a T n x) := by
  obtain ⟨p,hp,he⟩ := exp_jet_factor hs a n
  simp only [normalizedHeatJet,he]
  exact tilted_heat_polynomial hu ha hL hsub hp.smooth.continuous.measurable (by simpa using hp.growth 0)

lemma exp_smoothPolynomial {u : ℝ → ℝ} (hu : SmoothPolynomial u) {a B : ℝ}
    (ha : 0 ≤ a) (hB : ∀ x, u x ≤ B) : SmoothPolynomial (fun x => Real.exp (a*u x)) :=
  (hu.const_mul a).exp (fun x => mul_le_mul_of_nonneg_left (hB x) ha)

lemma normalizedHeatJet_smooth {u : ℝ → ℝ} (hu : SmoothPolynomial u) {a B : ℝ}
    (ha : 0 ≤ a) (hB : ∀ x, u x ≤ B) (T : ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (normalizedHeatJet u a T n) := by
  have hv := exp_smoothPolynomial hu ha hB
  have hj : SmoothPolynomial (iteratedDeriv n (fun y => Real.exp (a*u y))) := by
    induction n with
    | zero => simpa using hv
    | succ n ih => simpa only [iteratedDeriv_succ] using ih.derivative
  exact (heat_smooth hj T).div (heat_smooth hv T)
    (fun x => (exp_heat_pos hu.smooth.continuous hB ha).ne')

lemma normalizedHeatJet_space {u : ℝ → ℝ} (hu : SmoothPolynomial u) {a B : ℝ}
    (ha : 0 ≤ a) (hB : ∀ x, u x ≤ B) (T : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (normalizedHeatJet u a T n)
      (normalizedHeatJet u a T (n+1) x-normalizedHeatJet u a T n x*normalizedHeatJet u a T 1 x) x := by
  have hv := exp_smoothPolynomial hu ha hB
  have hd (k : ℕ) : HasDerivAt (gaussianHeat (iteratedDeriv k (fun y => Real.exp (a*u y))) T)
      (gaussianHeat (iteratedDeriv (k+1) (fun y => Real.exp (a*u y))) T x) x :=
    space_derivative (hv.continuous k).measurable (hv.continuous (k+1)).measurable
      (hv.growth k) (hv.growth (k+1)) (fun y => by
        simpa only [iteratedDeriv_succ] using (hv.differentiable k y).hasDerivAt) T x
  have hd0 : HasDerivAt (gaussianHeat (fun y => Real.exp (a*u y)) T)
      (gaussianHeat (iteratedDeriv 1 (fun y => Real.exp (a*u y))) T x) x := by simpa using hd 0
  have hZ : gaussianHeat (fun y => Real.exp (a*u y)) T x ≠ 0 :=
    (exp_heat_pos hu.smooth.continuous hB ha).ne'
  convert (hd n).div hd0 hZ using 1 <;> first | rfl | (dsimp [normalizedHeatJet]; field_simp)

lemma normalizedHeatJet_time {u : ℝ → ℝ} (hu : SmoothPolynomial u) {a B T : ℝ}
    (ha : 0 ≤ a) (hB : ∀ x, u x ≤ B) (hT : 0 < T) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t => normalizedHeatJet u a t n x)
      ((1/2:ℝ)*(normalizedHeatJet u a T (n+2) x-normalizedHeatJet u a T n x*normalizedHeatJet u a T 2 x)) T := by
  have hv := exp_smoothPolynomial hu ha hB
  have hd0 : HasDerivAt (fun t => gaussianHeat (fun y => Real.exp (a*u y)) t x)
      ((1/2:ℝ)*gaussianHeat (iteratedDeriv 2 (fun y => Real.exp (a*u y))) T x) T := by
    simpa using heat_jet_time_derivative hv hT 0 x
  have hZ : gaussianHeat (fun y => Real.exp (a*u y)) T x ≠ 0 :=
    (exp_heat_pos hu.smooth.continuous hB ha).ne'
  convert (heat_jet_time_derivative hv hT n x).div hd0 hZ using 1 <;>
    first | rfl | (dsimp [normalizedHeatJet]; field_simp)

lemma normalizedHeatJet_jointly_continuous {u : ℝ → ℝ} (hu : SmoothPolynomial u) {a B : ℝ}
    (ha : 0 ≤ a) (hB : ∀ x, u x ≤ B) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => normalizedHeatJet u a p.1 n p.2) := by
  have hv := exp_smoothPolynomial hu ha hB
  exact (heat_jointly_continuous (hv.continuous n) (hv.growth n)).div
    (heat_jointly_continuous (by simpa using hv.continuous 0) (by simpa using hv.growth 0))
    (fun p => (exp_heat_pos hu.smooth.continuous hB ha).ne')

lemma normalizedHeatJet_iterated_growth {u : ℝ → ℝ} {A B C κ Q a L : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (hs : SmoothPolynomial u)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hsub : a*κ*L < 1) (k n : ℕ) :
    UniformPolynomialGrowth (Icc 0 L) (fun T x => iteratedDeriv k (normalizedHeatJet u a T n) x) := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    cases k with
    | zero => simpa using normalizedHeatJet_growth hu hs ha hL hsub n
    | succ k =>
      have hc (T : ℝ) (p : ℕ) : ContDiff ℝ (k : WithTop ℕ∞) (normalizedHeatJet u a T p) :=
        (normalizedHeatJet_smooth hs ha (fun x => (hu.bounds x).2.1) T p).of_le
          (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
      have hd (T : ℝ) : deriv (normalizedHeatJet u a T n) = fun x =>
          normalizedHeatJet u a T (n+1) x-normalizedHeatJet u a T n x*normalizedHeatJet u a T 1 x := by
        funext x
        exact (normalizedHeatJet_space hs ha (fun x => (hu.bounds x).2.1) T n x).deriv
      have he (T x : ℝ) : iteratedDeriv (k+1) (normalizedHeatJet u a T n) x =
          iteratedDeriv k (normalizedHeatJet u a T (n+1)) x-
          ∑ i ∈ Finset.range (k+1),(k.choose i:ℝ)*iteratedDeriv i (normalizedHeatJet u a T n) x*
            iteratedDeriv (k-i) (normalizedHeatJet u a T 1) x := by
        rw [iteratedDeriv_succ',hd T,
          iteratedDeriv_fun_sub (hc T (n+1)).contDiffAt ((hc T n).mul (hc T 1)).contDiffAt,
          iteratedDeriv_fun_mul (hc T n).contDiffAt (hc T 1).contDiffAt]
      have hsum : UniformPolynomialGrowth (Icc 0 L) (fun T x =>
          ∑ i ∈ Finset.range (k+1),(k.choose i:ℝ)*iteratedDeriv i (normalizedHeatJet u a T n) x*
            iteratedDeriv (k-i) (normalizedHeatJet u a T 1) x) := by
        apply UniformPolynomialGrowth.finset_sum
        intro i hi
        exact ((ih i (Finset.mem_range.mp hi) n).const_mul (k.choose i:ℝ)).mul
          (ih (k-i) (by omega) 1)
      simpa only [he] using (ih k (by omega) (n+1)).sub hsum

lemma normalizedHeatJet_smoothPolynomial {u : ℝ → ℝ} {A B C κ Q a T : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (hs : SmoothPolynomial u)
    (ha : 0 ≤ a) (hT : 0 ≤ T) (hsub : a*κ*T < 1) (n : ℕ) :
    SmoothPolynomial (normalizedHeatJet u a T n) :=
  ⟨normalizedHeatJet_smooth hs ha (fun x => (hu.bounds x).2.1) T n,
    fun k => (normalizedHeatJet_iterated_growth hu hs ha hT hsub k n).at ⟨hT,le_rfl⟩⟩

end Higher
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming
namespace Higher

lemma gaussianRowOperator_deriv_normalized {u : ℝ → ℝ} (hu : SmoothPolynomial u) {a B : ℝ}
    (ha : 0 ≤ a) (haz : a ≠ 0) (hB : ∀ x, u x ≤ B) (T : ℝ) :
    deriv (gaussianRowOperator a T u) = fun x => (1/a)*normalizedHeatJet u a T 1 x := by
  have hv := exp_smoothPolynomial hu ha hB
  have he : gaussianRowOperator a T u = fun x => (1/a)*Real.log (gaussianHeat (fun y => Real.exp (a*u y)) T x) := by
    funext x; simp [gaussianRowOperator,haz]
  rw [he]
  funext x
  have hd : HasDerivAt (gaussianHeat (fun y => Real.exp (a*u y)) T)
      (gaussianHeat (iteratedDeriv 1 (fun y => Real.exp (a*u y))) T x) x := by
    simpa using space_derivative (hv.continuous 0).measurable (hv.continuous 1).measurable
      (hv.growth 0) (hv.growth 1) (fun y => by simpa using (hv.differentiable 0 y).hasDerivAt) T x
  simpa only [normalizedHeatJet] using
    ((hd.log (exp_heat_pos hu.smooth.continuous hB ha).ne').const_mul (1/a)).deriv

lemma gaussianRowOperator_polynomial {u : ℝ → ℝ} {A B C κ Q a T : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (hT : 0 ≤ T) :
    PolynomialGrowth (gaussianRowOperator a T u) := by
  let H := A*(1+T)+|B|
  have hH : 0 ≤ H := by dsimp [H]; have hA := hu.A_nonneg; positivity
  refine ⟨2,H,hH,fun x => ?_⟩
  have hb := gaussianRowOperator_barrier (R:=0) hu.differentiable.continuous.measurable
    hu.A_nonneg (by norm_num) ha hT (fun x => by simpa using And.intro (hu.bounds x).1 (hu.bounds x).2.1) x
  have hs : 1+x^2+T ≤ (1+T)*(1+|x|)^2 := by
    nlinarith [sq_abs x,abs_nonneg x,mul_nonneg hT (sq_nonneg x),mul_nonneg hT (abs_nonneg x)]
  have hsA := mul_le_mul_of_nonneg_left hs hu.A_nonneg
  have hBsq := mul_nonneg (abs_nonneg B) (sq_nonneg (1+|x|))
  have hAsq := mul_nonneg (mul_nonneg hu.A_nonneg (show 0 ≤ 1+T by linarith)) (sq_nonneg (1+|x|))
  have hbase : 1 ≤ (1+|x|)^2 := by nlinarith [sq_abs x,sq_nonneg x,abs_nonneg x]
  have hbb := mul_le_mul_of_nonneg_left hbase (abs_nonneg B)
  rw [abs_le]
  dsimp [H]
  constructor <;> nlinarith [hb.1,hb.2,le_abs_self B]

lemma gaussianRowOperator_smoothPolynomial {u : ℝ → ℝ} {A B C κ Q a T : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (hs : SmoothPolynomial u)
    (ha : 0 ≤ a) (hT : 0 ≤ T) (hsub : a*κ*T < 1) :
    SmoothPolynomial (gaussianRowOperator a T u) := by
  by_cases haz : a=0
  · subst a
    have he : gaussianRowOperator 0 T u = gaussianHeat u T := by funext x; simp [gaussianRowOperator]
    rw [he]
    refine ⟨heat_smooth hs T,fun n => ?_⟩
    rw [heat_iterated_derivative hs]
    exact (heat_uniform_growth hu hT (hs.continuous n).measurable (hs.growth n)).at ⟨hT,le_rfl⟩
  · have hv := exp_smoothPolynomial hs ha (fun x => (hu.bounds x).2.1)
    have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaussianRowOperator a T u) := by
      have he : gaussianRowOperator a T u = fun x => (1/a)*Real.log (gaussianHeat (fun y => Real.exp (a*u y)) T x) := by
        funext x; simp [gaussianRowOperator,haz]
      rw [he]
      exact contDiff_const.mul ((heat_smooth hv T).log (fun x =>
        (exp_heat_pos hs.smooth.continuous (fun x => (hu.bounds x).2.1) ha).ne'))
    refine ⟨hsmooth,?_⟩
    intro n
    cases n with
    | zero => simpa using gaussianRowOperator_polynomial hu ha hT
    | succ n =>
      rw [iteratedDeriv_succ',gaussianRowOperator_deriv_normalized hs ha haz (fun x => (hu.bounds x).2.1)]
      exact ((normalizedHeatJet_smoothPolynomial hu hs ha hT hsub 1).const_mul (1/a)).growth n

end Higher
end MicroscopicJamming

 
open Set

namespace MicroscopicJamming
namespace Higher

lemma gaussianRowComposition_twice {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q)
    {rs : List (ℝ × ℝ)} (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hsum : gaussianStepTime rs ≤ Q) :
    Twice.RowTwiceTerminal (gaussianRowComposition rs u) (A*(1+gaussianStepTime rs))
      B C (κ/(1-κ*gaussianStepTime rs)) (Q-gaussianStepTime rs) := by
  obtain ⟨hd,hd',hb⟩ := gaussian_step_bounds u A B C κ Q hQ hu rs hrs hsum
  have hR := gaussianStepTime_nonneg (fun r hr => (hrs r hr).2.2)
  have hsum' : κ*((Q-gaussianStepTime rs)+gaussianStepTime rs)<1 := by simpa using hu.2.2.2.2.1
  obtain ⟨hkn,hknQ,_⟩ := gaussian_curvature_update hu.2.2.2.1 hR (sub_nonneg.mpr hsum) hsum'
  refine ⟨hd,hd',mul_nonneg hu.2.1 (by linarith),hu.2.2.1,hkn,hknQ,fun x => ?_⟩
  refine ⟨?_,(hb x).1.2,(hb x).2⟩
  have hh := (hb x).1.1
  nlinarith [mul_nonneg (mul_nonneg hu.2.1 hR) (sq_nonneg x)]

lemma gaussianRowComposition_block_subcritical {u : ℝ → ℝ} {A B C κ Q a T : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q)
    {rs : List (ℝ × ℝ)} (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (_ha : 0 ≤ a) (ha1 : a ≤ 1) (hT : 0 ≤ T) (hsum : T+gaussianStepTime rs ≤ Q) :
    a*(κ/(1-κ*gaussianStepTime rs))*T < 1 := by
  have htq : gaussianStepTime rs ≤ Q := by linarith
  have htw := gaussianRowComposition_twice hQ hu hrs htq
  calc
    a*(κ/(1-κ*gaussianStepTime rs))*T = a*((κ/(1-κ*gaussianStepTime rs))*T) := by ring
    _ ≤ (κ/(1-κ*gaussianStepTime rs))*T :=
      mul_le_of_le_one_left (mul_nonneg htw.kappa_nonneg hT) ha1
    _ ≤ (κ/(1-κ*gaussianStepTime rs))*(Q-gaussianStepTime rs) :=
      mul_le_mul_of_nonneg_left (by linarith) htw.kappa_nonneg
    _ < 1 := htw.subcritical

lemma gaussianRowComposition_smoothPolynomial {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q) :
    ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
      gaussianStepTime rs ≤ Q → SmoothPolynomial (gaussianRowComposition rs u) := by
  intro rs
  induction rs with
  | nil => intro _ _; exact row_terminal_smoothPolynomial hu
  | cons r rs ih =>
    intro hrs hsum
    have hr := hrs r (by simp)
    have ht : ∀ v ∈ rs, 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2 := fun v hv => hrs v (by simp [hv])
    have htime : gaussianStepTime (r::rs)=r.2+gaussianStepTime rs := by simp [gaussianStepTime]
    rw [htime] at hsum
    have htq : gaussianStepTime rs ≤ Q := by linarith [hr.2.2]
    exact gaussianRowOperator_smoothPolynomial (gaussianRowComposition_twice hQ hu ht htq)
      (ih ht htq) hr.1 hr.2.2
      (gaussianRowComposition_block_subcritical hQ hu ht hr.1 hr.2.1 hr.2.2 hsum)
end Higher
end MicroscopicJamming

 
 

namespace MicroscopicJamming
namespace Higher

def heatCumulant1 (j : ℕ → ℝ) : ℝ := j 1

def heatCumulant2 (j : ℕ → ℝ) : ℝ := j 2-(j 1)^2

def heatCumulant3 (j : ℕ → ℝ) : ℝ := j 3-3*j 1*j 2+2*(j 1)^3

def heatCumulant4 (j : ℕ → ℝ) : ℝ := j 4-4*j 1*j 3-3*(j 2)^2+12*(j 1)^2*j 2-6*(j 1)^4

def heatCumulant5 (j : ℕ → ℝ) : ℝ := j 5-5*j 1*j 4-10*j 2*j 3+
  20*(j 1)^2*j 3+30*j 1*(j 2)^2-60*(j 1)^3*j 2+24*(j 1)^5

lemma heatCumulant1_space {j : ℕ → ℝ → ℝ} {x : ℝ}
    (hd : ∀ n, HasDerivAt (j n) (j (n+1) x-j n x*j 1 x) x) :
    HasDerivAt (fun y => heatCumulant1 (fun n => j n y)) (heatCumulant2 (fun n => j n x)) x := by
  convert hd 1 using 1 <;> first | rfl | (dsimp [heatCumulant2]; ring)

lemma heatCumulant2_space {j : ℕ → ℝ → ℝ} {x : ℝ}
    (hd : ∀ n, HasDerivAt (j n) (j (n+1) x-j n x*j 1 x) x) :
    HasDerivAt (fun y => heatCumulant2 (fun n => j n y)) (heatCumulant3 (fun n => j n x)) x := by
  convert (hd 2).sub ((hd 1).pow 2) using 1 <;>
    first | rfl | (dsimp [heatCumulant3]; ring)

lemma heatCumulant3_space {j : ℕ → ℝ → ℝ} {x : ℝ}
    (hd : ∀ n, HasDerivAt (j n) (j (n+1) x-j n x*j 1 x) x) :
    HasDerivAt (fun y => heatCumulant3 (fun n => j n y)) (heatCumulant4 (fun n => j n x)) x := by
  convert ((hd 3).sub (((hd 1).const_mul 3).mul (hd 2))).add (((hd 1).pow 3).const_mul 2) using 1 <;>
    first | rfl | (dsimp [heatCumulant4]; ring)

lemma heatCumulant4_space {j : ℕ → ℝ → ℝ} {x : ℝ}
    (hd : ∀ n, HasDerivAt (j n) (j (n+1) x-j n x*j 1 x) x) :
    HasDerivAt (fun y => heatCumulant4 (fun n => j n y)) (heatCumulant5 (fun n => j n x)) x := by
  convert ((((hd 4).sub (((hd 1).const_mul 4).mul (hd 3))).sub
    (((hd 2).pow 2).const_mul 3)).add ((((hd 1).pow 2).const_mul 12).mul (hd 2))).sub
    (((hd 1).pow 4).const_mul 6) using 1 <;> first | rfl | (dsimp [heatCumulant5]; ring)

lemma heatCumulant3_time {j : ℕ → ℝ → ℝ} {t : ℝ}
    (hd : ∀ n, HasDerivAt (j n) ((1/2:ℝ)*(j (n+2) t-j n t*j 2 t)) t) :
    HasDerivAt (fun r => heatCumulant3 (fun n => j n r))
      ((1/2:ℝ)*heatCumulant5 (fun n => j n t)+heatCumulant1 (fun n => j n t)*heatCumulant4 (fun n => j n t)+
        3*heatCumulant2 (fun n => j n t)*heatCumulant3 (fun n => j n t)) t := by
  convert ((hd 3).sub (((hd 1).const_mul 3).mul (hd 2))).add (((hd 1).pow 3).const_mul 2) using 1 <;>
    first | rfl | (dsimp [heatCumulant1,heatCumulant2,heatCumulant3,heatCumulant4,heatCumulant5]; ring)

end Higher
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming
namespace Higher

lemma gaussianRowOperator_cumulants {u : ℝ → ℝ} (hu : SmoothPolynomial u) {a B : ℝ}
    (ha : 0 ≤ a) (haz : a ≠ 0) (hB : ∀ x, u x ≤ B) (T : ℝ) :
    (iteratedDeriv 1 (gaussianRowOperator a T u) = fun x => (1/a)*heatCumulant1 (fun n => normalizedHeatJet u a T n x)) ∧
    (iteratedDeriv 2 (gaussianRowOperator a T u) = fun x => (1/a)*heatCumulant2 (fun n => normalizedHeatJet u a T n x)) ∧
    (iteratedDeriv 3 (gaussianRowOperator a T u) = fun x => (1/a)*heatCumulant3 (fun n => normalizedHeatJet u a T n x)) ∧
    (iteratedDeriv 4 (gaussianRowOperator a T u) = fun x => (1/a)*heatCumulant4 (fun n => normalizedHeatJet u a T n x)) ∧
    (iteratedDeriv 5 (gaussianRowOperator a T u) = fun x => (1/a)*heatCumulant5 (fun n => normalizedHeatJet u a T n x)) := by
  have hd (x : ℝ) (n : ℕ) := normalizedHeatJet_space hu ha hB T n x
  have h1 : iteratedDeriv 1 (gaussianRowOperator a T u) = fun x =>
      (1/a)*heatCumulant1 (fun n => normalizedHeatJet u a T n x) := by
    simpa only [iteratedDeriv_one,heatCumulant1] using gaussianRowOperator_deriv_normalized hu ha haz hB T
  have h2 : iteratedDeriv 2 (gaussianRowOperator a T u) = fun x =>
      (1/a)*heatCumulant2 (fun n => normalizedHeatJet u a T n x) := by
    rw [iteratedDeriv_succ (n:=1),h1]
    funext x
    exact ((heatCumulant1_space (hd x)).const_mul (1/a)).deriv
  have h3 : iteratedDeriv 3 (gaussianRowOperator a T u) = fun x =>
      (1/a)*heatCumulant3 (fun n => normalizedHeatJet u a T n x) := by
    rw [iteratedDeriv_succ (n:=2),h2]
    funext x
    exact ((heatCumulant2_space (hd x)).const_mul (1/a)).deriv
  have h4 : iteratedDeriv 4 (gaussianRowOperator a T u) = fun x =>
      (1/a)*heatCumulant4 (fun n => normalizedHeatJet u a T n x) := by
    rw [iteratedDeriv_succ (n:=3),h3]
    funext x
    exact ((heatCumulant3_space (hd x)).const_mul (1/a)).deriv
  have h5 : iteratedDeriv 5 (gaussianRowOperator a T u) = fun x =>
      (1/a)*heatCumulant5 (fun n => normalizedHeatJet u a T n x) := by
    rw [iteratedDeriv_succ (n:=4),h4]
    funext x
    exact ((heatCumulant4_space (hd x)).const_mul (1/a)).deriv
  exact ⟨h1,h2,h3,h4,h5⟩

lemma gaussianRowOperator_third_equation {u : ℝ → ℝ} (hu : SmoothPolynomial u) {a B T : ℝ}
    (ha : 0 ≤ a) (hB : ∀ x, u x ≤ B) (hT : 0 < T) (x : ℝ) :
    HasDerivAt (fun r => iteratedDeriv 3 (gaussianRowOperator a r u) x)
      ((1/2:ℝ)*iteratedDeriv 5 (gaussianRowOperator a T u) x+
        a*iteratedDeriv 1 (gaussianRowOperator a T u) x*iteratedDeriv 4 (gaussianRowOperator a T u) x+
        3*a*iteratedDeriv 2 (gaussianRowOperator a T u) x*iteratedDeriv 3 (gaussianRowOperator a T u) x) T := by
  by_cases haz : a=0
  · subst a
    have he (r : ℝ) : gaussianRowOperator 0 r u = gaussianHeat u r := by funext x; simp [gaussianRowOperator]
    simp only [he,zero_mul,mul_zero,add_zero,heat_iterated_derivative hu]
    exact heat_jet_time_derivative hu hT 3 x
  · have he (r : ℝ) := gaussianRowOperator_cumulants hu ha haz hB r
    simp only [(he T).1,(he T).2.1,(he T).2.2.2.1,(he T).2.2.2.2,
      fun r => (he r).2.2.1]
    convert (heatCumulant3_time (fun n => normalizedHeatJet_time hu ha hB hT n x)).const_mul (1/a) using 1
    first | rfl | field_simp [haz]

lemma gaussianRowOperator_third_continuous {u : ℝ → ℝ} (hu : SmoothPolynomial u) {a B : ℝ}
    (ha : 0 ≤ a) (hB : ∀ x, u x ≤ B) :
    Continuous (fun p : ℝ × ℝ => iteratedDeriv 3 (gaussianRowOperator a p.1 u) p.2) := by
  by_cases haz : a=0
  · subst a
    have he (r : ℝ) : gaussianRowOperator 0 r u = gaussianHeat u r := by funext x; simp [gaussianRowOperator]
    simp only [he,heat_iterated_derivative hu]
    exact heat_jointly_continuous (hu.continuous 3) (hu.growth 3)
  · have he (r : ℝ) := (gaussianRowOperator_cumulants hu ha haz hB r).2.2.1
    have h1 := normalizedHeatJet_jointly_continuous hu ha hB 1
    have h2 := normalizedHeatJet_jointly_continuous hu ha hB 2
    have h3 := normalizedHeatJet_jointly_continuous hu ha hB 3
    simp only [he,heatCumulant3]
    fun_prop

lemma gaussianRowOperator_third_growth {u : ℝ → ℝ} {A B C κ Q a L : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (hs : SmoothPolynomial u)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hsub : a*κ*L < 1) :
    UniformPolynomialGrowth (Icc 0 L) (fun T x => iteratedDeriv 3 (gaussianRowOperator a T u) x) := by
  by_cases haz : a=0
  · subst a
    have he (r : ℝ) : gaussianRowOperator 0 r u = gaussianHeat u r := by funext x; simp [gaussianRowOperator]
    simp only [he,heat_iterated_derivative hs]
    exact heat_uniform_growth hu hL (hs.continuous 3).measurable (hs.growth 3)
  · have he (r : ℝ) := (gaussianRowOperator_cumulants hs ha haz (fun x => (hu.bounds x).2.1) r).2.2.1
    have hg (n : ℕ) := normalizedHeatJet_growth hu hs ha hL hsub n
    simpa only [he,heatCumulant3] using
      (((hg 3).sub (((hg 1).const_mul 3).mul (hg 2))).add (((hg 1).pow 3).const_mul 2)).const_mul (1/a)

end Higher
end MicroscopicJamming

end

end OAI
