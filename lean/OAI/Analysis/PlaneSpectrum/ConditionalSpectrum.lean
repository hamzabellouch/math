import OAI.Analysis.PlaneSpectrum.FourierTests
import OAI.Analysis.PlaneSpectrum.SmallArcs
import OAI.MeasureTheory.CompactFactors.ConditionalSelection

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators ComplexConjugate

instance dualPolishSpace : PolishSpace D := by
  have : TopologicalSpace.SeparableSpace (DiscreteE → Circle) := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace (DiscreteE → Circle) := inferInstance
  exact ContinuousMonoidHom.isClosedEmbedding_coe.polishSpace

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- Evaluation at the exact algebraic argument. -/
def eval (a : E) : D →* Circle where
  toFun d := d (Multiplicative.ofAdd a)
  map_one' := rfl
  map_mul' _ _ := rfl

lemma continuous_eval (a : E) : Continuous (eval a) :=
  (continuous_apply (Multiplicative.ofAdd a)).comp
    ContinuousMonoidHom.isClosedEmbedding_coe.continuous

lemma measurable_eval (a : E) : Measurable (eval a) := (continuous_eval a).measurable
lemma measurable_eval_coe (a : E) : Measurable (fun d => (eval a d : ℂ)) :=
  ((show Continuous (fun z : Circle => (z : ℂ)) from continuous_subtype_val).comp
    (continuous_eval a)).measurable

@[simp] lemma eval_zero (d : D) : eval 0 d = 1 := map_one d
lemma eval_add (a b : E) (d : D) : eval (a+b) d = eval a d * eval b d :=
  map_mul d (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
lemma eval_neg (a : E) (d : D) : eval (-a) d = (eval a d)⁻¹ :=
  d.map_inv (Multiplicative.ofAdd a)
lemma eval_sub (a b : E) (d : D) : eval (a-b) d = eval a d / eval b d := by
  rw [sub_eq_add_neg, eval_add, eval_neg, div_eq_mul_inv]
lemma eval_nat_mul (n : ℕ) (a : E) (d : D) : eval (n*a) d = eval a d ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      eval_add, ih, pow_succ]
lemma eval_scalar (a b : E) (d : D) : eval a (scalar b d) = eval (b*a) d := rfl
lemma eval_smul_one (u : K) (d : D) : eval 1 (u • d) = eval (kCoeff u) d := by
  change eval (kCoeff u * 1) d = _
  rw [mul_one]
lemma lineFourier_eq (ν : Measure D) (a : E) (t : F) :
    lineFourier ν a t = ∫ d, (eval (a * ofF t) d : ℂ) ∂ν := rfl

variable {X W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W]

/-- The actual conditional moment on a predecessor fiber is the Fourier
coefficient of the actual relative difference law, not an extra hypothesis. -/
lemma predecessor_moment_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → W) (b : X → D) (hp : Measurable p) (hb : Measurable b) (a : E) :
    (∫ w, ‖∫ x, (eval a (b x) : ℂ) ∂condDistrib id p μ w‖^2 ∂μ.map p) =
      (∫ d, (eval a d : ℂ) ∂DifferenceFourier.differenceLaw (μ.map p)
        (condDistrib b p μ)).re := by
  let : IsProbabilityMeasure (μ.map p) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  rw [DifferenceFourier.difference_coefficient (eval a) (measurable_eval_coe a),
    Complex.ofReal_re]
  apply integral_congr_ae
  filter_upwards [ConditionalFiber.map_identity_fiber μ p hp.aemeasurable b hb] with w hw
  congr 1
  rw [← hw, integral_map hb.aemeasurable (measurable_eval_coe a).aestronglyMeasurable]

lemma integrable_predecessor_moment_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → W) (b : X → D) (hp : Measurable p) (hb : Measurable b) (a : E) :
    Integrable (fun w => ‖∫ x, (eval a (b x) : ℂ) ∂condDistrib id p μ w‖^2) (μ.map p) := by
  let : IsProbabilityMeasure (μ.map p) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hm := ((measurable_eval_coe a).comp hb).stronglyMeasurable.integral_kernel
    (κ := condDistrib id p μ)
  apply Integrable.of_bound (hm.norm.pow 2).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro w
  have hh : ‖∫ x, (eval a (b x) : ℂ) ∂condDistrib id p μ w‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := condDistrib id p μ w)
      (C := (1 : ℝ)) (Filter.Eventually.of_forall (fun x => (Circle.norm_coe _).le))
  simpa only [Real.norm_eq_abs, Pi.pow_apply, Function.comp_apply, abs_sq, one_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2

end

theorem real_algebraic_sum_two_rotations (x : F) (hx : |(x : ℝ)| < 2) :
    ∃ u v : K, ofF x = kCoeff u + kCoeff v := by
  let r : ℝ := (x : ℝ)/2
  have hr : |r| < 1 := by dsimp [r]; rw [abs_div]; norm_num; linarith
  have hnon : 0 ≤ 1-r^2 := by nlinarith [sq_abs r, abs_nonneg r]
  let s : ℝ := Real.sqrt (1-r^2)
  have hs : s^2 = 1-r^2 := Real.sq_sqrt hnon
  have hrAlg : IsAlgebraic ℚ r := by
    change IsAlgebraic ℚ ((x / 2 : F) : ℝ)
    exact mem_algebraicClosure_iff.mp (x / 2 : F).property
  have hsAlg : IsAlgebraic ℚ s := IsAlgebraic.of_pow (by norm_num : 0 < 2) (by
    rw [hs]; exact isAlgebraic_one.sub (hrAlg.pow 2))
  have huAlg : IsAlgebraic ℚ ((r : ℂ) + Complex.I * s) :=
    (hrAlg.algebraMap (A := ℂ)).add
      ((isAlgebraic_iff_isIntegral.mpr (Complex.isIntegral_I ℚ)).mul (hsAlg.algebraMap (A := ℂ)))
  have hvAlg : IsAlgebraic ℚ ((r : ℂ) - Complex.I * s) :=
    (hrAlg.algebraMap (A := ℂ)).sub
      ((isAlgebraic_iff_isIntegral.mpr (Complex.isIntegral_I ℚ)).mul (hsAlg.algebraMap (A := ℂ)))
  have huNorm : ‖(r : ℂ)+Complex.I*s‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith
  have hvNorm : ‖(r : ℂ)-Complex.I*s‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith
  let u : K := ⟨⟨(r : ℂ)+Complex.I*s, mem_sphere_zero_iff_norm.mpr huNorm⟩, huAlg⟩
  let v : K := ⟨⟨(r : ℂ)-Complex.I*s, mem_sphere_zero_iff_norm.mpr hvNorm⟩, hvAlg⟩
  refine ⟨u, v, ?_⟩
  apply Subtype.ext
  change ((x : ℝ) : ℂ) = ((r : ℂ)+Complex.I*s)+((r : ℂ)-Complex.I*s)
  simp only [r, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

end PlaneFiveColor.Spectral

namespace EuclideanFiveColor.PhaseEncoding
open MeasureTheory ProbabilityTheory
variable {Y G : Type*} [MeasurableSpace Y] [MeasurableSpace G]
/-- Covariance of the *actual* Newton-symmetric conditional encoding. -/
theorem kernelEncoding_covariance (ν : Measure Y) (β : Kernel Y G)
    (R : Y → Y) (T : G → G) (hT : Measurable T)
    (χ : G → ℂ) (hχ : Measurable χ) (m : ℕ)
    (hβ : ∀ᵐ y ∂ν, β (R y) = (β y).map T) :
    ∀ᵐ y ∂ν, kernelEncoding β χ m (R y) = kernelEncoding β (χ ∘ T) m y := by
  filter_upwards [hβ] with y hy
  have he (n : ℕ) : (∫ d, χ d ^ n ∂β (R y)) = ∫ d, χ (T d)^n ∂β y := by
    rw [hy, integral_map hT.aemeasurable (hχ.pow_const n).aestronglyMeasurable]
  funext i
  simp only [kernelEncoding, he, Function.comp_def]
end EuclideanFiveColor.PhaseEncoding

namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

abbrev MomentTest (M N : ℕ) := Fin N × {p : Fin M × Fin M // p.1 ≠ p.2}

def momentArgument {M N : ℕ} (z : MomentTest M N) : E :=
  (z.1.val + 1) * ((z.2.val.1.val : E) - z.2.val.2.val)

lemma momentArgument_ne_zero {M N : ℕ} (z : MomentTest M N) : momentArgument z ≠ 0 := by
  unfold momentArgument
  apply mul_ne_zero
  · exact_mod_cast Nat.succ_ne_zero z.1.val
  · apply sub_ne_zero.mpr
    intro h
    have hh : z.2.val.1.val = z.2.val.2.val := by exact_mod_cast h
    exact z.2.property (Fin.ext hh)

lemma momentTest_nonempty {M N : ℕ} (hM : 2 ≤ M) (hN : 0 < N) :
    Nonempty (MomentTest M N) := by
  refine ⟨⟨⟨0, hN⟩, ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩⟩⟩
  intro h
  have hh := congrArg Fin.val h
  norm_num at hh

/-- All integer multiples of all distinct pair differences are tested before
any coefficient bin is selected. -/
theorem exists_simultaneous_moment_parameter (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) (hn : ∀ a : E, 0 ≤ (∫ d, (eval a d : ℂ) ∂ν).re)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ t : F, t ≠ 0 ∧ |(t : ℝ)| < 1/(M : ℝ) ∧
      ∀ z : MomentTest M N, (∫ d, (eval (momentArgument z * ofF t) d : ℂ) ∂ν).re < ε := by
  let : Nonempty (MomentTest M N) := momentTest_nonempty hM hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  obtain ⟨t, ht, htr, hh⟩ := exists_small_wild_parameter
    (Finset.univ : Finset (MomentTest M N)) Finset.univ_nonempty ν hν
    momentArgument momentArgument_ne_zero
    (fun z t => by simpa only [lineFourier_eq] using hn (momentArgument z * ofF t))
    (one_div_pos.mpr hMr) hε hε1
  exact ⟨t, ht, htr, fun z => hh z (Finset.mem_univ z)⟩

lemma eval_dist (a b : E) (d : D) :
    dist (eval a d : ℂ) (eval b d : ℂ) = ‖(eval (a-b) d : ℂ)-1‖ := by
  rw [eval_sub, Circle.coe_div, dist_eq_norm]
  have he : (eval a d : ℂ) / (eval b d : ℂ) - 1 =
      ((eval a d : ℂ) - (eval b d : ℂ)) / (eval b d : ℂ) := by
    field_simp
  rw [he, norm_div, Circle.norm_coe, div_one]

/-- The finite Fejér implication is applied to the actual phase law on an
individual conditional fiber. -/
theorem pair_collision_upper {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (b : X → D) (hb : Measurable b)
    (a₁ a₂ : E) (m N : ℕ) (ρ c : ℝ)
    (harc : ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
      (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
      ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2))
    (hMom : ∀ n, 0 < n → n ≤ N →
      ‖∫ x, (eval ((n : E)*(a₁-a₂)) (b x) : ℂ) ∂μ‖ < c) :
    μ.real {x | dist (eval a₁ (b x) : ℂ) (eval a₂ (b x) : ℂ) ≤ 4*ρ}
      < 1/(4*(m : ℝ)^2) := by
  let φ : X → Circle := fun x => eval (a₁-a₂) (b x)
  have hφ : Measurable φ := (measurable_eval _).comp hb
  let ω := μ.map φ
  let : IsProbabilityMeasure ω :=
    (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance
  have hco : Measurable (fun z : Circle => (z : ℂ)) :=
    (show Continuous (fun z : Circle => (z : ℂ)) from continuous_subtype_val).measurable
  have hmom : ∀ n, 0 < n → n ≤ N → ‖∫ z, (z : ℂ)^n ∂ω‖ < c := by
    intro n hn hnN
    rw [show ω = μ.map φ from rfl,
      integral_map hφ.aemeasurable (hco.pow_const n).aestronglyMeasurable]
    simpa only [φ, eval_nat_mul, Circle.coe_pow] using hMom n hn hnN
  have hu := harc ω hmom
  have hs : MeasurableSet {z : Circle | ‖(z : ℂ)-1‖ ≤ 4*ρ} :=
    measurableSet_le ((hco.sub_const 1).norm) measurable_const
  rw [Measure.real, show ω = μ.map φ from rfl, Measure.map_apply hφ hs] at hu
  simpa only [Measure.real, Set.preimage_ofPred_eq, φ, eval_dist] using hu

end

open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

variable {X Y W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

def FiniteEncodingApproximationAt (μ : Measure X) [IsProbabilityMeasure μ] (p : X → Y) (q : Y → W)
    (b : X → D) (m : ℕ) (γ : ℝ) : Prop :=
  ∃ (r : ℕ) (B C : ℝ) (H : Fin r → Y → Fin m → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ y, ∑ i, ‖H i y‖ ≤ C) ∧
    ∀ k : K, ∃ coeff : W → Fin r → ℂ,
      (∀ w, ‖coeff w‖ ≤ B) ∧
      Integrable (fun x => dist
        (PhaseEncoding.kernelEncoding (condDistrib b p μ)
          (fun d => (eval (kCoeff k) d : ℂ)) m (p x))
        (∑ i, coeff (q (p x)) i • H i (p x)) ^ 2) μ ∧
      (∫ x, dist
        (PhaseEncoding.kernelEncoding (condDistrib b p μ)
          (fun d => (eval (kCoeff k) d : ℂ)) m (p x))
        (∑ i, coeff (q (p x)) i • H i (p x)) ^ 2 ∂μ) < γ^2

def FiniteEncodingApproximation (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → Y) (q : Y → W) (b : X → D) (m : ℕ) : Prop :=
  ∀ γ : ℝ, 0 < γ → FiniteEncodingApproximationAt μ p q b m γ

lemma two_array_norm_bound {r : ℕ} {a b : Fin r → ℂ} {B : ℝ}
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hB : 0 ≤ B) : ‖![a,b]‖ ≤ B := by
  rw [pi_norm_le_iff_of_nonneg hB]
  intro j
  fin_cases j <;> assumption

lemma simultaneous_test_budget {T : Type*} [Fintype T]
    (v : T → ℝ) (c : ℝ) (hc : 0 < c)
    (hv : ∀ t, v t < min 1 (c^2 / (4*(Fintype.card T+1)))) :
    (∑ t, v t)/(c^2) < 1/4 := by
  have hs : (∑ t, v t) ≤ (Fintype.card T : ℝ) *
      (c^2 / (4*(Fintype.card T+1))) := by
    calc
      _ ≤ ∑ _t : T, c^2 / (4*(Fintype.card T+1)) :=
        Finset.sum_le_sum fun t _ => (hv t).le.trans (min_le_right _ _)
      _ = _ := by simp
  have hn : (0 : ℝ) < Fintype.card T+1 := by positivity
  rw [div_lt_iff₀ (sq_pos_of_pos hc)]
  apply hs.trans_lt
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0 : ℝ) < 4*(Fintype.card T+1))]
  nlinarith [sq_pos_of_pos hc]

omit [StandardBorelSpace Y] [Nonempty Y] in

theorem finite_uniform_precision_contradiction
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → Y) (q : Y → W) (b : X → D)
    (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
    (hwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q ∘ p))
      (condDistrib b (q ∘ p) μ)))
    (ρ c : ℝ) (N : ℕ) (hρ : 0 < ρ) (hc : 0 < c) (hN : 0 < N)
    (harc : ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
      (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
      ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2))
    (happrox : FiniteEncodingApproximationAt μ p q b m (((ρ^m/(m : ℝ))/100)/100)) : False := by
  classical
  let P : X → W := q ∘ p
  have hP : Measurable P := hq.comp hp
  let : IsProbabilityMeasure (μ.map P) :=
    (Measure.isProbabilityMeasure_map_iff hP.aemeasurable).mpr inferInstance
  let ν := DifferenceFourier.differenceLaw (μ.map P) (condDistrib b P μ)
  let : IsProbabilityMeasure ν := inferInstance
  have hn (a : E) : 0 ≤ (∫ d, (eval a d : ℂ) ∂ν).re := by
    rw [← predecessor_moment_sq μ P b hP hb a]
    exact integral_nonneg fun _ => sq_nonneg _
  let τ := (ρ^m/(m : ℝ))/100
  let γ := τ/100
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτδ : 18*τ^2 < (ρ^m/(m : ℝ))^2/20 := by
    dsimp [τ]
    nlinarith [sq_pos_of_pos (div_pos (pow_pos hρ m) hmr)]
  obtain ⟨r, B, C, H, hB, hC, hH, happ⟩ := happrox
  choose coeff hcoeff hInt hErr using happ
  obtain ⟨L, bins, hbins⟩ := FiniteBins.bounded_coefficient_bins
    (V := Fin m → ℂ) r B C τ hC hτ
  let M := 20*(L+1)*m^2
  have hM : 2 ≤ M := by dsimp [M]; nlinarith [Nat.one_le_iff_ne_zero.mpr hm.ne']
  let : NeZero M := ⟨by omega⟩
  let T := MomentTest M N
  let ε := min 1 (c^2/(4*(Fintype.card T+1)))
  have hε : 0 < ε := by dsimp [ε]; apply lt_min (by norm_num); positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨t, ht, htM, hTest⟩ := exists_simultaneous_moment_parameter ν hwild hn M N hM hN ε hε hε1
  let xs : Fin M → F := fun j => (j.val+1)*t
  have hxs (j : Fin M) : |(xs j : ℝ)| < 2 := by
    have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
    have hj : (j.val+1 : ℝ) ≤ M := by exact_mod_cast j.isLt
    have hx : |(xs j : ℝ)| = (j.val+1 : ℝ)*|(t : ℝ)| := by
      simp [xs, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ j.val+1 by positivity)]
    rw [hx]
    have hmul := mul_lt_mul_of_pos_left htM (by positivity : (0 : ℝ) < j.val+1)
    have hbound : (j.val+1 : ℝ) * (1/(M : ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one hMr]
      exact hj
    linarith
  choose u v huv using fun j => real_algebraic_sum_two_rotations (xs j) (hxs j)
  let β := condDistrib b p μ
  let enc : K → Y → Fin m → ℂ := fun k =>
    PhaseEncoding.kernelEncoding β (fun d => (eval (kCoeff k) d : ℂ)) m
  let Hp : Fin M → X → Fin m → ℂ := fun j x => enc (u j) (p x)
  let Hm : Fin M → X → Fin m → ℂ := fun j x => enc (v j) (p x)
  let Ap : Fin M → X → Fin m → ℂ := fun j x => ∑ i, coeff (u j) (P x) i • H i (p x)
  let Am : Fin M → X → Fin m → ℂ := fun j x => ∑ i, coeff (v j) (P x) i • H i (p x)
  let ap : Fin M → X → Circle := fun j x => eval (kCoeff (u j)) (b x)
  let am : Fin M → X → Circle := fun j x => eval (kCoeff (v j)) (b x)
  let zp : X → Fin M → Fin m → Circle := fun x j i => eval (kCoeff (u j)) (g (p x) i)
  let zm : X → Fin M → Fin m → Circle := fun x j i => eval (kCoeff (v j)) (g (p x) i)
  have henc : ∀ᵐ x ∂μ, ∀ j, PhaseEncoding.encoding (zp x j) = Hp j x ∧
      PhaseEncoding.encoding (zm x j) = Hm j x := by
    filter_upwards [ae_of_ae_map hp.aemeasurable hg] with x hx
    intro j
    exact ⟨(PhaseEncoding.kernelEncoding_eq_encoding β (eval (kCoeff (u j))) m hm (p x) (g (p x)) hx).symm,
      (PhaseEncoding.kernelEncoding_eq_encoding β (eval (kCoeff (v j))) m hm (p x) (g (p x)) hx).symm⟩
  have hmem : ∀ᵐ x ∂μ, ∀ j, (∃ i, ap j x = zp x j i) ∧ (∃ i, am j x = zm x j i) := by
    filter_upwards [SampledAtoms.ae_sampled_list μ p b hp hb hm g hg] with x hx
    obtain ⟨i, hi⟩ := hx
    intro j
    exact ⟨⟨i, congrArg (eval (kCoeff (u j))) hi⟩, ⟨i, congrArg (eval (kCoeff (v j))) hi⟩⟩
  let f : T → W → ℝ := fun z w =>
    ‖∫ x, (eval (momentArgument z * ofF t) (b x) : ℂ) ∂condDistrib id P μ w‖^2
  have hf (z : T) : Integrable (f z) (μ.map P) :=
    integrable_predecessor_moment_sq μ P b hP hb _
  have hfTest (z : T) : (∫ w, f z w ∂μ.map P) < ε := by
    rw [show (∫ w, f z w ∂μ.map P) =
      (∫ d, (eval (momentArgument z * ofF t) d : ℂ) ∂ν).re from
        predecessor_moment_sq μ P b hP hb _]
    exact hTest z
  have hfBudget : (∑ z, ∫ w, f z w ∂μ.map P)/(c^2) < 1/4 :=
    simultaneous_test_budget _ c hc hfTest
  have heBudget : 10*(∑ j, ((∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
      (∫ x, dist (Hm j x) (Am j x)^2 ∂μ)))/((M : ℝ)*τ^2) < 1/4 := by
    have hs : (∑ j, ((∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
        (∫ x, dist (Hm j x) (Am j x)^2 ∂μ))) < (M : ℝ)*(2*γ^2) := by
      calc
        _ < ∑ _j : Fin M, 2*γ^2 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun j _ => by
            have h1 : (∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) < γ^2 := hErr (u j)
            have h2 : (∫ x, dist (Hm j x) (Am j x)^2 ∂μ) < γ^2 := hErr (v j)
            linarith)
        _ = _ := by simp
    have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
    rw [div_lt_iff₀ (mul_pos hMr (sq_pos_of_pos hτ))]
    dsimp [γ] at hs
    nlinarith
  let arr : W → Fin M → {a : Fin 2 → Fin r → ℂ // ‖a‖ ≤ B} := fun w j =>
    ⟨![coeff (u j) w, coeff (v j) w], two_array_norm_bound (hcoeff _ _) (hcoeff _ _) hB⟩
  let bin : W → Fin M → Fin L := fun w j => bins (arr w j)
  have hlarge : (L : ℝ)*(10*m^2 : ℕ) < (9/10 : ℝ)*Fintype.card (Fin M) := by
    simp only [Fintype.card_fin]
    dsimp [M]
    push_cast
    nlinarith [sq_pos_of_pos hmr, Nat.cast_nonneg (α := ℝ) L]
  have hbin : ∀ᵐ w ∂μ.map P, ∀ i j, bin w i = bin w j →
      ∀ᵐ x ∂condDistrib id P μ w, dist (Ap i x) (Ap j x) ≤ τ ∧
        dist (Am i x) (Am j x) ≤ τ := by
    filter_upwards [ConditionalFiber.ae_in_own_fiber μ P hP] with w hw
    intro i j hij
    filter_upwards [hw] with x hx
    have hh := hbins (arr w i) (arr w j) hij (fun k => H k (p x)) (hH (p x))
    have h0 := (hh 0).le
    have h1 := (hh 1).le
    change dist (∑ k, coeff (u i) (P x) k • H k (p x))
      (∑ k, coeff (u j) (P x) k • H k (p x)) ≤ τ ∧
      dist (∑ k, coeff (v i) (P x) k • H k (p x))
      (∑ k, coeff (v j) (P x) k • H k (p x)) ≤ τ
    rw [hx]
    exact ⟨h0, h1⟩
  have hupper : ∀ᵐ w ∂μ.map P, (∀ z, f z w < c^2) → ∀ i j, i ≠ j →
      (condDistrib id P μ w).real {x |
        dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ}
        < 1/(4*(m : ℝ)^2) := by
    apply Filter.Eventually.of_forall
    intro w hw i j hij
    have hMom : ∀ n : ℕ, 0 < n → n ≤ N →
        ‖∫ x, (eval ((n : E)*(ofF (xs i)-ofF (xs j))) (b x) : ℂ)
          ∂condDistrib id P μ w‖ < c := by
      intro n hn hnN
      let z : T := (⟨n-1, by omega⟩, ⟨(i,j), hij⟩)
      have he : (n : E)*(ofF (xs i)-ofF (xs j)) = momentArgument z * ofF t := by
        have hnv : (n-1)+1 = n := by omega
        have hnv' : ((n-1 : ℕ) : E)+1=(n : E) := by exact_mod_cast hnv
        simp only [momentArgument, z, hnv']
        dsimp [xs]
        simp only [map_mul, map_add, map_natCast, map_one]
        ring
      have hh := hw z
      change ‖∫ x, (eval (momentArgument z * ofF t) (b x) : ℂ)
         ∂condDistrib id P μ w‖^2 < c^2 at hh
      rw [he]
      nlinarith [norm_nonneg (∫ x, (eval (momentArgument z * ofF t) (b x) : ℂ)
         ∂condDistrib id P μ w)]
    have hh := pair_collision_upper (condDistrib id P μ w) b hb
      (ofF (xs i)) (ofF (xs j)) m N ρ c harc hMom
    have he (j : Fin M) (x : X) : (ap j x : ℂ)*(am j x : ℂ) =
        (eval (ofF (xs j)) (b x) : ℂ) := by
      change (eval (kCoeff (u j)) (b x) : ℂ) * (eval (kCoeff (v j)) (b x) : ℂ) = _
      rw [huv j]
      exact congrArg (fun z : Circle => (z : ℂ)) (eval_add _ _ _).symm
    simpa only [he] using hh
  apply FiniteModule.common_fiber_contradiction μ P hP m hm ρ τ (c^2) hρ hτ
    (sq_pos_of_pos hc) hτδ Hp Hm Ap Am
    (fun j => (PhaseEncoding.measurable_kernelEncoding β _ (measurable_eval_coe _) m).comp hp)
    (fun j => (PhaseEncoding.measurable_kernelEncoding β _ (measurable_eval_coe _) m).comp hp)
    (fun j => hInt (u j)) (fun j => hInt (v j)) zp zm ap am
    (fun j => (measurable_eval _).comp hb) (fun j => (measurable_eval _).comp hb)
    henc hmem f hf (Filter.Eventually.of_forall (fun w z => sq_nonneg _))
    (by simp only [Fintype.card_fin]; linarith) L bin hlarge hbin hupper

omit [StandardBorelSpace Y] [Nonempty Y] in
theorem finite_uniform_successor_contradiction
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → Y) (q : Y → W) (b : X → D)
    (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
    (hwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q ∘ p))
      (condDistrib b (q ∘ p) μ)))
    (happrox : FiniteEncodingApproximation μ p q b m) : False := by
  obtain ⟨ρ, c, N, hρ, hc, hN, harc⟩ := SmallArc.exists_small_arc_constants m hm
  exact finite_uniform_precision_contradiction μ p q b hp hq hb m hm g hg hwild
    ρ c N hρ hc hN harc (happrox _ (by positivity))

end PlaneFiveColor.Spectral

end

end OAI
