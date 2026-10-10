import Mathlib
import OAI.Probability.SKFluctuations.ScalarSourceJet

namespace OAI

/-! Backward Clock Derivative. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem clockTest_sub_test {ι : Type*} [Fintype ι] {F A B : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    (m t : ℝ) (x : ι → ℝ) :
    clockTest m F (fun y => A y-B y) t x = clockTest m F A t x-clockTest m F B t x := by
  have he : (fun y => A y-B y) = fun y => A y+(-1)*B y := by funext y; ring
  rw [he,clockTest_add_test hF hA (hB.const_mul (-1)),clockTest_const_mul]
  ring

theorem HeatJet.tested_trace_eq_rate {n : ℕ} (J : HeatJet n) (m : ℝ) :
    testedHeatTrace m J.G J.H J.A J.A₁ J.A₂ =
      fun y => 2*J.testRate m y+(2*m)*(J.A y*J.potentialRate m y) := by
  funext y
  unfold testedHeatTrace HeatJet.testRate HeatJet.potentialRate
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem HeatJet.backward_cancellation {n : ℕ} (J : HeatJet n) {B : (Fin (n+1) → ℝ) → ℝ}
    (hB : BddSmooth 0 B) (m t : ℝ) (x : Fin (n+1) → ℝ) :
    clockTestDerivative m J.F J.G J.H J.A J.A₁ J.A₂ t x-
      clockGradient m J.F (J.potentialRate m) J.A B t x =
      clockTest m J.F (fun y => J.testRate m y-B y) t x := by
  unfold clockTestDerivative clockGradient
  rw [J.tested_trace_eq_rate,J.trace_eq_rate,
    clockTest_add_test J.lipschitz ((J.smoothTestRate m).const_mul 2)
      ((J.smoothA.mul (J.smoothPotentialRate m)).const_mul (2*m)),
    clockTest_const_mul,clockTest_const_mul,clockTest_const_mul,
    clockTest_sub_test J.lipschitz (J.smoothTestRate m) hB]
  ring

theorem HeatJetFamily.hasDerivAt_backwardTest {n : ℕ} (V : HeatJetFamily n)
    {B : ℝ → (Fin (n+1) → ℝ) → ℝ} {m T t : ℝ}
    (hcB : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => B p.1 p.2))
    (hbB : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => B p.1 p.2))
    (hsB : ∀ r, BddSmooth 0 (B r))
    (hdF : ∀ r ∈ Ioo 0 (T+1), ∀ y, HasDerivAt (fun s => (V.J s).F y)
      ((V.J r).potentialRate m y) r)
    (hdA : ∀ r ∈ Ioo 0 (T+1), ∀ y, HasDerivAt (fun s => (V.J s).A y) (B r y) r)
    (ht : t ∈ Ioo 0 T) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => clockTest m (V.J (T-s)).F (V.J (T-s)).A s x)
      (clockTest m (V.J (T-t)).F (fun y => (V.J (T-t)).testRate m y-B (T-t) y) t x) t := by
  have hbt : T-t ∈ Ioo (0:ℝ) (T+1) := by constructor <;> linarith [ht.1,ht.2]
  have hd := hasDerivAt_dynamic_clockTest V.J m V.lipschitz V.continuousF V.continuousA
    (V.continuousPotentialRate m) hcB V.boundedA (V.boundedPotentialRate m) hbB
    (V.continuousP m) (V.continuousW m) (V.boundedP m) (V.boundedW m)
    hdF hdA x (hasDerivAt_id t) ((hasDerivAt_const t T).sub (hasDerivAt_id t)) ht.1 hbt
  apply hd.congr_deriv
  simpa only [Pi.add_apply, Pi.neg_apply, id_eq, sub_zero, zero_sub, zero_add,
    mul_one, mul_neg_one, sub_eq_add_neg] using
    (V.J (T-t)).backward_cancellation (hsB (T-t)) m t x

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

 theorem power_increment_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (p : ℕ) :
    y^p-x^p ≤ (p:ℝ)*y^(p-1)*(y-x) := by
  have h := abs_pow_sub_pow_le (a := y) (b := x) (n := p)
  rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hx hxy _)),
    abs_of_nonneg (sub_nonneg.mpr hxy), abs_of_nonneg hx,
    abs_of_nonneg (hx.trans hxy), max_eq_left hxy] at h
  nlinarith

 theorem sum_power_increment_le {A U : ℕ → ℝ} (hA : Monotone A)
    (hA0 : ∀ j, 0 ≤ A j) (hU : ∀ j, 0 ≤ U j) (p n : ℕ) :
    (∑ j ∈ Finset.range n, A (j+1)^p*(U (j+1)-U j)) ≤ A n^p*U n := by
  induction n with
  | zero => simpa using mul_nonneg (pow_nonneg (hA0 0) p) (hU 0)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hA0 n) (hA (Nat.le_succ n)) p) (hU n)
    nlinarith

 theorem power_sum_increment_le {A : ℕ → ℝ} (hA : Monotone A)
    (hA0 : A 0 = 0) {p : ℕ} (hp : 0 < p) (n : ℕ) :
    A n^p ≤ (p:ℝ)*∑ j ∈ Finset.range n, A (j+1)^(p-1)*(A (j+1)-A j) := by
  have hn j : 0 ≤ A j := by simpa [hA0] using hA (Nat.zero_le j)
  induction n with
  | zero => simp [hA0, Nat.ne_of_gt hp]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add]
    have h := power_increment_le (hn n) (hA (Nat.le_succ n)) p
    linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def finiteCompensator (μ : Measure Ω) (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›)
    (U : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, (μ[U (j+1)-U j | 𝒢 j]) ω

 theorem finiteCompensator_zero (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›)
    (U : ℕ → Ω → ℝ) (ω : Ω) : finiteCompensator μ 𝒢 U 0 ω = 0 := by
  simp [finiteCompensator]

 theorem finiteCompensator_succ (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›)
    (U : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) :
    finiteCompensator μ 𝒢 U (j+1) ω - finiteCompensator μ 𝒢 U j ω =
      (μ[U (j+1)-U j | 𝒢 j]) ω := by
  simp [finiteCompensator, Finset.sum_range_succ]

 theorem finiteCompensator_predictable (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›)
    (U : ℕ → Ω → ℝ) (j : ℕ) :
    StronglyMeasurable[𝒢 j] (finiteCompensator μ 𝒢 U (j+1)) := by
  unfold finiteCompensator
  have h := Finset.stronglyMeasurable_sum (Finset.range (j+1)) (fun k hk =>
    (stronglyMeasurable_condExp (μ := μ) (f := U (k+1)-U k) (m := 𝒢 k)).mono
      (𝒢.mono (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))
  convert h using 1
  ext ω
  simp

 theorem finiteCompensator_monotone {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    {U : ℕ → Ω → ℝ} (hU : Submartingale U 𝒢 μ) :
    ∀ᵐ ω ∂μ, Monotone (fun n => finiteCompensator μ 𝒢 U n ω) := by
  have h : ∀ᵐ ω ∂μ, ∀ j : ℕ, 0 ≤ (μ[U (j+1)-U j | 𝒢 j]) ω :=
    ae_all_iff.mpr fun j => hU.condExp_sub_nonneg (Nat.le_succ j)
  filter_upwards [h] with ω hω
  apply monotone_nat_of_le_succ
  intro j
  have he := finiteCompensator_succ (μ := μ) 𝒢 U j ω
  linarith [hω j]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

 

 theorem finiteCompensator_power_exchange {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    {U : ℕ → Ω → ℝ} (hU : Submartingale U 𝒢 μ)
    (hU0 : ∀ j, ∀ᵐ ω ∂μ, 0 ≤ U j ω) {p : ℕ} (hp : 0 < p) (N : ℕ)
    (hAp : Integrable (fun ω => finiteCompensator μ 𝒢 U N ω ^ p) μ)
    (hAU : Integrable (fun ω => finiteCompensator μ 𝒢 U N ω ^ (p-1)*U N ω) μ)
    (hprod : ∀ j, Integrable (fun ω =>
      finiteCompensator μ 𝒢 U (j+1) ω ^ (p-1)*(U (j+1) ω-U j ω)) μ) :
    (∫ ω, finiteCompensator μ 𝒢 U N ω ^ p ∂μ) ≤
      (p:ℝ)*∫ ω, finiteCompensator μ 𝒢 U N ω ^ (p-1)*U N ω ∂μ := by
  let A := finiteCompensator μ 𝒢 U
  let W : ℕ → Ω → ℝ := fun j ω => A (j+1) ω ^ (p-1)
  let q : ℕ → Ω → ℝ := fun j => μ[U (j+1)-U j | 𝒢 j]
  have hce j : μ[(W j)*(U (j+1)-U j) | 𝒢 j] =ᵐ[μ] (W j)*(q j) :=
    condExp_mul_of_stronglyMeasurable_left
      (finiteCompensator_predictable 𝒢 U j |>.pow (p-1)) (hprod j)
      ((hU.integrable (j+1)).sub (hU.integrable j))
  have hiq j : Integrable (fun ω => W j ω*q j ω) μ :=
    integrable_condExp.congr (hce j)
  have hE : (∫ ω, ∑ j ∈ Finset.range N, W j ω*q j ω ∂μ) =
      ∫ ω, ∑ j ∈ Finset.range N, W j ω*(U (j+1) ω-U j ω) ∂μ := by
    rw [integral_finsetSum _ (fun j _ => hiq j),
      integral_finsetSum _ (fun j _ => hprod j)]
    apply Finset.sum_congr rfl
    intro j _
    exact (integral_congr_ae (hce j)).symm.trans (integral_condExp (𝒢.le j))
  have hm := finiteCompensator_monotone hU
  have hnon : ∀ᵐ ω ∂μ, ∀ j : ℕ, 0 ≤ U j ω := ae_all_iff.mpr hU0
  have h1 : (∫ ω, A N ω ^ p ∂μ) ≤
      (p:ℝ)*(∫ ω, ∑ j ∈ Finset.range N, W j ω*q j ω ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hAp ((integrable_finsetSum _ (fun j _ => hiq j)).const_mul _)
    filter_upwards [hm] with ω hω
    have h := power_sum_increment_le hω (finiteCompensator_zero 𝒢 U ω) hp N
    simpa only [finiteCompensator_succ] using h
  have h2 : (∫ ω, ∑ j ∈ Finset.range N, W j ω*(U (j+1) ω-U j ω) ∂μ) ≤
      ∫ ω, A N ω^(p-1)*U N ω ∂μ := by
    apply integral_mono_ae (integrable_finsetSum _ (fun j _ => hprod j)) hAU
    filter_upwards [hm,hnon] with ω hω hpos
    exact sum_power_increment_le hω
      (fun j => by simpa only [finiteCompensator_zero] using hω (Nat.zero_le j)) hpos (p-1) N
  rw [hE] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg p))

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open Set

 theorem natPower_support {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (p : ℕ) :
    (p:ℝ)*x^(p-1)*(y-x) ≤ y^p-x^p := by
  rcases lt_trichotomy x y with h | h | h
  · have H := (convexOn_pow (𝕜 := ℝ) p).le_slope_of_hasDerivAt hx hy h (hasDerivAt_pow p x)
    rw [slope_def_field] at H
    exact (le_div_iff₀ (sub_pos.mpr h)).mp H
  · subst y; simp
  · have H := (convexOn_pow (𝕜 := ℝ) p).slope_le_of_hasDerivAt hy hx h (hasDerivAt_pow p x)
    rw [slope_def_field] at H
    have H' := (div_le_iff₀ (sub_pos.mpr h)).mp H
    nlinarith

 theorem integer_young {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {p : ℕ} (hp : 0 < p) :
    (p:ℝ)*x^(p-1)*y ≤ ((p:ℝ)-1)*x^p+y^p := by
  have h := natPower_support hx hy p
  have he : x^(p-1)*x = x^p := by rw [← pow_succ, Nat.sub_add_cancel hp]
  have h' : (p:ℝ)*x^(p-1)*(y-x) = (p:ℝ)*x^(p-1)*y-(p:ℝ)*x^p := by
    simp only [mul_sub, mul_assoc, he]
  rw [h'] at h
  nlinarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

 

 theorem finiteCompensator_moment_bound {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    {U : ℕ → Ω → ℝ} (hU : Submartingale U 𝒢 μ)
    (hU0 : ∀ j, ∀ᵐ ω ∂μ, 0 ≤ U j ω) {p : ℕ} (hp : 0 < p) (N : ℕ)
    (hAp : Integrable (fun ω => finiteCompensator μ 𝒢 U N ω ^ p) μ)
    (hUp : Integrable (fun ω => U N ω ^ p) μ)
    (hAU : Integrable (fun ω => finiteCompensator μ 𝒢 U N ω ^ (p-1)*U N ω) μ)
    (hprod : ∀ j, Integrable (fun ω =>
      finiteCompensator μ 𝒢 U (j+1) ω ^ (p-1)*(U (j+1) ω-U j ω)) μ) :
    (∫ ω, finiteCompensator μ 𝒢 U N ω ^ p ∂μ) ≤
      (p:ℝ)^p*∫ ω, U N ω ^ p ∂μ := by
  let A := finiteCompensator μ 𝒢 U
  have hex := finiteCompensator_power_exchange hU hU0 hp N hAp hAU hprod
  have hy : (p:ℝ)^2*(∫ ω, A N ω^(p-1)*U N ω ∂μ) ≤
      ((p:ℝ)-1)*(∫ ω, A N ω^p ∂μ)+(p:ℝ)^p*(∫ ω, U N ω^p ∂μ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hAp.const_mul _) (hUp.const_mul _)]
    apply integral_mono_ae (hAU.const_mul _) ((hAp.const_mul _).add (hUp.const_mul _))
    filter_upwards [finiteCompensator_monotone hU, hU0 N] with ω hm hu
    have ha : 0 ≤ A N ω := by
      simpa only [finiteCompensator_zero] using hm (Nat.zero_le N)
    have H := integer_young ha (mul_nonneg (Nat.cast_nonneg p) hu) hp
    simpa only [A, Pi.add_apply, mul_pow, pow_two, mul_assoc, mul_left_comm, mul_comm] using H
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
  have hh := mul_le_mul_of_nonneg_left hex hp0
  dsimp only [A] at hy
  nlinarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
 theorem finiteCompensator_measurable (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›)
    (U : ℕ → Ω → ℝ) (n : ℕ) : StronglyMeasurable (finiteCompensator μ 𝒢 U n) := by
  unfold finiteCompensator
  have h := Finset.stronglyMeasurable_sum (Finset.range n) (fun j _ =>
    (stronglyMeasurable_condExp (μ := μ) (f := U (j+1)-U j) (m := 𝒢 j)).mono (𝒢.le j))
  convert h using 1
  ext ω
  simp

omit [IsFiniteMeasure μ] in
 theorem finiteCompensator_bound (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›)
    {U : ℕ → Ω → ℝ} {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖U j ω‖ ≤ R) (n : ℕ) :
    ∀ᵐ ω ∂μ, ‖finiteCompensator μ 𝒢 U n ω‖ ≤ (n:ℝ)*(2*R) := by
  have hq j : ∀ᵐ ω ∂μ, ‖(μ[U (j+1)-U j | 𝒢 j]) ω‖ ≤ 2*R := by
    apply ae_bdd_norm_condExp_of_ae_bdd_norm
    filter_upwards [hR j,hR (j+1)] with ω hj hj'
    exact (norm_sub_le _ _).trans (by linarith)
  have hqall : ∀ᵐ ω ∂μ, ∀ j, ‖(μ[U (j+1)-U j | 𝒢 j]) ω‖ ≤ 2*R := ae_all_iff.mpr hq
  filter_upwards [hqall] with ω hω
  calc
    _ ≤ ∑ j ∈ Finset.range n, ‖(μ[U (j+1)-U j | 𝒢 j]) ω‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range n, 2*R := Finset.sum_le_sum fun j _ => hω j
    _ = _ := by simp

 theorem finiteCompensator_power_integrable (𝒢 : Filtration ℕ ‹MeasurableSpace Ω›)
    {U : ℕ → Ω → ℝ} {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖U j ω‖ ≤ R) (n p : ℕ) :
    Integrable (fun ω => finiteCompensator μ 𝒢 U n ω^p) μ := by
  apply Integrable.of_bound ((finiteCompensator_measurable 𝒢 U n).pow p).aestronglyMeasurable
    (((n:ℝ)*(2*R))^p)
  filter_upwards [finiteCompensator_bound 𝒢 hR n] with ω hω
  simp only [Pi.pow_apply, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hω p

 theorem boundedSubmartingale_compensator_moment {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    {U : ℕ → Ω → ℝ} (hU : Submartingale U 𝒢 μ)
    (hU0 : ∀ j, ∀ᵐ ω ∂μ, 0 ≤ U j ω)
    {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖U j ω‖ ≤ R) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∫ ω, finiteCompensator μ 𝒢 U N ω^p ∂μ) ≤
      (p:ℝ)^p*∫ ω, U N ω^p ∂μ := by
  have hm n : AEStronglyMeasurable (fun ω => finiteCompensator μ 𝒢 U n ω^(p-1)) μ := ((finiteCompensator_measurable (μ := μ) 𝒢 U n).pow (p-1)).aestronglyMeasurable
  have hb n : ∀ᵐ ω ∂μ, ‖finiteCompensator μ 𝒢 U n ω^(p-1)‖ ≤ ((n:ℝ)*(2*R))^(p-1) := by
    filter_upwards [finiteCompensator_bound 𝒢 hR n] with ω hω
    simp only [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hω _
  apply finiteCompensator_moment_bound hU hU0 hp N
    (finiteCompensator_power_integrable 𝒢 hR N p)
  · apply Integrable.of_bound ((hU.stronglyAdapted N).mono (𝒢.le N) |>.pow p).aestronglyMeasurable (R^p)
    filter_upwards [hR N] with ω hω
    simp only [Pi.pow_apply, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hω _
  · exact (hU.integrable N).bdd_mul (hm N) (hb N)
  · intro j
    exact ((hU.integrable (j+1)).sub (hU.integrable j)).bdd_mul (hm (j+1)) (hb (j+1))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

def BoundaryTree.chain (steps : List (GaussianStep ι)) : BoundaryTree ι Unit steps :=
  match steps with
  | [] => .leaf ()
  | st::tail => (chain tail).step st

def BoundaryTree.chainEquiv (steps : List (GaussianStep ι)) :
    (chain steps).Assignment (fun _ => Bool) ≃ Bool :=
  match steps with
  | [] => Equiv.refl _
  | _::tail => chainEquiv tail

 theorem BoundaryTree.chain_weight (steps : List (GaussianStep ι))
    (F : (ι → ℝ) → ℝ) (W : Bool → (ι → ℝ) → ℝ) (b : Bool) (x : ι → ℝ) :
    (chain steps).weight (fun _ => F) (fun _ b _ => W b)
      ((chainEquiv steps).symm b) 0 x = prefixTest steps F (W b) x := by
  induction steps generalizing x with
  | nil => rfl
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    simp only [chain,chainEquiv,weight,prefixTest]
    congr 1
    exact funext ih

 omit [Fintype ι] in
 theorem BoundaryTree.chain_budget (steps : List (GaussianStep ι)) (V : Unit → ℝ) :
    (chain steps).budget V = V () := by
  induction steps with
  | nil => rfl
  | cons st tail ih => exact ih

 theorem prefixTest_potential_stability {F G A : (ι → ℝ) → ℝ} {C₀ C₁ : ℝ≥0}
    {K L m : ℝ} (hF : LipschitzWith C₀ F) (hG : LipschitzWith C₁ G)
    (hK : 0 ≤ K) (hFG : ∀ x, |G x-F x| ≤ K)
    (hA : Continuous A) (hL : 0 < L) (hAL : ∀ x, |A x| ≤ L)
    (steps : List (GaussianStep ι)) (ho : PrefixOrdered 0 m steps) (x : ι → ℝ) :
    |prefixTest steps G A x-prefixTest steps F A x| ≤ 4*m*K*L := by
  let W : Unit → Bool → (ι → ℝ) → ℝ := fun _ b y =>
    if b then (1+A y/L)/2 else (1-A y/L)/2
  have hWc : ∀ b s, Continuous (W b s) := by
    intro b s
    cases s <;> simp only [W,Bool.false_eq_true,ite_false,ite_true] <;> fun_prop
  have hAW : BddSmooth 0 A := ⟨hA,L,hL.le,hAL⟩
  have hWp : ∀ b y, (∀ s, 0 ≤ W b s y) ∧ ∑ s, W b s y = 1 := by
    intro b y
    have ha := (abs_le.mp (hAL y))
    have hd : -1 ≤ A y/L ∧ A y/L ≤ 1 := by
      constructor
      · apply (le_div_iff₀ hL).2; nlinarith
      · apply (div_le_iff₀ hL).2; nlinarith
    constructor
    · intro s; cases s <;> simp only [W,Bool.false_eq_true,↓reduceIte] <;> linarith [hd.1,hd.2]
    · simp only [Fintype.sum_bool,W,Bool.false_eq_true,↓reduceIte]; ring
  have hh := (BoundaryTree.chain steps).finite_stability hF hG hK hFG hWc hWc hWp hWp
    (fun _ => 0) (fun _ _ => by simp) ho x
  rw [BoundaryTree.chain_budget] at hh
  simp only [zero_add] at hh
  have hs : (∑ b : Bool, |prefixTest steps G (W () b) x-prefixTest steps F (W () b) x|) ≤ 2*m*K := by
    have he := (BoundaryTree.chainEquiv steps).symm.sum_comp
      (fun b => |(BoundaryTree.chain steps).weight (fun _ => G) (fun _ b _ => W () b) b 0 x-
        (BoundaryTree.chain steps).weight (fun _ => F) (fun _ b _ => W () b) b 0 x|)
    simp_rw [BoundaryTree.chain_weight] at he
    exact he.le.trans hh
  have hb : |prefixTest steps G (W () true) x-prefixTest steps F (W () true) x| ≤ 2*m*K := by
    exact (Finset.single_le_sum (fun b _ => abs_nonneg _) (Finset.mem_univ true)).trans hs
  have heF := prefixTest_affine hF hAW steps ho.positive (1/2) (1/(2*L)) x
  have heG := prefixTest_affine hG hAW steps ho.positive (1/2) (1/(2*L)) x
  have hW : W () true = fun y => 1/2+1/(2*L)*A y := by
    funext y; simp only [W,ite_true]; ring
  rw [hW,heF,heG] at hb
  have he : (1/2+1/(2*L)*prefixTest steps G A x)-(1/2+1/(2*L)*prefixTest steps F A x) =
      (prefixTest steps G A x-prefixTest steps F A x)/(2*L) := by ring
  rw [he,abs_div,abs_of_pos (mul_pos (by norm_num) hL)] at hb
  have hh' := (div_le_iff₀ (mul_pos (by norm_num) hL)).mp hb
  nlinarith

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

def terminalPerturb (F A : (ι → ℝ) → ℝ) (s : ℝ) : (ι → ℝ) → ℝ :=
  fun x => F x+s*A x

 theorem terminalPerturb_lipschitz {F A : (ι → ℝ) → ℝ} {C D : ℝ≥0}
    (hF : LipschitzWith C F) (hA : LipschitzWith D A) (s : ℝ) :
    LipschitzWith (C+‖s‖₊*D) (terminalPerturb F A s) :=
  hF.add ((lipschitzWith_smul s).comp hA)

 theorem terminalPerturb_parametric {F A : (ι → ℝ) → ℝ} {C D : ℝ≥0} {K l r : ℝ}
    (hF : LipschitzWith C F) (hA : LipschitzWith D A) (hK : 0 ≤ K)
    (hb : ∀ x, |A x| ≤ K) :
    ParametricRegular l r K (terminalPerturb F A) (fun _ => A) := by
  refine ⟨hK,fun s _ => ⟨_,terminalPerturb_lipschitz hF hA s⟩,
    fun _ _ => hA.continuous,fun _ _ x => hb x,?_⟩
  intro s _ x
  convert ((hasDerivAt_id s).mul_const (A x)).const_add (F x) using 1 <;>
    first | rfl | simp only [one_mul]

 theorem prefixContinuation_terminal_deriv {F A : (ι → ℝ) → ℝ} {C D : ℝ≥0} {K : ℝ}
    (hF : LipschitzWith C F) (hA : LipschitzWith D A) (hK : 0 ≤ K)
    (hb : ∀ x, |A x| ≤ K) (steps : List (GaussianStep ι))
    (hm : ∀ st ∈ steps, 0 < st.1) (s : ℝ) (x : ι → ℝ) :
    HasDerivAt (fun t => prefixContinuation steps (terminalPerturb F A t) x)
      (prefixTest steps (terminalPerturb F A s) A x) s := by
  exact ((terminalPerturb_parametric (l := s-1) (r := s+1) hF hA hK hb).prefix steps hm).derivative
    s (by constructor <;> linarith) x

 theorem prefixTest_terminal_lipschitz_bound {F A : (ι → ℝ) → ℝ} {C D : ℝ≥0} {K m : ℝ}
    (hF : LipschitzWith C F) (hA : LipschitzWith D A) (hK : 0 < K)
    (hb : ∀ x, |A x| ≤ K) (steps : List (GaussianStep ι))
    (ho : PrefixOrdered 0 m steps) (s t : ℝ) (x : ι → ℝ) :
    |prefixTest steps (terminalPerturb F A s) A x-
      prefixTest steps (terminalPerturb F A t) A x| ≤ (4*m*K^2)*|s-t| := by
  have hh := prefixTest_potential_stability (terminalPerturb_lipschitz hF hA t)
    (terminalPerturb_lipschitz hF hA s) (show 0 ≤ |s-t| *K by positivity)
    (fun y => show |terminalPerturb F A s y-terminalPerturb F A t y| ≤ |s-t| *K from by
      rw [show terminalPerturb F A s y-terminalPerturb F A t y = (s-t)*A y by
        dsimp only [terminalPerturb]; ring, abs_mul]
      exact mul_le_mul_of_nonneg_left (hb y) (abs_nonneg _))
    hA.continuous hK hb steps ho x
  exact hh.trans_eq (by ring)

 theorem prefixTest_terminal_lipschitz {F A : (ι → ℝ) → ℝ} {C D : ℝ≥0} {K m : ℝ}
    (hF : LipschitzWith C F) (hA : LipschitzWith D A) (hK : 0 < K)
    (hb : ∀ x, |A x| ≤ K) (steps : List (GaussianStep ι))
    (ho : PrefixOrdered 0 m steps) (x : ι → ℝ) :
    LipschitzWith (Real.toNNReal (4*m*K^2))
      (fun s => prefixTest steps (terminalPerturb F A s) A x) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,Real.dist_eq,Real.coe_toNNReal _ (by nlinarith [ho.bounds.2,sq_nonneg K])]
  exact prefixTest_terminal_lipschitz_bound hF hA hK hb steps ho s t x

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem HeatJet.test_lipschitz {n : ℕ} (J : HeatJet n) :
    ∃ C : ℝ≥0, LipschitzWith C J.A := by
  choose B hB hb using fun i => (J.smoothA₁ i).bound
  have hsum : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => hB i
  refine ⟨Real.toNNReal (∑ i, B i),LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  let v := x-y
  obtain ⟨c,_,hc⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => J.A (y+t • v))
    (fun t => ∑ i, v i*J.A₁ i (y+t • v)) (by norm_num : (0:ℝ) < 1)
    (fun t _ => (J.derivA y v t).continuousAt.continuousWithinAt)
    (fun t _ => J.derivA y v t)
  have hh : |∑ i, v i*J.A₁ i (y+c • v)| ≤ (∑ i, B i)*‖v‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i, ‖v‖*B i := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        apply mul_le_mul _ (hb i _) (abs_nonneg _) (norm_nonneg _)
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
      _ = _ := by rw [← Finset.mul_sum]; ring
  rw [hc,one_smul,zero_smul,add_zero,sub_zero,div_one] at hh
  change |J.A (y+v)-J.A y| ≤ _ at hh
  have he' : y+v = x := by dsimp only [v]; abel
  rw [he'] at hh
  simpa only [Real.coe_toNNReal _ hsum,dist_eq_norm,v,Real.norm_eq_abs] using hh

 
noncomputable def HeatJet.terminalPerturb {n : ℕ} (J : HeatJet n) (s : ℝ) : HeatJet n where
  F := Hierarchy.terminalPerturb J.F J.A s
  A := J.A
  G i x := J.G i x+s*J.A₁ i x
  H i x := J.H i x+s*J.A₂ i x
  A₁ := J.A₁
  A₂ := J.A₂
  C := J.C+‖s‖₊*(J.test_lipschitz.choose)
  lipschitz := terminalPerturb_lipschitz J.lipschitz J.test_lipschitz.choose_spec s
  smoothA := J.smoothA
  smoothG i := (J.smoothG i).add ((J.smoothA₁ i).const_mul s)
  smoothH i := (J.smoothH i).add ((J.smoothA₂ i).const_mul s)
  smoothA₁ := J.smoothA₁
  smoothA₂ := J.smoothA₂
  derivF x v t := by
    have hh := (J.derivF x v t).add ((J.derivA x v t).const_mul s)
    apply hh.congr_deriv
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  derivG i x t := (J.derivG i x t).add ((J.derivA₁ i x t).const_mul s)
  derivA := J.derivA
  derivA₁ := J.derivA₁

 theorem HeatJet.schedule_F_prefix {n : ℕ} (J : HeatJet n) (cs : List HeatClock) :
    (J.schedule cs).F = prefixContinuation (heatSteps cs) J.F := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [HeatJet.schedule,heatSteps,List.map_cons,prefixContinuation,HeatJet.evolve]
    rw [ih]
    simp only [clockContinuation,heatSteps,Real.toNNReal_coe]

 theorem HeatJet.schedule_A_prefix {n : ℕ} (J : HeatJet n) (cs : List HeatClock) :
    (J.schedule cs).A = prefixTest (heatSteps cs) J.F J.A := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [HeatJet.schedule,heatSteps,List.map_cons,prefixTest,HeatJet.evolve]
    rw [ih,J.schedule_F_prefix]
    simp only [clockTest,heatSteps,Real.toNNReal_coe]

 theorem HeatJet.schedule_terminal_deriv {n : ℕ} (J : HeatJet n) (cs : List HeatClock)
    (s : ℝ) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun t => ((J.terminalPerturb t).schedule cs).F x)
      (((J.terminalPerturb s).schedule cs).A x) s := by
  obtain ⟨K,hK,hb⟩ := J.smoothA.bound
  simp only [HeatJet.schedule_F_prefix,HeatJet.schedule_A_prefix,HeatJet.terminalPerturb]
  apply prefixContinuation_terminal_deriv J.lipschitz J.test_lipschitz.choose_spec hK hb
  intro st hst
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hst
  exact c.positive

end SKFluctuations.Hierarchy

end

end OAI
