import Mathlib
import OAI.Probability.SKFluctuations.UniformActualLaterProjection

namespace OAI

/-! Radius Grid Count. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped BigOperators

 

def radiusGridCount (a b η ξ : ℝ) : ℕ :=
  if a+ξ ≤ b then ⌊(b-a-ξ)/η⌋₊+1 else 0

theorem lt_radiusGridCount {a b η ξ : ℝ} (hη : 0 < η) (j : ℕ) :
    j < radiusGridCount a b η ξ ↔ a+ξ+(j:ℝ)*η ≤ b := by
  unfold radiusGridCount
  split_ifs with h
  · have hn : 0 ≤ (b-a-ξ)/η := div_nonneg (by linarith) hη.le
    rw [Nat.lt_add_one_iff,Nat.le_floor_iff hn,le_div_iff₀ hη]
    constructor <;> intro hj <;> linarith
  · simp only [Nat.not_lt_zero,false_iff,not_le]
    have hp := mul_nonneg (Nat.cast_nonneg j) hη.le
    linarith

theorem radiusGridCount_le {a b η ξ : ℝ} (hη : 0 < η) (hξ : 0 ≤ ξ)
    {N : ℕ} (hb : b < a+(N:ℝ)*η) : radiusGridCount a b η ξ ≤ N := by
  by_contra h
  have hh := (lt_radiusGridCount hη N).mp (Nat.lt_of_not_ge h)
  linarith

theorem radiusGridCount_endpoint {a b η ξ : ℝ} (hab : a ≤ b) (hη : 0 < η) (hξ : ξ ≤ η) :
    a+ξ+(radiusGridCount a b η ξ:ℝ)*η ≤ b+η := by
  unfold radiusGridCount
  split_ifs with h
  · have hh : (⌊(b-a-ξ)/η⌋₊:ℝ) ≤ (b-a-ξ)/η := Nat.floor_le (div_nonneg (by linarith) hη.le)
    have he := (le_div_iff₀ hη).mp hh
    push_cast
    nlinarith
  · simp only [Nat.cast_zero,zero_mul,add_zero]
    linarith

theorem radiusGridCount_sum {E : Type*} [AddCommMonoid E] (q : ℝ → E)
    {a b η ξ : ℝ} (hη : 0 < η) (hξ : 0 ≤ ξ) {N : ℕ} (hb : b < a+(N:ℝ)*η) :
    (∑ j ∈ Finset.range N, if a+ξ+(j:ℝ)*η ≤ b then q (a+ξ+(j:ℝ)*η) else 0) =
      ∑ j ∈ Finset.range (radiusGridCount a b η ξ), q (a+ξ+(j:ℝ)*η) := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_range]
  constructor
  · exact fun h => (lt_radiusGridCount hη j).mpr h.2
  · intro h
    exact ⟨h.trans_le (radiusGridCount_le hη hξ hb),(lt_radiusGridCount hη j).mp h⟩

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω E : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {X : ℕ → Ω → E}

def radiusSquareIntegral (μ : Measure Ω) (𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → Ω → E) (τ : ℝ → ℕ) (a b η : ℝ) (ω : Ω) : ℝ :=
  ∫ s in a..b, conditionalBlockSquare μ 𝒢 X (τ s) (τ (s+η)) ω

 

theorem boundedMartingale_radiusSquareIntegral_moment (hX : Martingale X 𝒢 μ)
    {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R)
    {τ : ℝ → ℕ} (hτ : Monotone τ) {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) :
    (∫ ω, radiusSquareIntegral μ 𝒢 X τ a b η ω^p ∂μ) ≤
      η^p*(p:ℝ)^p*(∫ ω, ‖X (τ (b+η)) ω‖^(2*p) ∂μ) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((b-a)/η)
  have hb : b < a+(N:ℝ)*η := by
    have hh := (div_lt_iff₀ hη).mp hN
    linarith
  let q : ℝ → Ω → ℝ := fun s ω => conditionalBlockSquare μ 𝒢 X (τ s) (τ (s+η)) ω
  let f : ℝ → Ω → ℝ := fun ξ ω => ∑ j ∈ Finset.range N,
    if a+ξ+(j:ℝ)*η ≤ b then q (a+ξ+(j:ℝ)*η) ω else 0
  have hq : Measurable (Function.uncurry q) :=
    conditionalBlockSquare_joint hτ.measurable (hτ.measurable.comp (measurable_id.add_const η))
  have hf : Measurable (Function.uncurry f) := by
    apply Finset.measurable_sum
    intro j _
    have hj : Measurable (fun z : ℝ × Ω => a+z.1+(j:ℝ)*η) :=
      (measurable_const.add measurable_fst).add_const _
    exact Measurable.ite (measurableSet_le hj measurable_const)
      (hq.comp (hj.prodMk measurable_snd)) measurable_const
  have hB := conditionalBlockSquare_uniform_bounds (μ := μ) (𝒢 := 𝒢) hR
  have hfb : ∀ᵐ ω ∂μ, ∀ ξ, 0 ≤ f ξ ω ∧ f ξ ω ≤ (N:ℝ)*(2*R)^2 := by
    filter_upwards [hB] with ω hω
    intro ξ
    constructor
    · exact Finset.sum_nonneg fun j _ => ite_nonneg (hω _ _).1 le_rfl
    · calc
        _ ≤ ∑ j ∈ Finset.range N, (2*R)^2 := by
          apply Finset.sum_le_sum
          intro j _
          split_ifs
          · exact (hω _ _).2
          · positivity
        _ = _ := by simp
  have hm : ∀ᵐ ξ ∂volume.restrict (Ioc 0 η), (∫ ω, f ξ ω^p ∂μ) ≤
      (p:ℝ)^p*(∫ ω, ‖X (τ (b+η)) ω‖^(2*p) ∂μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ξ hξ
    let σ : ℕ → ℕ := fun j => τ (a+ξ+(j:ℝ)*η)
    have hσ : Monotone σ := by
      intro i j hij
      apply hτ
      have hh := mul_le_mul_of_nonneg_right (show (i:ℝ) ≤ (j:ℝ) by exact_mod_cast hij) hη.le
      linarith
    have he : f ξ = conditionalSquareSum μ (sampledFiltration 𝒢 σ hσ) (fun j => X (σ j))
        (radiusGridCount a b η ξ) := by
      funext ω
      rw [show f ξ ω = ∑ j ∈ Finset.range (radiusGridCount a b η ξ), q (a+ξ+(j:ℝ)*η) ω from
        radiusGridCount_sum (fun s => q s ω) hη hξ.1.le hb]
      unfold conditionalSquareSum
      apply Finset.sum_congr rfl
      intro j _
      have hr : a+ξ+(j:ℝ)*η+η = a+ξ+((j+1:ℕ):ℝ)*η := by push_cast; ring
      simp only [q,conditionalBlockSquare,sampledFiltration,σ,hr]
    rw [he]
    apply (boundedMartingale_conditionalSquareSum_moment (martingale_sampled hX σ hσ)
      (fun j => hR (σ j)) hp (radiusGridCount a b η ξ)).trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg p) p)
    apply boundedMartingale_cut_moment_mono hX hR (by omega : 0 < 2*p)
    exact hτ (radiusGridCount_endpoint hab hη hξ.2)
  have hi := parameter_integral_power_bound (volume.restrict (Ioc 0 η)) μ hf hfb hp hm
  have he : ∀ᵐ ω ∂μ, radiusSquareIntegral μ 𝒢 X τ a b η ω =
      ∫ ξ, f ξ ω ∂volume.restrict (Ioc 0 η) := by
    filter_upwards [hB] with ω hω
    have hqm : Measurable (fun s => q s ω) := hq.comp (measurable_id.prodMk measurable_const)
    have hqi (j : ℕ) (_hj : j < N) : IntervalIntegrable (fun s => q s ω) volume
        (a+(j:ℝ)*η) (a+((j+1:ℕ):ℝ)*η) := by
      constructor <;> apply Integrable.of_bound hqm.aestronglyMeasurable ((2*R)^2) <;>
        exact Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs,abs_of_nonneg (hω _ _).1]
          exact (hω _ _).2
    have h := shiftedGrid_integral_truncated (q := fun s => q s ω) a b η N hab hb.le hqi
    simpa only [radiusSquareIntegral,q,intervalIntegral.integral_of_le hη.le] using h
  have hei : (∫ ω, radiusSquareIntegral μ 𝒢 X τ a b η ω^p ∂μ) =
      ∫ ω, (∫ ξ, f ξ ω ∂volume.restrict (Ioc 0 η))^p ∂μ :=
    integral_congr_ae (he.mono fun ω hω => congrArg (fun r : ℝ => r^p) hω)
  rw [hei]
  simpa only [measureReal_restrict_apply_univ,Real.volume_real_Ioc,sub_zero,
    max_eq_left hη.le,mul_assoc] using hi

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω E : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {X : ℕ → Ω → E}

omit [IsFiniteMeasure μ] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem radiusSquareIntegral_ae_nonneg
    {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R)
    (τ : ℝ → ℕ) {a b : ℝ} (hab : a ≤ b) (η : ℝ) :
    ∀ᵐ ω ∂μ, 0 ≤ radiusSquareIntegral μ 𝒢 X τ a b η ω := by
  filter_upwards [conditionalBlockSquare_uniform_bounds (μ := μ) (𝒢 := 𝒢) hR] with ω hω
  unfold radiusSquareIntegral
  rw [intervalIntegral.integral_of_le hab]
  exact integral_nonneg fun s => (hω _ _).1

 
theorem boundedMartingale_radiusSquareIntegral_Lp (hX : Martingale X 𝒢 μ)
    {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R)
    {τ : ℝ → ℕ} (hτ : Monotone τ) {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) :
    (∫ ω, radiusSquareIntegral μ 𝒢 X τ a b η ω^p ∂μ)^((p:ℝ)⁻¹) ≤
      η*(p:ℝ)*(∫ ω, ‖X (τ (b+η)) ω‖^(2*p) ∂μ)^((p:ℝ)⁻¹) := by
  have hA : 0 ≤ ∫ ω, radiusSquareIntegral μ 𝒢 X τ a b η ω^p ∂μ :=
    integral_nonneg_of_ae ((radiusSquareIntegral_ae_nonneg hR τ hab η).mono
      fun _ h => pow_nonneg h _)
  have hN : 0 ≤ ∫ ω, ‖X (τ (b+η)) ω‖^(2*p) ∂μ :=
    integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _
  have hh := Real.rpow_le_rpow hA
    (boundedMartingale_radiusSquareIntegral_moment hX hR hτ hab hη hp)
    (inv_nonneg.mpr (Nat.cast_nonneg p))
  rw [Real.mul_rpow (by positivity) hN,
    Real.mul_rpow (pow_nonneg hη.le p) (pow_nonneg (Nat.cast_nonneg p) p),
    Real.pow_rpow_inv_natCast hη.le hp.ne',
    Real.pow_rpow_inv_natCast (Nat.cast_nonneg p) hp.ne'] at hh
  exact hh

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def actualRadiusSquareIntegral (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (τ : ℝ → ℕ) (a b η : ℝ) :=
  radiusSquareIntegral
    (μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx)
    (forwardFiltration P (FeatureIndex n → ℝ) (Spin n) steps.length)
    (actualSpinPath n steps x) τ a b η

 

theorem actualRadiusSquareIntegral_Lp (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {τ : ℝ → ℕ} (hτ : Monotone τ) {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) :
    (∫ q, actualRadiusSquareIntegral n steps μ x hx τ a b η q^p
      ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) ≤
      η*(p:ℝ)*(∫ q, ‖actualSpinPath n steps x (τ (b+η)) q‖^(2*p)
        ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps hc
  exact boundedMartingale_radiusSquareIntegral_Lp
    (actualSpinPath_martingale n steps hc μ x hx)
    (fun j => Eventually.of_forall (actualSpinPath_norm_le n steps hc x j)) hτ hab hη hp

end SKFluctuations

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {X : ℕ → Ω → E}

omit [IsFiniteMeasure μ] in
theorem radiusSquareIntegral_measurable {τ : ℝ → ℕ} (hτ : Monotone τ)
    (a b η : ℝ) : Measurable (radiusSquareIntegral μ 𝒢 X τ a b η) := by
  have hq := conditionalBlockSquare_joint (μ := μ) (𝒢 := 𝒢) (X := X)
    hτ.measurable (hτ.measurable.comp (measurable_id.add_const η))
  unfold radiusSquareIntegral intervalIntegral
  exact ((hq.comp measurable_swap).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc a b))).measurable.sub
    ((hq.comp measurable_swap).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc b a))).measurable

omit [IsFiniteMeasure μ] in
theorem radiusSquareIntegral_ae_bound {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) (τ : ℝ → ℕ) (a b η : ℝ) :
    ∀ᵐ ω ∂μ, ‖radiusSquareIntegral μ 𝒢 X τ a b η ω‖ ≤ |b-a| *(2*R)^2 := by
  filter_upwards [conditionalBlockSquare_uniform_bounds (μ := μ) (𝒢 := 𝒢) hR] with ω hω
  exact (intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hω _ _).1]
    exact (hω _ _).2)).trans_eq (mul_comm _ _)

theorem radiusSquareIntegral_power_integrable {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) {τ : ℝ → ℕ} (hτ : Monotone τ)
    (a b η : ℝ) (p : ℕ) :
    Integrable (fun ω => radiusSquareIntegral μ 𝒢 X τ a b η ω^p) μ := by
  apply Integrable.of_bound ((radiusSquareIntegral_measurable hτ a b η).stronglyMeasurable.pow p).aestronglyMeasurable
    ((|b-a| *(2*R)^2)^p)
  filter_upwards [radiusSquareIntegral_ae_bound (𝒢 := 𝒢) hR τ a b η] with ω hω
  simpa only [Pi.pow_apply,norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hω p

variable [InnerProductSpace ℝ E] [CompleteSpace E]

def nearPairMomentConstant (p : ℕ) : ℝ := (4:ℝ)^(2*p)+((2*p:ℕ):ℝ)^(2*p)

theorem nearPairMomentConstant_nonneg (p : ℕ) : 0 ≤ nearPairMomentConstant p := by
  unfold nearPairMomentConstant
  positivity

 

theorem boundedMartingale_nearPairProduct_moment (hX : Martingale X 𝒢 μ)
    {R : ℝ} (hR : ∀ j ω, ‖X j ω‖ ≤ R)
    {τ : ℝ → ℕ} (hτ : Monotone τ) {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) :
    (∫ ω, (runningMax (fun j => ‖X j ω‖^2) (τ (b+η))*
      radiusSquareIntegral μ 𝒢 X τ a b η ω)^p ∂μ) ≤
      nearPairMomentConstant p*η^p*(∫ ω, ‖X (τ (b+η)) ω‖^(4*p) ∂μ) := by
  let M := fun ω => runningMax (fun j => ‖X j ω‖^2) (τ (b+η))
  let A := radiusSquareIntegral μ 𝒢 X τ a b η
  let H := ∫ ω, ‖X (τ (b+η)) ω‖^(4*p) ∂μ
  have hRae j : ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R := Eventually.of_forall (hR j)
  have hM0 ω : 0 ≤ M ω := runningMax_nonneg (fun j => sq_nonneg _) _
  have hMbound ω : M ω ≤ R^2 := runningMax_le
    (fun j => pow_le_pow_left₀ (norm_nonneg _) (hR j ω) 2) _
  have hMa : StronglyAdapted 𝒢 (fun j ω => ‖X j ω‖^2) :=
    fun j => (hX.stronglyMeasurable j).norm.pow 2
  have hMi (k : ℕ) : Integrable (fun ω => M ω^k) μ :=
    runningMax_power_integrable hMa (fun j ω => sq_nonneg _) (fun j ω =>
      pow_le_pow_left₀ (norm_nonneg _) (hR j ω) 2) _ k
  have hAi (k : ℕ) : Integrable (fun ω => A ω^k) μ :=
    radiusSquareIntegral_power_integrable hRae hτ a b η k
  have hI : Integrable (fun ω => M ω^p*A ω^p) μ :=
    (hAi p).bdd_mul (hMi p).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hM0 ω) _)]
      exact pow_le_pow_left₀ (hM0 ω) (hMbound ω) p)
  have hy : 2*η^p*(∫ ω, M ω^p*A ω^p ∂μ) ≤
      η^(2*p)*(∫ ω, M ω^(2*p) ∂μ)+(∫ ω, A ω^(2*p) ∂μ) := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add ((hMi _).const_mul _) (hAi _)]
    apply integral_mono (hI.const_mul _) (((hMi _).const_mul _).add (hAi _))
    intro ω
    have h := sq_nonneg (η^p*M ω^p-A ω^p)
    simp only [pow_mul',Pi.add_apply] at h ⊢
    nlinarith
  have hm : (∫ ω, M ω^(2*p) ∂μ) ≤ (4:ℝ)^(2*p)*H := by
    simpa only [M,H,show 2*(2*p) = 4*p by omega] using
      boundedMartingale_runningMax_square_moment hX hR (by omega : 2 ≤ 2*p) (τ (b+η))
  have ha : (∫ ω, A ω^(2*p) ∂μ) ≤ η^(2*p)*((2*p:ℕ):ℝ)^(2*p)*H := by
    simpa only [A,H,show 2*(2*p) = 4*p by omega] using
      boundedMartingale_radiusSquareIntegral_moment hX hRae hτ hab hη (by omega : 0 < 2*p)
  have hH : 0 ≤ H := integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _
  have hc := nearPairMomentConstant_nonneg p
  have hh : 2*η^p*(∫ ω, M ω^p*A ω^p ∂μ) ≤
      η^(2*p)*nearPairMomentConstant p*H := by
    apply hy.trans
    apply (add_le_add (mul_le_mul_of_nonneg_left hm (pow_nonneg hη.le _)) ha).trans_eq
    unfold nearPairMomentConstant
    ring
  have hz : 0 ≤ η^p*nearPairMomentConstant p*H := by positivity
  have hηp : 0 < η^p := pow_pos hη _
  have he : η^(2*p) = η^p*η^p := by rw [show 2*p = p+p by omega,pow_add]
  rw [he] at hh
  have hb : (∫ ω, M ω^p*A ω^p ∂μ) ≤ nearPairMomentConstant p*η^p*H := by
    apply (mul_le_mul_iff_of_pos_left hηp).mp
    nlinarith
  simpa only [mul_pow,M,A,H] using hb

theorem boundedMartingale_nearPairProduct_Lp (hX : Martingale X 𝒢 μ)
    {R : ℝ} (hR : ∀ j ω, ‖X j ω‖ ≤ R)
    {τ : ℝ → ℕ} (hτ : Monotone τ) {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) :
    (∫ ω, (runningMax (fun j => ‖X j ω‖^2) (τ (b+η))*
      radiusSquareIntegral μ 𝒢 X τ a b η ω)^p ∂μ)^((p:ℝ)⁻¹) ≤
      (nearPairMomentConstant p)^((p:ℝ)⁻¹)*η*
        (∫ ω, ‖X (τ (b+η)) ω‖^(4*p) ∂μ)^((p:ℝ)⁻¹) := by
  have hA : 0 ≤ ∫ ω, (runningMax (fun j => ‖X j ω‖^2) (τ (b+η))*
      radiusSquareIntegral μ 𝒢 X τ a b η ω)^p ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [radiusSquareIntegral_ae_nonneg (𝒢 := 𝒢)
      (fun j => Eventually.of_forall (hR j)) τ hab η] with ω hω
    exact pow_nonneg (mul_nonneg (runningMax_nonneg (fun j => sq_nonneg _) _) hω) _
  have hN : 0 ≤ ∫ ω, ‖X (τ (b+η)) ω‖^(4*p) ∂μ :=
    integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _
  have hh := Real.rpow_le_rpow hA
    (boundedMartingale_nearPairProduct_moment hX hR hτ hab hη hp)
    (inv_nonneg.mpr (Nat.cast_nonneg p))
  rw [Real.mul_rpow (mul_nonneg (nearPairMomentConstant_nonneg p) (pow_nonneg hη.le p)) hN,
    Real.mul_rpow (nearPairMomentConstant_nonneg p) (pow_nonneg hη.le p),
    Real.pow_rpow_inv_natCast hη.le hp.ne'] at hh
  exact hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 

theorem actualNearPairProduct_Lp (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {τ : ℝ → ℕ} (hτ : Monotone τ) {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) :
    (∫ q, (runningMax (fun j => ‖actualSpinPath n steps x j q‖^2) (τ (b+η))*
      actualRadiusSquareIntegral n steps μ x hx τ a b η q)^p
      ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) ≤
      (nearPairMomentConstant p)^((p:ℝ)⁻¹)*η*
        (∫ q, ‖actualSpinPath n steps x (τ (b+η)) q‖^(4*p)
          ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps hc
  exact boundedMartingale_nearPairProduct_Lp (actualSpinPath_martingale n steps hc μ x hx)
    (actualSpinPath_norm_le n steps hc x) hτ hab hη hp

end SKFluctuations

end

end OAI
