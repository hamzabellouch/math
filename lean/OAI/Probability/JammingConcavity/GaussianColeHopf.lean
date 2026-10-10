import Mathlib

namespace OAI

/-! Gaussian Cole Hopf. -/

noncomputable section



 

 
 

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MicroscopicJamming

def RowAnalyticTerminal (u : ℝ → ℝ) (A B C κ Q : ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧ 0 ≤ A ∧ 0 ≤ C ∧ 0 ≤ κ ∧ κ*Q < 1 ∧
  (∀ n : ℕ, 2 ≤ n → ∃ K : ℝ, ∀ x, |iteratedDeriv n u x| ≤ K) ∧
  (∀ x, -A*(1+x^2) ≤ u x ∧ u x ≤ B ∧
    -C ≤ deriv (deriv u) x ∧ deriv (deriv u) x ≤ κ)

def gaussianHeat (v : ℝ → ℝ) (T x : ℝ) : ℝ :=
  ∫ z : ℝ, v (x+Real.sqrt T*z) ∂gaussianReal 0 1

def gaussianRowOperator (a T : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  if a=0 then gaussianHeat u T x else (1/a)*Real.log (gaussianHeat (fun y => Real.exp (a*u y)) T x)

def GaussianColeHopfStatement : Prop :=
  ∀ (u : ℝ → ℝ) (A B C κ Q : ℝ), 0 < Q → RowAnalyticTerminal u A B C κ Q →
  ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
    (∀ x, gaussianRowOperator a 0 u x = u x) ∧
    ∀ T : ℝ, 0 < T → T ≤ Q →
      Differentiable ℝ (gaussianRowOperator a T u) ∧
      Differentiable ℝ (deriv (gaussianRowOperator a T u)) ∧
      ∀ x : ℝ, HasDerivAt (fun r => gaussianRowOperator a r u x)
        ((1/2:ℝ)*(deriv (deriv (gaussianRowOperator a T u)) x+
          a*(deriv (gaussianRowOperator a T u) x)^2)) T
end MicroscopicJamming

 
 

namespace MicroscopicJamming

def gaussianRowComposition : List (ℝ × ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], u => u
  | (a,T)::rs,u => gaussianRowOperator a T (gaussianRowComposition rs u)

def gaussianStepTime (rs : List (ℝ × ℝ)) : ℝ := (rs.map Prod.snd).sum

def GaussianStepBoundsStatement : Prop :=
  ∀ (u : ℝ → ℝ) (A B C κ Q : ℝ), 0 < Q → RowAnalyticTerminal u A B C κ Q →
  ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    gaussianStepTime rs ≤ Q →
    Differentiable ℝ (gaussianRowComposition rs u) ∧
    Differentiable ℝ (deriv (gaussianRowComposition rs u)) ∧
    ∀ x, (-A*(1+x^2+gaussianStepTime rs) ≤ gaussianRowComposition rs u x ∧
      gaussianRowComposition rs u x ≤ B) ∧
      (-C ≤ deriv (deriv (gaussianRowComposition rs u)) x ∧
        deriv (deriv (gaussianRowComposition rs u)) x ≤ κ/(1-κ*gaussianStepTime rs))
end MicroscopicJamming

 
 

namespace MicroscopicJamming

def gaussianStepRemainder : List (ℝ × ℝ) → ℝ → List (ℝ × ℝ)
  | [], _ => []
  | (a,T)::rs,t => if t ≤ T then (a,T-t)::rs else gaussianStepRemainder rs (t-T)

def gaussianStepPath (rs : List (ℝ × ℝ)) (u : ℝ → ℝ) (t x : ℝ) : ℝ :=
  gaussianRowComposition (gaussianStepRemainder rs t) u x

def GaussianStepPathStatement : Prop :=
  ∀ A B C κ Q : ℝ, 0 < Q → 0 ≤ A → 0 ≤ C → 0 ≤ κ → κ*Q < 1 →
  ∃ D L : ℝ, 0 ≤ D ∧ 0 ≤ L ∧
  ∀ u : ℝ → ℝ, RowAnalyticTerminal u A B C κ Q →
  ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    gaussianStepTime rs ≤ Q →
    (∀ x, gaussianStepPath rs u 0 x = gaussianRowComposition rs u x) ∧
    (∀ x, gaussianStepPath rs u (gaussianStepTime rs) x = u x) ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ x,
      |gaussianStepPath rs u t x-gaussianStepPath rs u s x| ≤ D*(1+x^2)*|t-s|) ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ gaussianStepTime rs →
      Differentiable ℝ (gaussianStepPath rs u t) ∧
      Differentiable ℝ (deriv (gaussianStepPath rs u t)) ∧
      ∀ x, |deriv (gaussianStepPath rs u t) x| ≤ L*(1+|x|) ∧
        -C ≤ deriv (deriv (gaussianStepPath rs u t)) x ∧
        deriv (deriv (gaussianStepPath rs u t)) x ≤
          κ/(1-κ*(gaussianStepTime rs-t))
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

 
abbrev RowCylinder (Q R : ℝ) := {p : ℝ × ℝ // p ∈ Icc 0 Q ×ˢ Icc (-R) R}

 

def GaussianStepCompactnessStatement : Prop :=
  ∀ (u : ℝ → ℝ) (A B C κ Q R : ℝ), 0 < Q → 0 < R →
    RowAnalyticTerminal u A B C κ Q →
  ∀ rs : ℕ → List (ℝ × ℝ),
    (∀ n, ∀ r ∈ rs n, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    (∀ n, gaussianStepTime (rs n)=Q) →
    ∃ f : C(RowCylinder Q R, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun n (p : RowCylinder Q R) =>
        gaussianStepPath (rs (φ n)) u p.1.1 p.1.2) f atTop
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def cloudUniform : Measure ℝ := volume.restrict (Ico 0 1)
abbrev MarkedCloud := ℕ → (ℕ × (ℕ → ℝ × ℝ≥0))

def markedCloudLaw (ν : Measure ℝ≥0) : Measure MarkedCloud :=
  Measure.infinitePi (fun _ : ℕ =>
    (poissonMeasure 1).prod (Measure.infinitePi fun _ : ℕ => cloudUniform.prod ν))

def stableCloudWeight (m : ℝ) (ω : MarkedCloud) (n j : ℕ) : ℝ :=
  if j < (ω n).1 then
    ((n:ℝ)+((ω n).2 j).1) ^ (-1/m) * ((ω n).2 j).2
  else 0

def stableCloudSum (m : ℝ) (ω : MarkedCloud) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑' j : ℕ, ENNReal.ofReal (stableCloudWeight m ω n j)

def StableCloudStatement : Prop :=
  ∀ m : ℝ, 0 < m → m < 1 →
  ∀ ν : Measure ℝ≥0, IsProbabilityMeasure ν →
    Integrable (fun y : ℝ≥0 => (y:ℝ)^m) ν →
    0 < ∫ y : ℝ≥0, (y:ℝ)^m ∂ν →
    (∀ᵐ ω ∂markedCloudLaw ν, 0 < stableCloudSum m ω ∧ stableCloudSum m ω < ∞) ∧
    (∀ t : ℝ, 0 ≤ t →
      (∫ ω, Real.exp (-t * (stableCloudSum m ω).toReal) ∂markedCloudLaw ν) =
        Real.exp (-Real.Gamma (1-m) * (∫ y : ℝ≥0, (y:ℝ)^m ∂ν) * t^m)) ∧
    (∀ a : ℝ, 0 < a → a < m →
      Integrable (fun ω => (stableCloudSum m ω).toReal^a) (markedCloudLaw ν)) ∧
    (∀ a : ℝ, 0 < a →
      Integrable (fun ω => (stableCloudSum m ω).toReal^(-a)) (markedCloudLaw ν)) ∧
    Integrable (fun ω => |Real.log (stableCloudSum m ω).toReal|^2) (markedCloudLaw ν)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma iid_prefix_map {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (k : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => μ)).map (fun y => fun i : Fin k => y i) =
      Measure.pi (fun _ : Fin k => μ) := by
  rw [Measure.map_infinitePi_infinitePi_of_inj (f := fun i : Fin k => (i:ℕ)) Fin.val_injective,
    Measure.infinitePi_eq_pi]

lemma iid_prefix_product {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (g : X → ℝ) (hg : Measurable g) (k : ℕ) :
    (∫ y, ∏ j ∈ Finset.range k, g (y j) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      (∫ x, g x ∂μ)^k := by
  have hm : Measurable (fun y : Fin k → X => ∏ j : Fin k, g (y j)) := by fun_prop
  have h := integral_map (μ := Measure.infinitePi (fun _ : ℕ => μ)) (by fun_prop : Measurable (fun y : ℕ → X => fun i : Fin k => y i)).aemeasurable hm.aestronglyMeasurable
  rw [iid_prefix_map] at h
  have hfin : ∀ y : ℕ → X, (∏ j : Fin k, g (y j)) = ∏ j ∈ Finset.range k, g (y j) :=
    fun y => Fin.prod_univ_eq_prod_range (fun j => g (y j)) k
  change (∫ y : Fin k → X, ∏ j, g (y j) ∂Measure.pi (fun _ => μ)) =
    (∫ y : ℕ → X, ∏ j : Fin k, g (y j) ∂Measure.infinitePi (fun _ => μ)) at h
  simp_rw [hfin] at h
  rw [← h, integral_fintype_prod_eq_prod]
  simp

lemma poisson_one_pgf (a : ℝ) :
    (∫ k : ℕ, a^k ∂poissonMeasure 1) = Real.exp (a-1) := by
  rw [integral_poissonMeasure]
  simp only [NNReal.coe_one, one_pow, mul_one, smul_eq_mul]
  calc
    (∑' k : ℕ, Real.exp (-1) / (k.factorial:ℝ) * a^k) =
        Real.exp (-1) * ∑' k : ℕ, a^k / (k.factorial:ℝ) := by
      rw [← tsum_mul_left]; congr 1; ext k; ring
    _ = Real.exp (-1) * Real.exp a := by
      rw [(NormedSpace.expSeries_div_hasSum_exp a).tsum_eq, Real.exp_eq_exp_ℝ]
    _ = Real.exp (a-1) := by rw [← Real.exp_add]; congr 1; ring

lemma compound_poisson_product {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (g : X → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    (∫ z : ℕ × (ℕ → X), ∏ j ∈ Finset.range z.1, g (z.2 j)
      ∂(poissonMeasure 1).prod (Measure.infinitePi fun _ : ℕ => μ)) =
      Real.exp ((∫ x, g x ∂μ)-1) := by
  have hm : Measurable (fun z : ℕ × (ℕ → X) => ∏ j ∈ Finset.range z.1, g (z.2 j)) := by
    exact measurable_from_prod_countable_right (fun k => by
      change Measurable (fun y : ℕ → X => ∏ j ∈ Finset.range k, g (y j))
      fun_prop)
  have hi : Integrable (fun z : ℕ × (ℕ → X) => ∏ j ∈ Finset.range z.1, g (z.2 j))
      ((poissonMeasure 1).prod (Measure.infinitePi fun _ : ℕ => μ)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun _ _ => hg0 _)]
    exact Finset.prod_le_one₀ (fun _ _ => hg0 _) (fun _ _ => hg1 _)
  rw [integral_prod _ hi]
  simp_rw [iid_prefix_product μ g hg]
  exact poisson_one_pgf _
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def expNeg (x : ℝ≥0∞) : ℝ := (EReal.exp (-(x : EReal))).toReal

lemma expNeg_nonneg (x : ℝ≥0∞) : 0 ≤ expNeg x := ENNReal.toReal_nonneg
lemma expNeg_le_one (x : ℝ≥0∞) : expNeg x ≤ 1 := by
  have h : EReal.exp (-(x : EReal)) ≤ 1 :=
    EReal.exp_le_one_iff.mpr (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg x))
  exact (ENNReal.toReal_mono (by simp) h).trans_eq (by simp)
lemma expNeg_norm_le (x : ℝ≥0∞) : ‖expNeg x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (expNeg_nonneg x)]; exact expNeg_le_one x

lemma continuous_expNeg : Continuous expNeg := by
  unfold expNeg
  apply continuous_iff_continuousAt.mpr
  intro x
  have hne : EReal.exp (-(x : EReal)) ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt
      (EReal.exp_le_one_iff.mpr (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg x))) ENNReal.one_lt_top)
  exact (ENNReal.continuousAt_toReal hne).comp (f := fun y : ℝ≥0∞ => EReal.exp (-(y : EReal)))
    (ENNReal.continuous_exp.comp (continuous_coe_ennreal_ereal.neg)).continuousAt

@[simp] lemma expNeg_zero : expNeg 0 = 1 := by simp [expNeg]
@[simp] lemma expNeg_top : expNeg ∞ = 0 := by simp [expNeg]
lemma expNeg_ofReal {x : ℝ} (hx : 0 ≤ x) : expNeg (ENNReal.ofReal x) = Real.exp (-x) := by
  simp [expNeg, EReal.coe_ennreal_ofReal, hx, ← EReal.coe_neg, Real.exp_nonneg]
lemma expNeg_eq_of_ne_top {x : ℝ≥0∞} (hx : x ≠ ∞) : expNeg x = Real.exp (-x.toReal) := by
  rw [← ENNReal.ofReal_toReal hx, expNeg_ofReal ENNReal.toReal_nonneg]
  simp [ENNReal.toReal_ofReal]
lemma expNeg_add (x y : ℝ≥0∞) : expNeg (x+y) = expNeg x * expNeg y := by
  unfold expNeg
  rw [EReal.coe_ennreal_add, EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot x))
    (.inr (EReal.coe_ennreal_ne_bot y)), sub_eq_add_neg, EReal.exp_add, ENNReal.toReal_mul]
lemma expNeg_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) :
    expNeg (∑ i ∈ s, a i) = ∏ i ∈ s, expNeg (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, expNeg_add, ih]

lemma integral_expNeg_tsum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) :
    Tendsto (fun k => ∫ ω, expNeg (∑ n ∈ Finset.range k, f n ω) ∂μ) atTop
      (𝓝 (∫ ω, expNeg (∑' n, f n ω) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro k; exact (continuous_expNeg.measurable.comp (by fun_prop)).aestronglyMeasurable
  · exact integrable_const 1
  · intro k; exact Filter.Eventually.of_forall fun _ => expNeg_norm_le _
  · exact Filter.Eventually.of_forall fun ω =>
      continuous_expNeg.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum (fun n => f n ω))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma iid_prefix_product_varying {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (g : ℕ → X → ℝ) (hg : ∀ j, Measurable (g j)) (k : ℕ) :
    (∫ y, ∏ j ∈ Finset.range k, g j (y j) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∏ j ∈ Finset.range k, ∫ x, g j x ∂μ := by
  have hm : Measurable (fun y : Fin k → X => ∏ j : Fin k, g j (y j)) := by fun_prop
  have h := integral_map (μ := Measure.infinitePi (fun _ : ℕ => μ))
    (by fun_prop : Measurable (fun y : ℕ → X => fun i : Fin k => y i)).aemeasurable hm.aestronglyMeasurable
  rw [iid_prefix_map] at h
  have hfin : ∀ y : ℕ → X, (∏ j : Fin k, g j (y j)) = ∏ j ∈ Finset.range k, g j (y j) :=
    fun y => Fin.prod_univ_eq_prod_range (fun j => g j (y j)) k
  change (∫ y : Fin k → X, ∏ j : Fin k, g j (y j) ∂Measure.pi (fun _ => μ)) =
    (∫ y : ℕ → X, ∏ j : Fin k, g j (y j) ∂Measure.infinitePi (fun _ => μ)) at h
  simp_rw [hfin] at h
  rw [← h, integral_fintype_prod_eq_prod]
  exact Fin.prod_univ_eq_prod_range (fun j : ℕ => ∫ x, g j x ∂μ) k

abbrev PoissonBin (X : Type*) := ℕ × (ℕ → X)
def poissonBinLaw {X : Type*} [MeasurableSpace X] (μ : Measure X) : Measure (PoissonBin X) :=
  (poissonMeasure 1).prod (Measure.infinitePi fun _ : ℕ => μ)
def poissonSeriesLaw {X : Type*} [MeasurableSpace X] (μ : Measure X) : Measure (ℕ → PoissonBin X) :=
  Measure.infinitePi (fun _ : ℕ => poissonBinLaw μ)
def poissonBinSum {X : Type*} (F : X → ℝ≥0∞) (z : PoissonBin X) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range z.1, F (z.2 j)

instance poissonBinLaw_probability {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (poissonBinLaw μ) := by
  unfold poissonBinLaw; infer_instance
instance poissonSeriesLaw_probability {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (poissonSeriesLaw μ) := by
  unfold poissonSeriesLaw; infer_instance

lemma measurable_poissonBinSum {X : Type*} [MeasurableSpace X] {F : X → ℝ≥0∞}
    (hF : Measurable F) : Measurable (poissonBinSum F) := by
  apply measurable_from_prod_countable_right
  intro k
  change Measurable (fun y : ℕ → X => ∑ j ∈ Finset.range k, F (y j))
  fun_prop

lemma integrable_expNeg {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {F : X → ℝ≥0∞} (hF : Measurable F) :
    Integrable (fun x => expNeg (F x)) μ :=
  Integrable.of_bound (continuous_expNeg.measurable.comp hF).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _ => expNeg_norm_le _)

lemma poissonBin_laplace {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {F : X → ℝ≥0∞} (hF : Measurable F) :
    (∫ z, expNeg (poissonBinSum F z) ∂poissonBinLaw μ) =
      Real.exp (-(∫ x, 1-expNeg (F x) ∂μ)) := by
  simp only [poissonBinSum, expNeg_sum, poissonBinLaw]
  rw [compound_poisson_product μ (fun x => expNeg (F x)) (continuous_expNeg.measurable.comp hF)
    (fun _ => expNeg_nonneg _) (fun _ => expNeg_le_one _)]
  rw [integral_sub (integrable_const 1) (integrable_expNeg μ hF)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  congr 1; ring

lemma poisson_series_laplace {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (F : ℕ → X → ℝ≥0∞) (hF : ∀ n, Measurable (F n))
    {c : ℝ} (hc : HasSum (fun n => ∫ x, 1-expNeg (F n x) ∂μ) c) :
    (∫ ω, expNeg (∑' n : ℕ, poissonBinSum (F n) (ω n)) ∂poissonSeriesLaw μ) =
      Real.exp (-c) := by
  have hfinite : ∀ k : ℕ,
      (∫ ω, expNeg (∑ n ∈ Finset.range k, poissonBinSum (F n) (ω n)) ∂poissonSeriesLaw μ) =
      Real.exp (-(∑ n ∈ Finset.range k, ∫ x, 1-expNeg (F n x) ∂μ)) := by
    intro k
    simp only [expNeg_sum, poissonSeriesLaw]
    rw [iid_prefix_product_varying (poissonBinLaw μ)
      (fun n z => expNeg (poissonBinSum (F n) z))
      (fun n => continuous_expNeg.measurable.comp (measurable_poissonBinSum (hF n)))]
    simp_rw [poissonBin_laplace μ (hF _)]
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  have h₁ := integral_expNeg_tsum (poissonSeriesLaw μ)
    (fun n ω => poissonBinSum (F n) (ω n))
    (fun n => (measurable_poissonBinSum (hF n)).comp (measurable_pi_apply n))
  have h₂ := Real.continuous_exp.continuousAt.tendsto.comp hc.tendsto_sum_nat.neg
  exact tendsto_nhds_unique h₁ (h₂.congr (fun k => (hfinite k).symm))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma integral_exp_neg_zero (z : ℝ) :
    (∫ t in (0:ℝ)..z, Real.exp (-t)) = 1-Real.exp (-z) := by
  rw [intervalIntegral.integral_comp_neg, integral_exp]
  simp

lemma stable_tail_iff {m q t x : ℝ} (hm : 0 < m) (hq : 0 < q) (ht : 0 < t)
    (hx : 0 < x) : t < q*x^(-1/m) ↔ x < (q/t)^m := by
  have he : -1/m = -(m⁻¹) := by ring
  rw [he, Real.rpow_neg hx.le, ← div_eq_mul_inv]
  rw [lt_div_iff₀ (Real.rpow_pos_of_pos hx _)]
  rw [mul_comm t, ← lt_div_iff₀ ht]
  exact Real.rpow_inv_lt_iff_of_pos hx.le (div_nonneg hq.le ht.le) hm

lemma stable_tail_measure {m q t : ℝ} (hm : 0 < m) (hq : 0 < q) (ht : 0 < t) :
    (volume.restrict (Ioi (0:ℝ))) {x : ℝ | t < q*x^(-1/m)} =
      ENNReal.ofReal ((q/t)^m) := by
  rw [Measure.restrict_apply (measurableSet_lt measurable_const (by fun_prop))]
  have hs : {x : ℝ | t < q*x^(-1/m)} ∩ Ioi 0 = Ioo 0 ((q/t)^m) := by
    ext x
    constructor
    · rintro ⟨h, hx⟩; exact ⟨hx, (stable_tail_iff hm hq ht hx).mp h⟩
    · rintro ⟨hx,h⟩; exact ⟨(stable_tail_iff hm hq ht hx).mpr h, hx⟩
  rw [hs, Real.volume_Ioo]; simp

lemma stable_lintegral {m q : ℝ} (hm : 0 < m) (hm1 : m < 1) (hq : 0 ≤ q) :
    (∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (1-Real.exp (-q*x^(-1/m)))) =
      ENNReal.ofReal (Real.Gamma (1-m)*q^m) := by
  rcases hq.eq_or_lt with rfl | hq
  · simp [Real.zero_rpow hm.ne']
  have hf0 : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun x => q*x^(-1/m)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg hq.le (Real.rpow_nonneg hx.le _)
  have hc := lintegral_comp_eq_lintegral_meas_lt_mul (volume.restrict (Ioi (0:ℝ)))
    hf0 (by fun_prop) (g := fun t : ℝ => Real.exp (-t))
    (fun t _ => (by fun_prop : Continuous (fun t : ℝ => Real.exp (-t))).intervalIntegrable 0 t)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  simp_rw [integral_exp_neg_zero] at hc
  simp only [neg_mul]
  rw [hc]
  have hi : IntegrableOn (fun t : ℝ => t^(-m)*Real.exp (-t)) (Ioi 0) := by
    convert (Real.GammaIntegral_convergent (show 0 < 1-m by linarith)) using 1
    ext t
    rw [show 1-m-1 = -m by ring]
    exact mul_comm _ _
  have hval : (∫ t : ℝ in Ioi 0, t^(-m)*Real.exp (-t)) = Real.Gamma (1-m) := by
    convert Real.integral_rpow_mul_exp_neg_mul_Ioi (show 0 < 1-m by linarith) (show (0:ℝ)<1 by norm_num) using 1 <;> simp
  calc
    (∫⁻ t in Ioi (0:ℝ), (volume.restrict (Ioi 0)) {x : ℝ | t < q*x^(-1/m)} *
        ENNReal.ofReal (Real.exp (-t))) =
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (q^m*(t^(-m)*Real.exp (-t))) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [stable_tail_measure hm hq ht, ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg hq.le ht.le) m)]
        congr 1
        rw [Real.div_rpow hq.le ht.le, Real.rpow_neg ht.le]
        ring
    _ = ENNReal.ofReal (∫ t : ℝ in Ioi 0, q^m*(t^(-m)*Real.exp (-t))) := by
        symm
        apply ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) 
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg hq.le _)
          (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
    _ = ENNReal.ofReal (Real.Gamma (1-m)*q^m) := by
        rw [integral_const_mul, hval, mul_comm]

lemma stable_integrable {m q : ℝ} (hm : 0 < m) (hm1 : m < 1) (hq : 0 ≤ q) :
    IntegrableOn (fun x : ℝ => 1-Real.exp (-q*x^(-1/m))) (Ioi 0) := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun x => 1-Real.exp (-q*x^(-1/m))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (Real.rpow_nonneg hx.le _)
  refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal hn).mpr ?_⟩
  rw [stable_lintegral hm hm1 hq]; exact ENNReal.ofReal_lt_top

lemma stable_integral {m q : ℝ} (hm : 0 < m) (hm1 : m < 1) (hq : 0 ≤ q) :
    (∫ x in Ioi (0:ℝ), 1-Real.exp (-q*x^(-1/m))) = Real.Gamma (1-m)*q^m := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun x => 1-Real.exp (-q*x^(-1/m))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hq) (Real.rpow_nonneg hx.le _)))
  have h := ofReal_integral_eq_lintegral_ofReal (stable_integrable hm hm1 hq) hn
  rw [stable_lintegral hm hm1 hq] at h
  have hreal := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae hn),
    ENNReal.toReal_ofReal (show 0 ≤ Real.Gamma (1-m)*q^m by positivity)] using hreal
end MicroscopicJamming

 
 
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming
lemma unit_bins_union : (⋃ n : ℕ, Ioc (n:ℝ) ((n:ℝ)+1)) = Ioi (0:ℝ) := by
  have h : ¬ BddAbove (Set.range (fun n : ℕ => (n:ℝ))) := by
    rintro ⟨b,hb⟩
    obtain ⟨n,hn⟩ := exists_nat_gt b
    exact (not_lt_of_ge (hb (Set.mem_range_self n))) hn
  simpa [Order.succ_eq_add_one] using
    (iUnion_Ioc_map_succ_eq_Ioi (f := fun n : ℕ => (n:ℝ))
      (fun n => by simp) h)
lemma unit_bins_disjoint : Pairwise (fun n k : ℕ => Disjoint (Ioc (n:ℝ) ((n:ℝ)+1)) (Ioc (k:ℝ) ((k:ℝ)+1))) := by
  simpa only [Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    (show Monotone (fun n : ℕ => (n:ℝ)) from fun _ _ h => Nat.cast_le.mpr h).pairwise_disjoint_on_Ioc_succ
lemma integral_unit_shift (f : ℝ → ℝ) (n : ℕ) :
    (∫ u in Ico (0:ℝ) 1, f ((n:ℝ)+u)) = ∫ x in Ioc (n:ℝ) ((n:ℝ)+1), f x := by
  rw [restrict_Ico_eq_restrict_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_comp_add_left]
  simpa using (intervalIntegral.integral_of_le (show (n:ℝ) ≤ (n:ℝ)+1 by linarith)
    (f := f) (μ := volume))
lemma hasSum_integral_unit_shifts {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    HasSum (fun n : ℕ => ∫ u in Ico (0:ℝ) 1, f ((n:ℝ)+u)) (∫ x in Ioi 0, f x) := by
  simp_rw [integral_unit_shift]
  have h := hasSum_integral_iUnion (fun n : ℕ => measurableSet_Ioc) unit_bins_disjoint
    (by rwa [unit_bins_union])
  simpa only [unit_bins_union] using h
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def stableIntensity (m t : ℝ) (z : ℝ × ℝ≥0) : ℝ :=
  1-Real.exp (-t*z.1^(-1/m)*(z.2:ℝ))

lemma stableIntensity_nonneg {m t : ℝ} (ht : 0 ≤ t) {z : ℝ × ℝ≥0}
    (hz : 0 ≤ z.1) : 0 ≤ stableIntensity m t z := by
  unfold stableIntensity
  apply sub_nonneg.mpr
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (Real.rpow_nonneg hz _)) z.2.coe_nonneg

lemma stableIntensity_slice {m t : ℝ} (hm : 0 < m) (hm1 : m < 1) (ht : 0 ≤ t)
    (y : ℝ≥0) :
    (∫ x in Ioi (0:ℝ), stableIntensity m t (x,y)) =
      Real.Gamma (1-m)*t^m*(y:ℝ)^m := by
  have he : (fun x : ℝ => stableIntensity m t (x,y)) =
      (fun x : ℝ => 1-Real.exp (-(t*(y:ℝ))*x^(-1/m))) := by
    funext x; unfold stableIntensity; congr 2; ring
  rw [he, stable_integral hm hm1 (mul_nonneg ht y.coe_nonneg), Real.mul_rpow ht y.coe_nonneg]
  ring

lemma stableIntensity_integrable {m t : ℝ} (hm : 0 < m) (hm1 : m < 1) (ht : 0 ≤ t)
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hν : Integrable (fun y : ℝ≥0 => (y:ℝ)^m) ν) :
    Integrable (stableIntensity m t) ((volume.restrict (Ioi 0)).prod ν) := by
  apply (integrable_prod_iff' (by unfold stableIntensity; fun_prop)).mpr
  refine ⟨Filter.Eventually.of_forall (fun y => ?_), ?_⟩
  · have he : (fun x : ℝ => stableIntensity m t (x,y)) =
        (fun x : ℝ => 1-Real.exp (-(t*(y:ℝ))*x^(-1/m))) := by
      funext x; unfold stableIntensity; congr 2; ring
    rw [he]
    exact stable_integrable hm hm1 (mul_nonneg ht y.coe_nonneg)
  · have he : (fun y : ℝ≥0 => ∫ x in Ioi (0:ℝ), ‖stableIntensity m t (x,y)‖) =
        (fun y : ℝ≥0 => Real.Gamma (1-m)*t^m*(y:ℝ)^m) := by
      funext y
      rw [← stableIntensity_slice hm hm1 ht y]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact Real.norm_of_nonneg (stableIntensity_nonneg ht hx.le)
    rw [he]
    exact hν.const_mul _

lemma stableIntensity_integral {m t : ℝ} (hm : 0 < m) (hm1 : m < 1) (ht : 0 ≤ t)
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hν : Integrable (fun y : ℝ≥0 => (y:ℝ)^m) ν) :
    (∫ z, stableIntensity m t z ∂((volume.restrict (Ioi 0)).prod ν)) =
      Real.Gamma (1-m)*t^m*(∫ y : ℝ≥0, (y:ℝ)^m ∂ν) := by
  rw [integral_prod_symm _ (stableIntensity_integrable hm hm1 ht ν hν)]
  simp_rw [stableIntensity_slice hm hm1 ht]
  rw [integral_const_mul]

lemma stableIntensity_bins {m t : ℝ} (hm : 0 < m) (hm1 : m < 1) (ht : 0 ≤ t)
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hν : Integrable (fun y : ℝ≥0 => (y:ℝ)^m) ν) :
    HasSum (fun n : ℕ => ∫ u in Ico (0:ℝ) 1,
      ∫ y, stableIntensity m t ((n:ℝ)+u,y) ∂ν)
      (Real.Gamma (1-m)*t^m*(∫ y : ℝ≥0, (y:ℝ)^m ∂ν)) := by
  have hi := stableIntensity_integrable hm hm1 ht ν hν
  have h := hasSum_integral_unit_shifts hi.integral_prod_left
  rw [← integral_prod _ hi, stableIntensity_integral hm hm1 ht ν hν] at h
  exact h
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

instance cloudUniform_probability : IsProbabilityMeasure cloudUniform := by
  constructor
  simp [cloudUniform]

instance markedCloudLaw_probability (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (markedCloudLaw ν) := by
  unfold markedCloudLaw; infer_instance

lemma stableCloudSum_bins (m : ℝ) (ω : MarkedCloud) :
    stableCloudSum m ω = ∑' n : ℕ, poissonBinSum
      (fun z : ℝ × ℝ≥0 => ENNReal.ofReal (((n:ℝ)+z.1)^(-1/m)*(z.2:ℝ))) (ω n) := by
  unfold stableCloudSum poissonBinSum
  apply tsum_congr
  intro n
  rw [tsum_eq_sum (s := Finset.range (ω n).1)]
  · apply Finset.sum_congr rfl
    intro j hj
    simp [stableCloudWeight, Finset.mem_range.mp hj]
  · intro j hj
    have hj' : ¬j < (ω n).1 := by simpa only [Finset.mem_range] using hj
    simp [stableCloudWeight, hj']

lemma measurable_stableCloudSum (m : ℝ) : Measurable (stableCloudSum m) := by
  have he : stableCloudSum m = fun ω : MarkedCloud => ∑' n : ℕ, poissonBinSum
      (fun z : ℝ × ℝ≥0 => ENNReal.ofReal (((n:ℝ)+z.1)^(-1/m)*(z.2:ℝ))) (ω n) :=
    funext (stableCloudSum_bins m)
  rw [he]
  exact Measurable.tsum (fun n => (measurable_poissonBinSum (by fun_prop)).comp
    (measurable_pi_apply n))

lemma cloud_laplace_extended {m : ℝ} (hm : 0 < m) (hm1 : m < 1)
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hν : Integrable (fun y : ℝ≥0 => (y:ℝ)^m) ν)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, expNeg (ENNReal.ofReal t * stableCloudSum m ω) ∂markedCloudLaw ν) =
      Real.exp (-(Real.Gamma (1-m)*t^m*(∫ y : ℝ≥0, (y:ℝ)^m ∂ν))) := by
  let F : ℕ → (ℝ × ℝ≥0) → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal (t*(((n:ℝ)+z.1)^(-1/m)*(z.2:ℝ)))
  have hF : ∀ n, Measurable (F n) := by intro n; unfold F; fun_prop
  have he : ∀ n : ℕ, (∫ z, 1-expNeg (F n z) ∂cloudUniform.prod ν) =
      ∫ u in Ico (0:ℝ) 1, ∫ y, stableIntensity m t ((n:ℝ)+u,y) ∂ν := by
    intro n
    rw [integral_prod (fun z => 1-expNeg (F n z)) ((integrable_const 1).sub
      (integrable_expNeg (cloudUniform.prod ν) (hF n)))]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      have hn : 0 ≤ (n:ℝ)+u := add_nonneg (Nat.cast_nonneg _) hu.1
      dsimp only [F]
      rw [expNeg_ofReal (mul_nonneg ht
        (mul_nonneg (Real.rpow_nonneg hn _) y.coe_nonneg))]
      unfold stableIntensity
      congr 2; ring
  have hs : HasSum (fun n : ℕ => ∫ z, 1-expNeg (F n z) ∂cloudUniform.prod ν)
      (Real.Gamma (1-m)*t^m*(∫ y : ℝ≥0, (y:ℝ)^m ∂ν)) := by
    simp_rw [he]
    exact stableIntensity_bins hm hm1 ht ν hν
  have h := poisson_series_laplace (cloudUniform.prod ν) F hF hs
  have hv : ∀ ω : MarkedCloud, (∑' n, poissonBinSum (F n) (ω n)) =
      ENNReal.ofReal t * stableCloudSum m ω := by
    intro ω
    rw [stableCloudSum_bins, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro n
    unfold poissonBinSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact ENNReal.ofReal_mul ht
  simpa only [hv, poissonSeriesLaw, poissonBinLaw, markedCloudLaw] using h
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

abbrev PointCloud (A : Type*) := ℕ → PoissonBin (ℝ × A)

def pointCloudLaw {A : Type*} [MeasurableSpace A] (ν : Measure A) : Measure (PointCloud A) :=
  poissonSeriesLaw (cloudUniform.prod ν)

def pointCloudFunctional {A : Type*} (f : ℝ × A → ℝ≥0∞) (ω : PointCloud A) : ℝ≥0∞ :=
  ∑' n : ℕ, poissonBinSum (fun z : ℝ × A => f ((n:ℝ)+z.1,z.2)) (ω n)

def pointCloudTilt {A : Type*} [MeasurableSpace A] (m : ℝ) (c : A → ℝ)
    (ν : Measure A) : Measure A := ν.withDensity (fun a => ENNReal.ofReal ((c a)^m))

def PointCloudMarkingStatement : Prop :=
  ∀ (A : Type) (_ : MeasurableSpace A) (ν : Measure A), IsProbabilityMeasure ν →
  ∀ m : ℝ, 0 < m → m < 1 → ∀ c : A → ℝ,
    Measurable c → (∀ a, 0 < c a) → Integrable (fun a => (c a)^m) ν →
    (∫ a, (c a)^m ∂ν) = 1 →
    IsProbabilityMeasure (pointCloudTilt m c ν) ∧
    (∀ f : ℝ × A → ℝ≥0∞, Measurable f →
      (∫ ω, expNeg (pointCloudFunctional (fun z => f (z.1/(c z.2)^m,z.2)) ω) ∂pointCloudLaw ν) =
      (∫ ω, expNeg (pointCloudFunctional f ω) ∂pointCloudLaw (pointCloudTilt m c ν)))
end MicroscopicJamming

end

end OAI
