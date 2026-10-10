import Mathlib
import OAI.Probability.SKRatio.Gaussian.ExponentialEvents

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real Set
namespace SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

def cdfRamp (a b x : ℝ) : ℝ := max 0 (min 1 ((b-x)/(b-a)))

lemma cdfRamp_bounds (a b x : ℝ) : 0≤cdfRamp a b x ∧ cdfRamp a b x≤1 := by
  unfold cdfRamp
  exact ⟨le_max_left ..,max_le (by norm_num) (min_le_left ..)⟩

lemma cdfRamp_lipschitz {a b : ℝ} (hab : a<b) :
    LipschitzWith ⟨(b-a)⁻¹,by positivity⟩ (cdfRamp a b) := by
  let K : ℝ≥0 := ⟨(b-a)⁻¹,by positivity⟩
  change LipschitzWith K (cdfRamp a b)
  have hlin : LipschitzWith K (fun x : ℝ => (b-x)/(b-a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((b-x)/(b-a)) ((b-y)/(b-a)) ≤ (b-a)⁻¹*dist x y
    simp only [Real.dist_eq]
    rw [←sub_div,show b-x-(b-y)=-(x-y) by ring,abs_div,abs_neg,
      abs_of_pos (sub_pos.mpr hab)]
    exact le_of_eq (by ring)
  unfold cdfRamp
  simpa only [max_self] using
    (LipschitzWith.const' 0 (K:=K)).max
      ((LipschitzWith.const' 1 (K:=K)).min hlin)

lemma cdfRamp_sandwich {a b : ℝ} (hab : a<b) (x : ℝ) :
    (Set.Iic a).indicator (fun _ : ℝ => (1:ℝ)) x≤cdfRamp a b x ∧
    cdfRamp a b x≤(Set.Iic b).indicator (fun _ : ℝ => (1:ℝ)) x := by
  constructor
  · by_cases hx : x≤a
    · rw [indicator_of_mem (show x∈Set.Iic a from hx)]
      unfold cdfRamp
      have hh : 1≤(b-x)/(b-a) := (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
      rw [min_eq_left hh,max_eq_right (by norm_num : (0:ℝ)≤1)]
    · rw [indicator_of_notMem (show x∉Set.Iic a from hx)]
      exact (cdfRamp_bounds ..).1
  · by_cases hx : x≤b
    · rw [indicator_of_mem (show x∈Set.Iic b from hx)]
      exact (cdfRamp_bounds ..).2
    · rw [indicator_of_notMem (show x∉Set.Iic b from hx)]
      have hh : (b-x)/(b-a)≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      unfold cdfRamp
      rw [min_eq_right (hh.trans (by norm_num)),max_eq_left hh]

lemma integrable_cdfRamp {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a<b) :
    Integrable (cdfRamp a b) μ :=
  (integrable_const (1:ℝ)).mono' (cdfRamp_lipschitz hab).continuous.aestronglyMeasurable
    (ae_of_all μ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (cdfRamp_bounds ..).1]; exact (cdfRamp_bounds ..).2))

lemma integral_cdfRamp_bounds {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a<b) :
    μ.real (Set.Iic a)≤∫ x, cdfRamp a b x ∂μ ∧ (∫ x, cdfRamp a b x ∂μ)≤μ.real (Set.Iic b) := by
  have h1 := integral_mono ((integrable_const (1:ℝ)).indicator measurableSet_Iic)
    (integrable_cdfRamp (μ:=μ) hab) (fun x => (cdfRamp_sandwich hab x).1)
  have h2 := integral_mono (integrable_cdfRamp (μ:=μ) hab)
    ((integrable_const (1:ℝ)).indicator measurableSet_Iic) (fun x => (cdfRamp_sandwich hab x).2)
  simpa only [integral_indicator measurableSet_Iic,integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using And.intro h1 h2

lemma continuous_measureReal_Iic (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Continuous (fun t : ℝ => μ.real (Set.Iic t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := ((integrable_const (1:ℝ) : Integrable (fun _ : ℝ => (1:ℝ)) μ).integrableOn).continuousOn_Iic_primitive_Iic (a₀:=t+1)
  have ht := h.continuousAt (Iic_mem_nhds (by linarith : t<t+1))
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using ht

theorem ExponentialEmpiricalConcentration.Iic
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    {μ : Measure ℝ} [IsFiniteMeasure μ] [NullSingletonClass μ]
    (hX : ExponentialEmpiricalConcentration ρ X μ) (t : ℝ) :
    ExponentialConvergence ρ
      (fun n ω => (∑ i, (Set.Iic t).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ))
      (μ.real (Set.Iic t)) := by
  intro ε hε
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousAt_iff.mp ((continuous_measureReal_Iic μ).continuousAt (x:=t)) (ε/4) (by positivity)
  let d := δ/2
  have hd : 0<d := by dsimp [d]; positivity
  have hlo := hnear (x:=t-d) (by simpa only [Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos hd] using (show d<δ by dsimp [d]; linarith))
  have hhi := hnear (x:=t+d) (by simpa only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hd] using (show d<δ by dsimp [d]; linarith))
  have hL := hX.average (cdfRamp (t-d) t) (cdfRamp_lipschitz (by linarith : t-d<t)) 1
    (fun x => by rw [abs_of_nonneg (cdfRamp_bounds ..).1]; exact (cdfRamp_bounds ..).2)
  have hU := hX.average (cdfRamp t (t+d)) (cdfRamp_lipschitz (by linarith : t<t+d)) 1
    (fun x => by rw [abs_of_nonneg (cdfRamp_bounds ..).1]; exact (cdfRamp_bounds ..).2)
  apply ((hL (ε/2) (by positivity)).union (hU (ε/2) (by positivity))).mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro ω hbad
  by_contra hh
  have heL : |(∑ i, cdfRamp (t-d) t (X n ω i))/(n:ℝ)-∫ x, cdfRamp (t-d) t x ∂μ|<ε/2 := by
    apply lt_of_not_ge
    intro he
    exact hh (Or.inl he)
  have heU : |(∑ i, cdfRamp t (t+d) (X n ω i))/(n:ℝ)-∫ x, cdfRamp t (t+d) x ∂μ|<ε/2 := by
    apply lt_of_not_ge
    intro he
    exact hh (Or.inr he)
  have hsumL : (∑ i, cdfRamp (t-d) t (X n ω i))/(n:ℝ)≤
      (∑ i, (Set.Iic t).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ) :=
    div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => (cdfRamp_sandwich (by linarith : t-d<t) _).2)) (Nat.cast_nonneg n)
  have hsumU : (∑ i, (Set.Iic t).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ)≤
      (∑ i, cdfRamp t (t+d) (X n ω i))/(n:ℝ) :=
    div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => (cdfRamp_sandwich (by linarith : t<t+d) _).1)) (Nat.cast_nonneg n)
  have hibL := (integral_cdfRamp_bounds (μ:=μ) (by linarith : t-d<t)).1
  have hibU := (integral_cdfRamp_bounds (μ:=μ) (by linarith : t<t+d)).2
  change ε≤|(∑ i, (Set.Iic t).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ) - μ.real (Set.Iic t)| at hbad
  rw [Real.dist_eq] at hlo hhi
  rcases abs_cases ((∑ i, (Set.Iic t).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ) - μ.real (Set.Iic t)) with ⟨he,_⟩ | ⟨he,_⟩
  · rw [he] at hbad
    linarith only [hε,hbad,hsumU,hibU,(abs_lt.mp heU).2,(abs_lt.mp hhi).2]
  · rw [he] at hbad
    linarith only [hε,hbad,hsumL,hibL,(abs_lt.mp heL).1,(abs_lt.mp hlo).1]

lemma ExponentialConvergence.congr_eventually
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {ρ : ∀ n, Measure (Ω n)}
    {E : Type*} [PseudoMetricSpace E] {X Y : ∀ n, Ω n → E} {x : E}
    (hX : ExponentialConvergence ρ X x) (he : ∀ᶠ n in atTop, X n=Y n) :
    ExponentialConvergence ρ Y x := by
  intro ε hε
  apply (hX ε hε).mono
  filter_upwards [he] with n hn
  rw [hn]

lemma exponentialConvergence_const
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (ρ : ∀ n, Measure (Ω n))
    {E : Type*} [PseudoMetricSpace E] (x : E) :
    ExponentialConvergence ρ (fun _ _ => x) x := by
  intro ε hε
  apply (exponentiallyRare_empty ρ).mono
  filter_upwards [] with n
  simp only [dist_self,not_le.mpr hε,Set.ofPred_false,Set.Subset.rfl]

lemma indicator_Ioc_sub {a b : ℝ} (hab : a≤b) (x : ℝ) :
    (Set.Ioc a b).indicator (fun _ : ℝ => (1:ℝ)) x=
      (Set.Iic b).indicator (fun _ : ℝ => (1:ℝ)) x-
        (Set.Iic a).indicator (fun _ : ℝ => (1:ℝ)) x := by
  by_cases hxa : x≤a
  · have hxb := hxa.trans hab
    simp [Set.indicator,Set.mem_Ioc,Set.mem_Iic,hxa,hxb,not_lt_of_ge hxa]
  · by_cases hxb : x≤b <;>
      simp [Set.indicator,Set.mem_Ioc,Set.mem_Iic,hxa,hxb,lt_of_not_ge hxa]

lemma ExponentialEmpiricalConcentration.Ioc
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    {μ : Measure ℝ} [IsFiniteMeasure μ] [NullSingletonClass μ]
    (hX : ExponentialEmpiricalConcentration ρ X μ) {a b : ℝ} (hab : a≤b) :
    ExponentialConvergence ρ
      (fun n ω => (∑ i, (Set.Ioc a b).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ))
      (μ.real (Set.Ioc a b)) := by
  have hm : μ.real (Set.Ioc a b)=μ.real (Set.Iic b)-μ.real (Set.Iic a) := by
    rw [←integral_indicator_one measurableSet_Ioc]
    change (∫ x, (Set.Ioc a b).indicator (fun _ : ℝ => (1:ℝ)) x ∂μ)=_
    simp_rw [indicator_Ioc_sub hab]
    rw [integral_sub ((integrable_const (1:ℝ)).indicator measurableSet_Iic)
      ((integrable_const (1:ℝ)).indicator measurableSet_Iic)]
    simp only [integral_indicator measurableSet_Iic,integral_const,
      smul_eq_mul,mul_one,measureReal_restrict_apply_univ]
  rw [hm]
  convert! ((hX.Iic b).prod (hX.Iic a)).continuous_map (f:=fun q : ℝ×ℝ => q.1-q.2) (by fun_prop) using 1
  funext n ω
  simp only [indicator_Ioc_sub hab,Finset.sum_sub_distrib,sub_div]

lemma ExponentialEmpiricalConcentration.Ioi
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hX : ExponentialEmpiricalConcentration ρ X μ) (a : ℝ) :
    ExponentialConvergence ρ
      (fun n ω => (∑ i, (Set.Ioi a).indicator (fun _ : ℝ => (1:ℝ)) (X n ω i))/(n:ℝ))
      (μ.real (Set.Ioi a)) := by
  have hm : μ.real (Set.Ioi a)=1-μ.real (Set.Iic a) := by
    rw [←Set.compl_Iic,measureReal_compl measurableSet_Iic,probReal_univ]
  rw [hm]
  apply ((hX.Iic a).continuous_map (f:=fun x : ℝ => 1-x) (by fun_prop)).congr_eventually
  filter_upwards [eventually_gt_atTop 0] with n hn
  funext ω
  have hi (x : ℝ) : (Set.Ioi a).indicator (fun _ : ℝ => (1:ℝ)) x=
      1-(Set.Iic a).indicator (fun _ : ℝ => (1:ℝ)) x := by
    by_cases hx : x≤a
    · simp [Set.indicator,hx,not_lt_of_ge hx]
    · simp [Set.indicator,hx,lt_of_not_ge hx]
  simp only [hi,Finset.sum_sub_distrib,sub_div,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one,div_self (show (n:ℝ)≠0 from Nat.cast_ne_zero.mpr hn.ne')]

end SKRatioClock.Regression

end

end OAI
