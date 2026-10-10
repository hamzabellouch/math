import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.Entropy

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
noncomputable def finiteInformation {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (p : ι → α → ℝ) : ℝ := ∑ i,infoContribution μ (p i)

lemma infoContribution_le_negative_xlog_mass {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : α → ℝ)
    (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1) :
    infoContribution μ p ≤ -xlog (scoreMass μ p) := by
  have h : (∫ x,xlog (p x) ∂μ) ≤ 0 := integral_nonpos (fun x => xlog_nonpos (hp0 x) (hp1 x))
  dsimp [infoContribution]
  linarith

lemma finiteInformation_le_entropy_mass {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [Nonempty ι] (μ : Measure α) [IsFiniteMeasure μ] (p : ι → α → ℝ)
    (hp0 : ∀ i x,0 ≤ p i x) (hp1 : ∀ i x,p i x ≤ 1) :
    finiteInformation μ p ≤ (∑ i,scoreMass μ (p i))*Real.log (Fintype.card ι)-
      xlog (∑ i,scoreMass μ (p i)) := by
  calc
    _ ≤ ∑ i,-xlog (scoreMass μ (p i)) := Finset.sum_le_sum (fun i _ =>
      infoContribution_le_negative_xlog_mass μ _ (hp0 i) (hp1 i))
    _ = -(∑ i,xlog (scoreMass μ (p i))) := by simp
    _ ≤ _ := finite_entropy_mass_bound _ (fun i => scoreMass_nonneg μ _ (hp0 i))

lemma scoreMass_zero_of_sq_integral_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : α → ℝ) (hp : Measurable p)
    (hp0 : ∀ x,0 ≤ p x) (hp1 : ∀ x,p x ≤ 1) (h : (∫ x,(p x)^2 ∂μ) ≤ 0) :
    scoreMass μ p = 0 := by
  have hi : Integrable (fun x => (p x)^2) μ := by
    apply integrable_bounded_measurable μ _ (hp.pow_const 2) (C := 1)
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hp0 x,hp1 x]
  have hzero : (∫ x,(p x)^2 ∂μ) = 0 := le_antisymm h (integral_nonneg (fun _ => sq_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hzero
  have hpz : p =ᵐ[μ] 0 := by filter_upwards [hae] with x hx; simpa using hx
  simp [scoreMass,integral_congr_ae hpz]

lemma finiteInformation_good_bound {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [Nonempty ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ι → α → ℝ) (hp : ∀ i,Measurable (p i))
    (hp0 : ∀ i x,0 ≤ p i x) (hp1 : ∀ i x,p i x ≤ 1)
    (b : ι → ℝ) (hb0 : ∀ i,0 ≤ b i) (hb1 : ∑ i,b i = 1)
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r) (hr1 : r ≤ 1)
    (hbound : ∀ i,(∫ x,(p i x)^2 ∂μ) ≤ (A*(b i)^r)^2)
    (hmass : ∑ i,scoreMass μ (p i) ≤ 1) :
    finiteInformation μ p ≤ 2*Real.log A+(2-2*r)*Real.log (Fintype.card ι)-
      2*xlog (∑ i,scoreMass μ (p i)) := by
  let P := fun i => scoreMass μ (p i)
  have hP : ∀ i,0 ≤ P i := fun i => scoreMass_nonneg μ _ (hp0 i)
  have hz : ∀ i,b i = 0 → P i = 0 := by
    intro i hbi
    have h := hbound i
    simp only [hbi,Real.zero_rpow hr.ne',mul_zero,zero_pow (by norm_num : 2 ≠ 0)] at h
    exact scoreMass_zero_of_sq_integral_zero μ _ (hp i) (hp0 i) (hp1 i) h
  have hind (i : ι) : infoContribution μ (p i) ≤
      2*P i*Real.log A-2*r*(P i*Real.log (P i/b i))-(2-2*r)*xlog (P i) := by
    by_cases hPi : P i = 0
    · rw [infoContribution_zero_mass μ _ (hp i) (hp0 i) (hp1 i) hPi,hPi,xlog_zero]
      simp
    have hbi : 0 < b i := lt_of_le_of_ne (hb0 i) (Ne.symm (fun h => hPi (hz i h)))
    have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
    have hL : 0 < A*(b i)^r := mul_pos hAp (Real.rpow_pos_of_pos hbi r)
    have h := infoContribution_le_log_l2bound μ _ (hp i) (hp0 i) (hp1 i) hL (hbound i)
    rw [Real.log_mul hAp.ne' (Real.rpow_pos_of_pos hbi r).ne',Real.log_rpow hbi] at h
    rw [log_ratio_mul hbi.ne']
    dsimp only [xlog]
    change infoContribution μ (p i) ≤ 2*P i*(Real.log A+r*Real.log (b i)-Real.log (P i)) at h
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hind i)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul] at hsum
  have hls := finite_log_sum P b hP hb0 hb1 hz
  have hent := finite_entropy_mass_bound P hP
  have hc0 : 0 ≤ 2*r := by linarith
  have hc1 : 0 ≤ 2-2*r := by linarith
  have hc2 := mul_le_mul_of_nonneg_left hls hc0
  have hc3 := mul_le_mul_of_nonneg_left hent hc1
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlogN : 0 ≤ Real.log (Fintype.card ι) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := ι))
  have hmass' : ∑ i,P i ≤ 1 := hmass
  have h1 := mul_le_mul_of_nonneg_right hmass' hlogA
  have h2 := mul_le_mul_of_nonneg_right hmass' hlogN
  have h3 := mul_le_mul_of_nonneg_left h2 hc1
  change ∑ i,infoContribution μ (p i) ≤ _
  nlinarith

lemma binary_log_sum {a b P Q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : 0 < P) (hQ : 0 < Q) :
    xlog (a+b)-(a+b)*Real.log (P+Q) ≤
      xlog a-a*Real.log P+(xlog b-b*Real.log Q) := by
  have ht : 0 < P+Q := add_pos hP hQ
  have h := finite_log_sum (fun i : Fin 2 => if i = 0 then a else b)
    (fun i : Fin 2 => if i = 0 then P/(P+Q) else Q/(P+Q))
    (by intro i; split_ifs <;> assumption)
    (by intro i; split_ifs <;> positivity)
    (by simp [Fin.sum_univ_two]; field_simp)
    (by intro i; split_ifs
        · intro hz; exact ((div_pos hP ht).ne' hz).elim
        · intro hz; exact ((div_pos hQ ht).ne' hz).elim)
  simp only [Fin.sum_univ_two,ite_true,show (1 : Fin 2) ≠ 0 from by decide,ite_false] at h
  rw [log_ratio_mul (div_pos hP ht).ne',log_ratio_mul (div_pos hQ ht).ne',
    Real.log_div hP.ne' ht.ne',Real.log_div hQ.ne' ht.ne'] at h
  nlinarith

lemma infoContribution_add_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (p q : α → ℝ)
    (hp : Measurable p) (hq : Measurable q)
    (hp0 : ∀ x,0 ≤ p x) (hq0 : ∀ x,0 ≤ q x) (hpq1 : ∀ x,p x+q x ≤ 1) :
    infoContribution μ (fun x => p x+q x) ≤ infoContribution μ p+infoContribution μ q := by
  have hp1 : ∀ x,p x ≤ 1 := fun x => le_trans (le_add_of_nonneg_right (hq0 x)) (hpq1 x)
  have hq1 : ∀ x,q x ≤ 1 := fun x => le_trans (le_add_of_nonneg_left (hp0 x)) (hpq1 x)
  have hip := integrable_bounded_measurable μ p hp (C := 1) (fun x => by simpa [abs_of_nonneg (hp0 x)] using hp1 x)
  have hiq := integrable_bounded_measurable μ q hq (C := 1) (fun x => by simpa [abs_of_nonneg (hq0 x)] using hq1 x)
  have hP := scoreMass_nonneg μ p hp0
  have hQ := scoreMass_nonneg μ q hq0
  have hmass : scoreMass μ (fun x => p x+q x) = scoreMass μ p+scoreMass μ q := integral_add hip hiq
  by_cases hP0 : scoreMass μ p = 0
  · have hz : p =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hp0 hip).mp hP0
    have hxl : (fun x => xlog (p x+q x)) =ᵐ[μ] (fun x => xlog (q x)) := by
      filter_upwards [hz] with x hx
      simp [hx]
    rw [infoContribution_zero_mass μ p hp hp0 hp1 hP0]
    simp only [infoContribution,integral_congr_ae hxl,hmass,hP0,zero_add,le_refl]
  by_cases hQ0 : scoreMass μ q = 0
  · have hz : q =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hq0 hiq).mp hQ0
    have hxl : (fun x => xlog (p x+q x)) =ᵐ[μ] (fun x => xlog (p x)) := by
      filter_upwards [hz] with x hx
      simp [hx]
    rw [infoContribution_zero_mass μ q hq hq0 hq1 hQ0]
    simp only [infoContribution,integral_congr_ae hxl,hmass,hQ0,add_zero,le_refl]
  have hPp : 0 < scoreMass μ p := lt_of_le_of_ne hP (Ne.symm hP0)
  have hQp : 0 < scoreMass μ q := lt_of_le_of_ne hQ (Ne.symm hQ0)
  have hilp := integrable_xlog_probability μ p hp hp0 hp1
  have hilq := integrable_xlog_probability μ q hq hq0 hq1
  have hilpq := integrable_xlog_probability μ (fun x => p x+q x) (hp.add hq)
    (fun x => add_nonneg (hp0 x) (hq0 x)) hpq1
  have h := integral_mono (hilpq.sub ((hip.add hiq).mul_const (Real.log (scoreMass μ p+scoreMass μ q))))
    ((hilp.sub (hip.mul_const (Real.log (scoreMass μ p)))).add (hilq.sub (hiq.mul_const (Real.log (scoreMass μ q)))))
    (fun x => binary_log_sum (hp0 x) (hq0 x) hPp hQp)
  change (∫ x, xlog (p x+q x)-(p x+q x)*Real.log (scoreMass μ p+scoreMass μ q) ∂μ) ≤
    ∫ x, (xlog (p x)-p x*Real.log (scoreMass μ p))+(xlog (q x)-q x*Real.log (scoreMass μ q)) ∂μ at h
  have hel : (∫ x, xlog (p x+q x)-(p x+q x)*Real.log (scoreMass μ p+scoreMass μ q) ∂μ) =
      (∫ x,xlog (p x+q x) ∂μ)-(∫ x,(p x+q x)*Real.log (scoreMass μ p+scoreMass μ q) ∂μ) :=
    integral_sub hilpq ((hip.add hiq).mul_const (Real.log (scoreMass μ p+scoreMass μ q)))
  have her : (∫ x, (xlog (p x)-p x*Real.log (scoreMass μ p))+(xlog (q x)-q x*Real.log (scoreMass μ q)) ∂μ) =
      (∫ x,xlog (p x)-p x*Real.log (scoreMass μ p) ∂μ)+(∫ x,xlog (q x)-q x*Real.log (scoreMass μ q) ∂μ) :=
    integral_add (hilp.sub (hip.mul_const (Real.log (scoreMass μ p)))) (hilq.sub (hiq.mul_const (Real.log (scoreMass μ q))))
  rw [hel,her,integral_sub hilp (hip.mul_const (Real.log (scoreMass μ p))), integral_sub hilq (hiq.mul_const (Real.log (scoreMass μ q)))] at h
  simp only [integral_mul_const,integral_add hip hiq] at h
  simpa only [infoContribution,xlog,scoreMass,integral_add hip hiq] using h

lemma finiteInformation_good_bad_bound {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [Nonempty ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (p q : ι → α → ℝ) (hp : ∀ i,Measurable (p i)) (hq : ∀ i,Measurable (q i))
    (hp0 : ∀ i x,0 ≤ p i x) (hq0 : ∀ i x,0 ≤ q i x)
    (hsum : ∀ x,∑ i,(p i x+q i x) = 1)
    (b : ι → ℝ) (hb0 : ∀ i,0 ≤ b i) (hb1 : ∑ i,b i = 1)
    {A r δ : ℝ} (hA : 1 ≤ A) (hr : 0 < r) (hr1 : r ≤ 1)
    (hbound : ∀ i,(∫ x,(p i x)^2 ∂μ) ≤ (A*(b i)^r)^2)
    (hbad : ∑ i,scoreMass μ (q i) ≤ δ) :
    finiteInformation μ (fun i x => p i x+q i x) ≤
      2*Real.log A+(2-2*r+δ)*Real.log (Fintype.card ι)+3 := by
  have hpq1 : ∀ i x,p i x+q i x ≤ 1 := by
    intro i x
    rw [← hsum x]
    exact Finset.single_le_sum (fun j _ => add_nonneg (hp0 j x) (hq0 j x)) (Finset.mem_univ i)
  have hp1 : ∀ i x,p i x ≤ 1 := fun i x => le_trans (le_add_of_nonneg_right (hq0 i x)) (hpq1 i x)
  have hq1 : ∀ i x,q i x ≤ 1 := fun i x => le_trans (le_add_of_nonneg_left (hp0 i x)) (hpq1 i x)
  have hip : ∀ i,Integrable (p i) μ := fun i => integrable_bounded_measurable μ _ (hp i) (C := 1)
    (fun x => by simpa [abs_of_nonneg (hp0 i x)] using hp1 i x)
  have hiq : ∀ i,Integrable (q i) μ := fun i => integrable_bounded_measurable μ _ (hq i) (C := 1)
    (fun x => by simpa [abs_of_nonneg (hq0 i x)] using hq1 i x)
  have hmass : (∑ i,scoreMass μ (p i))+(∑ i,scoreMass μ (q i)) = 1 := by
    simp only [scoreMass,← integral_finsetSum _ (fun i _ => hip i),← integral_finsetSum _ (fun i _ => hiq i)]
    rw [← integral_add (integrable_finsetSum _ (fun i _ => hip i)) (integrable_finsetSum _ (fun i _ => hiq i))]
    simp_rw [← Finset.sum_add_distrib,hsum]
    simp
  have hPg := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => scoreMass_nonneg μ _ (hp0 i))
  have hPb := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => scoreMass_nonneg μ _ (hq0 i))
  have hgood := finiteInformation_good_bound μ p hp hp0 hp1 b hb0 hb1 hA hr hr1 hbound (by linarith)
  have hbad' := finiteInformation_le_entropy_mass μ q hq0 hq1
  have hlogN : 0 ≤ Real.log (Fintype.card ι) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := ι))
  have hb := mul_le_mul_of_nonneg_right hbad hlogN
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => infoContribution_add_le μ _ _ (hp i) (hq i) (hp0 i) (hq0 i) (hpq1 i))
  rw [Finset.sum_add_distrib] at h
  change finiteInformation μ (fun i x => p i x+q i x) ≤ finiteInformation μ p+finiteInformation μ q at h
  linarith [neg_xlog_le_one hPg,neg_xlog_le_one hPb]

lemma eLpNorm_eq_sqrt_integral_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : ∀ x,|f x| ≤ C) : eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x,(f x)^2 ∂μ)) := by
  have hmem : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ (fun x => by simpa using hC x))
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ∞) hmem]
  simp only [ENNReal.toReal_ofNat,Real.norm_eq_abs,Real.rpow_two, sq_abs,Real.sqrt_eq_rpow,one_div]

end RepeatedLocalization

end OAI
