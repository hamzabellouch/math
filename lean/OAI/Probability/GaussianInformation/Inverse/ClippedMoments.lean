import Mathlib
import OAI.Probability.GaussianInformation.Inverse.ExponentBounds

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def integerWeight (l : ℤ) : ℝ≥0∞ := (1/2:ℝ≥0∞)^l.natAbs
lemma tsum_integerWeight : (∑' l : ℤ,integerWeight l)=3 := by
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  simp only [integerWeight,Int.natAbs_natCast,Int.natAbs_neg,
    show ∀ n : ℕ,((n:ℤ)+1).natAbs=n+1 by intro n; omega]
  rw [ENNReal.tsum_geometric,ENNReal.tsum_geometric_add_one]
  norm_num
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  norm_num

lemma tsum_prod_integerWeight : ∀ k : ℕ,(∑' l : Fin k → ℤ,∏ i,integerWeight (l i))=3^k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    let e : (Fin (k+1) → ℤ) ≃ ℤ × (Fin k → ℤ) :=
      { toFun := fun f => (f (Fin.last k),fun i => f i.castSucc)
        invFun := fun p => Fin.snoc p.2 p.1
        left_inv := by
          intro f
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
        right_inv := by intro p; simp }
    rw [← e.symm.tsum_eq]
    change (∑' p : ℤ × (Fin k → ℤ),∏ i,integerWeight (e.symm p i))=3^(k+1)
    have he : ∀ (p : ℤ × (Fin k → ℤ)),
        (∏ i,integerWeight (e.symm p i))=integerWeight p.1*∏ i,integerWeight (p.2 i) := by
      intro p
      simp only [e,Equiv.coe_fn_symm_mk,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
      ring
    simp_rw [he]
    rw [ENNReal.tsum_prod (f := fun (a : ℤ) (b : Fin k → ℤ) => integerWeight a*(∏ i,integerWeight (b i)))]
    simp_rw [ENNReal.tsum_mul_left,ih]
    rw [ENNReal.tsum_mul_right,tsum_integerWeight,pow_succ]
    ring
noncomputable def clippedInverse {d k : ℕ} (ε : ℝ) (f : Fin k → Ambient d) : ℝ≥0∞ :=
  ∏ i,((ENNReal.ofReal (clippedLength ε f i))⁻¹)^k
noncomputable def binInverseExponent {k : ℕ} (l : Fin k → ℤ) : ℝ :=
  Real.log 2*(k*k+k*(positiveSum l-negativeSum l))
noncomputable def baseExponent (d k : ℕ) : ℝ :=
  k*(k*Real.log 5+(((d:ℝ)-1)/2)*Real.log 3)+Real.log 2*k*k

lemma measurable_clippedInverse {d k : ℕ} (ε : ℝ) :
    Measurable (clippedInverse (d := d) (k := k) ε) := by
  apply Finset.measurable_prod
  intro i _
  exact ((measurable_gramSchmidt i).norm.max measurable_const).ennreal_ofReal.inv.pow_const _

lemma clipped_length_inv_le {d k : ℕ} {ε : ℝ} {f : Fin k → Ambient d} {l : Fin k → ℤ}
    (hl : InBins ε f l) (i : Fin k) :
    (ENNReal.ofReal (clippedLength ε f i))⁻¹ ≤
      ENNReal.ofReal (Real.exp (Real.log 2*((l i:ℝ)+1))) := by
  calc
    _ ≤ (ENNReal.ofReal (dyadicRadius (l i+1)))⁻¹ :=
      ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (hl i).1.le)
    _ = _ := by
      rw [← ENNReal.ofReal_inv_of_pos (dyadicRadius_pos _),dyadicRadius_eq_exp,← Real.exp_neg]
      congr 2
      push_cast
      ring

lemma clippedInverse_le_bin {d k : ℕ} {ε : ℝ} {f : Fin k → Ambient d} {l : Fin k → ℤ}
    (hl : InBins ε f l) :
    clippedInverse ε f ≤ ENNReal.ofReal (Real.exp (binInverseExponent l)) := by
  classical
  calc
    _ ≤ ∏ i,ENNReal.ofReal (Real.exp (Real.log 2*((l i:ℝ)+1)))^k :=
      Finset.prod_le_prod (fun i _ => pow_le_pow_left' (clipped_length_inv_le hl i) k)
    _ = ENNReal.ofReal (Real.exp (∑ i : Fin k,k*(Real.log 2*((l i:ℝ)+1)))) := by
      simp only [Real.exp_sum,Real.exp_nat_mul]
      rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]
      apply Finset.prod_congr rfl
      intro i _
      rw [ENNReal.ofReal_pow (by positivity)]
    _ = _ := by
      congr 2
      unfold binInverseExponent
      rw [← sum_bins]
      simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul]
      ring

lemma abs_bins_sum {k : ℕ} (l : Fin k → ℤ) :
    (∑ i,|(l i:ℝ)|)=positiveSum l+negativeSum l := by
  rw [positiveSum,negativeSum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (max_zero_add_max_neg_zero_eq_abs_self (l i:ℝ)).symm

lemma integerWeight_eq_exp (l : ℤ) : integerWeight l=
    ENNReal.ofReal (Real.exp (-Real.log 2*|(l:ℝ)|)) := by
  have ha : (l.natAbs:ℝ)=|(l:ℝ)| := by rw [← Int.cast_natCast (R := ℝ),Int.natCast_natAbs,Int.cast_abs]
  have hex : Real.exp (-Real.log 2)=1/2 := by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num
  have hhalf : (1/2:ℝ≥0∞)=ENNReal.ofReal (1/2:ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  rw [integerWeight,hhalf]
  rw [← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2)]
  congr 1
  rw [← hex,← Real.exp_nat_mul,ha]
  congr 1
  ring

lemma prod_integerWeight_eq_exp {k : ℕ} (l : Fin k → ℤ) :
    (∏ i,integerWeight (l i))=ENNReal.ofReal (Real.exp (-Real.log 2*(positiveSum l+negativeSum l))) := by
  simp_rw [integerWeight_eq_exp]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),← Real.exp_sum]
  congr 2
  rw [← Finset.mul_sum,abs_bins_sum]

lemma exponent_small_negative {k : ℕ} {α P N : ℝ} (hk : 3 ≤ k) (hα : 10*k ≤ α)
    (hP : 0 ≤ P) (hN : 0 ≤ N) (hNP : N ≤ 2*P) :
    k*(P-N)+(2*k-α)*P+2*k*N ≤ -(P+N) := by
  have hk' : (3:ℝ) ≤ k := by exact_mod_cast hk
  have h1 := mul_nonneg (sub_nonneg.mpr hα) hP
  have h2 := mul_nonneg (sub_nonneg.mpr hNP) (show 0 ≤ 7*(k:ℝ)-1 by linarith)
  have h3 := mul_nonneg (show 0 ≤ 5*(k:ℝ)-3 by linarith) hN
  nlinarith only [h1,h2,h3]

lemma exponent_large_negative {k : ℕ} {P N : ℝ} (hk : 3 ≤ k)
    (hP : 0 ≤ P) (hNP : 2*P ≤ N) : k*(P-N) ≤ -(P+N) := by
  have hk' : (3:ℝ) ≤ k := by exact_mod_cast hk
  have h1 := mul_nonneg (sub_nonneg.mpr hNP) (show 0 ≤ (k:ℝ)-1 by linarith)
  have h2 := mul_nonneg (show 0 ≤ (k:ℝ)-3 by linarith) hP
  nlinarith

lemma lintegral_bin_clipped_le {d k : ℕ} (hd : 1 ≤ d) (hk : 3 ≤ k)
    (hα : 10*(k:ℝ) ≤ ((d:ℝ)-1)/2) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BallBound ν) (ε : ℝ) (u : Ambient d) (l : Fin k → ℤ) :
    (∫⁻ z,(BinEvent ε u l).indicator (fun z => clippedInverse ε (translated u z)) z
      ∂Measure.pi (fun _ : Fin k => ν)) ≤
      ENNReal.ofReal (Real.exp (baseExponent d k))*∏ i,integerWeight (l i) := by
  have hfirst : (∫⁻ z,(BinEvent ε u l).indicator (fun z => clippedInverse ε (translated u z)) z
      ∂Measure.pi (fun _ : Fin k => ν)) ≤
      ENNReal.ofReal (Real.exp (binInverseExponent l))*(Measure.pi (fun _ : Fin k => ν)) (BinEvent ε u l) := by
    calc
      _ ≤ ∫⁻ z,(BinEvent ε u l).indicator (fun _ => ENNReal.ofReal (Real.exp (binInverseExponent l))) z
          ∂Measure.pi (fun _ : Fin k => ν) := by
        apply lintegral_mono
        intro z
        by_cases hz : z∈BinEvent ε u l
        · simp only [indicator_of_mem hz]
          exact clippedInverse_le_bin hz.2
        · simp only [indicator_of_notMem hz,le_refl]
      _ = _ := by rw [lintegral_indicator (measurableSet_binEvent ε u l),lintegral_const,Measure.restrict_apply_univ]
  have hP := positiveSum_nonneg l
  have hN := negativeSum_nonneg l
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [prod_integerWeight_eq_exp,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  by_cases hNP : negativeSum l ≤ 2*positiveSum l
  · calc
      _ ≤ ENNReal.ofReal (Real.exp (binInverseExponent l))*
          ENNReal.ofReal (Real.exp (totalExponent (d := d) l)) :=
        hfirst.trans (mul_le_mul_right (measure_binEvent_le hd ν hν ε u l) _)
      _ = ENNReal.ofReal (Real.exp (binInverseExponent l+totalExponent (d := d) l)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have he := mul_le_mul_of_nonneg_left (exponent_small_negative hk hα hP hN hNP) hlog
        unfold binInverseExponent totalExponent baseExponent
        nlinarith
  · have hbase : 0 ≤ k*(k*Real.log 5+(((d:ℝ)-1)/2)*Real.log 3) := by
      have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
      have ha : 0 ≤ ((d:ℝ)-1)/2 := by linarith
      have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
      positivity
    calc
      _ ≤ ENNReal.ofReal (Real.exp (binInverseExponent l))*1 :=
        hfirst.trans (mul_le_mul_right (prob_le_one (μ := Measure.pi (fun _ : Fin k => ν))) _)
      _ = ENNReal.ofReal (Real.exp (binInverseExponent l)) := mul_one _
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have he := mul_le_mul_of_nonneg_left (exponent_large_negative hk hP (le_of_not_ge hNP)) hlog
        unfold binInverseExponent baseExponent
        nlinarith

end AllScaleInverseVolume

end OAI
