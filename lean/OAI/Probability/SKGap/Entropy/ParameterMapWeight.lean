import Mathlib
import OAI.Probability.SKGap.Entropy.ExponentiallyRare

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
namespace SKGapCutoff.Regression

theorem ExponentialEmpiricalConcentration.parameter_map_weight
    {E F A : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F] [PseudoMetricSpace A]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (C : ∀ n, H n → A) (c : A) (hC : ExponentialConvergence ρ C c)
    (g : A → E → F) {L : ℝ≥0} (hg : LipschitzWith L (g c))
    (W : E → ℝ) (D : ℝ) (hD : 0 < D)
    (hgc : ∀ a x, dist (g a x) (g c x) ≤ dist a c * W x)
    (hrare : ExponentiallyRare ρ (fun n => {h | D ≤ (∑ i, W (X n h i))/(n:ℝ)})) :
    ExponentialEmpiricalConcentration ρ (fun n h i => g (C n h) (X n h i))
      (ν.map (g c)) := by
  have hxmap := hX.map (g c) hg
  intro f K hf B hB ε hε
  have hs : ExponentiallyRare ρ (fun n => {h | ε/2 ≤
      |(∑ i, f (g c (X n h i)))/(n:ℝ) - ∫ x, f x ∂ν.map (g c)|}) :=
    hxmap f K hf B hB (ε/2) (by positivity)
  let δ := ε/(2*((K:ℝ)*D+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  apply ((hs.union (hC δ hδ)).union hrare).mono
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro h hh
  by_cases hb : ε/2 ≤ |(∑ i, f (g c (X n h i)))/(n:ℝ) - ∫ x, f x ∂ν.map (g c)|
  · exact Or.inl (Or.inl hb)
  by_cases hcnot : δ ≤ dist (C n h) c
  · exact Or.inl (Or.inr hcnot)
  apply Or.inr
  by_contra hlarge
  have hcclose : dist (C n h) c < δ := lt_of_not_ge hcnot
  have hsmall : (∑ i, W (X n h i))/(n:ℝ) < D := lt_of_not_ge hlarge
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hdiff : |(∑ i, f (g (C n h) (X n h i)))/(n:ℝ) -
      (∑ i, f (g c (X n h i)))/(n:ℝ)| ≤ (K:ℝ)*dist (C n h) c*D := by
    rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hnR]
    calc
      |∑ i, (f (g (C n h) (X n h i))-f (g c (X n h i)))|/(n:ℝ) ≤
          (∑ i, |f (g (C n h) (X n h i))-f (g c (X n h i))|)/(n:ℝ) := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (∑ i : Fin n, (K:ℝ)*dist (C n h) c*W (X n h i))/(n:ℝ) := by
        gcongr with i
        exact (hf.dist_le_mul _ _).trans
          (by calc
            (K:ℝ)*dist (g (C n h) (X n h i)) (g c (X n h i)) ≤
                (K:ℝ)*(dist (C n h) c*W (X n h i)) :=
              mul_le_mul_of_nonneg_left (hgc _ _) K.coe_nonneg
            _ = (K:ℝ)*dist (C n h) c*W (X n h i) := by ring)
      _ = (K:ℝ)*dist (C n h) c*((∑ i, W (X n h i))/(n:ℝ)) := by
        rw [← Finset.mul_sum]; ring
      _ ≤ (K:ℝ)*dist (C n h) c*D :=
        mul_le_mul_of_nonneg_left hsmall.le (mul_nonneg K.coe_nonneg dist_nonneg)
  have hδbound : (K:ℝ)*δ*D ≤ ε/2 := by
    dsimp [δ]
    have hp : 0 < 2*((K:ℝ)*D+1) := by positivity
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    field_simp
    nlinarith [mul_nonneg K.coe_nonneg hD.le]
  have hstep : (K:ℝ)*dist (C n h) c*D ≤ ε/2 :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcclose.le K.coe_nonneg) hD.le).trans hδbound
  have ht := abs_add_le
    ((∑ i, f (g (C n h) (X n h i)))/(n:ℝ) - (∑ i, f (g c (X n h i)))/(n:ℝ))
    ((∑ i, f (g c (X n h i)))/(n:ℝ) - ∫ x, f x ∂ν.map (g c))
  rw [sub_add_sub_cancel] at ht
  have hb' := lt_of_not_ge hb
  exact (not_lt_of_ge hh) (ht.trans_lt (by linarith))

lemma average_lipschitz_metric_sq {E : Type*} [PseudoMetricSpace E]
    {n : ℕ} (hn : 0 < n) (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (v w : Fin n → E) :
    |((∑ i, f (v i))-(∑ i, f (w i)))/(n:ℝ)|^2 ≤
      (K:ℝ)^2 * (∑ i, (dist (v i) (w i))^2)/(n:ℝ) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  rw [sq_abs, div_pow, ← Finset.sum_sub_distrib]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => (1:ℝ)) (fun i => f (v i)-f (w i))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  have hsite (i : Fin n) : (f (v i)-f (w i))^2 ≤ (K:ℝ)^2*(dist (v i) (w i))^2 := by
    have h := hf.dist_le_mul (v i) (w i)
    rw [Real.dist_eq] at h
    have hs := mul_self_le_mul_self (abs_nonneg _) h
    simpa [← pow_two, mul_pow] using hs
  apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
  calc
    _ ≤ (n:ℝ) * ∑ i, (f (v i)-f (w i))^2 := hcs
    _ ≤ (n:ℝ) * ∑ i, (K:ℝ)^2*(dist (v i) (w i))^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hsite i)) hnR.le
    _ = _ := by rw [← Finset.mul_sum]; field_simp

theorem ExponentialEmpiricalConcentration.l2_stability
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X Y : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (hXY : ExponentialConvergence ρ
      (fun n h => (∑ i, (dist (X n h i) (Y n h i))^2)/(n:ℝ)) 0) :
    ExponentialEmpiricalConcentration ρ Y ν := by
  intro f K hf B hB ε hε
  have hs : ExponentiallyRare ρ (fun n => {h | ε/2 ≤
      |(∑ i, f (X n h i))/(n:ℝ) - ∫ x, f x ∂ν|}) :=
    hX f K hf B hB (ε/2) (by positivity)
  let δ := ε^2/(4*((K:ℝ)^2+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  apply (hs.union (hXY δ hδ)).mono
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro h hh
  by_cases hb : ε/2 ≤ |(∑ i, f (X n h i))/(n:ℝ) - ∫ x, f x ∂ν|
  · exact Or.inl hb
  apply Or.inr
  by_contra hbad
  have hclose : (∑ i, (dist (X n h i) (Y n h i))^2)/(n:ℝ) < δ := by
    change ¬δ ≤ dist ((∑ i, (dist (X n h i) (Y n h i))^2)/(n:ℝ)) 0 at hbad
    have hk := lt_of_not_ge hbad
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
      0 ≤ (∑ i, (dist (X n h i) (Y n h i))^2)/(n:ℝ))] using hk
  have hbound := average_lipschitz_metric_sq hn f hf (X n h) (Y n h)
  rw [mul_div_assoc] at hbound
  have hδbound : (K:ℝ)^2*δ < ε^2/4 := by
    dsimp [δ]
    have hp : 0 < 4*((K:ℝ)^2+1) := by positivity
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    field_simp
    nlinarith [sq_pos_of_pos hε]
  have hsmall : |(∑ i, f (X n h i))/(n:ℝ) - (∑ i, f (Y n h i))/(n:ℝ)| < ε/2 := by
    rw [← sub_div]
    have ht : |((∑ i, f (X n h i))-(∑ i, f (Y n h i)))/(n:ℝ)|^2 < ε^2/4 :=
      hbound.trans_lt ((mul_le_mul_of_nonneg_left hclose.le (sq_nonneg _)).trans_lt hδbound)
    nlinarith [abs_nonneg (((∑ i, f (X n h i))-(∑ i, f (Y n h i)))/(n:ℝ))]
  have ht := abs_add_le
    ((∑ i, f (Y n h i))/(n:ℝ) - (∑ i, f (X n h i))/(n:ℝ))
    ((∑ i, f (X n h i))/(n:ℝ) - ∫ x, f x ∂ν)
  rw [sub_add_sub_cancel, abs_sub_comm ((∑ i, f (Y n h i))/(n:ℝ))
    ((∑ i, f (X n h i))/(n:ℝ))] at ht
  have hb' := lt_of_not_ge hb
  exact (not_lt_of_ge hh) (ht.trans_lt (by linarith))

lemma ExponentialConvergence.dominated_zero
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X Y : ∀ n, H n → ℝ}
    (hX : ExponentialConvergence ρ X 0) {A : ∀ n, Set (H n)}
    (hA : ExponentiallyRare ρ A) (B : ℝ) (hB : 0 ≤ B)
    (hXY : ∀ᶠ n in atTop, ∀ h ∉ A n, |Y n h| ≤ B*|X n h|) :
    ExponentialConvergence ρ Y 0 := by
  intro ε hε
  let δ := ε/(B+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  apply (hA.union (hX δ hδ)).mono
  filter_upwards [hXY] with n hn
  intro h hh
  by_cases ha : h ∈ A n
  · exact Or.inl ha
  apply Or.inr
  by_contra hx
  change ¬δ ≤ dist (X n h) 0 at hx
  have hx' : |X n h| < δ := by simpa only [Real.dist_eq, sub_zero] using lt_of_not_ge hx
  have hy : ε ≤ |Y n h| := by simpa only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] using hh
  have hδB : B*δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < B+1)).mpr
    nlinarith
  exact (not_lt_of_ge hy) ((hn h ha).trans_lt
    ((mul_le_mul_of_nonneg_left hx'.le hB).trans_lt hδB))

theorem ExponentialConvergence.operator_omit
    {H E F : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {ρ : ∀ n, Measure (H n)} (A : ∀ n, H n → E n →L[ℝ] F n)
    (X : ∀ n, H n → E n)
    (hX : ExponentialConvergence ρ (fun n h => ‖X n h‖^2/(n:ℝ)) 0)
    (M : ℝ)
    (hA : ExponentiallyRare ρ (fun n => {h | M ≤ ‖A n h‖})) :
    ExponentialConvergence ρ (fun n h => ‖A n h (X n h)‖^2/(n:ℝ)) 0 := by
  apply hX.dominated_zero hA (M^2) (sq_nonneg _)
  refine Filter.Eventually.of_forall ?_
  intro n h hn
  have ha : ‖A n h‖ < M := lt_of_not_ge hn
  rw [abs_of_nonneg (by positivity : 0 ≤ ‖A n h (X n h)‖^2/(n:ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ ‖X n h‖^2/(n:ℝ)), ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    ‖A n h (X n h)‖^2 ≤ (M*‖X n h‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((A n h).le_opNorm (X n h) |>.trans
        (mul_le_mul_of_nonneg_right ha.le (norm_nonneg _))) 2
    _ = _ := by ring

lemma empirical_quadratic_expansion {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Fin n → ℝ) (c : ι → ℝ) :
    (∑ a, (∑ i, c i*f i a)^2)/(n:ℝ) =
      ∑ i, ∑ j, c i*((∑ a, f i a*f j a)/(n:ℝ))*c j := by
  calc
    _ = (∑ i, ∑ j, ∑ a, c i*f i a*(c j*f j a))/(n:ℝ) := by
      congr 1
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      simp_rw [Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      ring

lemma ExponentialEmpiricalConcentration.linear_combination_second_moment
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K B : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hB : ∀ i x, |f i x| ≤ B)
    (C : ∀ n, H n → ι → ℝ) (c : ι → ℝ) (hC : ExponentialConvergence ρ C c) :
    ExponentialConvergence ρ (fun n h => (∑ a, (∑ i, C n h i*f i (X n h a))^2)/(n:ℝ))
      (∑ i, ∑ j, c i*(∫ x, f i x*f j x ∂ν)*c j) := by
  have hc : Continuous (fun z : (ι → ι → ℝ) × (ι → ℝ) =>
      ∑ i, ∑ j, z.2 i*z.1 i j*z.2 j) := by fun_prop
  have hh := ((hX.gram f hf hB).prod hC).continuous_map hc.continuousAt
  simpa only [empirical_quadratic_expansion] using hh

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology

end

end OAI
