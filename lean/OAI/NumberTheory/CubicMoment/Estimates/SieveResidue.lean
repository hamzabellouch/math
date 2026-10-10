import OAI.NumberTheory.CubicMoment.Estimates.SieveMobius
import OAI.NumberTheory.CubicMoment.Estimates.NormSeries

namespace OAI

/-!
# The residue sum after squarefree majorization

The actual collected coefficients agree with Möbius below the truncation.
Their uniformly convergent norm series therefore differs from the true
Möbius residue by `O(D⁻¹ᐟ²)`.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreeSieveResidueTerm (D : ℝ) (e : Eisenstein) : ℝ :=
  if primary e then
    collectedSquarefreeSieveCoefficient (squarefreeDivisorTruncation D) e / (norm e)^2
  else 0

def moebiusResidueTerm (e : Eisenstein) : ℝ :=
  if primary e then (idealMoebius e : ℝ)/(norm e)^2 else 0

lemma squarefreeTruncation_spec (D : ℝ) :
    ∀ c ∈ squarefreeDivisorTruncation D, primary c ∧ Squarefree c := by
  intro c hc
  exact ⟨(mem_squarefreeDivisorTruncation.mp hc).1,(mem_squarefreeDivisorTruncation.mp hc).2.1⟩

lemma squarefreeSieveCoefficient_zero {D : ℝ} {e : Eisenstein} (hs : ¬Squarefree e) :
    collectedSquarefreeSieveCoefficient (squarefreeDivisorTruncation D) e = 0 := by
  by_contra hn
  obtain ⟨a,ha,b,hb,hab⟩ := collectedSieveCoefficient_nonzero _ e hn
  apply hs
  rw [← hab]
  exact primarySquarefreeJoin_squarefree (squarefreeTruncation_spec D a ha).1
    (squarefreeTruncation_spec D b hb).1

lemma sieveResidueTerm_eq_of_norm_le {D : ℝ} {e : Eisenstein} (h : norm e ≤ D) :
    squarefreeSieveResidueTerm D e = moebiusResidueTerm e := by
  by_cases hp : primary e
  · simp only [squarefreeSieveResidueTerm,moebiusResidueTerm,hp,ite_true]
    by_cases hs : Squarefree e
    · rw [squarefreeSieveCoefficient_small hp hs h]
    · rw [squarefreeSieveCoefficient_zero hs]
      have hm : idealMoebius e = 0 := by simp [idealMoebius,UniqueFactorizationMonoid.moebius,hs]
      rw [hm]
      simp
  · simp [squarefreeSieveResidueTerm,moebiusResidueTerm,hp]

/-- Uniform pointwise majorant with the entire discrepancy beyond `D`. -/
theorem sieveResidue_difference_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, ∀ e : Eisenstein,
      |squarefreeSieveResidueTerm D e - moebiusResidueTerm e| ≤
        if D < norm e then K*norm e^(-(7/4:ℝ)) else 0 := by
  obtain ⟨K,hK,hbound⟩ := collectedSieveCoefficient_small_power (ε := (1/4:ℝ)) (by norm_num)
  refine ⟨K+1,by linarith,?_⟩
  intro D e
  by_cases ht : D < norm e
  · rw [ite_eq_left ht]
    by_cases hp : primary e
    · have hn : 0 < norm e := norm_pos_of_ne_zero (primary_ne_zero hp)
      have hpow : 1 ≤ norm e^(1/4:ℝ) :=
        Real.one_le_rpow (one_le_norm (primary_ne_zero hp)) (by norm_num)
      have hm := abs_idealMoebius_real_le_one e
      have hc := hbound (squarefreeDivisorTruncation D) (squarefreeTruncation_spec D) e
      have heq : norm e^(1/4:ℝ)/(norm e)^2 = norm e^(-(7/4:ℝ)) := by
        rw [← Real.rpow_natCast (norm e) 2,← Real.rpow_sub hn]
        congr 1
        norm_num
      simp only [squarefreeSieveResidueTerm,moebiusResidueTerm,hp,ite_true,← sub_div,
        abs_div,abs_of_nonneg (sq_nonneg (norm e))]
      calc
        _ ≤ (|collectedSquarefreeSieveCoefficient (squarefreeDivisorTruncation D) e|+
            |(idealMoebius e : ℝ)|)/(norm e)^2 :=
          div_le_div_of_nonneg_right (abs_sub _ _) (sq_nonneg _)
        _ ≤ ((K+1)*norm e^(1/4:ℝ))/(norm e)^2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          nlinarith
        _ = _ := by rw [mul_div_assoc,heq]
    · simp only [squarefreeSieveResidueTerm,moebiusResidueTerm,hp,ite_false,
        sub_self,abs_zero]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg e) _)
  · rw [ite_eq_right ht,sieveResidueTerm_eq_of_norm_le (le_of_not_gt ht)]
    simp

lemma moebiusResidueTerm_abs_le (e : Eisenstein) :
    |moebiusResidueTerm e| ≤ norm e^(-(2:ℝ)) := by
  by_cases hp : primary e
  · have hn := norm_pos_of_ne_zero (primary_ne_zero hp)
    simp only [moebiusResidueTerm,hp,ite_true,abs_div,abs_of_nonneg (sq_nonneg (norm e))]
    calc
      _ ≤ 1/(norm e)^2 :=
        div_le_div_of_nonneg_right (abs_idealMoebius_real_le_one e) (sq_nonneg _)
      _ = _ := by rw [Real.rpow_neg hn.le,Real.rpow_two,one_div]
  · simp only [moebiusResidueTerm,hp,ite_false,abs_zero]
    exact Real.rpow_nonneg (norm_nonneg e) _

lemma summable_moebiusResidueTerm : Summable moebiusResidueTerm := by
  apply (summable_eisenstein_norm_rpow (s := 2) (by norm_num)).of_norm_bounded
  intro e
  simpa only [Real.norm_eq_abs] using moebiusResidueTerm_abs_le e

lemma summable_sieveResidue_difference (D : ℝ) :
    Summable (fun e => squarefreeSieveResidueTerm D e - moebiusResidueTerm e) := by
  obtain ⟨K,_,hK⟩ := sieveResidue_difference_bound
  apply ((summable_eisenstein_norm_rpow (s := (7/4:ℝ)) (by norm_num)).mul_left K).of_norm_bounded
  intro e
  rw [Real.norm_eq_abs]
  apply (hK D e).trans
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (le_of_lt ‹0 < K›) (Real.rpow_nonneg (norm_nonneg e) _)

lemma summable_squarefreeSieveResidueTerm (D : ℝ) :
    Summable (squarefreeSieveResidueTerm D) := by
  have h := (summable_sieveResidue_difference D).add summable_moebiusResidueTerm
  simpa only [sub_add_cancel] using h

/-- The sieve residue has a uniform square-root truncation error. -/
theorem sieveResidue_difference_le :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 0 < D →
      |(∑' e : Eisenstein, squarefreeSieveResidueTerm D e) -
        (∑' e : Eisenstein, moebiusResidueTerm e)| ≤ C*D^(-(1/2:ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := sieveResidue_difference_bound
  let Z := ∑' e : Eisenstein, norm e^(-(5/4:ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg (fun e => Real.rpow_nonneg (norm_nonneg e) _)
  refine ⟨K*Z+1,by nlinarith,?_⟩
  intro D hD
  have htail : Summable (fun e : Eisenstein =>
      if D < norm e then norm e^(-(7/4:ℝ)) else 0) :=
    (summable_eisenstein_norm_rpow (s := (7/4:ℝ)) (by norm_num)).indicator _
  have hdiff := summable_sieveResidue_difference D
  have htailbound := eisenstein_norm_rpow_tail (s := (5/4:ℝ)) (t := (7/4:ℝ)) hD
    (by norm_num) (by norm_num)
  rw [show (5/4:ℝ)-7/4 = -(1/2:ℝ) by norm_num] at htailbound
  rw [← (summable_squarefreeSieveResidueTerm D).tsum_sub summable_moebiusResidueTerm]
  calc
    _ ≤ ∑' e : Eisenstein, |squarefreeSieveResidueTerm D e - moebiusResidueTerm e| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hdiff.norm
    _ ≤ ∑' e : Eisenstein, K*(if D < norm e then norm e^(-(7/4:ℝ)) else 0) := by
      apply Summable.tsum_le_tsum _ hdiff.norm (htail.mul_left K)
      intro e
      simpa only [mul_ite,mul_zero,Real.norm_eq_abs] using hbound D e
    _ = K*(∑' e : Eisenstein, if D < norm e then norm e^(-(7/4:ℝ)) else 0) := tsum_mul_left
    _ ≤ K*(D^(-(1/2:ℝ))*Z) := mul_le_mul_of_nonneg_left htailbound hK.le
    _ ≤ (K*Z+1)*D^(-(1/2:ℝ)) := by
      have hp := Real.rpow_nonneg hD.le (-(1/2:ℝ))
      nlinarith

/-- In particular, the precise series replacing the sieve coefficients
has an error of order `D⁻¹ᐟ²`; it is not an assumed residue identity. -/
theorem sieveResidue_difference_isBigO :
    (fun D : ℝ => (∑' e : Eisenstein, squarefreeSieveResidueTerm D e) -
      (∑' e : Eisenstein, moebiusResidueTerm e)) =O[Filter.atTop]
      (fun D : ℝ => D^(-(1/2:ℝ))) := by
  obtain ⟨C,hC,hbound⟩ := sieveResidue_difference_le
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with D hD
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (Real.rpow_nonneg hD.le _)]
  exact hbound D hD

end CubicFirstMoment

end

end OAI
