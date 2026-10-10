import OAI.NumberTheory.CubicMoment.Estimates.SieveResidue
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialEulerTail

namespace OAI

/-! The ordinary radial Möbius density converges to the same literal
residue series used by the positive square-divisor sieve. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma radialEulerPartial_one_eq (D : ℝ) :
    metaplecticRadialEulerPartial 1 D =
      ((∑ a ∈ primaryElementBall D, moebiusResidueTerm a : ℝ):ℂ) := by
  unfold metaplecticRadialEulerPartial
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hp := (mem_primaryElementBall.mp ha).1
  simp only [isCoprime_one_left,ite_true,moebiusResidueTerm,hp]
  rw [Real.rpow_neg (norm_nonneg a),Real.rpow_two]
  push_cast
  ring

lemma moebiusResidue_partial_error :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, 0 < D →
      |(∑ a ∈ primaryElementBall D, moebiusResidueTerm a)-
        (∑' a : Eisenstein, moebiusResidueTerm a)| ≤ K*D^(-(1/2:ℝ)) := by
  let Z := ∑' a : Eisenstein, norm a^(-(3/2:ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg (fun a => Real.rpow_nonneg (norm_nonneg a) _)
  refine ⟨Z+1,by positivity,?_⟩
  intro D hD
  let f : Eisenstein → ℝ := fun a => if a ∈ primaryElementBall D then moebiusResidueTerm a else 0
  have hf : Summable f := summable_of_ne_finset_zero
    (s := primaryElementBall D) (fun a ha => by simp only [f,ite_eq_right ha])
  have hsum : (∑' a, f a) = ∑ a ∈ primaryElementBall D, moebiusResidueTerm a := by
    calc
      _ = ∑ a ∈ primaryElementBall D, f a := tsum_eq_sum
        (fun a ha => by simp only [f,ite_eq_right ha])
      _ = _ := Finset.sum_congr rfl (fun a ha => by simp only [f,ite_eq_left ha])
  have htail := (summable_eisenstein_norm_rpow (s := 2) (by norm_num)).indicator
    (fun a => D < norm a)
  have hb (a : Eisenstein) : |f a-moebiusResidueTerm a| ≤
      if D < norm a then norm a^(-(2:ℝ)) else 0 := by
    by_cases ha : a ∈ primaryElementBall D
    · simp only [f,ha,ite_true,sub_self,abs_zero]
      split_ifs
      · exact Real.rpow_nonneg (norm_nonneg a) _
      · exact le_rfl
    · by_cases hp : primary a
      · have hn : D < norm a := lt_of_not_ge (fun hn => ha (mem_primaryElementBall.mpr ⟨hp,hn⟩))
        simpa only [f,ha,ite_false,zero_sub,abs_neg,hn,ite_true] using moebiusResidueTerm_abs_le a
      · simp only [f,ite_eq_right ha,moebiusResidueTerm,ite_eq_right hp,sub_self,abs_zero]
        split_ifs
        · exact Real.rpow_nonneg (norm_nonneg a) _
        · exact le_rfl
  rw [←hsum,←hf.tsum_sub summable_moebiusResidueTerm]
  calc
    _ ≤ ∑' a, |f a-moebiusResidueTerm a| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hf.sub summable_moebiusResidueTerm).norm
    _ ≤ ∑' a : Eisenstein, if D < norm a then norm a^(-(2:ℝ)) else 0 :=
      Summable.tsum_le_tsum hb (hf.sub summable_moebiusResidueTerm).abs htail
    _ ≤ D^(-(1/2:ℝ))*Z := by
      simpa only [show (3/2:ℝ)-2 = -(1/2:ℝ) by norm_num] using
        eisenstein_norm_rpow_tail (s := 3/2) (t := 2) hD (by norm_num) (by norm_num)
    _ ≤ (Z+1)*D^(-(1/2:ℝ)) := by nlinarith [Real.rpow_nonneg hD.le (-(1/2:ℝ))]

lemma radialEulerPartial_one_error :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, 0 < D →
      ‖metaplecticRadialEulerPartial 1 D-
        ((∑' a : Eisenstein, moebiusResidueTerm a):ℝ)‖ ≤ K*D^(-(1/2:ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := moebiusResidue_partial_error
  refine ⟨K,hK,?_⟩
  intro D hD
  rw [radialEulerPartial_one_eq,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact hbound D hD

end CubicFirstMoment

end

end OAI
