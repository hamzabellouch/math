import OAI.NumberTheory.CubicMoment.Transform.MetaplecticHeight
import OAI.NumberTheory.CubicGram.Mobius
import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebiusFinite
import OAI.NumberTheory.CubicGram.CubicOperator

namespace OAI

/-! The actual finite Möbius density has a uniform quantitative tail.
A convergent Eisenstein norm series supplies the only estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticRadialEulerPartial (r : Eisenstein) (C : ℝ) : ℂ :=
  ∑ c ∈ primaryElementBall C, if IsCoprime r c then
    (idealMoebius c:ℂ)*((norm c^(-2:ℝ):ℝ):ℂ) else 0

lemma metaplecticRadialEulerPartial_tail :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r C D, 0 < C → C ≤ D →
      ‖metaplecticRadialEulerPartial r D-metaplecticRadialEulerPartial r C‖ ≤
        K*C^(-(99/100):ℝ) := by
  let K := ∑' c : Eisenstein, norm c^(-(101/100):ℝ)
  have hK : 0 ≤ K := tsum_nonneg (fun c => Real.rpow_nonneg (norm_nonneg c) _)
  refine ⟨K,hK,?_⟩
  intro r C D hC hCD
  let S := primaryElementBall D \ primaryElementBall C
  have hsub : primaryElementBall C ⊆ primaryElementBall D := by
    intro c hc
    exact mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hc).1,
      (mem_primaryElementBall.mp hc).2.trans hCD⟩
  let g : Eisenstein → ℂ := fun c => if IsCoprime r c then
    (idealMoebius c:ℂ)*((norm c^(-2:ℝ):ℝ):ℂ) else 0
  have he : metaplecticRadialEulerPartial r D-metaplecticRadialEulerPartial r C =
      ∑ c ∈ S,g c := by
    exact (Finset.sum_sdiff_eq_sub (f := g) hsub).symm
  rw [he]
  have hpoint (c : Eisenstein) (hc : c ∈ S) :
      ‖g c‖ ≤ C^(-(99/100):ℝ)*norm c^(-(101/100):ℝ) := by
    have hm := Finset.mem_sdiff.mp hc
    obtain ⟨hcp,hcn⟩ := mem_primaryElementBall.mp hm.1
    have hnorm : C < norm c := by
      by_contra hn
      exact hm.2 (mem_primaryElementBall.mpr ⟨hcp,le_of_not_gt hn⟩)
    have hbase : ‖g c‖ ≤ norm c^(-2:ℝ) := by
      dsimp [g]
      split_ifs
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg c) _)]
        exact mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg c) _)
          (norm_idealMoebius_le_one c)
      · simpa only [norm_zero] using Real.rpow_nonneg (norm_nonneg c) (-2:ℝ)
    apply hbase.trans
    simpa only [show (101/100:ℝ)-2 = -(99/100:ℝ) by norm_num] using
      norm_rpow_tail_pointwise hC (show (101/100:ℝ) < 2 by norm_num) hnorm
  calc
    _ ≤ ∑ c ∈ S, C^(-(99/100):ℝ)*norm c^(-(101/100):ℝ) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hpoint)
    _ = C^(-(99/100):ℝ)*(∑ c ∈ S,norm c^(-(101/100):ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C^(-(99/100):ℝ)*K := mul_le_mul_of_nonneg_left
      ((summable_eisenstein_norm_rpow (show (1:ℝ) < 101/100 by norm_num)).sum_le_tsum S
        (fun c _ => Real.rpow_nonneg (norm_nonneg c) _)) (by positivity)
    _ = _ := mul_comm _ _

end CubicFirstMoment

end

end OAI
