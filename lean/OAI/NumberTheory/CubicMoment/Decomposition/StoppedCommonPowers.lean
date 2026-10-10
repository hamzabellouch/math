import OAI.NumberTheory.CubicMoment.Estimates.LargeCommonSaving
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBoundedTail
import OAI.NumberTheory.CubicMoment.Estimates.CommonVarianceSum

namespace OAI

/-! Large common factors use the proved power bound only after their exact
zero mode is removed. No roughness or cancellation of quotient rows is assumed. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma rough_common_small_quotient {Z r : ℝ} (hr : 0 < r)
    (hcut : 65536*(Z/2)^(1/4:ℝ) ≤ Z) (hrcut : r < (Z/2)^(1/4:ℝ)) :
    65536 ≤ Z/r := by
  apply (le_div_iff₀ hr).mpr
  exact (mul_le_mul_of_nonneg_left hrcut.le (by norm_num)).trans hcut

lemma rough_common_large_outer {Z A D : ℝ} (hZ : 2 ≤ Z)
    (hD : 0 < D) (hDhi : D ≤ Z^(1/1000:ℝ)) (hA : Z^(3/2:ℝ) ≤ A) :
    (Z/2)^(3/4:ℝ) ≤ (A/D^2) := by
  have hZ1 : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
  calc
    _ ≤ Z^(3/4:ℝ)*(Z^(1/1000:ℝ))^2 :=
      mul_le_mul (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num))
        (pow_le_pow_left₀ hD.le hDhi 2) (sq_nonneg D) (by positivity)
    _ = Z^((3/4:ℝ)+(1/1000)*2) := by
      rw [←Real.rpow_mul_natCast hZp.le,←Real.rpow_add hZp]
      norm_num
    _ ≤ Z^(3/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
    _ ≤ A := hA

theorem bounded_large_common_nonzero (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A M u : ℝ), 2 ≤ Z → 0 < A → (Z/2)^(3/4:ℝ) ≤ A →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      ‖∑ k ∈ (commonRowFactors S).filter (fun k => (Z/2)^(1/4:ℝ) ≤ norm k),
        (commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k-
          commonGramZeroMode S (fun a => star (dispersionAmplitude β u a)) V A k)‖ ≤
        K*A^(2/3:ℝ)*Z^(5/3-1/32:ℝ)*M^2 := by
  obtain ⟨K,hK,hbound⟩ := large_common_nonzero_power
    (δ := 1/4) (by norm_num) (by norm_num) V hV hV'
  refine ⟨18*K,by positivity,?_⟩
  intro S β Z A M u hZ hA hZA hS hβ
  have hZp : 0 < Z := by linarith
  let v : Eisenstein → ℂ := fun a => star (dispersionAmplitude β u a)
  have hv (a : Eisenstein) (ha : a ∈ S) : ‖v a‖ ≤ M := by
    simpa only [v,norm_star,dispersionAmplitude_norm_squarefree (hS a ha).1
      (hS a ha).2.1] using hβ a ha
  have he := bounded_coefficient_energy S v hZp.le
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2.2⟩) hv
  have hb := hbound S v A (Z/2) hA (by linarith) (by convert hZA using 1; norm_num)
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.1,
      by nlinarith [(hS a ha).2.2.2]⟩)
  have hpow : (Z/2)^(2/3-(1/4)/8:ℝ) ≤ Z^(2/3-1/32:ℝ) := by
    norm_num
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  calc
    _ ≤ K*A^(2/3:ℝ)*(Z/2)^(2/3-(1/4)/8:ℝ)*∑ a ∈ S, ‖v a‖^2 := hb
    _ ≤ K*A^(2/3:ℝ)*Z^(2/3-1/32:ℝ)*(18*Z*M^2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) he
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    _ = (18*K)*A^(2/3:ℝ)*(Z^(2/3-1/32:ℝ)*Z)*M^2 := by ring
    _ = _ := by
      rw [show Z^(2/3-1/32:ℝ)*Z = Z^(5/3-1/32:ℝ) by
        nth_rw 2 [←Real.rpow_one Z]
        rw [←Real.rpow_add hZp]
        congr 1
        ring]

end CubicFirstMoment

end

end OAI
