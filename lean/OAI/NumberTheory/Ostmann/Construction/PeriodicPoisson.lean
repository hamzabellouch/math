import OAI.NumberTheory.Ostmann.Construction.Poisson

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
open FourierTransform Filter Asymptotics
namespace Ostmann.Construction

def schwartzTranslate (f : SchwartzMap ℝ ℂ) (x : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun y : ℝ => x+y)
    (by fun_prop) (IsometryEquiv.addLeft x).isometry.antilipschitzWith f

@[simp] theorem schwartzTranslate_apply (f : SchwartzMap ℝ ℂ) (x y : ℝ) :
    schwartzTranslate f x y = f (x+y) := rfl

theorem schwartz_int_norm_summable (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => ‖f (n : ℝ)‖) := by
  apply summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ)<2))
  exact ((f.isBigO_cocompact_rpow (-2)).norm_left).comp_tendsto Int.tendsto_coe_cofinite

theorem schwartz_shift_norm_summable (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    Summable (fun n : ℤ => ‖f (x+n)‖) := by
  exact schwartz_int_norm_summable (schwartzTranslate f x)

def periodicResidueTest (Q : ℕ) [NeZero Q] (F : Fin Q → ℂ) (n : ℤ) : ℂ :=
  F ((Int.divModEquiv Q n).2)

theorem periodic_poisson_zero_frequency (Q : ℕ) [NeZero Q]
    (f : SchwartzMap ℝ ℂ) (F : Fin Q → ℂ)
    (hband : ∀ n : ℤ, n ≠ 0 → 𝓕 f (n : ℝ) = 0) :
    (∑' n : ℤ, periodicResidueTest Q F n * f ((n : ℝ)/Q)) =
      (∑ r, F r) * 𝓕 f 0 := by
  let e : (Fin Q × ℤ) ≃ ℤ := (Equiv.prodComm (Fin Q) ℤ).trans (Int.divModEquiv Q).symm
  let g : Fin Q × ℤ → ℂ := fun z => F z.1 * f ((z.1 : ℝ)/Q + z.2)
  have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne Q)
  have hcomp (z : Fin Q × ℤ) :
      periodicResidueTest Q F (e z) * f ((e z : ℤ) / (Q : ℝ)) = g z := by
    rcases z with ⟨r,k⟩
    have hr : (Int.divModEquiv Q (e (r,k))).2 = r := by
      exact congrArg Prod.snd ((Int.divModEquiv Q).apply_symm_apply (k,r))
    rw [periodicResidueTest, hr]
    congr 1
    change f (((k * (Q : ℤ) + r : ℤ) : ℝ) / Q) = f ((r : ℝ)/Q+k)
    congr 1
    push_cast
    field_simp
    ring
  have hfib (r : Fin Q) : Summable (fun k : ℤ => ‖g (r,k)‖) := by
    simpa only [g, norm_mul] using (schwartz_shift_norm_summable f ((r : ℝ)/Q)).mul_left ‖F r‖
  have hnorm : Summable (fun z : Fin Q × ℤ => ‖g z‖) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
      ⟨hfib, (hasSum_fintype _).summable⟩
  have hg : Summable g := hnorm.of_norm
  calc
    (∑' n : ℤ, periodicResidueTest Q F n * f ((n : ℝ)/Q)) =
        ∑' z : Fin Q × ℤ, g z := by
      rw [← e.tsum_eq (fun n : ℤ => periodicResidueTest Q F n * f ((n : ℝ)/Q))]
      exact tsum_congr hcomp
    _ = ∑' r : Fin Q, ∑' k : ℤ, F r * f ((r : ℝ)/Q+k) := hg.tsum_prod
    _ = ∑ r : Fin Q, F r * 𝓕 f 0 := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro r hr
      rw [tsum_mul_left, poisson_zero_frequency f hband]
    _ = (∑ r, F r) * 𝓕 f 0 := (Finset.sum_mul _ _ _).symm

theorem periodic_poisson_mean_zero (Q : ℕ) [NeZero Q]
    (f : SchwartzMap ℝ ℂ) (F : Fin Q → ℂ)
    (hband : ∀ n : ℤ, n ≠ 0 → 𝓕 f (n : ℝ) = 0)
    (hmean : ∑ r, F r = 0) :
    (∑' n : ℤ, periodicResidueTest Q F n * f ((n : ℝ)/Q)) = 0 := by
  rw [periodic_poisson_zero_frequency Q f F hband, hmean, zero_mul]

end Ostmann.Construction

end

end OAI
