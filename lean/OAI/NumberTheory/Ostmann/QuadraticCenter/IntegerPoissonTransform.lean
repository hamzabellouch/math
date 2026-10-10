import Mathlib.Logic.Equiv.Fin.Basic
import OAI.NumberTheory.Ostmann.Characters.FinitePoissonTransform

namespace OAI

/-! # Integer-lattice form of finite periodic Poisson summation -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap

private def integerResidueEquiv (N : ℕ) [NeZero N] : ℤ ≃ ZMod N × ℤ :=
  ((Int.divModEquiv N).trans (Equiv.prodComm ℤ (Fin N))).trans
    (Equiv.prodCongr (ZMod.finEquiv N).toEquiv (Equiv.refl ℤ))

private theorem integerResidueEquiv_symm_apply (N : ℕ) [NeZero N] (a : ZMod N) (k : ℤ) :
    (integerResidueEquiv N).symm (a, k) = k * N + a.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

theorem schwartz_translate_int_norm_summable (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    Summable (fun n : ℤ => ‖f (a + n)‖) := by
  simpa only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, add_comm] using
    schwartz_int_norm_summable (f.compSubConstCLM ℂ (-a))

theorem integer_lattice_residue_sum {N : ℕ} [NeZero N]
    (f : 𝓢(ℝ, ℂ)) (F : ZMod N → ℂ) :
    (∑' n : ℤ, F (n : ZMod N) * f ((n : ℝ) / N)) =
      ∑ a : ZMod N, F a * ∑' k : ℤ, f ((a.val : ℝ) / N + k) := by
  let H : ZMod N × ℤ → ℂ := fun z => F z.1 * f ((z.1.val : ℝ) / N + z.2)
  have hrow (a : ZMod N) : Summable (fun k : ℤ =>
      ‖F a‖ * ‖f ((a.val : ℝ) / N + k)‖) :=
    (schwartz_translate_int_norm_summable f ((a.val : ℝ) / N)).mul_left ‖F a‖
  have houter : Summable (fun a : ZMod N =>
      ∑' k : ℤ, ‖F a‖ * ‖f ((a.val : ℝ) / N + k)‖) := (hasSum_fintype _).summable
  have hnorm : Summable (fun z : ZMod N × ℤ =>
      ‖F z.1‖ * ‖f ((z.1.val : ℝ) / N + z.2)‖) :=
    (summable_prod_of_nonneg (fun z : ZMod N × ℤ =>
      mul_nonneg (norm_nonneg (F z.1)) (norm_nonneg (f ((z.1.val : ℝ) / N + z.2))))).2
        ⟨hrow, houter⟩
  have hH : Summable H := by
    apply Summable.of_norm
    simpa only [H, Complex.norm_mul] using hnorm
  have he (a : ZMod N) (k : ℤ) :
      F (((integerResidueEquiv N).symm (a, k) : ℤ) : ZMod N) *
        f (((integerResidueEquiv N).symm (a, k) : ℤ) / (N : ℝ)) = H (a, k) := by
    rw [integerResidueEquiv_symm_apply]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      mul_zero, zero_add, ZMod.natCast_zmod_val]
    congr 2
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    dsimp [H]
    field_simp
    ring
  calc
    _ = ∑' z : ZMod N × ℤ, H z := by
      rw [← (integerResidueEquiv N).symm.tsum_eq
        (fun n : ℤ => F (n : ZMod N) * f ((n : ℝ) / N))]
      apply tsum_congr
      rintro ⟨a, k⟩
      exact he a k
    _ = ∑' a : ZMod N, ∑' k : ℤ, H (a, k) := hH.tsum_prod
    _ = _ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro a ha
      change (∑' k : ℤ, F a * f ((a.val : ℝ) / N + k)) = _
      exact tsum_mul_left

theorem integer_poisson_transform {N : ℕ} [NeZero N]
    (f : 𝓢(ℝ, ℂ)) (F : ZMod N → ℂ) :
    (∑' n : ℤ, F (n : ZMod N) * f ((n : ℝ) / N)) =
      (N : ℂ) * ∑' n : ℤ, 𝓕 f (n : ℝ) * additiveFourier F (-(n : ZMod N)) := by
  rw [integer_lattice_residue_sum, finite_poisson_transform]

end Ostmann

end OAI
