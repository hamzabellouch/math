import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.UniformReciprocal

namespace OAI

/-! Uniform joint density bounds for the actual Moser homotopy. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem contraction_four_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (f : F → ℝ) (hf : ContDiff ℝ 4 f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ j ≤ 4, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ B)
    {k : ℕ} (hk : k ≤ 4) (x : E) : ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ B := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  have h := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  apply h.trans
  exact (mul_le_mul (hb k hk _) (pow_le_one₀ (norm_nonneg L) hL)
    (pow_nonneg (norm_nonneg L) _) hB).trans_eq (mul_one B)

private theorem fst_four_bound {k : ℕ} (x : ℝ × Position) (hx : |x.1| ≤ 1) :
    ‖iteratedFDeriv ℝ k (fun y : ℝ × Position => y.1) x‖ ≤ 1 := by
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hx
  | succ k =>
    rw [← norm_iteratedFDeriv_fderiv]
    change ‖iteratedFDeriv ℝ k (fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ Position)) x‖ ≤ 1
    have hder : fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ Position) =
        fun _ => ContinuousLinearMap.fst ℝ ℝ Position :=
      funext (fun _ => (ContinuousLinearMap.fst ℝ ℝ Position).fderiv)
    rw [hder]
    cases k with
    | zero => simpa only [norm_iteratedFDeriv_zero] using
        (ContinuousLinearMap.norm_fst_le (𝕜 := ℝ) (E := ℝ) (F := Position))
    | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, zero_le_one]

/-- A uniform bound for the four joint derivatives of rho+t*charge. -/
theorem homotopyDensity_uniform_derivatives {rho B : ℝ} (hB : 0 ≤ B)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    {k : ℕ} (hk : k ≤ 4) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Position) :
    ‖iteratedFDeriv ℝ k (fun p : ℝ × Position => homotopyDensity rho V p.1 p.2) (t,x)‖ ≤
      |rho|+16*(3*B/(4*Real.pi)) := by
  let C : ℝ := 3*B/(4*Real.pi)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcharge (j : ℕ) (hj : j ≤ 4) (y : ℝ × Position) :
      ‖iteratedFDeriv ℝ j (fun p : ℝ × Position => manufacturedCharge V p.2) y‖ ≤ C :=
    contraction_four_bound (ContinuousLinearMap.snd ℝ ℝ Position)
      (ContinuousLinearMap.norm_snd_le ℝ ℝ Position) (manufacturedCharge V) (manufacturedCharge_C4 V hV)
      hC (fun j hj z => manufacturedCharge_derivative_bound V hV hB hb hj z) hj y
  have hf : ContDiff ℝ 4 (fun p : ℝ × Position => p.1 * manufacturedCharge V p.2) :=
    contDiff_fst.mul ((manufacturedCharge_C4 V hV).comp contDiff_snd)
  have hprod : ‖iteratedFDeriv ℝ k (fun p : ℝ × Position =>
      p.1*manufacturedCharge V p.2) (t,x)‖ ≤ 16*C := by
    apply (norm_iteratedFDeriv_mul_le contDiff_fst
      ((manufacturedCharge_C4 V hV).comp contDiff_snd) (t,x)
      (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*C := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have ht' : |(t,x).1| ≤ 1 := by
          change |t| ≤ 1
          rw [abs_of_nonneg ht.1]
          exact ht.2
        exact (mul_le_mul
          (mul_le_mul_of_nonneg_left (fst_four_bound (k := i) (t,x) ht')
            (Nat.cast_nonneg _))
          (hcharge (k-i) ((Nat.sub_le k i).trans hk) (t,x))
          (norm_nonneg _) (by positivity)).trans_eq (by ring)
      _ = (2:ℝ)^k*C := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose k
      _ ≤ 16*C := mul_le_mul_of_nonneg_right
        ((pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)) hC
  change ‖iteratedFDeriv ℝ k (fun p : ℝ × Position =>
    rho + p.1*manufacturedCharge V p.2) (t,x)‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply contDiff_const.contDiffAt
    (hf.of_le (by exact_mod_cast hk)).contDiffAt]
  apply (norm_add_le _ _).trans
  apply add_le_add _ hprod
  cases k with
  | zero => simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, le_refl]
  | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, abs_nonneg]

end ContinuumCoulomb

end

end OAI
