import OAI.Probability.ClassicalON.FamilyKernel

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON
namespace LatticeGraph
variable {k : ℕ}

theorem mode_gradient_square_sum_le (G : LatticeGraph) (m s : Bool) (a : ℝ)
    (h : SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) (p : DyadicFreq k) :
    (∑ e, ‖G.modeGradient m s p e‖^2) ≤ a^2/(dyadicRadius p:ℝ) := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hh := h.column p
  simp only [scaledModeGradient, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hr.le] at hh
  rw [← Finset.mul_sum] at hh
  exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hh)

theorem mode_sup_square_le (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k)
    (C : ℝ) (hC : 0 ≤ C) (hv : ∀ z, |squareProfile m s z| ≤ C) :
    ‖(fun x : G.vertices => latticeMode m s p x.val)‖^2 ≤ C^2*(1/(dyadicRadius p:ℝ))^3 := by
  have hnorm : ‖(fun x : G.vertices => latticeMode m s p x.val)‖ ≤ dyadicWeight p*C := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (dyadicWeight_pos p).le hC)).mpr
    exact fun x => latticeMode_norm_bound m s p x.val C (hv _)
  calc _ ≤ (dyadicWeight p*C)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
       _ = _ := by rw [mul_pow, dyadicWeight_sq]; ring

theorem mode_gram_reweight (G : LatticeGraph) (m s : Bool) (e l : G.edges) :
    (∑ p : DyadicFreq k, G.scaledModeGradient m s p e*((1/(dyadicRadius p:ℝ)):ℂ)*
      conj (G.scaledModeGradient m s p l)) = ∑ p : DyadicFreq k,
        G.modeGradient m s p e*conj (G.modeGradient m s p l) := by
  apply Finset.sum_congr rfl
  intro p _
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hs : ((Real.sqrt (dyadicRadius p:ℝ):ℂ)*((1/(dyadicRadius p:ℝ)):ℂ)*
      (Real.sqrt (dyadicRadius p:ℝ):ℂ)) = 1 := by
    have hsreal : Real.sqrt (dyadicRadius p:ℝ)*(1/(dyadicRadius p:ℝ))*Real.sqrt (dyadicRadius p:ℝ) = 1 := by
      rw [show Real.sqrt (dyadicRadius p:ℝ)*(1/(dyadicRadius p:ℝ))*Real.sqrt (dyadicRadius p:ℝ) =
      (Real.sqrt (dyadicRadius p:ℝ))^2/(dyadicRadius p:ℝ) by ring, Real.sq_sqrt hr.le, div_self hr.ne']
    exact_mod_cast hsreal
  simp only [scaledModeGradient, map_mul, Complex.conj_ofReal]
  linear_combination G.modeGradient m s p e*conj (G.modeGradient m s p l)*hs

theorem mode_group_gram_bound (G : LatticeGraph) (m s : Bool) (a : ℝ)
    (h : SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) :
    (∑ e, ∑ l, ‖∑ p : DyadicFreq k, G.modeGradient m s p e*conj (G.modeGradient m s p l)‖^2)
      ≤ 3*a^4*(k:ℝ) := by
  have hh := h.gram_weighted (fun p => ((1/(dyadicRadius p:ℝ)):ℂ))
  simp_rw [G.mode_gram_reweight] at hh
  have he (p : DyadicFreq k) : ‖((1/(dyadicRadius p:ℝ)):ℂ)‖^2 = (1/(dyadicRadius p:ℝ))^2 := by
    have hr : (0:ℝ) ≤ dyadicRadius p := by positivity
    simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  simp_rw [he] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left (dyadic_inverse_square_sum k) (by positivity : 0≤a^4)])

abbrev ModeIndex (k : ℕ) := (Bool × Bool) × DyadicFreq k

def modes (G : LatticeGraph) (i : ModeIndex k) (x : G.vertices) : ℂ :=
  latticeMode i.1.1 i.1.2 i.2 x.val

def modeDifferences (G : LatticeGraph) (i : ModeIndex k) (e : G.edges) : ℂ :=
  G.modeGradient i.1.1 i.1.2 i.2 e

theorem modes_HS_bound (G : LatticeGraph) (a : ℝ)
    (h : ∀ m s, SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) :
    familyHSSquare (G.modeDifferences (k := k)) ≤ 48*a^4*(k:ℝ) := by
  unfold familyHSSquare rowSquare familyKernel modeDifferences
  simp only [Fintype.sum_prod_type]
  have hh := gram_groups_bound
    (fun (i : Bool × Bool) e l => ∑ p : DyadicFreq k,
      G.modeGradient i.1 i.2 p e*conj (G.modeGradient i.1 i.2 p l))
    (3*a^4*(k:ℝ)) (fun i => G.mode_group_gram_bound i.1 i.2 a (h i.1 i.2))
  simpa only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat,
    show ((2:ℝ)*2)^2*(3*a^4*(k:ℝ)) = 48*a^4*(k:ℝ) by ring] using hh

theorem modes_min_bound (G : LatticeGraph) (a C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ m s z, |squareProfile m s z| ≤ C)
    (h : ∀ m s, SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) :
    (∑ i : ModeIndex k, ∑ j : ModeIndex k,
      min (‖G.modes i‖^2*∑ e, ‖G.modeDifferences j e‖^2)
          (‖G.modes j‖^2*∑ e, ‖G.modeDifferences i e‖^2)) ≤ 576*C^2*a^2*(k:ℝ) := by
  have hv' (i : ModeIndex k) : ‖G.modes i‖^2 ≤ C^2*(1/(dyadicRadius i.2:ℝ))^3 :=
    G.mode_sup_square_le i.1.1 i.1.2 i.2 C hC (hv i.1.1 i.1.2)
  have hd' (i : ModeIndex k) : (∑ e, ‖G.modeDifferences i e‖^2) ≤ a^2/(dyadicRadius i.2:ℝ) :=
    G.mode_gradient_square_sum_le i.1.1 i.1.2 a (h i.1.1 i.1.2) i.2
  have hm (i j : ModeIndex k) :
      min (‖G.modes i‖^2*∑ e, ‖G.modeDifferences j e‖^2)
          (‖G.modes j‖^2*∑ e, ‖G.modeDifferences i e‖^2) ≤
      C^2*a^2*min ((1/(dyadicRadius i.2:ℝ))^3*(1/(dyadicRadius j.2:ℝ)))
                 ((1/(dyadicRadius j.2:ℝ))^3*(1/(dyadicRadius i.2:ℝ))) := by
    rw [mul_min_of_nonneg _ _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    apply min_le_min
    · calc _ ≤ (C^2*(1/(dyadicRadius i.2:ℝ))^3)*(a^2/(dyadicRadius j.2:ℝ)) :=
            mul_le_mul (hv' i) (hd' j) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
           _ = _ := by ring
    · calc _ ≤ (C^2*(1/(dyadicRadius j.2:ℝ))^3)*(a^2/(dyadicRadius i.2:ℝ)) :=
            mul_le_mul (hv' j) (hd' i) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
           _ = _ := by ring
  calc _ ≤ ∑ i : ModeIndex k, ∑ j : ModeIndex k,
        C^2*a^2*min ((1/(dyadicRadius i.2:ℝ))^3*(1/(dyadicRadius j.2:ℝ)))
                   ((1/(dyadicRadius j.2:ℝ))^3*(1/(dyadicRadius i.2:ℝ))) :=
           Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hm i j
       _ = 16*C^2*a^2*∑ p : DyadicFreq k, ∑ q : DyadicFreq k,
           min ((1/(dyadicRadius p:ℝ))^3*(1/(dyadicRadius q:ℝ)))
               ((1/(dyadicRadius q:ℝ))^3*(1/(dyadicRadius p:ℝ))) := by
          simp only [ModeIndex, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
            Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
          ring
       _ ≤ _ := by
          have hd := mul_le_mul_of_nonneg_left (dyadic_min_cost_sum k)
            (by positivity : 0 ≤ 16*C^2*a^2)
          nlinarith

end LatticeGraph
end ClassicalON

end

end OAI
