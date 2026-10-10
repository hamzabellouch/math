import OAI.Probability.BenjaminiSchramm.PeakSurvivalRealHeight

namespace OAI

noncomputable section
open Filter
open scoped ENNReal Topology

namespace Percolation.BenjaminiSchramm

theorem antitone_survival_real_lower (Q : ℝ → ℝ≥0∞) (hQ : Antitone Q)
    (R b : ℝ) (hR : 0 < R) (hb : 0 ≤ b)
    (hdisc : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (c*Real.exp (-(R*b+ε)*n)) ≤ Q (R*n)) :
    ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ ell : ℝ, 0 < ell →
      ENNReal.ofReal (c*Real.exp (-(b+δ)*ell)) ≤ Q ell := by
  intro δ hδ
  obtain ⟨c,hc,hcbd⟩ := hdisc (R*δ) (mul_pos hR hδ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hcbd
  let A := R*b+R*δ
  have hA : 0 ≤ A := add_nonneg (mul_nonneg hR.le hb) (mul_nonneg hR.le hδ.le)
  refine ⟨c*Real.exp (-A*((N : ℝ)+1)),mul_pos hc (Real.exp_pos _),fun ell hell => ?_⟩
  let n := max N ⌈ell/R⌉₊
  have hNn : N ≤ n := le_max_left _ _
  have helln : ell ≤ R*(n : ℝ) := by
    have hh : ell/R ≤ (n : ℝ) := (Nat.le_ceil (ell/R)).trans (Nat.cast_le.mpr (le_max_right _ _))
    have hh' := (div_le_iff₀ hR).mp hh
    nlinarith
  have hnn : (n : ℝ) ≤ ell/R+(N : ℝ)+1 := by
    have hh := (Nat.ceil_lt_add_one (div_nonneg hell.le hR.le)).le
    have hh' : (n : ℝ) ≤ (N : ℝ)+(⌈ell/R⌉₊ : ℝ) := by
      exact_mod_cast (show n ≤ N+⌈ell/R⌉₊ from
        Nat.max_le.mpr ⟨Nat.le_add_right _ _,Nat.le_add_left _ _⟩)
    linarith
  have hreal : (c*Real.exp (-A*((N : ℝ)+1)))*Real.exp (-(b+δ)*ell) ≤
      c*Real.exp (-(R*b+R*δ)*(n : ℝ)) := by
    rw [mul_assoc,←Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hnn hA
    have hcancel : A*(ell/R)=(b+δ)*ell := by
      dsimp [A]
      field_simp
    rw [mul_add,mul_add,hcancel] at hh
    dsimp [A] at hh ⊢
    nlinarith
  exact (ENNReal.ofReal_le_ofReal hreal).trans ((hN n hNn).trans (hQ helln))

end Percolation.BenjaminiSchramm

end

end OAI
