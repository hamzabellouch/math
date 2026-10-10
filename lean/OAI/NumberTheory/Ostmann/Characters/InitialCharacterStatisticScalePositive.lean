import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.InitialCharacterScale
open Filter
open scoped Topology

def positiveRate (Cw CI : ℝ) : ℝ := 3*Cw+CI+1

def amplitudeRate (Cw CI : ℝ) : ℝ := positiveRate Cw CI+1

theorem positive_scalar_lower {cψ δ CI N : ℝ} (hc : 0 < cψ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hCI : 0 ≤ CI) (_hN : 0 ≤ N)
    (Cw D : ℝ) (k : ℕ) (hNz : N ≤ depthScale k) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, (n : ℝ) ≤ N → ∀ V : ℝ,
      Real.exp (-Cw*(wordSize k L : ℝ)-CI*N*L-D) ≤ V →
      Real.exp (-positiveRate Cw CI*(wordSize k L : ℝ)) ≤
        cψ*V*(Real.exp (-Cw*(wordSize k L : ℝ))*δ^n)^2 := by
  let R := ⌈N⌉₊
  let K := cψ*Real.exp (-CI-D)*δ^(2*R)
  have hK : 0 < K := by dsimp [K]; positivity
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (wordSize_tendsto k)
  filter_upwards [ht.eventually (eventually_lt_nhds hK),eventually_ge_atTop (0 : ℝ)]
    with L hfixed hL
  intro n hn V hV
  let m := wordSize k L
  have hnR : n ≤ R := by
    exact_mod_cast hn.trans (Nat.le_ceil N)
  have hNL : N*L ≤ (m : ℝ)+1 := by
    have hh := mul_le_mul_of_nonneg_right hNz hL
    have hf := (wordSize_bounds k hL).1
    change depthScale k*L-1 < (m : ℝ) at hf
    linarith
  have hVl : Real.exp (-(Cw+CI)*(m : ℝ)-CI-D) ≤ V := by
    apply le_trans _ hV
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hNL hCI]
  have hV0 : 0 ≤ V := (Real.exp_pos _).le.trans hVl
  have hpow : δ^(2*R) ≤ δ^(2*n) :=
    pow_le_pow_of_le_one hδ.le hδone (Nat.mul_le_mul_left 2 hnR)
  have hsq : (Real.exp (-Cw*(m : ℝ))*δ^n)^2 =
      Real.exp (-(2*Cw)*(m : ℝ))*δ^(2*n) := by
    rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul]
    congr 1 <;> congr 1 <;> ring
  calc
    _ = Real.exp (-(m : ℝ))*Real.exp (-(3*Cw+CI)*(m : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [positiveRate,m]
      ring
    _ ≤ K*Real.exp (-(3*Cw+CI)*(m : ℝ)) :=
      mul_le_mul_of_nonneg_right hfixed.le (Real.exp_pos _).le
    _ = cψ*Real.exp (-(Cw+CI)*(m : ℝ)-CI-D)*
        (Real.exp (-(2*Cw)*(m : ℝ))*δ^(2*R)) := by
      have he : Real.exp (-CI-D)*Real.exp (-(3*Cw+CI)*(m : ℝ)) =
          Real.exp (-(Cw+CI)*(m : ℝ)-CI-D)*Real.exp (-(2*Cw)*(m : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (cψ*δ^(2*R))*(Real.exp (-CI-D)*Real.exp (-(3*Cw+CI)*(m : ℝ))) := by
          dsimp only [K]
          ring
        _ = _ := by rw [he]; ring
    _ ≤ cψ*V*(Real.exp (-(2*Cw)*(m : ℝ))*δ^(2*n)) := by
      gcongr
    _ = _ := by rw [← hsq]

end Ostmann.Characters.InitialCharacterScale

end

end OAI
