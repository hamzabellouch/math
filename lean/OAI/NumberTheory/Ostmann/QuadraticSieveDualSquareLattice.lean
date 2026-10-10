import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoisson
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareIntegral
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareLattice

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory Set
open scoped SchwartzMap FourierTransform

theorem positive_coprime_even_lattice (ψ : 𝓢(ℝ, ℂ)) (heven : Function.Even ψ)
    (X : ℝ) (hX : 0 < X) (k : ℕ) (hk : 2 ≤ k) :
    (∑' u : {u : ℕ // 0 < u}, if Nat.Coprime u.val k then ψ ((u.val : ℝ) / X) else 0) =
      (1 / 2 : ℂ) * ∑' m : ℤ, if Nat.Coprime m.natAbs k then ψ ((m : ℝ) / X) else 0 := by
  let F : ℤ → ℂ := fun m => if Nat.Coprime m.natAbs k then ψ ((m : ℝ) / X) else 0
  have hF : Summable F := by
    exact ((schwartz_summable_scaled ψ X hX.ne').indicator
      {m : ℤ | Nat.Coprime m.natAbs k}).congr (fun m => by simp [F, Set.indicator_apply])
  have he : Function.Even F := by
    intro m
    simp only [F, Int.natAbs_neg, Int.cast_neg, neg_div]
    rw [heven ((m : ℝ) / X)]
  have hz : F 0 = 0 := by
    have hk1 : k ≠ 1 := by omega
    simp [F, hk1]
  have h := tsum_int_eq_zero_add_two_mul_tsum_pnat he hF
  rw [hz, zero_add] at h
  calc
    _ = ∑' u : ℕ+, F (u : ℤ) := by
      apply tsum_congr
      intro u
      simp only [F, Int.natAbs_natCast, Int.cast_natCast]
      rfl
    _ = (1 / 2 : ℂ) * ∑' m : ℤ, F m := by rw [h]; ring

noncomputable def dualSquareSum (W : 𝓢(ℝ, ℂ)) (a e M b : ℝ) (q : ℕ) : ℂ :=
  ∑' u : {u : ℕ // 0 < u}, if Nat.Coprime u.val q then
    𝓕 W (a * b * M * (u.val : ℝ) ^ 2 / (e * q)) else 0

theorem dualSquareSum_eq_lattice (W : 𝓢(ℝ, ℂ)) (a e M b : ℝ) (q : ℕ)
    (ha : a ≠ 0) (he : 0 < e) (hM : 0 < M) (hb : 0 < b) (hq : 2 ≤ q) :
    dualSquareSum W a e M b q = (1 / 2 : ℂ) *
      ∑' m : ℤ, if Nat.Coprime m.natAbs q then
        squarePullback (𝓕 W) a ha ((m : ℝ) / Real.sqrt (e * q / (M * b))) else 0 := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hX : 0 < Real.sqrt (e * q / (M * b)) := Real.sqrt_pos.mpr (by positivity)
  have hf (x : ℝ) : 𝓕 W (a * b * M * x ^ 2 / (e * q)) =
      squarePullback (𝓕 W) a ha (x / Real.sqrt (e * q / (M * b))) := by
    rw [squarePullback_apply, div_pow, Real.sq_sqrt (by positivity)]
    congr 1
    field_simp
  unfold dualSquareSum
  simp_rw [hf]
  apply positive_coprime_even_lattice _ _ _ hX q hq
  intro x
  simp only [squarePullback_apply, neg_sq]

theorem dualSquareSum_poisson_error (W : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M b : ℝ) (q : ℕ),
      0 < e → 0 < M → 0 < b → 2 ≤ q → ∀ X₁ X₂ J L : ℝ,
      0 < X₁ → X₁ ≤ Real.sqrt (e * q / (M * b)) →
      Real.sqrt (e * q / (M * b)) ≤ X₂ → 0 < J →
      J ≤ min (Real.sqrt (e * q / (M * b)) / X₁)
        (X₂ / Real.sqrt (e * q / (M * b))) →
      (X₂ / Real.sqrt (e * q / (M * b))) ^ 2 ≤ L →
      ‖dualSquareSum W a e M b q - (1 / 2 : ℂ) *
        coprimePoissonMain (squarePullback (𝓕 W) a ha) q
          (Real.sqrt (e * q / (M * b))) X₁ X₂ L‖ ≤
        C * Real.sqrt (e * q / (M * b)) / J ^ A := by
  obtain ⟨C,hC,hbound⟩ := coprime_poisson_truncated (squarePullback (𝓕 W) a ha) A
  refine ⟨C / 2, by positivity, ?_⟩
  intro e M b q he hM hb hq X₁ X₂ J L h1 h2 h3 hJ hmin hL
  rw [dualSquareSum_eq_lattice W a e M b q ha he hM hb hq, ← mul_sub, norm_mul]
  have hn : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hn]
  calc
    _ ≤ (1 / 2 : ℝ) * (C * Real.sqrt (e * q / (M * b)) / J ^ A) :=
      mul_le_mul_of_nonneg_left (hbound q _ X₁ X₂ J L hq h1 h2 h3 hJ hmin hL)
        (by norm_num)
    _ = _ := by ring

theorem dualSquare_integral (W : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) (a : ℝ) (ha : a ≠ 0) :
    (∫ x : ℝ, squarePullback (𝓕 W) a ha x) =
      (1 - (Real.sign a : ℂ) * Complex.I) / (Real.sqrt |a| : ℂ) *
        (∫ x : ℝ in Ioi 0, W (x ^ 2)) := by
  simp only [squarePullback_apply]
  exact fourier_square_integral W hc hs ha

end Ostmann.QuadraticSieve

end OAI
