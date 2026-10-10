import OAI.NumberTheory.JointDickman.Arithmetic.PrimeWindowError
import OAI.NumberTheory.JointDickman.Counting.UnitProgressionBinShort
import OAI.NumberTheory.JointDickman.Analysis.FairLaplaceFeature

namespace OAI

/-! # Replacing prime features inside centered bin short averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

noncomputable def primeSiteWeight (Q : Finset ℕ) (F : (Q → Bool) → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else F (fun p => decide (p.val ∣ n)),by simp⟩

@[simp] theorem primeSiteWeight_apply (Q : Finset ℕ) (F : (Q → Bool) → ℝ)
    {n : ℕ} (hn : n ≠ 0) : primeSiteWeight Q F n = F (fun p => decide (p.val ∣ n)) := by
  simp [primeSiteWeight,hn]

theorem primeSiteWeight_laplace (Q : Finset ℕ) (B : ℝ) (V : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) :
    primeSiteWeight Q (fun x => ∑ v ∈ V, a v*primeLaplaceFeature Q B v x) n =
      ∑ v ∈ V, a v*finitePrimeWeight Q (fun p => (1+(p : ℝ)^(-(v : ℝ)/B))/2) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [primeSiteWeight_apply Q _ hn]
    apply sum_congr rfl
    intro v _
    rw [primeLaplaceFeature_at_integer Q B v hn]

theorem unit_prime_feature_error
    {ι : Type*} [Fintype ι] (ζ : ι → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F G : (Q → Bool) → ℝ) {H A : ℝ} (hH : 1 ≤ H) (hA : 0 < A)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {q : ℕ} [NeZero q] {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (E : ι → Finset ℕ) (r : (ZMod q)ˣ),
      (1/(A*scale n))*(∫ z in (A*scale n)..2*(A*scale n),
        ‖unitProgressionBinAverage E ζ μ (primeSiteWeight Q F) r H z-
          unitProgressionBinAverage E ζ μ (primeSiteWeight Q G) r H z‖^2) <
      24*(∑ x, fullPrimeMass Q x*(F x-G x)^2)+ε := by
  have hh := prime_site_window_energy_bound Q hQ (fun x => 4*(F x-G x)^2)
    hH hA scale hscale hε
  filter_upwards [hh] with n hn
  intro E r
  let f : ArithmeticFunction ℂ := ⟨fun k => if (k : ZMod q) = r then
    (binLabel E ζ k-μ)*((primeSiteWeight Q F k : ℂ)-(primeSiteWeight Q G k : ℂ)) else 0,
    by split_ifs <;> simp⟩
  have hf k : ‖f k‖^2 ≤ 4*(F (fun p => decide (p.val ∣ k))-G (fun p => decide (p.val ∣ k)))^2 := by
    by_cases hk : k = 0
    · subst k
      rw [ArithmeticFunction.map_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      positivity
    by_cases hr : (k : ZMod q) = r
    · simp only [f,ArithmeticFunction.coe_mk,hr,ite_true,primeSiteWeight_apply Q _ hk,
        ← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
      have hc := pow_le_pow_left₀ (norm_nonneg _) (norm_centered_binLabel_le_two E ζ hζ μ hμ k) 2
      exact mul_le_mul_of_nonneg_right (by norm_num at hc ⊢; exact hc) (sq_nonneg _)
    · have hz : f k = 0 := by simp [f,hr]
      rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hshort z : complexShortAverage f H z =
      unitProgressionBinAverage E ζ μ (primeSiteWeight Q F) r H z-
        unitProgressionBinAverage E ζ μ (primeSiteWeight Q G) r H z := by
    unfold complexShortAverage unitProgressionBinAverage
    rw [← sub_div,← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro k _
    simp only [f,ArithmeticFunction.coe_mk]
    split_ifs <;> ring
  have he := hn f hf
  simp only [hshort] at he
  have hid : (∑ x, fullPrimeMass Q x*(4*(F x-G x)^2)) =
      4*∑ x, fullPrimeMass Q x*(F x-G x)^2 := by rw [mul_sum]; congr 1; ext x; ring
  rw [hid] at he
  convert he using 1
  ring

end JointDickman

end OAI
