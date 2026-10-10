import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseNatMul

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryAdditiveBilinear

lemma phase_mul_star (x y : ℝ) : phase x*star (phase y)=phase (x-y) := by
  simp only [phase, Complex.star_def, ←Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal, ←Complex.exp_add]
  congr 1
  push_cast
  ring

lemma energy_le_gram {ι : Type*} (P : Finset ι) (b : ι → ℕ → ℂ) (N : ℕ) :
    (∑n∈range N,‖∑p∈P,b p n‖^2) ≤
      ∑p∈P,∑q∈P,‖∑n∈range N,b p n*star (b q n)‖ := by
  have he : ((∑n∈range N,‖∑p∈P,b p n‖^2:ℝ):ℂ)=
      ∑p∈P,∑q∈P,∑n∈range N,b p n*star (b q n) := by
    simp only [Complex.ofReal_sum,Complex.ofReal_pow,←Complex.mul_conj',map_sum]
    simp_rw [sum_mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    rw [sum_comm]
    rfl
  calc
    _ = ‖((∑n∈range N,‖∑p∈P,b p n‖^2:ℝ):ℂ)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
      exact sum_nonneg (fun n hn => sq_nonneg _)
    _ = _ := congrArg norm he
    _ ≤ ∑p∈P,‖∑q∈P,∑n∈range N,b p n*star (b q n)‖ := norm_sum_le _ _
    _ ≤ _ := sum_le_sum (fun p hp => norm_sum_le _ _)

lemma pair_identity (c d w v : ℂ) (α : ℝ) (p q n : ℕ) :
    (c*w*phase (α*(p:ℝ)*n))*star (d*v*phase (α*(q:ℝ)*n)) =
      (c*star d)*((w*star v)*phase (α*((p:ℝ)-q)*n)) := by
  have he : phase (α*(p:ℝ)*n)*star (phase (α*(q:ℝ)*n))=
      phase (α*((p:ℝ)-q)*n) := by
    rw [phase_mul_star]
    congr 1
    ring
  simp only [star_mul]
  calc
    _ = (c*star d)*((w*star v)*(phase (α*(p:ℝ)*n)*star (phase (α*(q:ℝ)*n)))) := by ring
    _ = _ := by rw [he]

lemma smoothed_pair_bound (u : ℕ → ℂ) (hu : ∀n,‖u n‖≤1)
    (c : ℕ → ℂ) (hc : ∀p,‖c p‖≤1) (D p q a N : ℕ) (α : ℝ)
    {κ : ℝ} (hκ : 0<κ) (hgap : κ≤‖1-phase (α*((p:ℝ)-q))‖) :
    ‖∑n∈range N,
      (c p*smooth u D (p*(a+n))*phase (α*(p:ℝ)*n))*
        star (c q*smooth u D (q*(a+n))*phase (α*(q:ℝ)*n))‖ ≤
      (2+(N:ℝ)*(((p:ℝ)+q)*(2/(D:ℝ))))/κ := by
  simp_rw [pair_identity,←mul_sum,norm_mul,norm_star]
  have hcoef : ‖c p*star (c q)‖≤1 := by
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hc p)).trans (hc q)
  have hh := smoothed_cross_phase u hu D p q a N α
  have hs : ‖∑n∈range N,(smooth u D (p*(a+n))*star (smooth u D (q*(a+n))))*
      phase (α*((p:ℝ)-q)*(n:ℝ))‖≤(2+(N:ℝ)*(((p:ℝ)+q)*(2/(D:ℝ))))/κ := by
    apply (le_div_iff₀ hκ).mpr
    calc
      _ = κ*‖∑n∈range N,(smooth u D (p*(a+n))*star (smooth u D (q*(a+n))))*
        phase (α*((p:ℝ)-q)*(n:ℝ))‖ := mul_comm _ _
      _ ≤ ‖1-phase (α*((p:ℝ)-q))‖*
        ‖∑n∈range N,(smooth u D (p*(a+n))*star (smooth u D (q*(a+n))))*
          phase (α*((p:ℝ)-q)*(n:ℝ))‖ := mul_le_mul_of_nonneg_right hgap (norm_nonneg _)
      _ ≤ _ := hh
  calc
    _ ≤ 1*‖∑n∈range N,(smooth u D (p*(a+n))*star (smooth u D (q*(a+n))))*
      phase (α*((p:ℝ)-q)*(n:ℝ))‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [norm_mul,norm_star] using hcoef
    _ ≤ _ := by simpa using hs

end OrdinaryAdditiveBilinear

end

end OAI
