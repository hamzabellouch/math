import OAI.MeasureTheory.Falconer.Estimates.LinearPieces
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-! Quantitative differentiation for the 2-Lipschitz profiles used in planar
Furstenberg regularization: the lower scale depends only on the error. -/
namespace Falconer
open Set

theorem quantitative_uniform_linear_decomposition {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (f : ℝ → ℝ), LipschitzWith 2 f →
      ∀ (a : ℝ) (h : ℝ), 0 < h → ∃ S : List (ℝ × ℝ),
        (∃ H : ℝ, 0 < H ∧ H ≤ h ∧ τ*h ≤ H ∧ ∀ c ∈ S, c.2 = H) ∧
        S.Pairwise (fun c d => c.1+c.2 ≤ d.1) ∧
        h*(1-ε) ≤ (S.map Prod.snd).sum ∧
        ∀ c ∈ S, a ≤ c.1 ∧ c.1+c.2 ≤ a+h ∧ τ*h ≤ c.2 ∧
          ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ ε*c.2 := by
  obtain ⟨m,hm⟩ := exists_pow_lt_of_lt_one (show 0 < ε/8 by positivity)
    (show (1/2 : ℝ) < 1 by norm_num)
  simp only [div_pow,one_pow] at hm
  have hm' : 4/(2 : ℝ)^m ≤ ε/2 := by
    calc
      _ = 4*(1/(2 : ℝ)^m) := by ring
      _ ≤ 4*(ε/8) := mul_le_mul_of_nonneg_left hm.le (by norm_num)
      _ = _ := by ring
  obtain ⟨L,hL⟩ := exists_nat_gt (4/(ε*(ε/2)^2))
  have hLR : (0 : ℝ) < L := lt_trans (by positivity : 0 < 4/(ε*(ε/2)^2)) hL
  have hLN : 0 < L := by exact_mod_cast hLR
  have hloss : 4/((L : ℝ)*(ε/2)^2) ≤ ε := by
    apply (div_le_iff₀ (by positivity : 0 < (L : ℝ)*(ε/2)^2)).2
    have he := (div_lt_iff₀ (by positivity : 0 < ε*(ε/2)^2)).mp hL
    nlinarith
  refine ⟨1/(2 : ℝ)^(L*m),by positivity,?_⟩
  intro f hf a h hh
  obtain ⟨n,hn,hord,hlen,hcells⟩ := exists_dyadic_linear_pieces hf a hh
    (show 0 < ε/2 by positivity) m L hLN
  refine ⟨dyadicLinearPieces f a h (ε/2) n m,?_,hord,?_,?_⟩
  · refine ⟨h/(2 : ℝ)^n,by positivity,div_le_self hh.le (one_le_pow₀ (by norm_num)),?_,?_⟩
    · have hpow : (2 : ℝ)^n ≤ 2^(L*m) := pow_le_pow_right₀ (by norm_num) hn
      have hw := div_le_div_of_nonneg_left hh.le (by positivity : 0 < (2 : ℝ)^n) hpow
      simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hw
    · exact fun c hc => (hcells c hc).2.2.1
  · exact (mul_le_mul_of_nonneg_left (by linarith : 1-ε ≤ 1-4/((L : ℝ)*(ε/2)^2)) hh.le).trans hlen
  · intro c hc
    obtain ⟨hlo,hhi,he,herr⟩ := hcells c hc
    have hpow : (2 : ℝ)^n ≤ 2^(L*m) := pow_le_pow_right₀ (by norm_num) hn
    have hwidth : h/(2 : ℝ)^(L*m) ≤ c.2 := by
      rw [he]
      exact div_le_div_of_nonneg_left hh.le (by positivity) hpow
    refine ⟨hlo,hhi,?_,?_⟩
    · simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hwidth
    · intro x hx
      have hcpos : 0 ≤ c.2 := by rw [he]; positivity
      have hcoef : ε/2+4/(2 : ℝ)^m ≤ ε := by linarith
      exact (herr x hx).trans (by nlinarith [mul_le_mul_of_nonneg_left hcoef hcpos])

theorem quantitative_linear_decomposition {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (f : ℝ → ℝ), LipschitzWith 2 f →
      ∀ (a : ℝ) (h : ℝ), 0 < h → ∃ S : List (ℝ × ℝ),
        S.Pairwise (fun c d => c.1+c.2 ≤ d.1) ∧
        h*(1-ε) ≤ (S.map Prod.snd).sum ∧
        ∀ c ∈ S, a ≤ c.1 ∧ c.1+c.2 ≤ a+h ∧ τ*h ≤ c.2 ∧
          ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ ε*c.2 := by
  obtain ⟨τ,hτ,ht⟩ := quantitative_uniform_linear_decomposition hε
  refine ⟨τ,hτ,?_⟩
  intro f hf a h hh
  obtain ⟨S,_,hord,hlen,hcells⟩ := ht f hf a h hh
  exact ⟨S,hord,hlen,hcells⟩

end Falconer

end OAI
