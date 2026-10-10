import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteClipping
import OAI.Combinatorics.KMedian.Geometry.BundleRounding

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem rescaled_bundle_law (P : T → Finset I) (y : I → ℝ) (p : T → ℝ)
    (K : T → ℕ) (Δ : ℕ) {g : ℝ} (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ t, 0 < p t)
    (hmass : ∀ t, ∑ i ∈ P t, y i=p t) (hK : ∀ t, K t ≤ Δ) :
    ∃ (μ : FiniteLaw (T → Finset I)) (C : (T → Finset I) → T × I → ℕ),
      (∀ ξ, 0 < μ.weight ξ → ∀ t,
        (∑ i, C ξ (t,i))=K t ∧
        (∀ i, C ξ (t,i) ≤ Δ) ∧
        (∀ i, i ∉ P t → C ξ (t,i)=0)) ∧
      (∀ t i, μ.expect (fun ξ => g*(C ξ (t,i):ℝ))=
        if i ∈ P t then (g*(K t:ℝ))*y i/p t else 0) ∧
      (∀ a b, a ≠ b → μ.expect (fun ξ => (g*(C ξ a:ℝ))*(g*(C ξ b:ℝ))) ≤
        (if a.2 ∈ P a.1 then (g*(K a.1:ℝ))*y a.2/p a.1 else 0)*
        (if b.2 ∈ P b.1 then (g*(K b.1:ℝ))*y b.2/p b.1 else 0)) ∧
      (∀ a, μ.variance (fun ξ => g*(C ξ a:ℝ)) ≤
        g*(if a.2 ∈ P a.1 then (g*(K a.1:ℝ))*y a.2/p a.1 else 0)) ∧
      (∀ ξ a, 0 ≤ g*(C ξ a:ℝ)) ∧
      (∀ ξ, 0 < μ.weight ξ → ∀ a, g*(C ξ a:ℝ) ≤ 1) := by
  classical
  let q := fun t i => if i ∈ P t then (K t:ℝ)*y i/p t else 0
  have hq0 : ∀ t i, 0 ≤ q t i := by
    intro t i
    dsimp only [q]
    split_ifs
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hy i)) (hp t).le
    · exact le_rfl
  have hqΔ : ∀ t i, q t i ≤ (Δ:ℝ) := by
    intro t i
    by_cases hi : i ∈ P t
    · have hyP : y i ≤ p t := (single_le_sum (fun i _ => hy i) hi).trans_eq (hmass t)
      have he : q t i ≤ (K t:ℝ) := by
        simp only [q,ite_eq_left hi]
        apply (div_le_iff₀ (hp t)).mpr
        exact mul_le_mul_of_nonneg_left hyP (Nat.cast_nonneg _)
      exact he.trans (Nat.cast_le.mpr (hK t))
    · simp only [q,ite_eq_right hi]
      exact Nat.cast_nonneg _
  have hqsum : ∀ t, ∑ i, q t i=K t := by
    intro t
    simp only [q,sum_ite_mem,univ_inter,← sum_div,← mul_sum,hmass]
    exact mul_div_cancel_right₀ _ (hp t).ne'
  obtain ⟨μ,C,hs,hm,hpair,hvar,hpos,hcap⟩ := bundle_law q K Δ hg.le hunit hq0 hqΔ hqsum
  have hmean : ∀ t i, μ.expect (fun ξ => g*(C ξ (t,i):ℝ))=
      if i ∈ P t then (g*(K t:ℝ))*y i/p t else 0 := by
    intro t i
    rw [hm]
    dsimp only [q]
    split_ifs <;> ring
  refine ⟨μ,C,?_,hmean,?_,?_,hpos,hcap⟩
  · intro ξ hξ t
    refine ⟨(hs ξ hξ t).1,(hs ξ hξ t).2,?_⟩
    intro i hi
    have he := hmean t i
    rw [ite_eq_right hi] at he
    have hz := μ.nonneg_expect_zero_support (fun ξ => g*(C ξ (t,i):ℝ))
      (fun ξ => hpos ξ (t,i)) he ξ hξ
    exact Nat.cast_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hg.ne')
  · intro a b hab
    have hm' : ∀ t i, g*q t i=if i ∈ P t then (g*(K t:ℝ))*y i/p t else 0 := by
      intro t i
      exact (hm t i).symm.trans (hmean t i)
    simpa only [hm'] using hpair a b hab
  · intro a
    have he := (hm a.1 a.2).symm.trans (hmean a.1 a.2)
    simpa only [he] using hvar a

omit [Fintype I] [Fintype T] [DecidableEq T] in

theorem rescaled_subset_mean {Ξ : Type} [Fintype Ξ] (μ : FiniteLaw Ξ)
    (Y : Ξ → T × I → ℝ) (P : T → Finset I) (y : I → ℝ) (p p' : T → ℝ)
    (hm : ∀ t i, μ.expect (fun ξ => Y ξ (t,i))=if i ∈ P t then p' t*y i/p t else 0)
    (F : Finset I) (d : I → ℝ) (t : T) :
    μ.expect (fun ξ => ∑ i ∈ F, Y ξ (t,i)*d i)=
      (p' t/p t)*(∑ i ∈ F ∩ P t, y i*d i) := by
  rw [FiniteLaw.expect_sum]
  simp_rw [FiniteLaw.expect_mul_right,hm]
  have he : ∀ i, (if i ∈ P t then p' t*y i/p t else 0)*d i=
      if i ∈ P t then (p' t/p t)*(y i*d i) else 0 := by
    intro i
    split_ifs <;> ring
  simp_rw [he]
  rw [sum_ite_mem,mul_sum]

end MetricKMedian.Preparation
end
end

end OAI
