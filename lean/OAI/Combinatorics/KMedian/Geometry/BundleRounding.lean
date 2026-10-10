import Mathlib
import OAI.Combinatorics.KMedian.Rounding.GridRounding

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {T I : Type} [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I]

theorem bundle_law (q : T → I → ℝ) (K : T → ℕ) (L : ℕ) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(L:ℝ)=1)
    (hq0 : ∀ t i, 0 ≤ q t i) (hqL : ∀ t i, q t i ≤ L)
    (hsum : ∀ t, ∑ i, q t i=K t) :
    ∃ (μ : FiniteLaw (T → Finset I)) (C : (T → Finset I) → T × I → ℕ),
      (∀ ω, 0 < μ.weight ω → ∀ t,
        (∑ i, C ω (t,i))=K t ∧ ∀ i, C ω (t,i) ≤ L) ∧
      (∀ t i, μ.expect (fun ω => g*(C ω (t,i):ℝ))=g*q t i) ∧
      (∀ a b, a ≠ b → μ.expect (fun ω => (g*(C ω a:ℝ))*(g*(C ω b:ℝ))) ≤
        (g*q a.1 a.2)*(g*q b.1 b.2)) ∧
      (∀ a, μ.variance (fun ω => g*(C ω a:ℝ)) ≤ g*(g*q a.1 a.2)) ∧
      (∀ ω a, 0 ≤ g*(C ω a:ℝ)) ∧
      (∀ ω, 0 < μ.weight ω → ∀ a, g*(C ω a:ℝ) ≤ 1) := by
  classical
  choose ν c hs hm hp hv using fun t => WeightedRounding.integer_law (q t) (K t) L
    (hq0 t) (hqL t) (hsum t)
  let μ := FiniteLaw.product ν
  let C := fun (ω : T → Finset I) (a : T × I) => c a.1 (ω a.1) a.2
  have hc : ∀ ω, 0 < μ.weight ω → ∀ t,
      (∑ i, C ω (t,i))=K t ∧ ∀ i, C ω (t,i) ≤ L := by
    intro ω hω t
    have h := hs t (ω t) (FiniteLaw.support_product ν ω hω t)
    exact ⟨h.1,h.2.1⟩
  have hm' : ∀ t i, μ.expect (fun ω => (C ω (t,i):ℝ))=q t i := by
    intro t i
    exact (FiniteLaw.product_marginal ν t (fun S => (c t S i:ℝ))).trans (hm t i)
  have hp' : ∀ a b : T × I, a ≠ b → μ.expect (fun ω => (C ω a:ℝ)*(C ω b:ℝ)) ≤
      q a.1 a.2*q b.1 b.2 := by
    rintro ⟨t,i⟩ ⟨s,j⟩ hne
    by_cases hts : t=s
    · subst s
      have hij : i ≠ j := fun he => hne (he ▸ rfl)
      exact (FiniteLaw.product_marginal ν t (fun S => (c t S i:ℝ)*(c t S j:ℝ))).le.trans (hp t i j hij)
    · exact (FiniteLaw.product_pair ν hts (fun S => (c t S i:ℝ)) (fun S => (c s S j:ℝ))).le.trans
        (by rw [hm,hm])
  have hv' : ∀ a : T × I, μ.variance (fun ω => (C ω a:ℝ)) ≤ q a.1 a.2 := by
    rintro ⟨t,i⟩
    have he : μ.variance (fun ω => (C ω (t,i):ℝ))=(ν t).variance (fun S => (c t S i:ℝ)) := by
      rw [FiniteLaw.variance_eq,FiniteLaw.variance_eq]
      change ((FiniteLaw.product ν).expect (fun ω => (c t (ω t) i:ℝ)^2))-
        ((FiniteLaw.product ν).expect (fun ω => (c t (ω t) i:ℝ)))^2=_
      rw [FiniteLaw.product_marginal ν t (fun S => (c t S i:ℝ)^2),
        FiniteLaw.product_marginal ν t (fun S => (c t S i:ℝ))]
    exact he.le.trans (hv t i)
  refine ⟨μ,C,hc,?_,?_,?_,?_,?_⟩
  · intro t i
    rw [FiniteLaw.expect_mul,hm']
  · intro a b hab
    have he : (fun ω => (g*(C ω a:ℝ))*(g*(C ω b:ℝ)))=
        (fun ω => g^2*((C ω a:ℝ)*(C ω b:ℝ))) := by funext ω; ring
    rw [he,FiniteLaw.expect_mul]
    exact (mul_le_mul_of_nonneg_left (hp' a b hab) (sq_nonneg g)).trans_eq (by ring)
  · intro a
    rw [FiniteLaw.variance_mul]
    exact (mul_le_mul_of_nonneg_left (hv' a) (sq_nonneg g)).trans_eq (by ring)
  · intro ω a; exact mul_nonneg hg (Nat.cast_nonneg _)
  · intro ω hω a
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((hc ω hω a.1).2 a.2)) hg).trans_eq hunit

end MetricKMedian.Preparation
end
end

end OAI
