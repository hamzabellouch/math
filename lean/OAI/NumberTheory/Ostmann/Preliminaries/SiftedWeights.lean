import OAI.NumberTheory.Ostmann.Statement

namespace OAI

namespace Ostmann.SiftedWeights
open Finset

theorem total_mass {ι : Type*} (s : Finset ι) (w : ι → ℝ) :
    ∑ t ∈ s.powerset, ∏ a ∈ t, w a = ∏ a ∈ s, (1+w a) :=
  (Finset.prod_one_add s).symm

theorem first_moment {ι : Type*} (s : Finset ι) (w c : ι → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) :
    ∑ t ∈ s.powerset, (∏ a ∈ t, w a) * (∑ a ∈ t, c a) =
      (∏ a ∈ s, (1+w a)) * (∑ a ∈ s, w a/(1+w a)*c a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hwa := hw a (mem_insert_self _ _)
    have hws : ∀ b ∈ s, 0 ≤ w b := fun b hb => hw b (mem_insert_of_mem hb)
    have hnz : 1+w a ≠ 0 := by positivity
    rw [Finset.sum_powerset_insert ha]
    have hnew :
        (∑ t ∈ s.powerset, (∏ b ∈ insert a t, w b) * (∑ b ∈ insert a t, c b)) =
        w a*c a*(∑ t ∈ s.powerset, ∏ b ∈ t, w b) +
          w a*(∑ t ∈ s.powerset, (∏ b ∈ t, w b)*(∑ b ∈ t, c b)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have hat : a ∉ t := fun h => ha ((mem_powerset.mp ht) h)
      rw [Finset.prod_insert hat, Finset.sum_insert hat]
      ring
    rw [hnew, ih hws, total_mass, Finset.prod_insert ha, Finset.sum_insert ha]
    field_simp
    ring

theorem retain_half {ι : Type*} (s : Finset ι) (w c : ι → ℝ) {L : ℝ}
    (hw : ∀ a ∈ s, 0 ≤ w a) (hc : ∀ a ∈ s, 0 ≤ c a) (hL : 0 < L)
    (hmean : ∑ a ∈ s, w a/(1+w a)*c a ≤ L/2) :
    (∏ a ∈ s, (1+w a))/2 ≤
      ∑ t ∈ s.powerset with (∑ a ∈ t, c a) ≤ L, ∏ a ∈ t, w a := by
  classical
  let W : Finset ι → ℝ := fun t => ∏ a ∈ t, w a
  let C : Finset ι → ℝ := fun t => ∑ a ∈ t, c a
  have hW : ∀ t ∈ s.powerset, 0 ≤ W t := by
    intro t ht
    exact Finset.prod_nonneg (fun a ha => hw a ((mem_powerset.mp ht) ha))
  have hC : ∀ t ∈ s.powerset, 0 ≤ C t := by
    intro t ht
    exact Finset.sum_nonneg (fun a ha => hc a ((mem_powerset.mp ht) ha))
  have hpoint : ∀ t ∈ s.powerset, L*W t ≤
      L*(if C t ≤ L then W t else 0)+W t*C t := by
    intro t ht
    split_ifs with htL
    · exact le_add_of_nonneg_right (mul_nonneg (hW t ht) (hC t ht))
    · have htL' : L ≤ C t := le_of_lt (lt_of_not_ge htL)
      simpa only [mul_zero, zero_add, mul_comm] using mul_le_mul_of_nonneg_left htL' (hW t ht)
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hmoment := first_moment s w c hw
  have hmass := total_mass s w
  have hprod : 0 ≤ ∏ a ∈ s, (1+w a) :=
    Finset.prod_nonneg (fun a ha => by linarith [hw a ha])
  have hmle := mul_le_mul_of_nonneg_left hmean hprod
  change (∑ t ∈ s.powerset, W t*C t) = _ at hmoment
  change (∑ t ∈ s.powerset, W t) = _ at hmass
  rw [hmoment, hmass] at hsum
  have hfilter : (∑ t ∈ s.powerset, if C t ≤ L then W t else 0) =
      ∑ t ∈ s.powerset with (∑ a ∈ t, c a) ≤ L, ∏ a ∈ t, w a := by
    rw [Finset.sum_filter]
  rw [hfilter] at hsum
  nlinarith

end Ostmann.SiftedWeights

end OAI
