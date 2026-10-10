import Mathlib

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def pmfMean {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (p a).toReal * f a

theorem pmf_weight_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

@[simp] theorem pmfMean_const {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) :
    pmfMean p (fun _ => c) = c := by
  simp only [pmfMean, ← Finset.sum_mul, pmf_weight_sum, one_mul]

theorem pmfMean_congr {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a = g a) : pmfMean p f = pmfMean p g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_add {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a + g a) = pmfMean p f + pmfMean p g := by
  simp only [pmfMean, mul_add, Finset.sum_add_distrib]

theorem pmfMean_sub {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a - g a) = pmfMean p f - pmfMean p g := by
  simp only [pmfMean, mul_sub, Finset.sum_sub_distrib]

theorem pmfMean_mul_const {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => f a * c) = pmfMean p f * c := by
  simp only [pmfMean, ← mul_assoc, ← Finset.sum_mul]

theorem pmfMean_const_mul {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) (f : α → ℝ) :
    pmfMean p (fun a => c * f a) = c * pmfMean p f := by
  simpa only [mul_comm] using pmfMean_mul_const p f c

theorem pmfMean_nonneg {α : Type*} [Fintype α] (p : PMF α) {f : α → ℝ}
    (h : ∀ a ∈ p.support, 0 ≤ f a) : 0 ≤ pmfMean p f := by
  apply Finset.sum_nonneg
  intro a _
  by_cases ha : a ∈ p.support
  · exact mul_nonneg ENNReal.toReal_nonneg (h a ha)
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_mono {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a ≤ g a) : pmfMean p f ≤ pmfMean p g := by
  have hh := pmfMean_nonneg p (fun a ha => sub_nonneg.mpr (h a ha))
  rwa [pmfMean_sub, sub_nonneg] at hh

theorem pmfMean_sq_sub {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => (f a - c) ^ 2) =
      pmfMean p (fun a => f a ^ 2) - 2 * c * pmfMean p f + c ^ 2 := by
  have hpoly : (fun a => (f a - c) ^ 2) =
      (fun a => (f a ^ 2 - (2 * c) * f a) + c ^ 2) := by
    funext a
    ring
  rw [hpoly, pmfMean_add, pmfMean_sub, pmfMean_const_mul, pmfMean_const]

theorem pmfMean_sq_le {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) :
    (pmfMean p f) ^ 2 ≤ pmfMean p (fun a => f a ^ 2) := by
  have h := pmfMean_nonneg p
    (fun a (_ : a ∈ p.support) => sq_nonneg (f a - pmfMean p f))
  rw [pmfMean_sq_sub] at h
  nlinarith

theorem pmfMean_markov_sq {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    pmfMean p (fun a => if ε < |f a| then 1 else 0) ≤
      pmfMean p (fun a => f a ^ 2) / ε ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  rw [← pmfMean_mul_const]
  apply pmfMean_mono
  intro a _
  split_ifs with ha
  · simp only [one_mul]
    exact sq_le_sq.mpr (by rw [abs_of_pos hε]; exact le_of_lt ha)
  · simp only [zero_mul]
    exact sq_nonneg _

@[simp] theorem pmfMean_pure {α : Type*} [Fintype α] (a : α) (f : α → ℝ) :
    pmfMean (PMF.pure a) f = f a := by
  classical
  simp [pmfMean, PMF.pure_apply, apply_ite]

theorem pmfMean_bind {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    pmfMean (p.bind q) f = pmfMean p (fun a => pmfMean (q a) f) := by
  classical
  simp only [pmfMean, PMF.bind_apply, tsum_fintype]
  have hfin (b : β) (a : α) : p a * q a b ≠ ⊤ :=
    ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)
  simp_rw [ENNReal.toReal_sum (fun a _ => hfin _ a), Finset.sum_mul,
    ENNReal.toReal_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

@[simp] theorem pmfMean_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ) :
    pmfMean (p.map g) f = pmfMean p (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, pmfMean_bind]
  simp

theorem pmfMean_uniformOfFinset {α : Type*} [Fintype α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    pmfMean (PMF.uniformOfFinset s hs) f = (∑ a ∈ s, f a) / (s.card : ℝ) := by
  classical
  simp only [pmfMean, PMF.uniformOfFinset_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_univ_mem]
  simp only [div_eq_mul_inv, mul_comm, Finset.sum_mul]

end SharpTerminalLeave
end
end

end OAI
