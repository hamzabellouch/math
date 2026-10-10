import Mathlib
import OAI.Combinatorics.KMedian.Preparation.CoupledPreparation
import OAI.Combinatorics.KMedian.Sparse.SparsePreparedProbability
import OAI.Combinatorics.KMedian.Sparse.SparseBundleEncoding
import OAI.Combinatorics.KMedian.Sparse.SparseOuterReal

namespace OAI


                                                
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

theorem request_mean (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (ha : ∀ e, 0 ≤ a e ∧ a e ≤ 1) (hq : ∀ e, 0 ≤ q e) {g : ℝ} (hg : 0 ≤ g)
    (j : Fin n) (e : Fin m) :
    (SparseOuterLaw.law D a q ha hq).realIndex.expect (fun b =>
      g * (requests D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val] j e : ℝ)) ≤
      if j ∈ D e then g * (q e : ℝ) else 0 := by
  calc
    _ ≤ (SparseOuterLaw.law D a q ha hq).realIndex.expect (fun b =>
        g * (activation D q (SparseOuterLaw.law D a q ha hq).states[b.val] e j : ℝ)) := by
      apply FiniteLaw.expect_mono
      intro b
      apply mul_le_mul_of_nonneg_left _ hg
      have h := requests_le D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val] j e
      have he := activationCount_cast D q (SparseOuterLaw.law D a q ha hq).states[b.val] e j
      have hr : (requests D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val] j e : ℚ) ≤
          activation D q (SparseOuterLaw.law D a q ha hq).states[b.val] e j := by
        rw [← he]
        exact_mod_cast h
      exact_mod_cast hr
    _ = _ := by
      rw [FiniteLaw.expect_mul, activation_real_mean]
      split_ifs <;> simp

theorem opening_cast (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (g : ℝ) :
    g * (opening D a q Δ z : ℝ) =
      (∑ e, (a e : ℝ) * (g * (outsideCount q z e : ℝ))) +
      (∑ j, g * (total D q Δ z j : ℝ)) := by
  simp only [opening, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast,
    mul_add, mul_sum]
  congr 1
  exact sum_congr rfl (fun _ _ => by ring)

noncomputable def coupled
    (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (ha : ∀ e, 0 ≤ a e ∧ a e ≤ 1) (hq : ∀ e, 0 ≤ q e) (g : ℚ)
    (δ : Fin n → ℝ) (γ B : ℝ)
    (hg : 0 < g) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (heven : Even Δ)
    (hunit : g * (Δ : ℚ) = 1)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hδ : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1/8)
    (hpunit : ∀ j, (p j : ℝ) + δ j = 1)
    (hmean : ∀ j, (g : ℝ) * (targetMean D q j : ℝ) = (1+γ) * δ j)
    (hplan : (g : ℝ) * (((n : ℚ) * (Δ : ℚ) +
      (∑ e, SparseSignedPreparation.signed D a e * q e) : ℚ) : ℝ) = B - γ * ∑ j, δ j) :
    Preparation.CoupledLaw D (fun e => (a e : ℝ)) (fun e => (g : ℝ) * (q e : ℝ))
      P (fun i => (y i : ℝ)) (fun j => (p j : ℝ)) δ (g : ℝ) γ B Δ := by
  let μ := SparseOuterLaw.law D a q ha hq
  let z := fun b : Fin μ.length => μ.states[b.val]
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have huR : (g : ℝ) * (Δ : ℝ) = 1 := by exact_mod_cast hunit
  refine {
    Ω := Fin μ.length
    ν := μ.realIndex
    κ := fun b => SparseRescaledInner.encodedLaw P y p (total D q Δ (z b))
    O := fun b => outsideCount q (z b)
    N := fun b => nominalMass q (g : ℝ) (z b)
    R := fun b => requests D q Δ (z b)
    K := fun b => total D q Δ (z b)
    C := fun b => SparseRescaledInner.encodedCount P y p (total D q Δ (z b))
    open_cap := ?_
    open_zero := ?_
    nominal_nonneg := fun b _ e => nominalMass_nonneg q hgR.le (z b) e
    nominal_cap := fun b _ e => nominalMass_cap D a q ha hq hgR.le b e
    nominal_mean := fun e => nominalMass_mean D a q ha hq (g : ℝ) e
    nominal_variance := fun e => nominalMass_variance D a q ha hq (g : ℝ) e
    nominal_pair := fun e h heh => nominalMass_pair D a q ha hq (g : ℝ) e h heh
    request_cap := ?_
    request_target := ?_
    request_mean := fun j e => request_mean D a q Δ ha hq hgR.le j e
    exact_total := fun b j => exact_total D q Δ (z b) j
    half := fun b j => total_half D q Δ (z b) j hgR heven huR
    total_cap := fun b j => total_le D q Δ (z b) j
    total_deviation := ?_
    pieces := fun b ξ hξ => SparseRescaledInner.encoded_pieces P y p _ Δ hy hp hm
      (total_le D q Δ (z b)) ξ hξ
    piece_mean := fun b j i => SparseRescaledInner.encoded_mean P y p _ Δ (g : ℝ) hy hp hm
      (total_le D q Δ (z b)) j i
    piece_pair := fun b u v huv => SparseRescaledInner.encoded_pair P y p _ Δ (g : ℝ) hy hp hm
      (total_le D q Δ (z b)) u v huv
    piece_variance := fun b u => SparseRescaledInner.encoded_variance P y p _ Δ (g : ℝ) hy hp hm
      (total_le D q Δ (z b)) u
    budget := ?_ }
  · intro b _ e he
    have he' : q e ≤ (Δ : ℚ) := by
      have hr : (q e : ℝ) ≤ (Δ : ℝ) := (mul_le_mul_iff_right₀ hgR).mp (he.trans_eq huR.symm)
      exact_mod_cast hr
    have hcap := outsideCount_le_at D a q ha hq Δ b e he'
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hgR.le).trans_eq huR
  · intro b _ e he
    have hz : q e = 0 := by
      have hr : (q e : ℝ) = 0 := (mul_eq_zero.mp he).resolve_left hgR.ne'
      exact_mod_cast hr
    exact Nat.eq_zero_of_le_zero (outsideCount_le_at D a q ha hq 0 b e (by simp [hz]))
  · intro b _ j e
    exact (requests_le D q Δ (z b) j e).trans (activationCount_le D a q ha hq b e j)
  · intro b j e hj
    have h := requests_le D q Δ (z b) j e
    have hz := activationCount_support D a q ha hq b e j hj
    exact Nat.eq_zero_of_le_zero (h.trans_eq hz)
  · intro j
    exact total_deviation D a q Δ ha hq g (fun j => (p j : ℝ)) δ hg hγ.le heven hunit hδ
      (fun j => (hδ1 j).trans (by norm_num)) hpunit hmean j
  · have hsmall : ∀ j, (1+γ) * δ j ≤ 1/4 := by
      intro j
      calc
        _ ≤ 2 * δ j := mul_le_mul_of_nonneg_right (by linarith only [hγ1]) (hδ j)
        _ ≤ 1/4 := by linarith only [hδ1 j]
    have h := opening_probability D a q Δ ha hq g δ hg hγ heven hunit hδ hmean hsmall hplan
    simpa only [opening_cast] using h

end MetricKMedian.SparsePrepared
end

end OAI
