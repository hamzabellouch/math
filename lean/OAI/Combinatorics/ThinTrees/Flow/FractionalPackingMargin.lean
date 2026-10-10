import Mathlib
import OAI.Combinatorics.ThinTrees.Flow.FractionalOrientation
import OAI.Combinatorics.ThinTrees.Flow.ParallelCopies

namespace OAI

/-! Fractional packing margin. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

lemma partCount_le_vertices (p : Setoid (Fin n)) : partCount p ≤ n := by
  simpa [partCount] using Fintype.card_le_of_surjective (Quotient.mk p) Quotient.mk_surjective

lemma capacity_nonneg (G : MultiGraph n m) {c : Fin m → ℝ} (hc : ∀e, 0 ≤ c e)
    (p : Setoid (Fin n)) : 0 ≤ capacity G.left G.right c p :=
  sum_nonneg fun e _ => mul_nonneg (hc e) (crossingIndicator_nonneg p _ _)

lemma floor_capacity_lower (G : MultiGraph n m) (c : Fin m → ℝ) (N : ℕ)
    (p : Setoid (Fin n)) :
    (N:ℝ)*capacity G.left G.right c p-m ≤
      capacity G.left G.right (fun e => (⌊(N:ℝ)*c e⌋₊:ℕ)) p := by
  rw [capacity_eq_sum,capacity_eq_sum]
  have h := sum_le_sum (s:=Partitions.crossing G p) (fun e _ =>
    show (N:ℝ)*c e-1 ≤ (⌊(N:ℝ)*c e⌋₊:ℕ) by linarith [Nat.lt_floor_add_one ((N:ℝ)*c e)])
  simp only [sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one] at h
  have hc : (Partitions.crossing G p).card ≤ m :=
    (card_le_card (subset_univ _)).trans_eq (card_univ.trans (Fintype.card_fin m))
  have hc' : ((Partitions.crossing G p).card:ℝ) ≤ m := by exact_mod_cast hc
  linarith only [h,hc']

lemma FlowPoint.zero_exact (G : MultiGraph n m) {c : Fin m → ℝ} (hc : ∀e, 0 ≤ c e) :
    (FlowPoint.mk (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0)).Exact G c 0 := by
  simp [FlowPoint.Exact,out,hc]

theorem exact_flow_of_margin (G : MultiGraph n m) (hn : 0 < n)
    (c : Fin m → ℝ) (hc : ∀e, 0 ≤ c e) {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ)
    (hp : ∀p : Setoid (Fin n), (q+δ)*((partCount p:ℝ)-1) ≤ capacity G.left G.right c p) :
    ∃F : FlowPoint n m, F.Exact G c q := by
  rcases eq_or_lt_of_le hq with hq0|hq0
  · subst q
    exact ⟨_,FlowPoint.zero_exact G hc⟩
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨N,hN⟩ := exists_nat_gt (((m:ℝ)+n+1)/δ)
  have hNδ : (m:ℝ)+n+1 < (N:ℝ)*δ := (div_lt_iff₀ hδ).mp hN
  have hN0 : 0 < (N:ℝ) := by
    by_contra h
    have hh : (N:ℝ)*δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hδ.le
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hh,hNδ,hm0,hn0]
  let a : Fin m → ℕ := fun e => ⌊(N:ℝ)*c e⌋₊
  let r : ℕ := ⌈(N:ℝ)*q⌉₊
  have hrlo : (N:ℝ)*q ≤ r := Nat.le_ceil _
  have hrhi : (r:ℝ) ≤ (N:ℝ)*q+1 := (Nat.ceil_lt_add_one (mul_nonneg hN0.le hq)).le
  have hrpos : 0 < (r:ℝ) := (mul_pos hN0 hq0).trans_le hrlo
  have hr : 0 < r := by exact_mod_cast hrpos
  have hpack : (copies G a).TreePackable univ r := by
    apply packing_of_partitions _ hn hr
    intro p
    by_cases htop : p=⊤
    · subst p
      simp [capacity,crossingIndicator,partCount_top]
    · have hd : (2:ℝ) ≤ partCount p := by exact_mod_cast two_le_partCount htop
      have hdhi : (partCount p:ℝ) ≤ n := by exact_mod_cast partCount_le_vertices p
      rw [capacity_unit,capacity_copies]
      have hf := floor_capacity_lower G c N p
      have hpN := mul_le_mul_of_nonneg_left (hp p) hN0.le
      have hround := mul_le_mul_of_nonneg_right hrhi (show 0 ≤ (partCount p:ℝ)-1 by linarith)
      have hδgain := mul_le_mul_of_nonneg_left (show 1 ≤ (partCount p:ℝ)-1 by linarith)
        (mul_nonneg hN0.le hδ.le)
      change (r:ℝ)*((partCount p:ℝ)-1) ≤ capacity G.left G.right (fun e => (a e:ℝ)) p
      change (N:ℝ)*capacity G.left G.right c p-m ≤
        capacity G.left G.right (fun e => (a e:ℝ)) p at hf
      nlinarith only [hf,hpN,hround,hδgain,hNδ,hdhi]
  obtain ⟨F,hF⟩ := packed_exact_flow (copies G a) hn hpack
  have hpush := hF.push G (copies G a) (copyProjection a) (fun _ => rfl) (fun _ => rfl)
  simp only [fiber_copies] at hpush
  have hs := hpush.scale (div_nonneg hq hrpos.le)
  rw [div_mul_cancel₀ q (ne_of_gt hrpos)] at hs
  refine ⟨_,hs.mono fun e => ?_⟩
  have ha : (a e:ℝ) ≤ (N:ℝ)*c e := Nat.floor_le (mul_nonneg hN0.le (hc e))
  have hα : q/(r:ℝ)*N ≤ 1 := by
    rw [div_mul_eq_mul_div,div_le_one hrpos]
    simpa [mul_comm] using hrlo
  calc
    _ ≤ (q/(r:ℝ))*((N:ℝ)*c e) := mul_le_mul_of_nonneg_left ha (div_nonneg hq hrpos.le)
    _ = ((q/(r:ℝ))*N)*c e := by ring
    _ ≤ c e := by simpa using mul_le_mul_of_nonneg_right hα (hc e)

end
end AlgorithmicThinTrees.Orientations
end

end OAI
