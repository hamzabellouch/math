import Mathlib
import OAI.Combinatorics.KMedian.Amplification.Majority

namespace OAI

section Inline_PCPPoweringMean

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Stopped
lemma weight_pair (t i j : ℕ) :
    stopping t * survival t ^ (i+(j+1)) =
      (t:ℝ) * (stopping t * survival t ^ i) * (stopping t * survival t ^ j) := by
  have hq : survival t = (t:ℝ) * stopping t := by unfold survival stopping; ring
  rw [pow_add, pow_succ, hq]
  ring

lemma atom_expect (t cap k : ℕ) (hk : k < cap) (b : ℝ) :
    (𝔼 c : Fin cap → Fin (t+1), if length t cap c = k then b else 0) =
      stopping t * survival t ^ k * b := by
  rw [expectation t cap (fun n => if n=k then b else 0)]
  have hc : cap ≠ k := by omega
  simp only [ite_eq_right hc,mul_zero,add_zero]
  rw [sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp [mem_range,hk]
end Stopped

namespace PortGraph.Walk
variable {V D : Type} {G : PortGraph V D}
def cast {n m : ℕ} (h : n=m) (p : G.Walk n) : G.Walk m := h ▸ p
@[simp] lemma cast_rfl {n : ℕ} (p : G.Walk n) : p.cast rfl = p := rfl
@[simp] lemma cast_vertex {n m : ℕ} (h : n=m) (p : G.Walk n) (i : Fin (m+1)) :
    (p.cast h).vertex i = p.vertex ⟨i.val,by omega⟩ := by subst m; rfl
@[simp] lemma cast_port {n m : ℕ} (h : n=m) (p : G.Walk n) (i : Fin m) :
    (p.cast h).port i = p.port ⟨i.val,by omega⟩ := by subst m; rfl
end PortGraph.Walk

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}

noncomputable def diagHit (a : V → Advice D A cap) (x : V → A) (i j n : ℕ)
    (p : G.Walk n) : ℝ :=
  if h : n=i+(j+1) then C.cutHit a x i j (p.cast h) else 0

omit [Nonempty V] [Nonempty D] [Fintype A] in
lemma diagHit_mean (a : V → Advice D A cap) (x : V → A) (i j n : ℕ) :
    (𝔼 p : G.Walk n, C.diagHit a x i j n p) =
      if n=i+(j+1) then (𝔼 p : G.Walk (i+(j+1)), C.cutHit a x i j p) else 0 := by
  classical
  by_cases h : n=i+(j+1)
  · subst n
    simp [diagHit]
  · simp [diagHit,h]

noncomputable def witness (a : V → Advice D A cap) (x : V → A) (L n : ℕ)
    (p : G.Walk n) : ℝ :=
  ∑ i ∈ range (L+1), ∑ j ∈ range (L+1), C.diagHit a x i j n p

noncomputable def stoppedWitness (a : V → Advice D A cap) (x : V → A) (t L : ℕ)
    (z : (Fin cap → Fin (t+1)) × G.Walk cap) : ℝ :=
  C.witness a x L (Stopped.length t cap z.1)
    (z.2.segment 0 (Stopped.length t cap z.1) (by have := Stopped.length_le t cap z.1; omega))

omit [Nonempty V] [Fintype A] in
lemma stopped_diag_mean (a : V → Advice D A cap) (x : V → A) (t i j : ℕ)
    (hij : i+(j+1) < cap) :
    (𝔼 c : Fin cap → Fin (t+1), 𝔼 p : G.Walk cap,
      C.diagHit a x i j (Stopped.length t cap c)
        (p.segment 0 (Stopped.length t cap c) (by have := Stopped.length_le t cap c; omega))) =
      Stopped.stopping t * Stopped.survival t ^ (i+(j+1)) *
        (𝔼 p : G.Walk (i+(j+1)), C.cutHit a x i j p) := by
  calc
    _ = 𝔼 c : Fin cap → Fin (t+1), 𝔼 p : G.Walk (Stopped.length t cap c),
        C.diagHit a x i j (Stopped.length t cap c) p := by
      apply expect_congr rfl
      intro c _
      exact PortGraph.Walk.prefix_expect_le _ _ (Stopped.length_le t cap c) _
    _ = _ := by
      simp_rw [diagHit_mean]
      exact Stopped.atom_expect _ _ _ hij _

omit [Nonempty V] [Fintype A] in
theorem witness_mean_eq (a : V → Advice D A cap) (x : V → A) (t L : ℕ)
    (hcap : 2*L+1 < cap) :
    (𝔼 z, C.stoppedWitness a x t L z) =
      (t:ℝ) * (𝔼 v : V, 𝔼 d : D, G.edgeHit (C.Bad x) v d *
        G.mass a t L v (x v) * G.mass a t L (G.step v d) (x (G.step v d))) := by
  unfold stoppedWitness witness
  rw [expect_prod]
  simp_rw [expect_sum_comm]
  calc
    _ = ∑ i ∈ range (L+1), ∑ j ∈ range (L+1),
        Stopped.stopping t * Stopped.survival t ^ (i+(j+1)) *
          (𝔼 p : G.Walk (i+(j+1)), C.cutHit a x i j p) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      exact C.stopped_diag_mean a x t i j (by simp only [mem_range] at hi hj; omega)
    _ = _ := by
      simp_rw [cutHit_mean,Stopped.weight_pair,PortGraph.mass,mul_sum,sum_mul,
        expect_sum_comm,mul_expect]
      simp_rw [mul_sum,mul_expect]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      apply expect_congr rfl
      intro v _
      apply expect_congr rfl
      intro d _
      ring

omit [Nonempty V] in
theorem witness_mean_ge (a : V → Advice D A cap) (t L : ℕ) (hcap : 2*L+1 < cap) :
    (t:ℝ) * testRate (C.Bad (G.plurality a t L)) *
      (PortGraph.totalMass t L / Fintype.card A)^2 ≤
        𝔼 z, C.stoppedWitness a (G.plurality a t L) t L z := by
  rw [witness_mean_eq _ _ _ _ _ hcap]
  let x := G.plurality a t L
  let b : ℝ := PortGraph.totalMass t L / Fintype.card A
  have hb : 0 ≤ b := div_nonneg (PortGraph.totalMass_nonneg _ _) (Nat.cast_nonneg _)
  have hm (v : V) : b ≤ G.mass a t L v (x v) := G.plurality_mass a t L v
  have h : testRate (C.Bad x) * b^2 ≤
      𝔼 v : V, 𝔼 d : D, G.edgeHit (C.Bad x) v d *
        G.mass a t L v (x v) * G.mass a t L (G.step v d) (x (G.step v d)) := by
    rw [← G.edgeMass_mean (C.Bad x)]
    unfold PortGraph.edgeMass
    rw [expect_mul]
    apply expect_le_expect
    intro v _
    rw [expect_mul]
    apply expect_le_expect
    intro d _
    have hp := mul_le_mul (hm v) (hm (G.step v d)) hb (G.mass_nonneg a t L v (x v))
    have he := mul_le_mul_of_nonneg_left hp (G.edgeHit_bounds (C.Bad x) v d).1
    nlinarith only [he]
  have ht := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg t : (0:ℝ) ≤ t)
  simpa only [mul_assoc] using ht

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringMean

end OAI
