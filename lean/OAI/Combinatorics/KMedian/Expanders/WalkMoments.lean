import Mathlib
import OAI.Combinatorics.KMedian.Expanders.SpectralWalk

namespace OAI

section Inline_PCPWalkMoments

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {D : Type} [Fintype D]

theorem expect_word_succ (n : ℕ) (f : (Fin (n+1) → D) → ℝ) :
    (𝔼 c, f c) = 𝔼 d : D, 𝔼 c : Fin n → D, f (Fin.cons d c) := by
  have h := Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n+1) => D))
    (fun p : D × (Fin n → D) => f (Fin.cons p.1 p.2)) f (fun _ => rfl)
  rw [← h, expect_prod]

theorem mean_sq_le_support_energy {S : Type} [Fintype S] (f : S → ℝ) :
    (𝔼 s, f s)^2 ≤ testRate (fun s => f s ≠ 0) * energy f := by
  classical
  let g : S → ℝ := fun s => if f s ≠ 0 then 1 else 0
  have h := pairing_sq_le g f
  have hp : pairing g f = 𝔼 s, f s := by
    apply expect_congr rfl
    intro s _
    by_cases hh : f s = 0 <;> simp [g,hh]
  have hg : energy g = testRate (fun s => f s ≠ 0) := by
    apply expect_congr rfl
    intro s _
    by_cases hh : f s = 0 <;> simp [g,hh]
  rwa [hp,hg] at h

namespace PortGraph
variable {V : Type} [Fintype V] [Nonempty V] [Nonempty D]
variable (G : PortGraph V D) (bad : V × D → Prop)

noncomputable def edgeHit (_G : PortGraph V D) (v : V) (d : D) : ℝ := by
  classical
  exact if bad (v,d) then 1 else 0

noncomputable def edgeMass (v : V) : ℝ := 𝔼 d, G.edgeHit bad v d

noncomputable def badCount : (n : ℕ) → V → (Fin n → D) → ℝ
  | 0, _, _ => 0
  | n+1, v, c => G.edgeHit bad v (c 0) + badCount n (G.step v (c 0)) (fun i => c i.succ)

noncomputable def countMean (n : ℕ) (v : V) : ℝ := 𝔼 c, G.badCount bad n v c

noncomputable def countSquareMean (n : ℕ) : ℝ := 𝔼 v, 𝔼 c, (G.badCount bad n v c)^2

omit [Fintype D] [Fintype V] [Nonempty V] [Nonempty D] in
@[simp] theorem edgeHit_sq (v : V) (d : D) : G.edgeHit bad v d ^ 2 = G.edgeHit bad v d := by
  classical
  unfold edgeHit
  split_ifs <;> norm_num

omit [Fintype D] [Fintype V] [Nonempty V] [Nonempty D] in
theorem edgeHit_bounds (v : V) (d : D) : 0 ≤ G.edgeHit bad v d ∧ G.edgeHit bad v d ≤ 1 := by
  classical
  unfold edgeHit
  split_ifs <;> norm_num

omit [Fintype V] [Nonempty V] in
theorem edgeMass_bounds (v : V) : 0 ≤ G.edgeMass bad v ∧ G.edgeMass bad v ≤ 1 :=
  ⟨expect_nonneg (fun d _ => (G.edgeHit_bounds bad v d).1),
    expect_le univ_nonempty (fun d _ => (G.edgeHit_bounds bad v d).2)⟩

omit [Nonempty V] [Nonempty D] in
theorem edgeMass_mean : (𝔼 v, G.edgeMass bad v) = testRate bad := by
  rw [testRate_prod (fun v d => bad (v,d))]
  rfl

omit [Fintype D] [Fintype V] [Nonempty V] [Nonempty D] in
@[simp] theorem badCount_cons (n : ℕ) (v : V) (d : D) (c : Fin n → D) :
    G.badCount bad (n+1) v (Fin.cons d c) = G.edgeHit bad v d + G.badCount bad n (G.step v d) c := by
  simp only [badCount, Fin.cons_zero, Fin.cons_succ]

omit [Fintype V] [Nonempty V] [Nonempty D] in
@[simp] theorem countMean_zero : G.countMean bad 0 = fun _ => 0 := by
  funext v
  simp [countMean,badCount]

omit [Fintype V] [Nonempty V] in
theorem countMean_succ (n : ℕ) : G.countMean bad (n+1) =
    fun v => G.edgeMass bad v + G.adjacency (G.countMean bad n) v := by
  funext v
  rw [countMean, expect_word_succ]
  simp only [badCount_cons, expect_add_distrib, Fintype.expect_const]
  rfl

omit [Nonempty V] in
theorem countMean_mean (n : ℕ) :
    (𝔼 v, G.countMean bad n v) = n * testRate bad := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [countMean_succ, expect_add_distrib, edgeMass_mean, adjacency_mean, ih]
    push_cast
    ring

omit [Fintype V] [Nonempty V] in
theorem countMean_sum (n : ℕ) :
    G.countMean bad n = fun v => ∑ k ∈ range n, G.propagate k (G.edgeMass bad) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [countMean_succ, ih]
    funext v
    rw [sum_range_succ']
    unfold adjacency
    rw [expect_sum_comm]
    simp only [propagate_zero, propagate_succ, adjacency]
    ring

omit [Nonempty V] [Nonempty D] in
theorem edge_cross (hsym : ∀ p, bad (G.rotate p) ↔ bad p) (f : V → ℝ) :
    (𝔼 v, 𝔼 d, G.edgeHit bad v d * f (G.step v d)) = pairing (G.edgeMass bad) f := by
  rw [← expect_prod (fun p : V × D => G.edgeHit bad p.1 p.2 * f (G.step p.1 p.2))]
  have hh := Fintype.expect_equiv G.rotate
    (fun p : V × D => G.edgeHit bad p.1 p.2 * f (G.step p.1 p.2))
    (fun p : V × D => G.edgeHit bad p.1 p.2 * f p.1) (by
      intro p
      change _ = G.edgeHit bad (G.step p.1 p.2) (G.back p.1 p.2) * f (G.step p.1 p.2)
      congr 1
      unfold edgeHit
      rw [show (G.step p.1 p.2,G.back p.1 p.2) = G.rotate p from rfl, hsym p])
  rw [hh, expect_prod]
  unfold pairing edgeMass
  simp only [← expect_mul]

theorem edge_future_le (hG : G.Contracts (1/2)) (n : ℕ) :
    pairing (G.edgeMass bad) (G.countMean bad n) ≤ n * (testRate bad)^2 + 2 * testRate bad := by
  rw [countMean_sum]
  unfold pairing
  simp_rw [mul_sum]
  rw [expect_sum_comm]
  have hc (k : ℕ) :
      pairing (G.edgeMass bad) (G.propagate k (G.edgeMass bad)) ≤
        (testRate bad)^2 + (1/2 : ℝ)^k * testRate bad := by
    simpa only [edgeMass_mean] using
      G.bounded_correlation (by norm_num : (0:ℝ) ≤ 1/2) hG k (G.edgeMass bad) (G.edgeMass_bounds bad)
  calc
    _ ≤ ∑ k ∈ range n, ((testRate bad)^2 + (1/2 : ℝ)^k * testRate bad) :=
      sum_le_sum (fun k _ => hc k)
    _ = n * (testRate bad)^2 + (∑ k ∈ range n, (1/2 : ℝ)^k) * testRate bad := by
      rw [sum_add_distrib, ← sum_mul]
      simp
    _ ≤ n * (testRate bad)^2 + 2 * testRate bad := by
      have h := mul_le_mul_of_nonneg_right (sum_geometric_two_le n) (testRate_nonneg bad)
      linarith

omit [Nonempty V] in
theorem countSquareMean_succ (hsym : ∀ p, bad (G.rotate p) ↔ bad p) (n : ℕ) :
    G.countSquareMean bad (n+1) = G.countSquareMean bad n + testRate bad +
      2 * pairing (G.edgeMass bad) (G.countMean bad n) := by
  have hfut : (𝔼 v, 𝔼 d, 𝔼 c, (G.badCount bad n (G.step v d) c)^2) =
      G.countSquareMean bad n := G.adjacency_mean (fun v : V => 𝔼 c : Fin n → D, (G.badCount bad n v c)^2)
  have hcross := G.edge_cross bad hsym (G.countMean bad n)
  have hbase : (𝔼 v, 𝔼 d, (G.edgeHit bad v d)^2) = testRate bad := by
    simp only [edgeHit_sq]
    exact G.edgeMass_mean bad
  calc
    _ = (𝔼 v, 𝔼 d, (G.edgeHit bad v d)^2) +
        2 * (𝔼 v, 𝔼 d, G.edgeHit bad v d * G.countMean bad n (G.step v d)) +
        (𝔼 v, 𝔼 d, 𝔼 c, (G.badCount bad n (G.step v d) c)^2) := by
      unfold countSquareMean
      have hs (a b : ℝ) : (a+b)^2 = a^2 + 2*(a*b) + b^2 := by ring
      simp_rw [expect_word_succ n, badCount_cons, hs, expect_add_distrib]
      simp only [Fintype.expect_const, ← mul_expect, countMean]
    _ = _ := by rw [hfut,hcross,hbase]; ring

theorem countSquareMean_le (hsym : ∀ p, bad (G.rotate p) ↔ bad p)
    (hG : G.Contracts (1/2)) (n : ℕ) :
    G.countSquareMean bad n ≤ 5*n*testRate bad + (n:ℝ)^2*(testRate bad)^2 := by
  induction n with
  | zero => simp [countSquareMean,badCount]
  | succ n ih =>
    rw [G.countSquareMean_succ bad hsym n]
    have hc := G.edge_future_le bad hG n
    push_cast
    nlinarith [sq_nonneg (testRate bad)]

omit [Nonempty V] [Nonempty D] in
theorem witness_second_moment (n : ℕ) (X : V × (Fin n → D) → ℝ)
    (hX : ∀ p, 0 ≤ X p ∧ X p ≤ G.badCount bad n p.1 p.2) :
    energy X ≤ G.countSquareMean bad n := by
  rw [energy, expect_prod]
  apply expect_le_expect
  intro v _
  apply expect_le_expect
  intro c _
  exact sq_le_sq₀ (hX (v,c)).1 ((hX (v,c)).1.trans (hX (v,c)).2) |>.2 (hX (v,c)).2

end PortGraph
end MetricKMedian.PCP

end Inline_PCPWalkMoments

end OAI
