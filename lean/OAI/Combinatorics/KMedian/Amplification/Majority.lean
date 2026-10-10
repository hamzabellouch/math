import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweringObjects
import OAI.Combinatorics.KMedian.Expanders.Stopped

namespace OAI

section Inline_PCPMajority

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D A : Type} [Fintype D] [Nonempty D] [Fintype A] [Inhabited A]
variable (G : PortGraph V D) {cap : ℕ} (a : V → Advice D A cap)

noncomputable def vote (n : ℕ) (v : V) (b : A) : ℝ :=
  testRate (fun c : Fin n → D => G.opinion a n v c = b)

noncomputable def mass (t L : ℕ) (v : V) (b : A) : ℝ :=
  ∑ i ∈ range (L+1), Stopped.stopping t * Stopped.survival t ^ i * G.vote a i v b

noncomputable def totalMass (t L : ℕ) : ℝ :=
  ∑ i ∈ range (L+1), Stopped.stopping t * Stopped.survival t ^ i

omit [Nonempty D] [Fintype A] in
lemma vote_nonneg (n : ℕ) (v : V) (b : A) : 0 ≤ G.vote a n v b := testRate_nonneg _

lemma vote_sum (n : ℕ) (v : V) : ∑ b : A, G.vote a n v b = 1 := by
  classical
  unfold vote testRate
  rw [← expect_sum_comm]
  simp

omit [Nonempty D] [Fintype A] in
lemma mass_nonneg (t L : ℕ) (v : V) (b : A) : 0 ≤ G.mass a t L v b := by
  exact sum_nonneg (fun i _ => mul_nonneg
    (mul_nonneg (Stopped.stopping_nonneg _) (pow_nonneg (Stopped.survival_nonneg _) _))
    (G.vote_nonneg a i v b))

lemma mass_sum (t L : ℕ) (v : V) : ∑ b : A, G.mass a t L v b = totalMass t L := by
  unfold mass totalMass
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← mul_sum, vote_sum, mul_one]

omit [Nonempty D] in
lemma exists_plurality (t L : ℕ) (v : V) :
    ∃ b : A, ∀ c : A, G.mass a t L v c ≤ G.mass a t L v b := by
  obtain ⟨b,_,hb⟩ := exists_max_image univ (G.mass a t L v) univ_nonempty
  exact ⟨b, fun c => hb c (mem_univ c)⟩

noncomputable def plurality (t L : ℕ) (v : V) : A :=
  Classical.choose (G.exists_plurality a t L v)

omit [Nonempty D] in
lemma plurality_max (t L : ℕ) (v : V) (b : A) :
    G.mass a t L v b ≤ G.mass a t L v (G.plurality a t L v) :=
  Classical.choose_spec (G.exists_plurality a t L v) b

lemma plurality_mass (t L : ℕ) (v : V) :
    totalMass t L / Fintype.card A ≤ G.mass a t L v (G.plurality a t L v) := by
  have hn : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_iff₀ hn]
  calc
    totalMass t L = ∑ b : A, G.mass a t L v b := (G.mass_sum a t L v).symm
    _ ≤ ∑ b : A, G.mass a t L v (G.plurality a t L v) :=
      sum_le_sum (fun b _ => G.plurality_max a t L v b)
    _ = _ := by simp [mul_comm]

lemma totalMass_nonneg (t L : ℕ) : 0 ≤ totalMass t L :=
  sum_nonneg (fun _ _ => mul_nonneg (Stopped.stopping_nonneg _) (pow_nonneg (Stopped.survival_nonneg _) _))

lemma totalMass_eq (t L : ℕ) : totalMass t L = 1 - Stopped.survival t ^ (L+1) := by
  have h := Stopped.weights_sum t (L+1)
  unfold totalMass
  linarith

end PortGraph

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}

noncomputable def rootHit (a : V → Advice D A cap) (x : V → A) (i j : ℕ)
    (z : (V × (Fin i → D)) × (D × (Fin j → D))) : ℝ := by
  classical
  exact G.edgeHit (C.Bad x) z.1.1 z.2.1 *
    (if G.opinion a i z.1.1 z.1.2 = x z.1.1 then 1 else 0) *
    (if G.opinion a j (G.step z.1.1 z.2.1) z.2.2 = x (G.step z.1.1 z.2.1) then 1 else 0)

noncomputable def cutHit (a : V → Advice D A cap) (x : V → A) (i j : ℕ)
    (p : G.Walk (i+(j+1))) : ℝ := C.rootHit a x i j (PortGraph.Walk.centerEquiv i j p)

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma rootHit_nonneg (a : V → Advice D A cap) (x : V → A) (i j : ℕ) (z) :
    0 ≤ C.rootHit a x i j z := by
  classical
  unfold rootHit
  split_ifs <;> simp_all [PortGraph.edgeHit_bounds]

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma rootHit_le (a : V → Advice D A cap) (x : V → A) (i j : ℕ) (z) :
    C.rootHit a x i j z ≤ G.edgeHit (C.Bad x) z.1.1 z.2.1 := by
  classical
  unfold rootHit
  split_ifs <;> simp_all [PortGraph.edgeHit_bounds]

omit [Nonempty V] [Nonempty D] [Fintype A] in
theorem cutHit_mean (a : V → Advice D A cap) (x : V → A) (i j : ℕ) :
    (𝔼 p : G.Walk (i+(j+1)), C.cutHit a x i j p) =
      𝔼 v : V, 𝔼 d : D, G.edgeHit (C.Bad x) v d * G.vote a i v (x v) *
        G.vote a j (G.step v d) (x (G.step v d)) := by
  classical
  unfold cutHit
  rw [Fintype.expect_equiv (PortGraph.Walk.centerEquiv (G := G) i j)
    (fun p => C.rootHit a x i j (PortGraph.Walk.centerEquiv i j p))
    (C.rootHit a x i j) (fun _ => rfl)]
  rw [expect_prod]
  simp_rw [expect_prod]
  unfold rootHit
  apply expect_congr rfl
  intro v _
  rw [expect_comm univ univ (fun (w : Fin i → D) (d : D) =>
    𝔼 z : Fin j → D, G.edgeHit (C.Bad x) v d *
      (if G.opinion a i v w = x v then 1 else 0) *
      (if G.opinion a j (G.step v d) z = x (G.step v d) then 1 else 0))]
  simp only [← expect_mul, ← mul_expect]
  have hv (k : ℕ) (u : V) (b : A) :
      (𝔼 w : Fin k → D, if G.opinion a k u w = b then (1:ℝ) else 0) = G.vote a k u b := by
    unfold PortGraph.vote testRate
    apply expect_congr rfl
    intro w _
    by_cases hh : G.opinion a k u w = b <;> simp [hh]
  simp_rw [hv]

end PortCSP
end MetricKMedian.PCP

end Inline_PCPMajority

end OAI
