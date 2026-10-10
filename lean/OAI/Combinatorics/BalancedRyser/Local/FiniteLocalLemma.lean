import OAI.Combinatorics.BalancedRyser.Local.LocalLemma
import OAI.Combinatorics.BalancedRyser.Probability.FiniteProbability

namespace OAI

namespace Balanced.FiniteProbability

open scoped BigOperators

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]

@[simp] theorem mem_avoid (E : ι → Finset Ω) (S : Finset ι) (ω : Ω) :
    ω ∈ avoid E S ↔ ∀ i ∈ S, ω ∉ E i := by
  simp [avoid]

@[simp] theorem avoid_empty (E : ι → Finset Ω) : avoid E ∅ = Finset.univ := by
  ext ω
  simp

theorem avoid_antitone (E : ι → Finset Ω) {S T : Finset ι} (h : S ⊆ T) :
    avoid E T ⊆ avoid E S := by
  intro ω hω
  simp only [mem_avoid] at hω ⊢
  exact fun i hi => hω i (h hi)

variable [DecidableEq ι]

theorem avoid_insert (E : ι → Finset Ω) (S : Finset ι) (i : ι) :
    avoid E (insert i S) = avoid E S \ E i := by
  ext ω
  simp [and_comm]

omit [Fintype Ω] [DecidableEq Ω] in
theorem mass_nonneg (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (A : Finset Ω) :
    0 ≤ mass w A := Finset.sum_nonneg (fun ω _ => hw ω)

omit [Fintype Ω] [DecidableEq Ω] in
theorem mass_mono (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    {A B : Finset Ω} (h : A ⊆ B) : mass w A ≤ mass w B := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun ω _ _ => hw ω)

omit [Fintype Ω] in
theorem mass_sdiff (w : Ω → ℝ) (A B : Finset Ω) :
    mass w (A \ B) = mass w A - mass w (A ∩ B) := by
  have h := Finset.sum_sdiff (Finset.inter_subset_left (s₁ := A) (s₂ := B)) (f := w)
  have heq : A \ (A ∩ B) = A \ B := by ext ω; simp
  rw [heq] at h
  unfold mass
  linarith

theorem local_lemma (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (htotal : mass w Finset.univ = 1)
    (E : ι → Finset Ω) (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, mass w (E i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hind : ∀ i T, i ∉ T → Disjoint T (N i) →
      mass w (E i ∩ avoid E T) = mass w (E i) * mass w (avoid E T)) :
    ∀ S, 0 < mass w (avoid E S) ∧ ∀ i, i ∉ S →
      mass w (E i ∩ avoid E S) / mass w (avoid E S) ≤ x i := by
  have hcore := LocalLemma.avoidance_induction
    (fun S => mass w (avoid E S)) (fun i => mass w (E i)) x N
    (by simpa using htotal) (fun S => mass_nonneg w hw _) hx0 hx1 hp
    (by
      intro S i hiS
      rw [avoid_insert, mass_sdiff]
      have hiT : i ∉ S \ N i := fun hi => hiS (Finset.mem_sdiff.mp hi).1
      have hd : Disjoint (S \ N i) (N i) := by
        simp [Finset.disjoint_left]
      have hm : mass w (avoid E S ∩ E i) ≤ mass w (E i ∩ avoid E (S \ N i)) := by
        apply mass_mono w hw
        intro ω hω
        simp only [Finset.mem_inter] at hω ⊢
        exact ⟨hω.2, avoid_antitone E Finset.sdiff_subset hω.1⟩
      rw [hind i (S \ N i) hiT hd] at hm
      linarith)
  intro S
  refine ⟨(hcore S).1, ?_⟩
  intro i hiS
  have hstep := (hcore S).2 i hiS
  rw [avoid_insert, mass_sdiff] at hstep
  rw [div_le_iff₀ (hcore S).1]
  have heq : E i ∩ avoid E S = avoid E S ∩ E i := Finset.inter_comm _ _
  rw [heq]
  nlinarith

end Balanced.FiniteProbability

end OAI
