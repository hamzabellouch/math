import OAI.Combinatorics.BalancedRyser.Local.LocalLemma
import OAI.Combinatorics.BalancedRyser.Probability.CylinderConditioning

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced.CylinderConditioning

variable {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]

theorem local_lemma (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, μ.real (B i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hind : ∀ i T, i ∉ T → Disjoint T (N i) →
      μ.real (B i ∩ avoid B T) = μ.real (B i) * μ.real (avoid B T)) :
    ∀ S, 0 < μ.real (avoid B S) ∧ ∀ i, i ∉ S →
      μ.real (avoid B S ∩ B i) ≤ x i * μ.real (avoid B S) := by
  have hcore := LocalLemma.avoidance_induction
    (fun S => μ.real (avoid B S)) (fun i => μ.real (B i)) x N
    (by simp) (fun S => measureReal_nonneg) hx0 hx1 hp
    (by
      intro S i hiS
      have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := avoid B S) (hB i)
      rw [avoid_insert]
      have hiT : i ∉ S \ N i := fun hi => hiS (Finset.mem_sdiff.mp hi).1
      have hd : Disjoint (S \ N i) (N i) := by simp [Finset.disjoint_left]
      have hm : μ.real (avoid B S ∩ B i) ≤ μ.real (B i ∩ avoid B (S \ N i)) := by
        apply measureReal_mono _ (by finiteness)
        intro ω hω
        exact ⟨hω.2, avoid_antitone B Finset.sdiff_subset hω.1⟩
      rw [hind i (S \ N i) hiT hd] at hm
      linarith)
  intro S
  refine ⟨(hcore S).1, ?_⟩
  intro i hiS
  have hstep := (hcore S).2 i hiS
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := avoid B S) (hB i)
  rw [avoid_insert] at hstep
  nlinarith

theorem local_lemma_conditional (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, μ.real (B i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hind : ∀ i T, i ∉ T → Disjoint T (N i) →
      μ.real (B i ∩ avoid B T) = μ.real (B i) * μ.real (avoid B T))
    (S : Finset ι) (i : ι) (hi : i ∉ S) :
    μ.real (avoid B S ∩ B i) / μ.real (avoid B S) ≤ x i := by
  have h := local_lemma μ B hB N x hx0 hx1 hp hind S
  exact (div_le_iff₀ h.1).2 (h.2 i hi)

theorem local_lemma_cylinder (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : ι → Set Ω) (hB : ∀ i, MeasurableSet (B i))
    (N : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, μ.real (B i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hind : ∀ i T, i ∉ T → Disjoint T (N i) →
      μ.real (B i ∩ avoid B T) = μ.real (B i) * μ.real (avoid B T))
    (C : Set Ω) (T U : Finset ι) (hdisj : Disjoint T U)
    (hC : μ.real (C ∩ avoid B T) = μ.real C * μ.real (avoid B T)) :
    0 < μ.real (avoid B (T ∪ U)) ∧
      μ.real (C ∩ avoid B (T ∪ U)) / μ.real (avoid B (T ∪ U)) ≤
        μ.real C * ∏ i ∈ U, (1 - x i)⁻¹ := by
  have h := local_lemma μ B hB N x hx0 hx1 hp hind
  exact ⟨(h _).1, conditional_event_bound μ B x hB hx1
    (fun S i hi => (h S).2 i hi) C T U hdisj (h _).1 hC⟩

end Balanced.CylinderConditioning

end OAI
