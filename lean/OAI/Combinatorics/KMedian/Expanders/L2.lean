import Mathlib
import OAI.Combinatorics.KMedian.Expanders.SpectralWalk

namespace OAI

section Inline_PCPL2

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section
variable {S : Type} [Fintype S]

noncomputable def l2 (f : S → ℝ) : ℝ := Real.sqrt (energy f)
lemma l2_nonneg (f : S → ℝ) : 0 ≤ l2 f := Real.sqrt_nonneg _
lemma l2_sq (f : S → ℝ) : l2 f ^ 2=energy f := Real.sq_sqrt (energy_nonneg f)

lemma pairing_le_l2 (f g : S → ℝ) : pairing f g ≤ l2 f*l2 g := by
  have h := pairing_sq_le f g
  have hf := l2_sq f
  have hg := l2_sq g
  have hp := mul_nonneg (l2_nonneg f) (l2_nonneg g)
  rw [← hf,← hg,← mul_pow] at h
  nlinarith

lemma energy_add (f g : S → ℝ) :
    energy (fun x => f x+g x)=energy f+energy g+2*pairing f g := by
  unfold energy pairing
  have he (x : S) : (f x+g x)^2=f x^2+g x^2+2*(f x*g x) := by ring
  simp_rw [he]
  rw [expect_add_distrib,expect_add_distrib,← mul_expect]

lemma l2_add (f g : S → ℝ) : l2 (fun x => f x+g x) ≤ l2 f+l2 g := by
  have h := pairing_le_l2 f g
  have he := l2_sq (fun x => f x+g x)
  rw [energy_add,← l2_sq f,← l2_sq g] at he
  have hn := l2_nonneg (fun x => f x+g x)
  have hf := l2_nonneg f
  have hg := l2_nonneg g
  nlinarith

lemma l2_le_of_energy_le {a : ℝ} (ha : 0 ≤ a) (f g : S → ℝ)
    (h : energy f ≤ a^2*energy g) : l2 f ≤ a*l2 g := by
  rw [← l2_sq f,← l2_sq g,← mul_pow] at h
  have hp := mul_nonneg ha (l2_nonneg g)
  nlinarith [l2_nonneg f]

lemma l2_mono (f g : S → ℝ) (h : energy f ≤ energy g) : l2 f ≤ l2 g :=
  Real.sqrt_le_sqrt h

lemma mean_sq_le_energy [Nonempty S] (f : S → ℝ) : (𝔼 x, f x)^2 ≤ energy f := by
  have h := pairing_sq_le (fun _ : S => (1:ℝ)) f
  simpa [pairing,energy] using h

end

namespace PortGraph
variable {V D : Type} [Fintype V] [Fintype D]
variable (G : PortGraph V D)

lemma energy_adjacency_le [Nonempty D] (f : V → ℝ) : energy (G.adjacency f) ≤ energy f := by
  unfold energy
  calc
    (𝔼 v, G.adjacency f v^2) ≤ 𝔼 v, 𝔼 d, f (G.step v d)^2 :=
      expect_le_expect (fun v _ => mean_sq_le_energy (fun d => f (G.step v d)))
    _ = _ := G.adjacency_mean (fun v => f v^2)

lemma l2_adjacency_le [Nonempty D] (f : V → ℝ) : l2 (G.adjacency f) ≤ l2 f :=
  l2_mono _ _ (G.energy_adjacency_le f)

lemma l2_contracts {ρ : ℝ} (hρ : 0 ≤ ρ) (hG : G.Contracts ρ) (f : V → ℝ)
    (hf : (𝔼 v, f v)=0) : l2 (G.adjacency f) ≤ ρ*l2 f :=
  l2_le_of_energy_le hρ _ _ (hG f hf)

end PortGraph
end MetricKMedian.PCP

end Inline_PCPL2

end OAI
