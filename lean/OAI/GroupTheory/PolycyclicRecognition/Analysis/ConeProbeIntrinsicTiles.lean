import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeProbeEndpoints

namespace OAI

/-! # Intrinsic ideal increments of the three actual probe sheets -/

namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {I N : Type*} [Group I] [Group N]

/-- The intrinsic inverse flow is precisely conjugation back by the
normalized neighbor step. -/
theorem intrinsic_probe_inverse_flow (ι : I →* N) (φ : MulAut I) (k : N)
    (hφ : ∀ z, ι (φ z) = k * ι z * k⁻¹) (i : I) :
    k⁻¹ * ι i * k = ι (φ.symm i) := by
  have h := hφ (φ.symm i)
  rw [φ.apply_symm_apply] at h
  rw [h]
  simp [mul_assoc]

/-- The tile covering gives an actual small ideal coordinate, without
choosing a second preimage of a point under the ambient inclusion. -/
theorem intrinsic_probe_tile_mem (φ : MulAut I) (a i : I) (B : Set I)
    (hi : i ∈ a • (φ '' B)) : φ.symm (a⁻¹ * i) ∈ B := by
  obtain ⟨_, ⟨z, hz, rfl⟩, he⟩ := hi
  have hi' : i = a * φ z := he.symm
  rw [hi', inv_mul_cancel_left, φ.symm_apply_apply]
  exact hz

/-- The anchor chain starts at the second original sheet and uses the
reverse-flow anchor controlled by the larger template. -/
theorem coneProbe_intrinsic_anchor_increment
    (ι : I →* N) (φ : MulAut I) (k : N)
    (hφ : ∀ z, ι (φ z) = k * ι z * k⁻¹)
    (S : MulAut N) (n : N) (a : I) :
    (n * S k)⁻¹ * coneProbeSecond S n (ι a) k = S (ι (φ.symm a)) := by
  rw [coneProbe_anchor_increment, intrinsic_probe_inverse_flow ι φ k hφ]

/-- The within-tile chain has the intrinsic ideal coordinate supplied by
that same tile; it keeps the actual endpoint being counted. -/
theorem coneProbe_intrinsic_tile_increment
    (ι : I →* N) (φ : MulAut I) (k : N)
    (hφ : ∀ z, ι (φ z) = k * ι z * k⁻¹)
    (S : MulAut N) (n : N) (a i : I) :
    (coneProbeSecond S n (ι a) k)⁻¹ * coneProbeSecond S n (ι i) k =
      S (ι (φ.symm (a⁻¹ * i))) := by
  rw [coneProbe_tile_increment]
  congr 1
  simpa only [map_mul, map_inv, mul_assoc] using
    intrinsic_probe_inverse_flow ι φ k hφ (a⁻¹ * i)

end PolycyclicRecognition

end OAI
