import Mathlib
import OAI.Geometry.Cannon.Energy.SquareMap
import OAI.Geometry.Cannon.Modulus.IndicesPreimageImage

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval

namespace CannonCharts

open CannonCells

theorem normalized_modulus {X ι : Type*} [Fintype ι]
    (e : Plane → X) (C : ι → Set X) :
    modulus (fun i => (e ∘ squareMap) ⁻¹' C i) CannonRectangle.leftRight =
      modulus C (stripFamily e) := by
  rw [modulus_preimage_image,stripFamily_eq_image]

end CannonCharts

namespace CannonApprox

open CannonCharts CannonRectangle CannonCells

theorem localized_reciprocal_weights {X : Type*} [MetricSpace X] [CompactSpace X]
    (φ : X ≃ₜ CannonCharts.SphereTwo) (d : ℝ) (hd : 0 < d)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (C : (n : ℕ) → ι n → Set X) (hC : ∀ n x, ∃ i, x ∈ C n i)
    (hM : ∀ n, 0 < modulus (C n) (macroFamily (X := X) d)) :
    ∃ E : CannonGrid.Square → X, Topology.IsEmbedding E ∧
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ → ℕ, StrictMono N ∧
        ∃ ρ : (n : ℕ) → ι (N n) → ℝ, ∀ n,
          (∀ i, 0 ≤ ρ n i) ∧ Admissible (fun i => E ⁻¹' C (N n) i) (ρ n) ∧
          (∑ i, (ρ n i)^2) ≤ A / modulus (C (N n)) (macroFamily d) := by
  obtain ⟨e,he,_,c,hc,N,hN,hlocal⟩ := rectangle_modulus_localization φ d hd ι C hC
  let E : CannonGrid.Square → X := e ∘ squareMap
  have hE : Topology.IsEmbedding E := he.isEmbedding.comp squareMap_embedding
  have hweights (n : ℕ) := CannonRectangle.exists_dual_weights
    (fun i => E ⁻¹' C (N n) i) (fun z => hC (N n) (E z))
  choose ρ hρ hadm heq using fun n => (hweights n).2
  refine ⟨E,hE,c⁻¹,inv_pos.mpr hc,N,hN,ρ,?_⟩
  intro n
  refine ⟨hρ n,hadm n,?_⟩
  rw [heq]
  have hloc : c*modulus (C (N n)) (macroFamily d) ≤
      modulus (fun i => E ⁻¹' C (N n) i) leftRight := by
    simpa only [E,normalized_modulus] using hlocal n
  calc
    (modulus (fun i => E ⁻¹' C (N n) i) leftRight)⁻¹ ≤
        (c*modulus (C (N n)) (macroFamily d))⁻¹ :=
      inv_anti₀ (mul_pos hc (hM (N n))) hloc
    _ = c⁻¹ / modulus (C (N n)) (macroFamily d) := by rw [mul_inv,div_eq_mul_inv]

theorem localized_chart_reciprocal_weights {X : Type*} [MetricSpace X] [CompactSpace X]
    (φ : X ≃ₜ CannonCharts.SphereTwo) (d : ℝ) (hd : 0 < d)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (C : (n : ℕ) → ι n → Set X) (hC : ∀ n x, ∃ i, x ∈ C n i)
    (hM : ∀ n, 0 < modulus (C n) (macroFamily (X := X) d)) :
    ∃ e : Plane → X, Topology.IsOpenEmbedding e ∧
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ → ℕ, StrictMono N ∧
        ∃ ρ : (n : ℕ) → ι (N n) → ℝ, ∀ n,
          (∀ i, 0 ≤ ρ n i) ∧
          Admissible (fun i => (e ∘ squareMap) ⁻¹' C (N n) i) (ρ n) ∧
          (∑ i, (ρ n i)^2) ≤ A / modulus (C (N n)) (macroFamily d) := by
  obtain ⟨e,he,_,c,hc,N,hN,hlocal⟩ := rectangle_modulus_localization φ d hd ι C hC
  let E : CannonGrid.Square → X := e ∘ squareMap
  have hweights (n : ℕ) := CannonRectangle.exists_dual_weights
    (fun i => E ⁻¹' C (N n) i) (fun z => hC (N n) (E z))
  choose ρ hρ hadm heq using fun n => (hweights n).2
  refine ⟨e,he,c⁻¹,inv_pos.mpr hc,N,hN,ρ,?_⟩
  intro n
  refine ⟨hρ n,hadm n,?_⟩
  rw [heq]
  have hloc : c*modulus (C (N n)) (macroFamily d) ≤
      modulus (fun i => E ⁻¹' C (N n) i) leftRight := by
    simpa only [E,normalized_modulus] using hlocal n
  calc
    (modulus (fun i => E ⁻¹' C (N n) i) leftRight)⁻¹ ≤
        (c*modulus (C (N n)) (macroFamily d))⁻¹ :=
      inv_anti₀ (mul_pos hc (hM (N n))) hloc
    _ = c⁻¹ / modulus (C (N n)) (macroFamily d) := by rw [mul_inv,div_eq_mul_inv]

end CannonApprox

open Set Filter Topology

end
end
end
end
end
end
end
end
end

end OAI
