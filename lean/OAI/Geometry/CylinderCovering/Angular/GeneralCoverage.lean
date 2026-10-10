import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GeneralCapCoverage

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace CylinderCovering.AngularGeneral
open TriangularCovering (point projection)

theorem lowerDirection_ne_zero (τ : ℝ) (D : Data) (j : ℕ) :
    lowerDirection τ D j ≠ 0 := by
  intro h
  have h0 := congrArg (fun z : Space => z 0) h
  norm_num [lowerDirection, point] at h0

theorem upperDirection_ne_zero (τ : ℝ) (D : Data) (j : ℕ) :
    upperDirection τ D j ≠ 0 := by
  intro h
  have h0 := congrArg (fun z : Space => z 1) h
  norm_num [upperDirection, point] at h0

theorem mem_carrier_projected {v : Space} (hv : v ≠ 0)
    {P : Set Space} {p : Space} (hp : p ∈ P) (t : ℝ) :
    p + t • v ∈ carrier (unitDirection v) (projection (unitDirection v) '' P) := by
  have hu : ‖v‖ • unitDirection v = v := by
    rw [unitDirection, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  refine ⟨projection (unitDirection v) p, ⟨p, hp, rfl⟩,
    inner ℝ (unitDirection v) p + t * ‖v‖, ?_⟩
  rw [add_smul, mul_smul, hu, projection]
  module

theorem carrier_projected_eq {v : Space} (hv : v ≠ 0) (P : Set Space) :
    carrier (unitDirection v) (projection (unitDirection v) '' P) =
      {z | ∃ p ∈ P, ∃ t : ℝ, z = p + t • v} := by
  ext z
  constructor
  · rintro ⟨b, ⟨p, hp, rfl⟩, r, rfl⟩
    refine ⟨p, hp, (r - inner ℝ (unitDirection v) p) * ‖v‖⁻¹, ?_⟩
    simp only [projection, unitDirection, mul_smul, sub_smul]
    module
  · rintro ⟨p, hp, t, rfl⟩
    exact mem_carrier_projected hv hp t

theorem lowerCylinder_mem {τ : ℝ} {D : Data} {j : ℕ}
    {q S : ℝ} (hq : q ∈ interval D j) (hS : S ∈ Icc (0 : ℝ) (D.radius j q))
    (x : ℝ) :
    point x (q * S + τ * x * D.alpha j) (S + τ * x * D.beta j) ∈
      lowerCylinder τ D j := by
  have hp : point 0 (q * S) S ∈ lowerIntercept D j := ⟨q, hq, S, hS, rfl⟩
  have hm := mem_carrier_projected (lowerDirection_ne_zero τ D j) hp x
  have heq : point 0 (q * S) S + x • lowerDirection τ D j =
      point x (q * S + τ * x * D.alpha j) (S + τ * x * D.beta j) := by
    ext i
    fin_cases i <;> simp [point, lowerDirection] <;> ring
  exact heq ▸ hm

theorem upperCylinder_mem {τ : ℝ} {D : Data} {j : ℕ}
    {q T : ℝ} (hq : q ∈ interval D j) (hT : T ∈ Icc (0 : ℝ) (D.radius j q))
    (y : ℝ) :
    point (q * T - τ * y * D.alpha j) y (1 - T + τ * y * D.beta j) ∈
      upperCylinder τ D j := by
  have hp : point (q * T) 0 (1 - T) ∈ upperIntercept D j := ⟨q, hq, T, hT, rfl⟩
  have hm := mem_carrier_projected (upperDirection_ne_zero τ D j) hp y
  have heq : point (q * T) 0 (1 - T) + y • upperDirection τ D j =
      point (q * T - τ * y * D.alpha j) y (1 - T + τ * y * D.beta j) := by
    ext i
    fin_cases i <;> simp [point, upperDirection] <;> ring
  exact heq ▸ hm

theorem covers_of_admissible {τ η E : ℝ} {D : Data}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 2) (hE : 0 ≤ E)
    (hη : 0 < η) (hη1 : η ≤ 1 / 480)
    (hsmall : (10 + 4 * E) * τ ≤ η) (hD : Admissible τ η E D) :
    covers τ D := by
  rcases hD with ⟨hN, hn0, hnN, hinc, hnode, ⟨L, hLc, hL0, hL1, hmatch⟩,
    hRc, hRpos, herr⟩
  have hleft : ∀ j < D.count, D.alpha j - D.node j * D.beta j = L (D.node j) := by
    intro j hj
    exact hmatch j hj _ ⟨le_rfl, (hinc j hj).le⟩
  have hright : ∀ j < D.count, D.alpha j - D.node (j + 1) * D.beta j = L (D.node (j + 1)) := by
    intro j hj
    exact hmatch j hj _ ⟨(hinc j hj).le, le_rfl⟩
  intro z hz
  obtain ⟨x, y, t, ht0, ht1, hx, hy, rfl⟩ := hz
  rcases GeneralCap.coordinate_coverage hN D.node D.alpha D.beta (fun j => L (D.node j))
    D.radius hn0 hnN hnode (by simpa [hn0] using hL0) (by simpa [hnN] using hL1)
    hinc hleft hright hτ hτ1 hE hη hη1 hsmall
    (fun j hj q hq => ⟨(herr j hj q hq).1, (herr j hj q hq).2.1⟩)
    (fun j hj q hq => by have he := (abs_le.mp (herr j hj q hq).2.2).1; dsimp [profile] at he; linarith)
    hx hy with h | h
  · obtain ⟨j, hj, q, hq, hS0, hSR, hY⟩ := h
    refine ⟨⟨j, hj⟩, Or.inl ?_⟩
    have hm := lowerCylinder_mem (τ := τ) hq ⟨hS0, hSR⟩ x
    have heq : point x (q * (t - τ * x * D.beta j) + τ * x * D.alpha j)
        ((t - τ * x * D.beta j) + τ * x * D.beta j) = point x y t := by
      rw [mul_comm q, ← hY, sub_add_cancel]
    exact heq ▸ hm
  · obtain ⟨j, hj, q, hq, hT0, hTR, hX⟩ := h
    refine ⟨⟨j, hj⟩, Or.inr ?_⟩
    have hm := upperCylinder_mem (τ := τ) hq ⟨hT0, hTR⟩ y
    have heq : point (q * (1 - t + τ * y * D.beta j) - τ * y * D.alpha j) y
        (1 - (1 - t + τ * y * D.beta j) + τ * y * D.beta j) = point x y t := by
      rw [mul_comm q, ← hX]
      congr 1
      ring
    exact heq ▸ hm

theorem exists_uniform_cover_threshold {η E : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 480) (hE : 0 ≤ E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ δ →
      ∀ D : Data, Admissible τ η E D → covers τ D := by
  obtain ⟨δ, hδ, hsmall⟩ := GeneralCap.exists_positive_threshold hE hη
  refine ⟨δ, hδ, ?_⟩
  intro τ hτ hτδ D hD
  exact covers_of_admissible hτ (hsmall τ hτ hτδ).1 hE hη hη1
    (hsmall τ hτ hτδ).2 hD

end CylinderCovering.AngularGeneral

end

end OAI
