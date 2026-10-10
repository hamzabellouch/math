import OAI.Analysis.MassAction.AffineUniformCertificate
import OAI.Analysis.MassAction.Model

namespace OAI

noncomputable section

namespace Problem326.Affine

/-- Reindex the fixed finite label set by `Fin n`, as required by the
network barrier construction. This theorem is definitionally the uniform
approximation interface there, with the active comparison expanded. -/
theorem FullCertificate.uniform_affine_data {d : ℕ}
    {E : (Fin d → ℝ) → ℝ} (hE : ∀ r, 0 < E r)
    (C : FullCertificate d (-1) 1 E) :
    ∃ n : ℕ, 0 < n ∧ ∃ (r : Fin n → Fin d → ℝ)
      (c : Fin n → ℝ → ℝ) (h₀ : ℝ), 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∀ p : Fin d → ℝ,
        (∀ i, |p i| ≤ 1) → ∀ j : Fin n,
          (∀ k : Fin n,
            dot (r j) (fun i => h ^ p i) + c j h ≤
              dot (r k) (fun i => h ^ p i) + c k h) →
          ∀ i, |p i - r j i| < E (r j) := by
  classical
  let ι := {L : Label d // L ∈ C.labels}
  let : Nonempty ι := ⟨⟨C.nonempty.choose, C.nonempty.choose_spec⟩⟩
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let r : Fin (Fintype.card ι) → Fin d → ℝ := fun j => (e.symm j).val.slope
  let c : Fin (Fintype.card ι) → ℝ → ℝ := fun j => (e.symm j).val.offset
  obtain ⟨h₀, hh₀, huniform⟩ := C.uniform_activity
  refine ⟨Fintype.card ι, Fintype.card_pos, r, c, h₀, hh₀, ?_⟩
  intro h hhpos hhsmall p hp j ha i
  have hpcube : Cube (-1) 1 p := fun k => abs_le.mp (hp k)
  have hactive : Active C.labels (e.symm j).val h (powerPoint h p) := by
    refine ⟨(e.symm j).property, ?_⟩
    intro J hJ
    have hc := ha (e ⟨J, hJ⟩)
    simpa [r, c, Label.value, dot, powerPoint] using hc
  have hnorm := huniform h hhpos hhsmall p hpcube (e.symm j).val
    (e.symm j).property hactive
  have hi := (pi_norm_lt_iff (hE ((e.symm j).val.slope))).mp hnorm i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hi

/-- The full affine-certificate theorem supplies the network's entire
arbitrary-positive-tolerance uniform approximation interface. -/
theorem uniform_affine_data_of_full_certificates {d : ℕ}
    (hfull : ∀ E : (Fin d → ℝ) → ℝ, (∀ r, 0 < E r) →
      Nonempty (FullCertificate d (-1) 1 E)) :
    ∀ E : (Fin d → ℝ) → ℝ, (∀ r, 0 < E r) →
      ∃ n : ℕ, 0 < n ∧ ∃ (r : Fin n → Fin d → ℝ)
        (c : Fin n → ℝ → ℝ) (h₀ : ℝ), 0 < h₀ ∧
        ∀ h : ℝ, 0 < h → h < h₀ → ∀ p : Fin d → ℝ,
          (∀ i, |p i| ≤ 1) → ∀ j : Fin n,
            (∀ k : Fin n,
              dot (r j) (fun i => h ^ p i) + c j h ≤
                dot (r k) (fun i => h ^ p i) + c k h) →
            ∀ i, |p i - r j i| < E (r j) := by
  intro E hE
  obtain ⟨C⟩ := hfull E hE
  exact C.uniform_affine_data hE

end Problem326.Affine

end

end OAI
