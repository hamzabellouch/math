import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTerminal

namespace OAI

/-! Canonical choice of the genuine outgoing solution on a prescribed exterior ray. -/

open Set Filter
namespace DefocusingNLS

def HasRadialExterior (ν : ℂ) (n : ℕ) (m : ℂ) (L : ℝ) : Prop :=
  ∃ Z : ℝ → ℂ × ℂ, Continuous Z ∧ HasRadialOutgoingExpansion ν n m Z ∧
    ∀ t, L ≤ t → (Z t).1 ≠ 0 ∧ HasDerivAt Z (radialExteriorODEField ν n t (Z t)) t

noncomputable def radialExteriorCanonical (ν : ℂ) (n : ℕ) (m : ℂ) (L : ℝ) : ℝ → ℂ × ℂ := by
  classical
  exact if h : HasRadialExterior ν n m L then Classical.choose h else fun _ => 0

theorem radialExteriorCanonical_spec {ν : ℂ} {n : ℕ} {m : ℂ} {L : ℝ}
    (h : HasRadialExterior ν n m L) :
    Continuous (radialExteriorCanonical ν n m L) ∧
    HasRadialOutgoingExpansion ν n m (radialExteriorCanonical ν n m L) ∧
    ∀ t, L ≤ t → (radialExteriorCanonical ν n m L t).1 ≠ 0 ∧
      HasDerivAt (radialExteriorCanonical ν n m L)
        (radialExteriorODEField ν n t (radialExteriorCanonical ν n m L t)) t := by
  classical
  unfold radialExteriorCanonical
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem radialExteriorCanonical_eq {ν : ℂ} {n : ℕ} {m : ℂ} {L : ℝ}
    (Z : ℝ → ℂ × ℂ) (hc : Continuous Z) (he : HasRadialOutgoingExpansion ν n m Z)
    (hd : ∀ t, L ≤ t → (Z t).1 ≠ 0 ∧ HasDerivAt Z (radialExteriorODEField ν n t (Z t)) t)
    (t : ℝ) (ht : L ≤ t) : radialExteriorCanonical ν n m L t=Z t := by
  have hh : HasRadialExterior ν n m L := ⟨Z,hc,he,hd⟩
  obtain ⟨hc',he',hd'⟩ := radialExteriorCanonical_spec hh
  exact radialExterior_outgoing_unique ν n m L _ Z hc' hc
    (fun s hs => (hd' s hs).2) (fun s hs => (hd s hs).2) he' he t ht

end DefocusingNLS

end OAI
