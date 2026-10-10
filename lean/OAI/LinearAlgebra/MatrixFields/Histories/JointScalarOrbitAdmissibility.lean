import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryRecoveryBudget

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointScalarOrbitAdmissibility

open JointPopulation JointCanonicalization PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ) (L R : H → Type*)

def ClassWeights (wl : ∀ h, L h → ℕ) (wr : ∀ h, R h → ℕ)
    (vl vr : H → Shape → ℕ) (e : Target counts) (w : RawPairs counts L R) : Prop :=
  ∀ h j, wl h (w h j).1 = vl h ((e h).val j) ∧
    wr h (w h j).2 = vr h ((e h).val j)

omit [Fintype H] [DecidableEq H] in
theorem classWeights_smul (wl : ∀ h, L h → ℕ) (wr : ∀ h, R h → ℕ)
    (vl vr : H → Shape → ℕ) (e : Target counts) :
    letI : MulAction (HalfClassPermutations (ClassPositions counts)) (RawPairs counts L R) :=
      EquivOrbitTransport.action (pairEquiv counts L R e)
    ∀ (g : HalfClassPermutations (ClassPositions counts)) (w : RawPairs counts L R),
      ClassWeights counts L R wl wr vl vr e w →
      ClassWeights counts L R wl wr vl vr e ((EquivOrbitTransport.action (pairEquiv counts L R e)).smul g w) := by
  let : MulAction (HalfClassPermutations (ClassPositions counts)) (RawPairs counts L R) :=
    EquivOrbitTransport.action (pairEquiv counts L R e)
  intro g w hw h j
  constructor
  · change wl h (w h ((positionEquiv counts e h).symm
      ⟨(e h).val j, (g.1 (h, (e h).val j)).symm (positionEquiv counts e h j).2⟩)).1 = _
    simpa only [positionEquiv_symm_shape] using
      (hw h ((positionEquiv counts e h).symm
        ⟨(e h).val j, (g.1 (h, (e h).val j)).symm (positionEquiv counts e h j).2⟩)).1
  · change wr h (w h ((positionEquiv counts e h).symm
      ⟨(e h).val j, (g.2 (h, (e h).val j)).symm (positionEquiv counts e h j).2⟩)).2 = _
    simpa only [positionEquiv_symm_shape] using
      (hw h ((positionEquiv counts e h).symm
        ⟨(e h).val j, (g.2 (h, (e h).val j)).symm (positionEquiv counts e h j).2⟩)).2

section Windows

variable {SL SR : H → Type*}
    [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)]
    [∀ h, DecidableEq (SL h)] [∀ h, DecidableEq (SR h)]
    (sl : ∀ c : ClassKey (H := H), L c.1 → SL c.1)
    (sr : ∀ c : ClassKey (H := H), R c.1 → SR c.1)
    (νl : ∀ c : ClassKey (H := H), SL c.1 → ℝ)
    (νr : ∀ c : ClassKey (H := H), SR c.1 → ℝ)
    (ηl ηr : ClassKey (H := H) → ℝ)

omit [Fintype H] [DecidableEq H] in
theorem rawWindows_smul (e : Target counts) :
    letI : MulAction (HalfClassPermutations (ClassPositions counts)) (RawPairs counts L R) :=
      EquivOrbitTransport.action (pairEquiv counts L R e)
    ∀ (g : HalfClassPermutations (ClassPositions counts)) (w : RawPairs counts L R),
      rawWindows counts L R sl sr νl νr ηl ηr e ((EquivOrbitTransport.action (pairEquiv counts L R e)).smul g w) ↔
      rawWindows counts L R sl sr νl νr ηl ηr e w := by
  let : MulAction (HalfClassPermutations (ClassPositions counts)) (RawPairs counts L R) :=
    EquivOrbitTransport.action (pairEquiv counts L R e)
  intro g w
  rw [rawWindows_iff_childWindows, rawWindows_iff_childWindows]
  change HistorySymmetry.childWindows _ _ _ _ _ _
      ((pairEquiv counts L R e) ((pairEquiv counts L R e).symm
        (g • (pairEquiv counts L R e) w))) ↔ _
  rw [Equiv.apply_symm_apply]
  exact HistorySymmetry.childWindows_smul _ _ _ _ _ _ g _

end Windows

end MatrixMultiplication.JointScalarOrbitAdmissibility

end
end

end MatrixAllFields

end OAI
