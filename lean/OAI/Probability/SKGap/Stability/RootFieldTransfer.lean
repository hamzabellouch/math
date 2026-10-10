import Mathlib
import OAI.Probability.SKGap.Stability.RootDiagonalTransfer

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators
variable {n : ℕ}

lemma tapField_field_difference (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h h' y : Field n) : tapField j J h' y=tapField j J h y+(h-h') := by
  ext i
  simp only [tapField,Pi.add_apply,Pi.sub_apply]
  ring

lemma rootBad_field_transfer {j A ε c ρ κ : ℝ}
    (J : Matrix (Fin n) (Fin n) ℝ) (h h' : Field n)
    (hd : vectorNorm (h-h') ≤ κ*sqrt (n:ℝ)) :
    rootBad j A ε c ρ J h → rootBad j A ε c (ρ+κ) J h' := by
  rintro ⟨y,hy,a,ha,hdist,x,hx,hq⟩
  refine ⟨y,?_,a,ha,hdist,x,hx,hq⟩
  rw [tapField_field_difference]
  exact (vectorNorm_add_le _ _).trans ((add_le_add hy hd).trans_eq (by ring))

theorem rootBad_mesh_transfer {ι τ : Type*} (mesh : ι→τ) (h : τ→Field n)
    (j A ε c ρ κ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (hcover : ∀ t : τ, ∃ k : ι,vectorNorm (h t-h (mesh k)) ≤ κ*sqrt (n:ℝ)) :
    (∃ t,rootBad j A ε c ρ J (h t)) → ∃ k,rootBad j A ε c (ρ+κ) J (h (mesh k)) := by
  rintro ⟨t,ht⟩
  obtain ⟨k,hk⟩ := hcover t
  exact ⟨k,rootBad_field_transfer J (h t) (h (mesh k)) hk ht⟩
end SKGap.ObservationBridge

end
end

end OAI
