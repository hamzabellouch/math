import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalMass
import OAI.Probability.InvariantIsing.Cavity.ConsecutiveGroupProfile

namespace OAI

/-! Finite field populations admit exact block templates and canonical
all-dimensional labels with the corresponding limiting proportions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma spinGroupSize_equiv {A B : Type*} [DecidableEq A] [DecidableEq B]
    {N : ℕ} (E : A ≃ B) (g : Fin N → B) (a : A) :
    spinGroupSize (fun i => E.symm (g i)) a=spinGroupSize g (E a) := by
  simp only [spinGroupSize,Equiv.symm_apply_eq]

def countedFieldGroup {A : Type*} [Fintype A] {N : ℕ} (s : A → ℕ)
    (hs : ∑ a, s a=N) : Fin N → A :=
  let E := Fintype.equivFin A
  fun i => E.symm (cavityOrderedGroup (fun j => s (E.symm j))
    ((Equiv.sum_comp E.symm s).trans hs) i)

lemma countedFieldGroup_size {A : Type*} [Fintype A] [DecidableEq A]
    {N : ℕ} (s : A → ℕ) (hs : ∑ a, s a=N) (a : A) :
    spinGroupSize (countedFieldGroup s hs) a=s a := by
  rw [countedFieldGroup,spinGroupSize_equiv]
  exact (cavityOrderedGroup_card _ _ _).trans (by simp)

def canonicalFieldLabel {A : Type*} [Fintype A] (a0 : A) (s : A → ℕ)
    (N : ℕ) : Fin N → A :=
  let E := Fintype.equivFin A
  fun i => E.symm (cavityResidueLabel
    (Fintype.card_pos_iff.mpr ⟨a0⟩) (fun j => s (E.symm j)) (Equiv.sum_comp E.symm s) N i)

lemma canonicalFieldLabel_population {A : Type*} [Fintype A] [DecidableEq A]
    (a0 : A) (s : A → ℕ) (hs : 0 < ∑ a, s a) :
    Tendsto (fun N a => (spinGroupSize (canonicalFieldLabel a0 s N) a : ℝ)/N)
      atTop (𝓝 (fun a => (s a : ℝ)/(∑ a, s a))) := by
  let E := Fintype.equivFin A
  have hh := cavity_canonical_mass_tendsto (Fintype.card_pos_iff.mpr ⟨a0⟩) hs
    (fun j => s (E.symm j)) (Equiv.sum_comp E.symm s)
  apply tendsto_pi_nhds.mpr
  intro a
  have ha := (tendsto_pi_nhds.mp hh) (E a)
  dsimp only [canonicalFieldLabel]
  simp only [spinGroupSize_equiv]
  simpa only [E,Equiv.symm_apply_apply,spinGroupSize,cavitySpectralGroup] using ha

end InvariantIsing

end

end OAI
