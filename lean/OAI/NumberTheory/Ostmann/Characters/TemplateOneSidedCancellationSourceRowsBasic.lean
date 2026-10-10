import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationResidueRows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

theorem residueGuards_progression_of_dvd (g : List (ResidueGuard ι))
    (hg : ∀ q ∈ g,q.Valid) (Q : ℕ) (hQ : residueModulus g ∣ (Q:ℤ))
    (i : ι) (x : Other i → ℤ) (r n : ℤ) :
    (∀ q ∈ g,q.holds (insertCoordinate i x ((Q:ℤ)*n+r))) ↔
      (∀ q ∈ g,q.holds (insertCoordinate i x r)) := by
  apply residueGuards_iff_of_modEq g hg
  intro u
  by_cases hu : u=i
  · subst u
    simp only [insertCoordinate_self]
    apply Int.modEq_iff_dvd.mpr
    convert dvd_mul_of_dvd_left hQ (-n) using 1; ring
  · simp only [insertCoordinate,hu,dite_false]
    exact Int.ModEq.refl _

theorem frequencyArithmetic_progression_of_dvd (k : ℕ) (V : ℕ → ℤ)
    (j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (hf : historyFrequencyBounds V j s t)
    (he : ∀ a u,HistoryReconstruction.Good a (e u))
    (Q : ℕ) (hQ : residueModulus (historyResidueGuards k j s e t) ∣ (Q:ℤ))
    (i : ι) (x : Other i → ℤ) (r n : ℤ) :
    frequencyArithmetic k V j s (evalExpressions (insertCoordinate i x ((Q:ℤ)*n+r)) e) t ↔
      frequencyArithmetic k V j s (evalExpressions (insertCoordinate i x r) e) t := by
  have hv := historyResidueGuards_valid k V j s e t (fun u => (he (fun _ => 0) u).1) hf
  rw [←historyResidueGuards_holds k V j s e t _ (he _) hf,
    ←historyResidueGuards_holds k V j s e t _ (he _) hf]
  exact residueGuards_progression_of_dvd _ hv Q hQ i x r n

def pairResidueModulus (g h : List (ResidueGuard ι)) : ℕ :=
  naturalResidueModulus g * naturalResidueModulus h

omit [DecidableEq ι] in
theorem pairResidueModulus_pos (g h : List (ResidueGuard ι))
    (hg : ∀ q ∈ g,q.Valid) (hh : ∀ q ∈ h,q.Valid) : 0 < pairResidueModulus g h :=
  Nat.mul_pos (naturalResidueModulus_pos g hg) (naturalResidueModulus_pos h hh)

omit [DecidableEq ι] in
theorem residueModulus_dvd_pair_left (g h : List (ResidueGuard ι)) :
    residueModulus g ∣ (pairResidueModulus g h:ℤ) := by
  have hd : residueModulus g ∣ (naturalResidueModulus g:ℤ) :=
    Int.dvd_natCast.mpr (dvd_refl _)
  simpa only [pairResidueModulus,Nat.cast_mul] using
    dvd_mul_of_dvd_left hd (naturalResidueModulus h:ℤ)

omit [DecidableEq ι] in
theorem residueModulus_dvd_pair_right (g h : List (ResidueGuard ι)) :
    residueModulus h ∣ (pairResidueModulus g h:ℤ) := by
  have hd : residueModulus h ∣ (naturalResidueModulus h:ℤ) :=
    Int.dvd_natCast.mpr (dvd_refl _)
  simpa only [pairResidueModulus,Nat.cast_mul] using
    dvd_mul_of_dvd_right hd (naturalResidueModulus g:ℤ)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
