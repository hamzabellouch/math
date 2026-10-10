import Mathlib
import OAI.Probability.GaussianInformation.Kernel.ScaledReference

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace RowConcat
abbrev index (k : ℕ) : Fin k ⊕ Fin k ≃ Fin (2*k) :=
  finSumFinEquiv.trans (finCongr (by omega))
noncomputable def join {E : Type*} [MeasurableSpace E] (k : ℕ) :
    ((Fin k → E) × (Fin k → E)) ≃ᵐ (Fin (2*k) → E) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => E)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (2*k) => E) (index k))

lemma join_apply {E : Type*} [MeasurableSpace E] (k : ℕ) (x y : Fin k → E) (i : Fin (2*k)) :
    join k (x,y) i=Sum.elim x y ((index k).symm i) := by
  obtain ⟨j,rfl⟩ := (index k).surjective i
  change (Equiv.piCongrLeft (fun _ : Fin (2*k) => E) (index k))
    ((Equiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => E)).symm (x,y)) ((index k) j)=_
  rw [Equiv.piCongrLeft_apply_apply,Equiv.symm_apply_apply]
  cases j <;> rfl

lemma join_bound {E : Type*} [MeasurableSpace E] (k : ℕ) (x y : Fin k → E)
    (P : E → Prop) (hx : ∀ i,P (x i)) (hy : ∀ i,P (y i)) : ∀ i,P (join k (x,y) i) := by
  intro i
  rw [join_apply]
  cases (index k).symm i with
  | inl i => exact hx i
  | inr i => exact hy i

lemma join_add (k : ℕ) (x y e f : Fin k → ℝ) :
    join k (x+e,y+f)=join k (x,y)+join k (e,f) := by
  ext i
  simp only [join_apply,Pi.add_apply]
  cases (index k).symm i <;> rfl

lemma join_rows (k d : ℕ) (X Z : Fin k → Fin d → ℝ) (s : Fin d → ℝ) :
    join k ((fun i => ∑ j,X i j*s j),(fun i => ∑ j,Z i j*s j))=
      (fun i => ∑ j,join k (X,Z) i j*s j) := by
  ext i
  simp only [join_apply]
  cases (index k).symm i <;> rfl

lemma join_measurePreserving {E : Type*} [MeasurableSpace E] (k : ℕ) (μ : Measure E) [SigmaFinite μ] :
    MeasurePreserving (join (E := E) k)
      ((Measure.pi (fun _ : Fin k => μ)).prod (Measure.pi (fun _ : Fin k => μ)))
      (Measure.pi (fun _ : Fin (2*k) => μ)) := by
  exact (measurePreserving_piCongrLeft (fun _ : Fin (2*k) => μ) (index k)).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin k ⊕ Fin k => μ))

lemma join_volume_measurePreserving (k : ℕ) :
    MeasurePreserving (join (E := ℝ) k) (volume.prod volume) volume := by
  simpa only [← volume_pi] using join_measurePreserving k (volume : Measure ℝ)
end RowConcat

end OAI
