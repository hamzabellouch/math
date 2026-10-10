import OAI.NumberTheory.DirichletL.Reflection.PuncturedMarks
import OAI.NumberTheory.DirichletL.Reflection.MarkedLevel

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {α σ : Type*} [Fintype σ]

def punctureRetainedTuples (tuples : Finset α) (S : α→PrimeFamily σ) (m : Eis) : Finset α :=
  tuples.filter (fun p => ∀ i,m∉(S p).ideal i)

theorem original_tuple_filter_puncture (tuples : Finset α) (S : α→PrimeFamily σ)
    (w : α→ℂ) (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) :
    (∑ p∈tuples,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (S p).ideal i∣A then (1:ℂ) else 0))=
    ∑ p∈punctureRetainedTuples tuples S m,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (S p).ideal i∣A then (1:ℂ) else 0) := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpbad
  have hh : ¬∀ i,m∉(S p).ideal i := fun h => hpbad (Finset.mem_filter.mpr ⟨hp,h⟩)
  push Not at hh
  obtain ⟨i,hi⟩ := hh
  rw [markedCompletedT_zero_punctured_slot (S p) i Ψ m f z hi W X,mul_zero]

lemma retained_slot_period (tuples : Finset α) (S : α→PrimeFamily σ)
    (m : Eis) (Q : Ideal Eis) (hQ : Q∣Ideal.span {m})
    (p : α) (hp : p∈punctureRetainedTuples tuples S m) (i : σ) :
    IsCoprime Q ((S p).ideal i) := by
  apply (maximal_coprime_of_not_dvd _ _ ?_).symm
  intro h
  have hd := dvd_trans h hQ
  exact (Finset.mem_filter.mp hp).2 i ((Ideal.dvd_iff_le.mp hd) (Ideal.subset_span (by simp)))

lemma retained_markedRowFamily_period {m f z : Eis} (D : GoodMaskRowData m f z)
    (tuples : Finset α) (S : α→PrimeFamily σ) (Q : Ideal Eis) (c : Eis)
    (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (hpuncture : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (p : α) (hp : p∈punctureRetainedTuples tuples S m) :
    ∀ i,IsCoprime (Ideal.span {(9:Eis)*c}) ((markedRowFamily D (S p) Q).ideal i) := by
  exact markedRowFamily_period D (S p) Q
    (fun i => retained_slot_period tuples S m _ hpuncture p hp i) c hcQ

end
end SevenEighths.InverseReflectedPhase

end OAI
