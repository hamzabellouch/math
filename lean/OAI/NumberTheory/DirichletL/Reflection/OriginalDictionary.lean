import OAI.NumberTheory.DirichletL.Reflection.OriginalFiber
import OAI.NumberTheory.DirichletL.Reflection.ActiveDictionary
import OAI.NumberTheory.DirichletL.Reflection.ReindexReflection

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def poolPrimeFamily (R Q Q₀ : Ideal Eis) : PrimeFamily (FreeReflection.pool R Q Q₀) where
  ideal P := P.val
  maximal P := FreeReflection.pool_maximal R Q Q₀ P
  good P := FreeReflection.pool_good R Q Q₀ P

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad

lemma original_active_family_ideal (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).ideal (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).ideal x := by
  cases x with
  | inl b =>
    change (E (Sum.inr b.val)).val.val=b.val.val
    exact D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b.val)
  | inr x => cases x with
    | inl a =>
      change (E (Sum.inl a)).val.val=a.val
      exact D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
    | inr t => rfl

lemma original_active_family_generator (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).generator (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator x :=
  congrArg primaryPrime (original_active_family_ideal D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T x)

lemma original_active_exponent
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
      (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) (fun _ : σ => 0)
      (markedActiveEquiv E B T x).val =
    Sum.elim (fun b : B => completedLocalExponent R F b.val.val)
      (Sum.elim (fun _ : PrimeIndex K => 1) (fun _ : T => 0)) x := by
  cases x with
  | inl b => exact D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b.val)
  | inr x => cases x with
    | inl a => exact D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
    | inr t => rfl

lemma original_active_marks
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ) :
    reindexMarks (markedActiveEquiv E B T) (activeMarks (markedActiveSet E B T) markedSumSlots)=
    Finset.univ.filter (fun x : B⊕(PrimeIndex K⊕T) => match x with
      | Sum.inr (Sum.inr _) => True | _ => False) := by
  ext x
  simp only [mem_reindexMarks,mem_activeMarks,Finset.mem_filter,Finset.mem_univ,true_and]
  cases x with
  | inl b => simp [markedActiveEquiv_frozen,markedSumSlots]
  | inr x => cases x with
    | inl a => simp [markedActiveEquiv_residual,markedSumSlots]
    | inr t => simp [markedActiveEquiv_slot,markedSumSlots]
end
end SevenEighths.InverseReflectedPhase

end OAI
