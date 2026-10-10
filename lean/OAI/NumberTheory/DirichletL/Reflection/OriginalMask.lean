import OAI.NumberTheory.DirichletL.Reflection.OriginalTransport

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma maximal_coprime_iff_ne (P Q : Ideal Eis) [P.IsMaximal] [Q.IsMaximal] :
    IsCoprime P Q ↔ P≠Q := by
  constructor
  · intro h he
    subst Q
    exact (show P.IsPrime from inferInstance).ne_top (by simpa using h.sup_eq)
  · exact Ideal.isCoprime_of_isMaximal

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

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem original_slot_mask_iff (S : PrimeFamily σ) :
    (∀ P : FreePrimeIndex D.movingIdeal Q₀, ∀ t, S.ideal t≠P.val.val) ↔
    IsCoprime K (∏ t, S.ideal t) ∧
      ∀ b : FreeReflection.pool R (Ideal.span {m}*F) Q₀, ∀ t, S.ideal t≠b.val := by
  constructor
  · intro h
    constructor
    · rw [← PrimeFamily.residual_product K hK]
      apply IsCoprime.prod_left_iff.mpr
      intro a ha
      apply IsCoprime.prod_right_iff.mpr
      intro t ht
      apply Ideal.isCoprime_of_isMaximal
      have hh := h (E (Sum.inl a)) t
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)] at hh
      exact hh.symm
    · intro b t
      have hh := h (E (Sum.inr b)) t
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)] at hh
      exact hh
  · rintro ⟨hrow,hfixed⟩ P t
    obtain ⟨x,rfl⟩ := (E).surjective P
    cases x with
    | inl a =>
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)]
      have hc := (hrow.of_isCoprime_of_dvd_left (PrimeFamily.residual_dvd K hK a)).of_isCoprime_of_dvd_right
        (Finset.dvd_prod_of_mem S.ideal (Finset.mem_univ t))
      exact ((maximal_coprime_iff_ne _ _).mp hc).symm
    | inr b =>
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)]
      exact hfixed b t
end
end SevenEighths.InverseReflectedPhase

end OAI
