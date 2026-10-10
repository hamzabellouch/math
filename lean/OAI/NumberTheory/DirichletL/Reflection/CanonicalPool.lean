import OAI.NumberTheory.DirichletL.Reflection.NormalizedPhysical

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def canonicalFrozenFamily (I Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6) :
    PrimeFamily (FreeReflection.reflectionActivePool I Q Q₀ e) where
  ideal P := P.val
  maximal P := FreeReflection.pool_maximal I Q Q₀
    ⟨P.val,FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩
  good P := FreeReflection.pool_good I Q Q₀
    ⟨P.val,FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩

def canonicalFrozenExponent (I F Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) : ℕ := completedLocalExponent I F P.val

lemma canonicalFrozenExponent_lt (I F Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) : canonicalFrozenExponent I F Q Q₀ e P<6 :=
  Nat.mod_lt _ (by norm_num)

lemma canonicalFrozenFamily_pairwise (I Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6) :
    Pairwise (Function.onFun IsCoprime (canonicalFrozenFamily I Q Q₀ e).ideal) := by
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)

lemma canonicalFrozenFamily_odd (I Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) :
    ringChar (Eis⧸(canonicalFrozenFamily I Q Q₀ e).ideal P)≠2 :=
  FreeReflection.pool_odd I Q Q₀ ⟨P.val,FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩

lemma maximal_coprime_of_not_dvd (P J : Ideal Eis) [P.IsMaximal] (h : ¬P∣J) : IsCoprime P J := by
  rw [Ideal.isCoprime_iff_codisjoint]
  apply ((Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)).not_le_iff_codisjoint).mp
  exact fun hle => h (Ideal.dvd_iff_le.mpr hle)

lemma canonicalFrozenFamily_row_coprime (I Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) :
    IsCoprime ((canonicalFrozenFamily I Q Q₀ e).ideal P) (rowResidualPart I Q) :=
  maximal_coprime_of_not_dvd _ _ (FreeReflection.pool_nonresidual I Q Q₀
    ⟨P.val,FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩)

lemma canonicalFrozenFamily_level_coprime (I Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) :
    IsCoprime Q₀ ((canonicalFrozenFamily I Q Q₀ e).ideal P) := by
  apply (maximal_coprime_of_not_dvd _ _ ?_).symm
  intro hd
  exact FreeReflection.pool_free I Q Q₀
    ⟨P.val,FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩ (Ideal.dvd_iff_le.mp hd)

theorem canonicalFrozenExponent_on_fiber (R I F Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (e : FreeReflection.pool R Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool R Q Q₀ e) :
    completedLocalExponent I F ((canonicalFrozenFamily R Q Q₀ e).ideal P)=
      canonicalFrozenExponent R F Q Q₀ e P := by
  exact CanonicalRowCompletion.nonresidualPoolEquiv_exponent R I F Q Q₀ hR hI hQ hpow hmask
    ⟨P.val,FreeReflection.reflectionActivePool_subset R Q Q₀ e P.property⟩

lemma canonicalFrozenFamily_row_coprime_on_fiber (R I Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (e : FreeReflection.pool R Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool R Q Q₀ e) :
    IsCoprime ((canonicalFrozenFamily R Q Q₀ e).ideal P) (rowResidualPart I Q) := by
  apply maximal_coprime_of_not_dvd
  exact FreeReflection.pool_nonresidual I Q Q₀
    (CanonicalRowCompletion.nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask
      ⟨P.val,FreeReflection.reflectionActivePool_subset R Q Q₀ e P.property⟩)

lemma canonicalFrozenFamily_extracted (I F Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (v : Fin 3) :
    frozenExtracted (canonicalFrozenFamily I Q Q₀ e) (canonicalFrozenExponent I F Q Q₀ e)
      (FreeReflection.reflectionActiveLabel I Q Q₀ e) v =
    reflectionExtractedDivisor (fun P : FreeReflection.reflectionActivePool I Q Q₀ e => P.val)
      (fun P => completedLocalExponent I F P.val) (FreeReflection.reflectionActiveLabel I Q Q₀ e) v := by
  rw [frozenExtracted_eq_ideal]
  rfl

lemma canonicalFrozenFamily_divides_on_fiber (J I Q Q₀ : Ideal Eis)
    (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (e : FreeReflection.pool J Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool J Q Q₀ e) :
    (canonicalFrozenFamily J Q Q₀ e).ideal P ∣ I*Q :=
  FreeReflection.pool_divides I Q Q₀ hI hQ
    (CanonicalRowCompletion.nonresidualPoolEquiv J I Q Q₀ hJ hI hQ hpow hmask
      ⟨P.val,FreeReflection.reflectionActivePool_subset J Q Q₀ e P.property⟩)

lemma canonicalFrozenFamily_nonresidual_on_fiber (J I Q Q₀ : Ideal Eis)
    (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (e : FreeReflection.pool J Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool J Q Q₀ e) :
    ¬(canonicalFrozenFamily J Q Q₀ e).ideal P ∣ rowResidualPart I Q :=
  FreeReflection.pool_nonresidual I Q Q₀
    (CanonicalRowCompletion.nonresidualPoolEquiv J I Q Q₀ hJ hI hQ hpow hmask
      ⟨P.val,FreeReflection.reflectionActivePool_subset J Q Q₀ e P.property⟩)

end
end SevenEighths.InverseReflectedPhase

end OAI
