import OAI.Analysis.KadisonKastler.RegularCoreMonomials
import OAI.Analysis.KadisonKastler.RegularCoreCentralField
import OAI.Analysis.KadisonKastler.TrivialCoreCenter
import OAI.Analysis.KadisonKastler.FactorCornerCentralProjection

namespace OAI

/-! # Translations commute with core corners on which the action is trivial -/

namespace KadisonKastler

open MeasureTheory Filter Generator.Tracial
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def compressedCommutant (p S : H →L[ℂ] H) : Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | Commute (p * T * p) S}
  zero_mem' := by change p * 0 * p * S = S * (p * 0 * p); simp
  add_mem' := by
    intro A B hA hB
    change p * (A + B) * p * S = S * (p * (A + B) * p)
    simpa only [mul_add, add_mul] using congrArg₂ (· + ·) hA.eq hB.eq
  smul_mem' := by
    intro z A hA
    change p * (z • A) * p * S = S * (p * (z • A) * p)
    simpa only [mul_smul_comm, smul_mul_assoc] using congrArg (z • ·) hA.eq

theorem regularCore_compressed_commute_of_monomials
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M : VonNeumannAlgebra H) (hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (p S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hm : ∀ a ∈ M, ∀ s, Commute (p * regularCoreMonomial U hU a s * p) S)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU M) : Commute (p * T * p) S := by
  classical
  let A := StarAlgebra.adjoin ℂ (regularCoreGenerators U hU M)
  have hsub : A.toSubalgebra.toSubmodule ≤ compressedCommutant p S := by
    rw [show A = StarAlgebra.adjoin ℂ (regularCoreGenerators U hU M) from rfl,
      regularCore_adjoin_eq_span_monomials U hU M hn]
    apply Submodule.span_le.mpr
    rintro x ⟨a, ha, s, rfl⟩
    exact hm a ha s
  have ht : T ∈ Set.centralizer (Set.centralizer (A :
      Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))) := by
    change T ∈ (generatedVonNeumannAlgebra A :
      Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) at hT
    rwa [generatedVonNeumannAlgebra_coe] at hT
  obtain ⟨a, ha⟩ := Generator.bicommutant_exists_strong_net A T ht
  apply ContinuousLinearMap.ext
  intro x
  have hl : Tendsto (fun i : Finset (RegularCoreHilbert H) × ℕ =>
      p ((a i).val (p (S x)))) atTop (𝓝 (p (T (p (S x))))) :=
    p.continuous.continuousAt.tendsto.comp (ha (p (S x)))
  have hr : Tendsto (fun i : Finset (RegularCoreHilbert H) × ℕ =>
      S (p ((a i).val (p x)))) atTop (𝓝 (S (p (T (p x))))) :=
    S.continuous.continuousAt.tendsto.comp
    (p.continuous.continuousAt.tendsto.comp (ha (p x)))
  apply tendsto_nhds_unique hl
  apply hr.congr'
  exact Filter.Eventually.of_forall (fun i =>
    (congrArg (fun B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => B x)
      (hsub (a i).property).eq).symm)

theorem regularCore_fixed_corner_commute_translations
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M : VonNeumannAlgebra H) (hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (p : AlgebraProjection M)
    (hfix : ∀ t a, a ∈ M → unitaryConj (U t) (p.val.val * a * p.val.val) =
      p.val.val * a * p.val.val)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU M) (s : Multiplicative ℝ) :
    Commute (regularCoreEmbedding U hU p.val.val * T * regularCoreEmbedding U hU p.val.val)
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  have hp : ∀ t, unitaryConj (U t) p.val.val = p.val.val := by
    intro t
    have h := hfix t 1 M.one_mem
    simpa only [mul_one, show p.val.val * p.val.val = p.val.val from
      congrArg Subtype.val p.property.isIdempotentElem.eq] using h
  have hpconst := regularCoreEmbedding_eq_constant_of_fixed U hU p.val.val hp
  apply regularCore_compressed_commute_of_monomials U hU M hn _ _ ?_ T hT
  intro a ha t
  have hpt : Commute (regularCoreEmbedding U hU p.val.val)
      (regularRightTranslation (H := H) t :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    rw [hpconst]
    exact regularConstant_commute_translation _ _
  have he : regularCoreEmbedding U hU p.val.val * regularCoreMonomial U hU a t *
      regularCoreEmbedding U hU p.val.val =
      regularConstantHom volume (p.val.val * a * p.val.val) *
        (regularRightTranslation (H := H) t :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    unfold regularCoreMonomial
    calc
      _ = (regularCoreEmbedding U hU p.val.val * regularCoreEmbedding U hU a *
          regularCoreEmbedding U hU p.val.val) *
          (regularRightTranslation (H := H) t :
            RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
        simp only [mul_assoc]
        rw [hpt.symm.eq]
      _ = _ := by
        rw [← map_mul, ← map_mul, regularCoreEmbedding_eq_constant_of_fixed U hU _
          (fun t => hfix t a ha)]
  rw [he]
  apply (regularConstant_commute_translation _ s).mul_left
  change (regularRightTranslation (H := H) t :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
    (regularRightTranslation (H := H) s :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      (regularRightTranslation (H := H) t :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  exact congrArg Subtype.val (show regularRightTranslation (H := H) t *
    regularRightTranslation s = regularRightTranslation s * regularRightTranslation t by
      rw [← map_mul, ← map_mul, mul_comm])

end

end KadisonKastler

end OAI
