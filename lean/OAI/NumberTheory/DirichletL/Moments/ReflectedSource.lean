import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSource
import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
import OAI.NumberTheory.DirichletL.Moments.ExceptionalReflection
import OAI.NumberTheory.DirichletL.Hecke.UnitRows
import OAI.NumberTheory.DirichletL.Hecke.PrimeScale

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentReflectedSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CanonicalUnitEuler
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonLinearSource CenteredMomentCommonPairedSource
open CenteredMomentFirstSectors CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondHeightFamily CenteredMomentSourceRow
local notation "O" => HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def reflected (η:Character):Character:=η.product (HeckeUnitRows.character (-1:Oˣ))

theorem unit_ideal (I:Ideal O)(hI:Supported I):
    idealCoeff (HeckeUnitRows.character (-1:Oˣ)) I=idealRowHom (-1) I:=by
  rw [←ConcretePrimeRowBridge.span_idealGenerator I,
    idealCoeff_span _ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI.1),
    HeckeUnitRows.elementCoeff_character]
  change (if Supported (Ideal.span {ConcretePrimeRowBridge.idealGenerator I}) then _ else 0)=_
  rw [ConcretePrimeRowBridge.span_idealGenerator,ite_eq_left hI]
  rfl

theorem reflected_height (η:Character)(t:ℝ)(I:Ideal O)(hI:Supported I):
    heightCoeff (reflected η) t I=heightCoeff η t I*idealRowHom (-1) I:=by
  rw [heightCoeff,reflected,idealCoeff_product,unit_ideal I hI,heightCoeff]
  ring

theorem polynomial_neg {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(η:Character)(t:ℝ)(z:O):
    rowPolynomial S a (fun i=>c i*heightCoeff η t (Ideal.span {a i})) (-z)=
      rowPolynomial S a (fun i=>c i*heightCoeff (reflected η) t (Ideal.span {a i})) z:=by
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [reflected_height η t _ (ha i),show -z=(-1)*z by ring,idealRowHom_argument_mul]
  ring

theorem sourceColumn_neg {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):
    sourceColumn s C hC R seed L (-z)=
      sourceColumn (withHeight s (reflected s.η) s.t) C hC R seed L z:=by
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  have h:=polynomial_neg Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then β (C*I) else 0)
    s.η s.t z
  have hspan (I:supportedColumns Q):Ideal.span {sourceGenerator Q I}=(I:Ideal O):=
    primary_span_supported I (Finset.mem_filter.mp I.property).2
  simp only [hspan] at h
  dsimp only [sourceColumn, withHeight, Input.pools, Q, β] at h ⊢
  convert h using 1
  rfl

theorem normalizedColumn_neg {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):
    normalizedColumn s C hC R seed L (-z)=
      normalizedColumn (withHeight s (reflected s.η) s.t) C hC R seed L z:=by
  unfold normalizedColumn
  rw [sourceColumn_neg]
  simp only [withHeight,CenteredMomentExceptionalAmplitudePair.volume]

theorem reflected_row (η:Character)(m A z n:O)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m):
    rowTwist (HeckeRowClosure.elementHom η) m 1 (A*(-z)) n=
      rowTwist (HeckeRowClosure.elementHom (reflected η)) m 1 (A*z) n:=by
  by_cases hn:Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 _ n hn,rowTwist_extract_sixth_mask _ m 1 _ n hn]
    simp only [one_pow,one_mul]
    change elementCoeff η n*coprimalityMask m n*idealRowHom (A*(-z)) (Ideal.span {n})=
      elementCoeff (reflected η) n*coprimalityMask m n*idealRowHom (A*z) (Ideal.span {n})
    rw [reflected,elementCoeff_product,HeckeUnitRows.elementCoeff_character]
    have hu:unitSupplement (-1:Oˣ) n=idealRowHom (-1) (Ideal.span {n}):=by
      change (if Supported (Ideal.span {n}) then idealRowHom (-1) (Ideal.span {n}) else 0)=_
      rw [ite_eq_left hn]
    rw [hu,show A*(-z)=(-1)*(A*z) by ring,idealRowHom_argument_mul]
    ring
  · rw [CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
      CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn]

theorem reflected_inducing (η:Character)(Q:Ideal O)(m A z:O)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m):
    CenteredExceptionalProfile.FixedInducingRow η Q m A (-z) ↔
      CenteredExceptionalProfile.FixedInducingRow (reflected η) Q m A z:=by
  unfold CenteredExceptionalProfile.FixedInducingRow
  simp_rw [←reflected_row η m A z _ hmLam hm2]

end SevenEighths.CenteredMomentReflectedSource

end

end OAI
