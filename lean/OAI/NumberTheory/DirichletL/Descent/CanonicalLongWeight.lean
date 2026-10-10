import OAI.NumberTheory.DirichletL.Descent.CanonicalLongNormalization
import OAI.NumberTheory.DirichletL.Descent.TripleMass

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem second_label_weight_uniform (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀(Z V:ℝ),1≤Z→V≤L→∀I:Ideal O,I≠0→
      (I.absNorm:ℝ)≤Z^V→secondLabelWeight K I≤C*Z^eps := by
  let delta:=eps/(L+1)
  have hd:0<delta:=div_pos heps (by linarith)
  obtain ⟨C,hC,hh⟩:=ideal_divisor_power_small (9+4*K) delta hd
  refine ⟨C,hC,?_⟩
  intro Z V hZ hV I hI hnorm
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hbudget:L*delta≤eps := by
    have he:(L+1)*delta=eps:=by dsimp [delta];field_simp
    nlinarith
  calc
    secondLabelWeight K I≤C*(I.absNorm:ℝ)^delta:=hh I hI
    _≤C*(Z^L)^delta:=by
      gcongr
      exact hnorm.trans (Real.rpow_le_rpow_of_exponent_le hZ hV)
    _=C*Z^(L*delta):=by rw [←Real.rpow_mul hz.le]
    _≤C*Z^eps:=by gcongr

theorem normalized_second_energy_le_actual_family (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,goodLambda∉Ideal.span {p i})
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,Admissible I)
      (W:ℝ→ℂ)(X Z F V R:ℝ),1≤Z→0<R→V≤L→
      (∀I∈labels,(I.absNorm:ℝ)≤Z^V)→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K) W X Z F≤
        C*Z^(-F+eps)*rowFamilyEnergy labels (fun I k=>
          finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X) R := by
  obtain ⟨C,hC,hh⟩:=second_label_weight_uniform K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg pool Ψ m slots lists a labels hlabels W X Z F V R hZ hR hV hnorm
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hb:=normalized_energy_le_actual_family p hp hcop hg pool Ψ m slots lists a labels
    (fun I hI=>supported_primaryGenerator_ne_zero I (admissible_supported (hlabels I hI)))
    (secondLabelWeight K) (C*Z^eps) (by positivity)
    (fun I hI=>⟨by unfold secondLabelWeight;positivity,
      hh Z V hZ hV I (hlabels I hI).1 (hnorm I hI)⟩) W X Z F R hz hR
  convert hb using 1
  rw [Real.rpow_add hz]
  ring

end SevenEighths.InverseMoment

end

end OAI
