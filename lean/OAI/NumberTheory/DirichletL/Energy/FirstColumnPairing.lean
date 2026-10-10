import OAI.NumberTheory.DirichletL.Moments.FirstReferenceEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstColumnPairing
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstReferenceEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildInput CenteredMomentGaussEnergy
open CenteredMomentFirstMixedAllowance CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSecondRetainedAggregate CenteredMomentChildAssembly
open CenteredMomentFirstNonexceptionalWeightSum
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma fixed_pair_moduli (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(χ:RayCharacter):
    (fixedPair η C D hC E χ χ).left.modulus=(fixedPair η C D hC E 1 1).left.modulus ∧
    (fixedPair η C D hC E χ χ).right.modulus=(fixedPair η C D hC E 1 1).right.modulus:=by
  constructor
  · rw [(fixedPair η C D hC E χ χ).left_modulus,
      (fixedPair η C D hC E 1 1).left_modulus]
  · rw [(fixedPair η C D hC E χ χ).right_modulus,
      (fixedPair η C D hC E 1 1).right_modulus]

lemma reference_sum (ref seed front Z:ℝ)(loss:Fin 4→ℝ)(v:ℝ)(J:ℕ):
    (ref/seed)*(front*∑j:Fin 4,Z^(loss j))*(1+|v|)^(2*J)=
      ((∑j:Fin 4,ref*(front*Z^(loss j)))/seed)*(1+‖v‖)^(2*J):=by
  rw [Real.norm_eq_abs]
  simp only [←Finset.mul_sum]
  ring

omit [DecidableEq ι] in
theorem column_bounds_of_reference_sums
    (s:Input ι)(R seed:Ideal O)(Z:ℝ)(Jleft Jright:ℕ)
    (frontLeft frontRight:ℝ)(lossLeft lossRight:Fin 4→ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(n:Fin 4→ℤ)
    (hleft:∀L:Ideal O,(L.absNorm:ℝ)≤sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.1 (supported s R seed p).1
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left.modulus.absNorm:ℝ)*
            (CenteredMomentExceptionalAmplitudePair.volume s.toData/(p.val.1.absNorm:ℝ))^2*Z^(allowance p.val.1 p.val.2 Z)/(L.absNorm:ℝ))*
          (frontLeft*∑j:Fin 4,Z^(lossLeft j))*(1+|v|)^(2*Jleft))
    (hright:∀L:Ideal O,(L.absNorm:ℝ)≤sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.2 (supported s R seed p).2
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right.modulus.absNorm:ℝ)*
            (CenteredMomentExceptionalAmplitudePair.volume s.toData/(p.val.2.absNorm:ℝ))^2*Z^(allowance p.val.2 p.val.1 Z)/(L.absNorm:ℝ))*
          (frontRight*∑j:Fin 4,Z^(lossRight j))*(1+|v|)^(2*Jright)):
    ColumnBounds s R seed Z Jleft Jright
      (fun j=>frontLeft*Z^(lossLeft j)) (fun j=>frontRight*Z^(lossRight j)) p E n:=by
  constructor
  · intro L _ hcap hL χ v
    have hh:=hleft L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).1] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)
  · intro L _ hcap hL χ v
    have hh:=hright L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).2] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)

end SevenEighths.CenteredMomentEnergyFirstColumnPairing

end

end OAI
