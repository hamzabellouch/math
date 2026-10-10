import OAI.Combinatorics.PolynomialVacuum.Algebra.PairImage

namespace OAI

namespace PolynomialVacuumAlgebra

abbrev BitTensorFamily := Bool → Bool → Bool → Spin → Spin → Spin → ℂ

noncomputable def bitSwap : Matrix Pair Pair ℂ := Pone-zeta • Ptwo

 

def BitTensorEquations (W : BitTensorFamily) : Prop :=
  (∀ i j k a b c, ¬(allowedSpin i a ∧ allowedSpin j b ∧ allowedSpin k c) → W i j k a b c=0) ∧
  (∀ i k c, Pone.mulVec (fun ab => W i i k ab.1 ab.2 c)=fun ab => W i i k ab.1 ab.2 c) ∧
  (∀ i k a, Pone.mulVec (fun bc => W i k k a bc.1 bc.2)=fun bc => W i k k a bc.1 bc.2) ∧
  (∀ i j k c, ∑ ab : Pair, cup ab*W i j k ab.1 ab.2 c=0) ∧
  (∀ i j k a, ∑ bc : Pair, cup bc*W i j k a bc.1 bc.2=0) ∧
  (∀ i a, bitSwap.mulVec (fun bc => W i false true a bc.1 bc.2)=fun bc => W i true false a bc.1 bc.2)

end PolynomialVacuumAlgebra

end OAI
