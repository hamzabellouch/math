import OAI.NumberTheory.DirichletL.Detector.RawIndexGrouping

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def sourceOuterEquiv (S : Finset (Ideal O)) : SourceOuter S ≃
    {K : {I : Ideal O // Supported I} // ∀P∈S,¬P∣K.val} where
  toFun K := ⟨⟨K.val,K.property.1⟩,K.property.2⟩
  invFun K := ⟨K.val.val,K.val.property,K.property⟩
  left_inv _K := rfl
  right_inv _K := rfl

lemma sourceOuter_tsum (S : Finset (Ideal O)) (f : {I : Ideal O // Supported I}→ℂ) :
    (∑'K : {I : Ideal O // Supported I},if ∀P∈S,¬P∣K.val then f K else 0)=
      ∑'K : SourceOuter S,f ⟨K.val,K.property.1⟩ := by
  have hs := tsum_subtype {K : {I : Ideal O // Supported I} | ∀P∈S,¬P∣K.val} f
  have he := (sourceOuterEquiv S).tsum_eq (fun K=>f K.val)
  calc
    _ = ∑' K : {I : Ideal O // Supported I},
        Set.indicator {K | ∀ P ∈ S, ¬P ∣ K.val} f K := by
      apply tsum_congr
      intro K
      simp only [Set.indicator, Set.mem_ofPred_eq]
      split_ifs <;> rfl
    _ = _ := hs.symm.trans he.symm

end SevenEighths.ProbePhysical
end

end OAI
