import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.TwoScaleMatching

namespace OAI

section
noncomputable section
namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder

theorem actual_iterated_normalized_matching (n p : ℕ)
    (F : Finset C(Interval,Mat p)) {ε : ℝ} (hε : 0<ε) :
    ∃ k : ℕ,∀ l,k≤l → ∃ U : C(Interval×Interval,unitary (TensorMat p (iteratedSize n l))),
      (∀ s : Interval,U (s,s)=1) ∧ ∀ f∈F,∀ s t : Interval,
        ‖unitaryConjugation (U (s,t)) (blockDiagonalHom (f ∘ iteratedTuple n l s))-
          blockDiagonalHom (f ∘ iteratedTuple n l t)‖<ε := by
  obtain ⟨δ,hδ,hF⟩ := finite_continuous_modulus F (show 0<ε/3 by positivity)
  obtain ⟨k,hk⟩ := iteratedTuple_shifted_counts n hδ
  refine ⟨k,?_⟩
  intro l hl
  let L : ℝ := ((sortingNetwork (iteratedSize n l)).length:ℝ)
  have hL : 0≤L := Nat.cast_nonneg _
  let ηs := ε/(3*(6*L+1))
  have hηs : 0<ηs := by dsimp [ηs]; positivity
  obtain ⟨r,hr,hFs⟩ := finite_continuous_modulus F hηs
  let U : C(Interval×Interval,unitary (TensorMat p (iteratedSize n l))) :=
    (continuousMatchingUnitary p (iteratedSize n l) r).comp
      ⟨fun z => (iteratedTuple n l z.1,iteratedTuple n l z.2),
        ((iteratedTuple_continuous n l).comp continuous_fst).prodMk
          ((iteratedTuple_continuous n l).comp continuous_snd)⟩
  refine ⟨U,?_,?_⟩
  · intro s
    change ((networkUnitary p (iteratedSize n l) r (sortingNetwork (iteratedSize n l)) _)⁻¹ *
      networkUnitary p (iteratedSize n l) r (sortingNetwork (iteratedSize n l)) _)=1
    exact inv_mul_cancel _
  intro f hf s t
  have hh := continuous_matching_control_two_scales p (iteratedSize n l) hr
    (iteratedTuple n l s) (iteratedTuple n l t) (hk l hl s t) (hk l hl t s)
    f (show 0≤ε/3 by positivity) hηs.le (hF f hf) (hFs f hf)
  change ‖unitaryConjugation (continuousMatchingUnitary p (iteratedSize n l) r
    (iteratedTuple n l s,iteratedTuple n l t)) _-_‖<ε
  apply hh.trans_lt
  change 6*L*ηs+ε/3<ε
  have heq : ηs*(3*(6*L+1))=ε := by
    dsimp [ηs]
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith

end JiangSuConstruction

end
end

end OAI
