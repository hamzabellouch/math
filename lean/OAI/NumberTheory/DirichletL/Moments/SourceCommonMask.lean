import OAI.NumberTheory.DirichletL.Moments.CommonProfile
import OAI.NumberTheory.DirichletL.Moments.CompleteCommon

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceCommonMask
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem profile_nonzero_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι)
    (hne : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    IsCoprime (finiteTupleProduct v) R ∧ s∣finiteTupleProduct v := by
  constructor
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero,zero_mul])
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero])

theorem column_nonzero_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (S : Finset (Tuple ι)) (I : Ideal O)
    (hne : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) :
    IsCoprime I R ∧ s∣I := by
  obtain ⟨v,hv,hvne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have he := (Finset.mem_filter.mp hv).2
  have hm := profile_nonzero_masks R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v hvne
  rwa [he] at hm

theorem pair_common_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (hs : Squarefree s)
    (S : Finset (Tuple ι)) (I J : Ideal O) (hI : I≠0) (hJ : J≠0)
    (hi : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0)
    (hj : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) J≠0) :
    s∣commonPart I J ∧ s∣commonPart J I ∧
      IsCoprime (commonPart I J) R ∧ IsCoprime (commonPart J I) R := by
  have hmi := column_nonzero_masks R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s S I hi
  have hmj := column_nonzero_masks R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s S J hj
  have hd := squarefree_mask_survives s I J hs hI hJ hmi.2 hmj.2
  exact ⟨hd.2.1,hd.2.2.1,
    hmi.1.of_isCoprime_of_dvd_left (commonPart_dvd I J hI),
    hmj.1.of_isCoprime_of_dvd_left (commonPart_dvd J I hJ)⟩

end SevenEighths.CenteredMomentSourceCommonMask

end

end OAI
