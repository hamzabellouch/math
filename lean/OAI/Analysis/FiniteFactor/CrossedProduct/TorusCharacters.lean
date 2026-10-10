import OAI.Analysis.FiniteFactor.CrossedProduct.TorusModel
import OAI.Analysis.FiniteFactor.CrossedProduct.AngleRelations
import Mathlib.Analysis.Fourier.AddCircle

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set Algebra Submodule
open scoped ENNReal ComplexConjugate
noncomputable section

def sourceCharacter (v : SourceCoordinate →₀ ℤ) : C(SourceTorus, ℂ) where
  toFun x := fourier 1 (v.sum fun i n => n • x i)
  continuous_toFun := (fourier 1).continuous.comp (by
    unfold Finsupp.sum
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).zsmul (v i))

theorem sourceCharacter_zero : sourceCharacter 0 = 1 := by
  ext x
  simp [sourceCharacter]

theorem sourceCharacter_add (v w : SourceCoordinate →₀ ℤ) :
    sourceCharacter (v+w) = sourceCharacter v * sourceCharacter w := by
  ext x
  simp only [sourceCharacter, ContinuousMap.coe_mk, ContinuousMap.mul_apply]
  rw [Finsupp.sum_add_index (by simp) (by intros; simp [add_zsmul])]
  simp [fourier, AddCircle.toCircle_add]

theorem sourceCharacter_neg (v : SourceCoordinate →₀ ℤ) :
    sourceCharacter (-v) = star (sourceCharacter v) := by
  ext x
  have he := congrArg (fun f : C(SourceTorus, ℂ) => f x) (sourceCharacter_add v (-v))
  rw [add_neg_cancel, sourceCharacter_zero] at he
  have hn : ‖sourceCharacter v x‖ = 1 := by
    change ‖(AddCircle.toCircle (1 • v.sum (fun i n => n • x i)) : ℂ)‖ = 1
    exact Circle.norm_coe _
  have hc : sourceCharacter v x * star (sourceCharacter v x) = 1 := by
    change sourceCharacter v x * conj (sourceCharacter v x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  change sourceCharacter (-v) x = star (sourceCharacter v x)
  exact mul_left_cancel₀ (by intro h; simp [h] at hn) (he.symm.trans hc.symm)

def sourceCharacterAlgebra : StarSubalgebra ℂ C(SourceTorus, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range sourceCharacter)
  star_mem' := by
    change Algebra.adjoin ℂ (range sourceCharacter) ≤ star (Algebra.adjoin ℂ (range sourceCharacter))
    refine adjoin_le ?_
    rintro _ ⟨v,rfl⟩
    exact subset_adjoin ⟨-v,sourceCharacter_neg v⟩

theorem sourceCharacterAlgebra_span :
    sourceCharacterAlgebra.toSubalgebra.toSubmodule = span ℂ (range sourceCharacter) := by
  apply adjoin_eq_span_of_subset
  refine .trans (fun x => Submonoid.closure_induction (fun _ => id) ⟨0,sourceCharacter_zero⟩ ?_) subset_span
  rintro _ _ _ _ ⟨v,rfl⟩ ⟨w,rfl⟩
  exact ⟨v+w,sourceCharacter_add v w⟩

theorem sourceCharacter_single (i : SourceCoordinate) (x : SourceTorus) :
    sourceCharacter (Finsupp.single i 1) x = fourier 1 (x i) := by
  simp [sourceCharacter, Finsupp.sum_single_index]

theorem sourceCharacterAlgebra_separates : sourceCharacterAlgebra.SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_,⟨sourceCharacter (Finsupp.single i 1),subset_adjoin ⟨_,rfl⟩,rfl⟩,?_⟩
  dsimp only
  rw [sourceCharacter_single,sourceCharacter_single,fourier_one,fourier_one,Ne,Circle.coe_inj]
  exact fun he => hi (AddCircle.injective_toCircle one_ne_zero he)

/-- Uniform density on the full countable product, with no finite-dimensional truncation assumption. -/
theorem sourceCharacter_span_dense :
    (span ℂ (range sourceCharacter)).topologicalClosure = ⊤ := by
  rw [← sourceCharacterAlgebra_span]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      sourceCharacterAlgebra_separates)

abbrev sourceCharacterL2 (v : SourceCoordinate →₀ ℤ) : Lp ℂ 2 sourceTorusHaar :=
  ContinuousMap.toLp 2 sourceTorusHaar ℂ (sourceCharacter v)

theorem sourceCharacterL2_span_dense :
    (span ℂ (range sourceCharacterL2)).topologicalClosure = ⊤ := by
  simpa only [map_span,ContinuousLinearMap.coe_coe,← range_comp,Function.comp_def] using
    (ContinuousMap.toLp_denseRange ℂ sourceTorusHaar ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).topologicalClosure_map_submodule
      sourceCharacter_span_dense

end
end FiniteFactor

end OAI
