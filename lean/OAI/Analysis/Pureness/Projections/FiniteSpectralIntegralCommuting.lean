import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralAbelian
import OAI.Analysis.Pureness.Operators.PositiveContinuousRepresentation

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Set
open scoped NNReal ENNReal ComplexOrder IsMulCommutative
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteSpectralIntegral_add_commute
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤)
    (n : ℕ) (M N : Positive (FinMatrix A n)) (hMN : Commute M.1 N.1) :
    finiteSpectralIntegral d n (Positive.add M N) =
      finiteSpectralIntegral d n M + finiteSpectralIntegral d n N := by
  let S : StarSubalgebra ℂ (FinMatrix A n) := (StarAlgebra.adjoin ℂ {M.1,N.1}).topologicalClosure
  let : IsClosed (S : Set (FinMatrix A n)) := (StarAlgebra.adjoin ℂ {M.1,N.1}).isClosed_topologicalClosure
  have hcomm : ∀ x ∈ ({M.1,N.1} : Set (FinMatrix A n)), ∀ y ∈ ({M.1,N.1} : Set (FinMatrix A n)), x*y = y*x := by
    intro x hx y hy
    simp only [mem_insert_iff,mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hMN.eq
    · exact hMN.eq.symm
    · rfl
  let : IsMulCommutative (StarAlgebra.adjoin ℂ {M.1,N.1}) :=
    StarAlgebra.isMulCommutative_adjoin ℂ (by
      intro element hmem
      simp only [mem_insert_iff, mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl
      · exact M.2.isSelfAdjoint.isStarNormal
      · exact N.2.isSelfAdjoint.isStarNormal)
      (fun left hleft right hright _ => hcomm left hleft right hright) (by
      intro x hx y hy _
      have hyStar : star y = y := by
        simp only [mem_insert_iff,mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact M.2.star_eq
        · exact N.2.star_eq
      rw [hyStar]
      exact hcomm x hx y hy)
  let : IsMulCommutative S :=
    (StarAlgebra.adjoin ℂ {M.1,N.1}).isMulCommutative_topologicalClosure
  let : CommCStarAlgebra S := { }
  have hMS : M.1 ∈ S := (StarAlgebra.adjoin ℂ {M.1,N.1}).le_topologicalClosure
    (StarAlgebra.subset_adjoin ℂ _ (by simp))
  have hNS : N.1 ∈ S := (StarAlgebra.adjoin ℂ {M.1,N.1}).le_topologicalClosure
    (StarAlgebra.subset_adjoin ℂ _ (by simp))
  let X := WeakDual.characterSpace ℂ S
  let e := gelfandStarTransform S
  let φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n :=
    (S.subtype.comp e.symm.toStarAlgHom).toNonUnitalStarAlgHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  let m : C(X, ℂ) := e ⟨M.1,hMS⟩
  let q : C(X, ℂ) := e ⟨N.1,hNS⟩
  have hm : φ m = M.1 := by change (e.symm (e ⟨M.1,hMS⟩)).1 = M.1; rw [e.symm_apply_apply]
  have hq : φ q = N.1 := by change (e.symm (e ⟨N.1,hNS⟩)).1 = N.1; rw [e.symm_apply_apply]
  have hmpos : 0 ≤ m := (nonUnitalStarAlgHom_nonneg_iff φ hφ m).mp (hm.symm ▸ M.2)
  have hqpos : 0 ≤ q := (nonUnitalStarAlgHom_nonneg_iff φ hφ q).mp (hq.symm ▸ N.2)
  obtain ⟨f,hf⟩ := continuousNNRealPositive_surjective (⟨m,hmpos⟩ : Positive C(X, ℂ))
  obtain ⟨g,hg⟩ := continuousNNRealPositive_surjective (⟨q,hqpos⟩ : Positive C(X, ℂ))
  have hfM : Positive.map φ (continuousNNRealPositive f) = M := by rw [hf]; exact Subtype.ext hm
  have hgN : Positive.map φ (continuousNNRealPositive g) = N := by rw [hg]; exact Subtype.ext hq
  simpa only [hfM,hgN] using finiteSpectralIntegral_image_add d hd hlsc hfinite n φ f g
end CuntzPureness

end

end OAI
