import OAI.Analysis.KadisonKastler.ProperInfiniteProjectionCopies
import OAI.Analysis.KadisonKastler.CanonicalMatrixCorner
import OAI.Analysis.KadisonKastler.SymmetricSupportTransfer

namespace OAI

/-! # Full projection copies identify the countable Hilbert amplification -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

namespace CountableProjectionCopies

variable (C : CountableProjectionCopies M (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))

def fullCopyIsometry (i : ℕ) : H →ₗᵢ[ℂ] H where
  toLinearMap := (C.witness i).val.toLinearMap
  norm_map' x := norm_apply_of_operator_isometry (C.witness i).val
    (congrArg Subtype.val (C.initial i)) x

theorem fullCopyIsometry_orthogonal :
    OrthogonalFamily ℂ (fun _ : ℕ => H) C.fullCopyIsometry := by
  intro i j hij x y
  have hvi : (C.projection i).val*C.witness i=C.witness i := by
    rw [← C.final,mul_assoc,C.initial,mul_one]
  have hvj : (C.projection j).val*C.witness j=C.witness j := by
    rw [← C.final,mul_assoc,C.initial,mul_one]
  have hvi' : star (C.witness i)*(C.projection i).val=star (C.witness i) := by
    simpa only [star_mul,(C.projection i).property.isSelfAdjoint.star_eq] using congrArg star hvi
  have hc : star (C.witness i)*C.witness j=0 := by
    calc
      _ = (star (C.witness i)*(C.projection i).val)*
          ((C.projection j).val*C.witness j) := by rw [hvi',hvj]
      _ = star (C.witness i)*((C.projection i).val*(C.projection j).val)*C.witness j := by
        simp only [mul_assoc]
      _ = 0 := by rw [C.orthogonal hij,mul_zero,zero_mul]
  change inner ℂ ((C.witness i).val x) ((C.witness j).val y)=0
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ x ((star (C.witness i)*C.witness j).val y)=0
  rw [hc]
  simp

theorem fullCopyIsometry_total :
    ⊤ ≤ (⨆ i, LinearMap.range (C.fullCopyIsometry i).toLinearMap).topologicalClosure := by
  intro x _
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (C.total x)
  apply Filter.Eventually.of_forall
  intro F
  apply Submodule.sum_mem
  intro i _
  apply Submodule.le_topologicalClosure
  apply (le_iSup (fun j => LinearMap.range (C.fullCopyIsometry j).toLinearMap) i)
  refine ⟨(star (C.witness i)).val x,?_⟩
  change (C.witness i).val ((star (C.witness i)).val x)=(C.projection i).val.val x
  exact congrArg (fun a : Algebra M => a.val x) (C.final i)

theorem fullCopyHilbertSum : IsHilbertSum ℂ (fun _ : ℕ => H) C.fullCopyIsometry :=
  IsHilbertSum.mk C.fullCopyIsometry_orthogonal C.fullCopyIsometry_total

def fullCopyUnitary : CountableHilbertSum H ≃ₗᵢ[ℂ] H :=
  C.fullCopyHilbertSum.linearIsometryEquiv.symm

theorem fullCopyUnitary_single (i : ℕ) (x : H) :
    C.fullCopyUnitary (lp.single 2 i x)=(C.witness i).val x :=
  C.fullCopyHilbertSum.linearIsometryEquiv_symm_apply_single x

theorem fullCopyUnitary_intertwines (a : H →L[ℂ] H)
    (ha : ∀ i, Commute a (C.witness i).val) (x : CountableHilbertSum H) :
    C.fullCopyUnitary (l2Diagonal a x)=a (C.fullCopyUnitary x) := by
  have hs := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x
  have h1 := (C.fullCopyUnitary.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (l2Diagonal a)).hasSum hs
  have h2 := (a.comp C.fullCopyUnitary.toContinuousLinearEquiv.toContinuousLinearMap).hasSum hs
  have he (i : ℕ) :
      C.fullCopyUnitary (l2Diagonal a (lp.single 2 i (x i)))=
        a (C.fullCopyUnitary (lp.single 2 i (x i))) := by
    have hl : l2Diagonal a (lp.single 2 i (x i))=lp.single 2 i (a (x i)) := by
      ext j
      by_cases hji : j=i
      · subst j
        simp
      · simp [lp.single_apply,hji]
    rw [hl,fullCopyUnitary_single,fullCopyUnitary_single]
    exact congrArg (fun T : H →L[ℂ] H => T (x i)) (ha i).symm
  change HasSum (fun i => C.fullCopyUnitary (l2Diagonal a (lp.single 2 i (x i)))) _ at h1
  change HasSum (fun i => a (C.fullCopyUnitary (lp.single 2 i (x i)))) _ at h2
  simp_rw [he] at h1
  exact h1.unique h2

end CountableProjectionCopies

end

end KadisonKastler

end OAI
