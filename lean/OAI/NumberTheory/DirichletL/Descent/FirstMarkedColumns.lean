import OAI.NumberTheory.DirichletL.Descent.FirstPhysicalTail
import OAI.NumberTheory.DirichletL.Descent.MarkBounds

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]

theorem cube_whole_column_norm (p : ι→O) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C N : Finset ι) (hC : Disjoint C b.support) (hN : Disjoint N (b.support∪C))
    (negative : Bool) :
    primeProductNorm p (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N) =
      ‖eisEmbedding (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
        primeProductNorm p C * primeProductNorm p N := by
  have hd : (if negative then b.rightDivisor else b.leftDivisor) ⊆ b.support := by
    cases negative
    · exact hb.1
    · exact hb.2
  rw [primeProductNorm_union p _ _ (hN.symm.mono_left (Finset.union_subset_union hd (Finset.Subset.refl C))),
    primeProductNorm_union p _ _ (hC.symm.mono_left hd)]
  congr 2
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [CubeCoordinates.aLabel_left p b hb]; rfl
  · rw [CubeCoordinates.aLabel_right p b hb]; rfl

def wholeMarkedTest {σ : Type*} [DecidableEq σ] (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (test : Finset ι→ℂ) (U : Finset ι) : ℂ :=
  primeMark slots lists a U * test U

theorem whole_marked_test_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ, 0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test : Finset ι→ℂ) (G L : ℝ),0≤G → 0≤L →
      (∀ U,‖test U‖≤G) → (∀ U,test U≠0 → primeProductNorm p U≤L) →
      ∀ U,‖wholeMarkedTest slots lists a test U‖≤Cm*L^ε*G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha test G L hG hL hb hs U
  by_cases hz : test U=0
  · simp only [wholeMarkedTest,hz,mul_zero,norm_zero]; positivity
  · have hn0 := (primeProductNorm_pos p hp U).le
    rw [wholeMarkedTest,norm_mul]
    calc
      _ ≤ (Cm*(primeProductNorm p U)^ε)*G :=
        mul_le_mul (hmark p hp hcop slots lists a hslots ha U) (hb U) (norm_nonneg _) (by positivity)
      _ ≤ Cm*L^ε*G := by gcongr; exact hs U hz

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_residual_norm (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (hΨ : ∀ u,‖Ψ u‖≤1) (m f : O) (H : Finset ι→ℂ) (N : Finset ι) :
    ‖canonicalCubeResidual p hg b C negative Ψ m f H N‖ ≤
      ‖H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N)‖ := by
  exact originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit negative
    Ψ hΨ m (∏i∈C,p i) f _ N

theorem canonical_residual_test_nonzero (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) (N : Finset ι)
    (hn : canonicalCubeResidual p hg b C negative Ψ m f H N≠0) :
    H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N)≠0 := by
  exact originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit negative
    Ψ m (∏i∈C,p i) f _ N hn

theorem canonical_marked_residual_support {σ : Type*} [DecidableEq σ]
    (b : CubeCoordinates ι) (hb : b.Admissible) (C N : Finset ι)
    (hC : Disjoint C b.support) (hN : Disjoint N (b.support∪C)) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (test : Finset ι→ℂ) (L : ℝ) (hs : ∀ U,test U≠0 → primeProductNorm p U≤L)
    (hn : canonicalCubeResidual p hg b C negative Ψ m f (wholeMarkedTest slots lists a test) N≠0) :
    ‖eisEmbedding (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
      primeProductNorm p C * primeProductNorm p N≤L := by
  have ht := canonical_residual_test_nonzero p hg b C negative Ψ m f _ N hn
  have htest := (mul_ne_zero_iff.mp ht).2
  simpa only [cube_whole_column_norm p b hb C N hC hN negative] using hs _ htest

end
end SevenEighths.InverseMoment

end OAI
