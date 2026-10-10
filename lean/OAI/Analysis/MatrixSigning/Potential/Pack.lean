import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Vars
import OAI.Analysis.MatrixSigning.Optimization.EquivSymmetricMap
import OAI.Analysis.MatrixSigning.Matrices.JordanCLMStrictPos

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d : ℕ}

def pack (z : Point d) (P Q : H d) : Vars d :=
  (z.1, (pairEquiv d).symm z.2, (pairEquiv d).symm (P,Q))

def unpack (z : Vars d) : Point d := (tCoord d z, xCoord d z, yCoord d z)

lemma identityPair_ne_zero [NeZero d] : identityPair d ≠ 0 := by
  intro h
  have he : (Hermitian.one : H d) = 0 := congrArg (fun u : PairHilbert d => (WithLp.ofLp u).1) h
  have hh := congrArg (fun A : H d => (A : Mat d) 0 0) he
  simp at hh

lemma hessian_strict_pos [NeZero d] (X Y P Q : H d)
    (hX : X ∈ pd d) (hY : Y ∈ pd d) (hP : P ∈ pd d) (hQ : Q ∈ pd d)
    (u : PairHilbert d) (hu : u ≠ 0) : 0 < inner ℝ u (hessian X Y P Q u) := by
  have hp := sandwich_pd (invH X) P hX.inv hP
  have hq := sandwich_pd (invH Y) Q hY.inv hQ
  have h₁ : 0 ≤ inner ℝ (WithLp.ofLp u).1
      (jordanCLM (invH X) (sandwich (invH X) P) (WithLp.ofLp u).1) := by
    rw [jordanCLM_quadratic]
    exact mul_nonneg (by norm_num) (inner_nonneg_of_psd _ _ hp.posSemidef
      (sandwich_psd _ _ hX.inv.posSemidef))
  have h₂ : 0 ≤ inner ℝ (WithLp.ofLp u).2
      (jordanCLM (invH Y) (sandwich (invH Y) Q) (WithLp.ofLp u).2) := by
    rw [jordanCLM_quadratic]
    exact mul_nonneg (by norm_num) (inner_nonneg_of_psd _ _ hq.posSemidef
      (sandwich_psd _ _ hY.inv.posSemidef))
  change 0 < inner ℝ (WithLp.ofLp u).1
      (jordanCLM (invH X) (sandwich (invH X) P) (WithLp.ofLp u).1) +
    inner ℝ (WithLp.ofLp u).2
      (jordanCLM (invH Y) (sandwich (invH Y) Q) (WithLp.ofLp u).2)
  by_cases hx : (WithLp.ofLp u).1 = 0
  · have hy : (WithLp.ofLp u).2 ≠ 0 := by
      intro hy
      apply hu
      apply (pairEquiv d).injective
      exact Prod.ext hx hy
    exact add_pos_of_nonneg_of_pos h₁ (jordanCLM_strict_pos _ _ hY.inv hq _ hy)
  · exact add_pos_of_pos_of_nonneg (jordanCLM_strict_pos _ _ hX.inv hp _ hx) h₂

theorem kkt_regular [NeZero d] (X Y P Q : H d) (η : H d →L[ℝ] H d)
    (hηpos : ∀ A ∈ psdCone d, η A ∈ psdCone d) (hηsym : SymmetricMap η)
    (hX : X ∈ pd d) (hY : Y ∈ pd d) (hP : P ∈ pd d) (hQ : Q ∈ pd d)
    {ε : ℝ} (hε : 0 < ε)
    (hPX : P = sandwich X (η Q) + ε • sandwich X (Hermitian.one : H d))
    (hQY : Q = sandwich Y (η P) + ε • sandwich Y (Hermitian.one : H d)) :
    ∃ J : Vars d ≃L[ℝ] Vars d, ∀ v, J v = CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint X Y η)) (hessian X Y P Q) v := by
  obtain ⟨V,hV,_⟩ := linConstraint_positive_inverse X Y P Q η hηpos hX hY hP hQ hε hPX hQY
  let L : PairHilbert d ≃L[ℝ] PairHilbert d := ((pairEquiv d).trans V).trans (pairEquiv d).symm
  have he : L.toContinuousLinearMap = onPairHilbert (linConstraint X Y η) := by
    apply ContinuousLinearMap.ext
    intro u
    change (pairEquiv d).symm (V (pairEquiv d u)) =
      (pairEquiv d).symm (linConstraint X Y η (pairEquiv d u))
    rw [hV]
  have hs := CurrentKS.KKT.equiv_symmetric_of_map_eq L _ he
    (linConstraint_symmetric X Y η hηsym)
  obtain ⟨J,hJ⟩ := CurrentKS.KKT.exists_jacobian_equiv (identityPair d)
    identityPair_ne_zero L hs (hessian X Y P Q) (hessian_strict_pos X Y P Q hX hY hP hQ)
  refine ⟨J, fun v => ?_⟩
  exact (hJ v).trans (congrArg (fun T =>
    CurrentKS.KKT.jacobian (identityPair d) T (hessian X Y P Q) v) he)

lemma pack_kkt (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Point d) (P Q : H d)
    (htr : realTrace P + realTrace Q = 1)
    (ht : residual S η z = 0)
    (hX : sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d))
    (hY : sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d)) :
    kktSystem ε S η (pack z P Q) = 0 := by
  apply Prod.ext
  · change inner ℝ (Hermitian.one : H d) P + inner ℝ (Hermitian.one : H d) Q - 1 = 0
    rw [inner_one,inner_one,htr]
    ring
  · apply Prod.ext
    · apply (pairEquiv d).injective
      have ht₁ := congrArg Prod.fst ht
      have ht₂ := congrArg Prod.snd ht
      change invH z.2.1 + S + η z.2.2 - z.1 • (Hermitian.one : H d) = 0 at ht₁
      change invH z.2.2 - S + η z.2.1 - z.1 • (Hermitian.one : H d) = 0 at ht₂
      apply Prod.ext
      · change z.1 • (Hermitian.one : H d) - invH z.2.1 - S - η z.2.2 = 0
        calc
          _ = -(invH z.2.1 + S + η z.2.2 - z.1 • (Hermitian.one : H d)) := by module
          _ = 0 := by rw [ht₁, neg_zero]
      · change z.1 • (Hermitian.one : H d) - invH z.2.2 + S - η z.2.1 = 0
        calc
          _ = -(invH z.2.2 - S + η z.2.1 - z.1 • (Hermitian.one : H d)) := by module
          _ = 0 := by rw [ht₂, neg_zero]
    · apply (pairEquiv d).injective
      apply Prod.ext
      · change sandwich (invH z.2.1) P - η Q - ε • (Hermitian.one : H d) = 0
        rw [hX]
        module
      · change sandwich (invH z.2.2) Q - η P - ε • (Hermitian.one : H d) = 0
        rw [hY]
        module

end
end CurrentKS.Variational

end OAI
