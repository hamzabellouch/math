import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Pair
import OAI.Analysis.MatrixSigning.Potential.NormalizedMinimizer

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

abbrev PairHilbert (d : ℕ) := WithLp 2 (H d × H d)

private local instance : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace

def pairEquiv (d : ℕ) : PairHilbert d ≃L[ℝ] Pair d :=
  WithLp.prodContinuousLinearEquiv 2 ℝ (H d) (H d)

def pairHilbertCone (d : ℕ) : ConvexCone ℝ (PairHilbert d) where
  carrier := {z | pairEquiv d z ∈ pairCone d}
  smul_mem' a ha z hz := by
    change pairEquiv d (a • z) ∈ pairCone d
    rw [map_smul]
    exact (pairCone d).smul_mem ha hz
  add_mem' z hz w hw := by
    change pairEquiv d (z+w) ∈ pairCone d
    rw [map_add]
    exact (pairCone d).add_mem hz hw

lemma pairHilbertCone_pointed (z : PairHilbert d)
    (hz : z ∈ pairHilbertCone d) (hnz : -z ∈ pairHilbertCone d) : z = 0 := by
  apply (pairEquiv d).injective
  rw [map_zero]
  have hn : -(pairEquiv d z) ∈ pairCone d := by
    change pairEquiv d (-z) ∈ pairCone d at hnz
    rwa [map_neg] at hnz
  exact Prod.ext (psd_pointed _ hz.1 hn.1) (psd_pointed _ hz.2 hn.2)

lemma isClosed_pairHilbertCone : IsClosed (pairHilbertCone d : Set (PairHilbert d)) :=
  isClosed_pairCone.preimage (pairEquiv d).continuous

lemma pairHilbert_interior [NeZero d] {P Q : H d} (hP : P ∈ pd d) (hQ : Q ∈ pd d) :
    (pairEquiv d).symm (P,Q) ∈ interior (pairHilbertCone d : Set (PairHilbert d)) := by
  change (pairEquiv d).symm (P,Q) ∈ interior ((pairEquiv d).toHomeomorph ⁻¹' (pairCone d : Set (Pair d)))
  rw [← (pairEquiv d).toHomeomorph.preimage_interior]
  change pairEquiv d ((pairEquiv d).symm (P,Q)) ∈ interior (pairCone d : Set (Pair d))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact pair_pd_interior hP hQ

def onPairHilbert (T : Pair d →L[ℝ] Pair d) : PairHilbert d →L[ℝ] PairHilbert d :=
  (pairEquiv d).symm.toContinuousLinearMap.comp (T.comp (pairEquiv d).toContinuousLinearMap)

lemma linConstraint_symmetric (X Y : H d) (η : H d →L[ℝ] H d) (hη : SymmetricMap η) :
    LinearMap.IsSymmetric (𝕜 := ℝ) (E := PairHilbert d) (onPairHilbert (linConstraint X Y η)).toLinearMap := by
  intro u v
  change inner ℝ (sandwich (invH X) (WithLp.ofLp u).1 - η (WithLp.ofLp u).2) (WithLp.ofLp v).1 +
    inner ℝ (sandwich (invH Y) (WithLp.ofLp u).2 - η (WithLp.ofLp u).1) (WithLp.ofLp v).2 =
    inner ℝ (WithLp.ofLp u).1 (sandwich (invH X) (WithLp.ofLp v).1 - η (WithLp.ofLp v).2) +
    inner ℝ (WithLp.ofLp u).2 (sandwich (invH Y) (WithLp.ofLp v).2 - η (WithLp.ofLp v).1)
  simp only [inner_sub_left, inner_sub_right, inner_sandwich]
  rw [hη (WithLp.ofLp u).1 (WithLp.ofLp v).2, hη (WithLp.ofLp u).2 (WithLp.ofLp v).1]
  ring

lemma linConstraint_stationary (X Y P Q : H d) (η : H d →L[ℝ] H d) (ε : ℝ)
    (hPX : sandwich (invH X) P = η Q + ε • (Hermitian.one : H d))
    (hQY : sandwich (invH Y) Q = η P + ε • (Hermitian.one : H d)) :
    linConstraint X Y η (P,Q) = ε • ((Hermitian.one : H d),Hermitian.one) := by
  calc
    _ = (sandwich (invH X) P - η Q, sandwich (invH Y) Q - η P) :=
      linConstraint_apply X Y η (P, Q)
    _ = _ := by
      rw [hPX, hQY]
      apply Prod.ext <;> simp

theorem linConstraint_inverse_norm [NeZero d]
    (X Y P Q : H d) (η : H d →L[ℝ] H d) (hη : SymmetricMap η)
    {ε : ℝ} (hε : 0 < ε)
    (hPle : P ≤ (Hermitian.one : H d)) (hQle : Q ≤ (Hermitian.one : H d))
    (hPX : sandwich (invH X) P = η Q + ε • (Hermitian.one : H d))
    (hQY : sandwich (invH Y) Q = η P + ε • (Hermitian.one : H d))
    (V : Pair d ≃L[ℝ] Pair d) (hV : ∀ z, V z = linConstraint X Y η z)
    (hVpos : ∀ z ∈ pairCone d, V.symm z ∈ pairCone d) :
    ‖onPairHilbert V.symm.toContinuousLinearMap‖ ≤ ε⁻¹ := by
  let e := pairEquiv d
  let W := (e.trans V).trans e.symm
  have hW : LinearMap.IsSymmetric (𝕜 := ℝ) (E := PairHilbert d) W.toLinearEquiv.toLinearMap := by
    convert linConstraint_symmetric X Y η hη using 1
    ext z
    change e.symm (V (e z)) = e.symm (linConstraint X Y η (e z))
    rw [hV]
  have hWsym : LinearMap.IsSymmetric (𝕜 := ℝ) (E := PairHilbert d) (onPairHilbert V.symm.toContinuousLinearMap).toLinearMap :=
    hW.toLinearMap_symm
  let E : Pair d := ((Hermitian.one : H d),Hermitian.one)
  have hVE : V (P,Q) = ε • E := by
    rw [hV]
    exact linConstraint_stationary X Y P Q η ε hPX hQY
  have hiE : V.symm E = ε⁻¹ • (P,Q) := by
    apply V.injective
    rw [V.apply_symm_apply, map_smul, hVE, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  have hp : e.symm E ∈ interior (pairHilbertCone d : Set (PairHilbert d)) :=
    pairHilbert_interior Matrix.PosDef.one Matrix.PosDef.one
  apply CurrentKS.PositiveMap.symmetric_norm_bound (pairHilbertCone d)
    (show (0 : PairHilbert d) ∈ pairHilbertCone d from ⟨zero_mem_psdCone, zero_mem_psdCone⟩)
    isClosed_pairHilbertCone pairHilbertCone_pointed
    (onPairHilbert V.symm.toContinuousLinearMap)
    (fun z hz => by
      change e (e.symm (V.symm (e z))) ∈ pairCone d
      rw [e.apply_symm_apply]
      exact hVpos _ hz)
    hWsym hp (inv_pos.mpr hε).le
  change e (ε⁻¹ • e.symm E - e.symm (V.symm (e (e.symm E)))) ∈ pairCone d
  simp only [map_sub, map_smul, e.apply_symm_apply, hiE]
  rw [← smul_sub ε⁻¹ E (P,Q)]
  apply CurrentKS.PositiveMap.cone_smul_nonneg (pairCone d)
    ⟨zero_mem_psdCone,zero_mem_psdCone⟩ (inv_pos.mpr hε).le
  exact ⟨(mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hPle),
    (mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hQle)⟩

end
end CurrentKS.Variational

end OAI
