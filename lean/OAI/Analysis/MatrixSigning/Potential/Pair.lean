import Mathlib
import OAI.Analysis.MatrixSigning.Potential.LagrangianObjective
import OAI.Analysis.MatrixSigning.Matrices.SandwichCLM

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

abbrev Pair (d : ℕ) := H d × H d

def linConstraint (X Y : H d) (η : H d →L[ℝ] H d) : Pair d →L[ℝ] Pair d :=
  ((sandwichCLM (invH X)).comp (ContinuousLinearMap.fst ℝ (H d) (H d)) -
    η.comp (ContinuousLinearMap.snd ℝ (H d) (H d))).prod
  ((sandwichCLM (invH Y)).comp (ContinuousLinearMap.snd ℝ (H d) (H d)) -
    η.comp (ContinuousLinearMap.fst ℝ (H d) (H d)))

def linPositive (X Y : H d) (η : H d →L[ℝ] H d) : Pair d →L[ℝ] Pair d :=
  ((sandwichCLM X).comp (η.comp (ContinuousLinearMap.snd ℝ (H d) (H d)))).prod
    ((sandwichCLM Y).comp (η.comp (ContinuousLinearMap.fst ℝ (H d) (H d))))

def linCongruence (X Y : H d) : Pair d →L[ℝ] Pair d :=
  ((sandwichCLM X).comp (ContinuousLinearMap.fst ℝ (H d) (H d))).prod
    ((sandwichCLM Y).comp (ContinuousLinearMap.snd ℝ (H d) (H d)))

@[simp] lemma linConstraint_apply (X Y : H d) (η : H d →L[ℝ] H d) (z : Pair d) :
    linConstraint X Y η z = (sandwich (invH X) z.1 - η z.2,
      sandwich (invH Y) z.2 - η z.1) := rfl

@[simp] lemma linPositive_apply (X Y : H d) (η : H d →L[ℝ] H d) (z : Pair d) :
    linPositive X Y η z = (sandwich X (η z.2), sandwich Y (η z.1)) := rfl

@[simp] lemma linCongruence_apply (X Y : H d) (z : Pair d) :
    linCongruence X Y z = (sandwich X z.1, sandwich Y z.2) := rfl

lemma linPositive_preserves (X Y : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d) (z : Pair d) (hz : z ∈ pairCone d) :
    linPositive X Y η z ∈ pairCone d :=
  ⟨sandwich_psd _ _ (hη z.2 hz.2), sandwich_psd _ _ (hη z.1 hz.1)⟩

lemma linCongruence_preserves (X Y : H d) (z : Pair d) (hz : z ∈ pairCone d) :
    linCongruence X Y z ∈ pairCone d :=
  ⟨sandwich_psd _ _ hz.1, sandwich_psd _ _ hz.2⟩

lemma linConstraint_conjugate (X Y : H d) (η : H d →L[ℝ] H d)
    (hX : X ∈ pd d) (hY : Y ∈ pd d) (z : Pair d) :
    linCongruence X Y (linConstraint X Y η z) = z - linPositive X Y η z := by
  apply Prod.ext
  · change sandwich X (sandwich (invH X) z.1 - η z.2) = _
    rw [sandwich_sub, sandwich_inverse_cancel X z.1 hX]
    rfl
  · change sandwich Y (sandwich (invH Y) z.2 - η z.1) = _
    rw [sandwich_sub, sandwich_inverse_cancel Y z.2 hY]
    rfl

lemma pair_pd_interior [NeZero d] {P Q : H d} (hP : P ∈ pd d) (hQ : Q ∈ pd d) :
    (P,Q) ∈ interior (pairCone d : Set (Pair d)) := by
  change (P,Q) ∈ interior ((psdCone d : Set (H d)) ×ˢ (psdCone d : Set (H d)))
  rw [interior_prod_eq]
  exact ⟨posDef_mem_interior _ hP, posDef_mem_interior _ hQ⟩

theorem linConstraint_positive_inverse [NeZero d]
    (X Y P Q : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    (hX : X ∈ pd d) (hY : Y ∈ pd d) (hP : P ∈ pd d) (hQ : Q ∈ pd d)
    {ε : ℝ} (hε : 0 < ε)
    (hPX : P = sandwich X (η Q) + ε • sandwich X (Hermitian.one : H d))
    (hQY : Q = sandwich Y (η P) + ε • sandwich Y (Hermitian.one : H d)) :
    ∃ V : Pair d ≃L[ℝ] Pair d, (∀ z, V z = linConstraint X Y η z) ∧
      ∀ z ∈ pairCone d, V.symm z ∈ pairCone d := by
  have hgap : (P,Q) - linPositive X Y η (P,Q) ∈ interior (pairCone d : Set (Pair d)) := by
    have he : (P,Q) - linPositive X Y η (P,Q) =
        (ε • sandwich X (Hermitian.one : H d), ε • sandwich Y (Hermitian.one : H d)) := by
      apply Prod.ext <;> simp only [linPositive_apply, Prod.fst_sub, Prod.snd_sub]
      · rw [hPX]; abel
      · rw [hQY]; abel
    rw [he]
    apply pair_pd_interior
    · rw [← sandwich_smul]
      exact sandwich_pd X _ hX (scalar_posDef hε)
    · rw [← sandwich_smul]
      exact sandwich_pd Y _ hY (scalar_posDef hε)
  obtain ⟨N, hN, hNpos⟩ := CurrentKS.PositiveMap.positive_inverse_of_gap
    (pairCone d) ⟨zero_mem_psdCone,zero_mem_psdCone⟩ isClosed_pairCone
    (fun z hz hnz => Prod.ext (psd_pointed _ hz.1 hnz.1) (psd_pointed _ hz.2 hnz.2))
    (linPositive X Y η) (linPositive_preserves X Y η hη)
    (pair_pd_interior hP hQ) hgap
  have he (z : Pair d) : linCongruence X Y (linConstraint X Y η z) = N z := by
    rw [hN]
    exact linConstraint_conjugate X Y η hX hY z
  have hinj : Function.Injective (linConstraint X Y η).toLinearMap := by
    intro u v huv
    apply N.injective
    rw [← he, ← he]
    exact congrArg (linCongruence X Y) huv
  let V : Pair d ≃L[ℝ] Pair d :=
    (LinearEquiv.ofBijective (linConstraint X Y η).toLinearMap
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  refine ⟨V, fun _ => rfl, fun z hz => ?_⟩
  have hh : V.symm z = N.symm (linCongruence X Y z) := by
    apply N.injective
    rw [N.apply_symm_apply, ← he]
    change linCongruence X Y (V (V.symm z)) = _
    rw [V.apply_symm_apply]
  rw [hh]
  exact hNpos _ (linCongruence_preserves X Y z hz)

end
end CurrentKS.Variational

end OAI
