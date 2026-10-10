import Mathlib
import OAI.Analysis.Commutator.CommutatorPerturbation
import OAI.Analysis.Commutator.EquivariantBicommutant

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (U : H ≃ₗᵢ[ℂ] K)

def algebra (M : VonNeumannAlgebra H) : VonNeumannAlgebra K where
  toStarSubalgebra := M.toStarSubalgebra.map U.conjStarAlgEquiv.toStarAlgHom
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (U.conjStarAlgEquiv.toMulEquiv '' (M : Set (H →L[ℂ] H))))=_
    rw [EquivariantBicommutant.bicommutant_image U.conjStarAlgEquiv.toMulEquiv]
    change U.conjStarAlgEquiv.toMulEquiv '' Set.centralizer (Set.centralizer M.carrier)=_
    rw [M.centralizer_centralizer']
    rfl

@[simp] lemma mem_algebra (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    U.conjStarAlgEquiv a∈algebra U M ↔ a∈M := by
  change (∃ b,b∈M ∧ U.conjStarAlgEquiv b=U.conjStarAlgEquiv a) ↔ a∈M
  constructor
  · rintro ⟨b,hb,he⟩
    exact U.conjStarAlgEquiv.injective he ▸ hb
  · intro ha; exact ⟨a,ha,rfl⟩

lemma conj_norm (a : H →L[ℂ] H) : ‖U.conjStarAlgEquiv a‖=‖a‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
    intro x
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.norm_map]
      using a.le_opNorm (U.symm x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.norm_map,
      U.symm_apply_apply] using (U.conjStarAlgEquiv a).le_opNorm (U x)

lemma seminorm (M : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    commutatorSeminorm (algebra U M) (U.conjStarAlgEquiv Y)=commutatorSeminorm M Y := by
  apply le_antisymm
  · apply commutatorSeminorm_le
    rintro a ⟨b,hb,rfl⟩ hna
    change ‖U.conjStarAlgEquiv Y * U.conjStarAlgEquiv b -
      U.conjStarAlgEquiv b * U.conjStarAlgEquiv Y‖ ≤ _
    rw [←map_mul,←map_mul,←map_sub,conj_norm]
    change ‖U.conjStarAlgEquiv b‖ ≤ 1 at hna
    exact commutator_bound_unitball M Y hb (by simpa only [conj_norm] using hna)
  · apply commutatorSeminorm_le
    intro a ha hna
    have hh := commutator_bound_unitball (algebra U M) (U.conjStarAlgEquiv Y)
      ((mem_algebra U M a).mpr ha) (by
        rw [conj_norm]
        exact hna)
    simpa only [←map_mul U.conjStarAlgEquiv,←map_sub U.conjStarAlgEquiv,
      conj_norm] using hh

def copies (h : ℕ) : PiLp 2 (fun _ : Fin h => H) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Fin h => K) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => U)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] lemma copies_apply (h : ℕ) (x : PiLp 2 (fun _ : Fin h => H)) (i : Fin h) :
    copies U h x i=U (x i) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] lemma copies_symm_apply (h : ℕ) (x : PiLp 2 (fun _ : Fin h => K)) (i : Fin h) :
    (copies U h).symm x i=U.symm (x i) := rfl

lemma diagonal (h : ℕ) (Y : H →L[ℂ] H) :
    (copies U h).conjStarAlgEquiv (diagonalAmplification h Y)=
      diagonalAmplification h (U.conjStarAlgEquiv Y) := by
  ext x i
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,copies_apply,copies_symm_apply,
    diagonalAmplification_apply]

lemma matrix (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) :
    (copies U h).conjStarAlgEquiv (matrixOperator h X)=
      matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j)) := by
  ext x i
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,copies_apply,copies_symm_apply,
    matrixOperator_apply,map_sum]
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using
    (matrixOperator_apply h (fun i j => U.conjStarAlgEquiv (X i j)) x i).symm

lemma matrix_norm (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) :
    ‖matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))‖=‖matrixOperator h X‖ := by
  rw [←matrix,conj_norm]

lemma matrix_commutator_norm (h : ℕ) (Y : H →L[ℂ] H)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) :
    ‖diagonalAmplification h (U.conjStarAlgEquiv Y)*
        matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))-
      matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))*
        diagonalAmplification h (U.conjStarAlgEquiv Y)‖=
      ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖ := by
  rw [←diagonal,←matrix,←map_mul,←map_mul,←map_sub,conj_norm]

end Kadison.UnitaryTransport

end

end
end

end OAI
