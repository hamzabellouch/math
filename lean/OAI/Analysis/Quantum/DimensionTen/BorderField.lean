import OAI.Analysis.Quantum.DimensionTen.FieldRepresentation
import OAI.Analysis.Quantum.DimensionTen.NormalizedMatrices

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

abbrev fQ : ℚ[X] := F.map (algebraMap ℤ ℚ)
abbrev L := AdjoinRoot fQ
instance : Fact (Irreducible fQ) := ⟨F_irreducible⟩
instance : FiniteDimensional ℚ L := (AdjoinRoot.powerBasis F_irreducible.ne_zero).finite

lemma fQ_degree : fQ.natDegree = 20 := by
  rw [F_monic.natDegree_map]
  exact F_degree

lemma eQ_ne : eQ 0 ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simp [eQ] at hh

lemma representation_exists :
    ∃ ρ : L →ₐ[ℚ] Matrix (Fin 20) (Fin 20) ℚ,
      ρ (AdjoinRoot.root fQ) = B0.map (Int.castRingHom ℚ) ∧
      Function.Bijective (fun a => ρ a *ᵥ eQ 0) :=
  Arithmetic.field_representation fQ F_irreducible fQ_degree _ QB_annihilator _ eQ_ne

def rho : L →ₐ[ℚ] Matrix (Fin 20) (Fin 20) ℚ := representation_exists.choose

lemma rho_root : rho (AdjoinRoot.root fQ) = B0.map (Int.castRingHom ℚ) :=
  representation_exists.choose_spec.1

lemma rho_eval_bijective : Function.Bijective (fun a => rho a *ᵥ eQ 0) :=
  representation_exists.choose_spec.2

def E : L →ₗ[ℚ] (Fin 20 → ℚ) :=
  { toFun := fun a => rho a *ᵥ eQ 0
    map_add' := fun a b => by simp only [map_add, Matrix.add_mulVec]
    map_smul' := fun c a => by simp only [map_smul, RingHom.id_apply, Matrix.smul_mulVec] }

lemma E_injective : Function.Injective E := rho_eval_bijective.1
lemma E_surjective : Function.Surjective E := rho_eval_bijective.2
lemma E_one : E 1 = eQ 0 := by change rho 1 *ᵥ eQ 0 = _; simp
lemma E_mul (a b : L) : E (a * b) = rho a *ᵥ E b := by
  change rho (a * b) *ᵥ eQ 0 = rho a *ᵥ (rho b *ᵥ eQ 0)
  rw [map_mul, Matrix.mulVec_mulVec]

lemma QB_eq : B0.map (Int.castRingHom ℚ) = (d : ℚ) • NB 0 := by
  change _ = (d : ℚ) • ((d : ℚ)⁻¹ • B0.map (Int.castRingHom ℚ))
  rw [smul_smul, mul_inv_cancel₀ dQ_ne_zero, one_smul]

lemma NB_in_image (i : Fin 3) : ∃ a : L, rho a = NB i := by
  have hc : Commute (rho (AdjoinRoot.root fQ)) (NB i) := by
    rw [rho_root, QB_eq]
    exact (NB_commute 0 i).smul_left _
  exact Arithmetic.centralizer_in_image fQ rho (eQ 0) rho_eval_bijective.2 (NB i) hc

def alpha : Fin 3 → L :=
  ![(d : ℚ)⁻¹ • AdjoinRoot.root fQ, (NB_in_image 1).choose, (NB_in_image 2).choose]

lemma rho_alpha (i : Fin 3) : rho (alpha i) = NB i := by
  fin_cases i
  · change rho ((d : ℚ)⁻¹ • AdjoinRoot.root fQ) = _
    rw [map_smul, rho_root]
    rfl
  · exact (NB_in_image 1).choose_spec
  · exact (NB_in_image 2).choose_spec

end DimensionTen.Border

end
end

end OAI
