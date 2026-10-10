import Mathlib

namespace OAI

section
noncomputable section
open Matrix Polynomial
open scoped IsMulCommutative
namespace DimensionTen.Arithmetic

lemma field_representation {n : ℕ} (f : ℚ[X]) (hirr : Irreducible f)
    (hdegree : f.natDegree = n) (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : aeval B f = 0) (e : Fin n → ℚ) (he : e ≠ 0) :
    ∃ ρ : AdjoinRoot f →ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ,
      ρ (AdjoinRoot.root f) = B ∧ Function.Bijective (fun a => ρ a *ᵥ e) := by
  let : Fact (Irreducible f) := ⟨hirr⟩
  let A := Algebra.adjoin ℚ ({B} : Set (Matrix (Fin n) (Fin n) ℚ))
  let : IsMulCommutative A := Algebra.isMulCommutative_adjoin_singleton ℚ B
  let b : A := ⟨B, Algebra.subset_adjoin (by simp)⟩
  have hb : f.eval₂ (Algebra.ofId ℚ A) b = 0 := by
    change aeval b f = 0
    apply Subtype.ext
    simpa only [Polynomial.aeval_subalgebra_coe, ZeroMemClass.coe_zero] using hB
  let ρ : AdjoinRoot f →ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ :=
    A.val.comp (AdjoinRoot.liftAlgHom f (Algebra.ofId ℚ A) b hb)
  have hroot : ρ (AdjoinRoot.root f) = B := by
    change ((AdjoinRoot.liftAlgHom f (Algebra.ofId ℚ A) b hb) (AdjoinRoot.root f)).val = B
    rw [AdjoinRoot.liftAlgHom_root]
  let E : AdjoinRoot f →ₗ[ℚ] (Fin n → ℚ) :=
    { toFun := fun a => ρ a *ᵥ e
      map_add' := fun a b => by simp only [map_add, Matrix.add_mulVec]
      map_smul' := fun c a => by simp only [map_smul, RingHom.id_apply, Matrix.smul_mulVec] }
  have hEinj : Function.Injective E := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro a ha
    by_contra hane
    apply he
    have hh := congrArg (fun v => ρ a⁻¹ *ᵥ v) ha
    simpa only [E, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec_mulVec,
      ← map_mul, inv_mul_cancel₀ hane, map_one, Matrix.one_mulVec, Matrix.mulVec_zero] using hh
  let : FiniteDimensional ℚ (AdjoinRoot f) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hdim : Module.finrank ℚ (AdjoinRoot f) = Module.finrank ℚ (Fin n → ℚ) := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdegree]
    simp
  exact ⟨ρ, hroot, hEinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hEinj⟩


lemma commute_image {n : ℕ} (f : ℚ[X]) [Fact (Irreducible f)]
    (ρ : AdjoinRoot f →ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) (hc : Commute (ρ (AdjoinRoot.root f)) C)
    (a : AdjoinRoot f) : Commute (ρ a) C := by
  induction a using AdjoinRoot.induction_on f with
  | ih p =>
    rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, Polynomial.aeval_eq_smeval]
    exact Polynomial.smeval_commute_left ℚ p hc

lemma centralizer_in_image {n : ℕ} (f : ℚ[X]) [Fact (Irreducible f)]
    (ρ : AdjoinRoot f →ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ) (e : Fin n → ℚ)
    (hsurj : Function.Surjective (fun a => ρ a *ᵥ e))
    (C : Matrix (Fin n) (Fin n) ℚ) (hc : Commute (ρ (AdjoinRoot.root f)) C) :
    ∃ a, ρ a = C := by
  obtain ⟨a, ha⟩ := hsurj (C *ᵥ e)
  change ρ a *ᵥ e = C *ᵥ e at ha
  refine ⟨a, Matrix.mulVec_injective ?_⟩
  funext v
  obtain ⟨b, rfl⟩ := hsurj v
  change ρ a *ᵥ (ρ b *ᵥ e) = C *ᵥ (ρ b *ᵥ e)
  have hab : Commute (ρ a) (ρ b) := (Commute.all a b).map ρ
  have hbc := commute_image f ρ C hc b
  rw [Matrix.mulVec_mulVec, hab.eq, ← Matrix.mulVec_mulVec, ha,
    Matrix.mulVec_mulVec, hbc.eq, ← Matrix.mulVec_mulVec]

end DimensionTen.Arithmetic

end
end

end OAI
