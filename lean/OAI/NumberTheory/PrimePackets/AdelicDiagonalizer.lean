import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicMonomial
import OAI.NumberTheory.PrimePackets.AdelicRealIdentity

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set
namespace PrimeDegreePackets.Adelic

 

theorem allowed_real_diagonalizer_factorization {n : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K)
    (h : PGL(Fin n, ℝ)) (hh : AllowedRealDiagonalizer b h) :
    ∃ σ : OrderedEmbeddings n K, ∃ z : (Fin n → ℝ)ˣ,
      h = ProjGenLinGroup.mk (realBasisGL hn b σ * diagonalUnits n z) := by
  classical
  let σ := chooseOrderedEmbeddings K hn
  let w : Fin n → ℝ := fun i => (i.val : ℝ)
  let z := signedExpUnit n 1 w
  let B := realBasisGL hn b σ
  let T := rowRegularUnits (b.baseChange ℝ) (Units.map (realTensorEquiv σ hn).symm.toMonoidHom z)
  have hT : T * B = B * diagonalUnits n z := regular_realTensorEquiv_symm hn b σ z
  have ht : ProjGenLinGroup.mk T ∈ realTorusIdentity b := realExpTorus_mem_identity hn b σ w
  have himem : h⁻¹ * ProjGenLinGroup.mk T * h ∈ SpecialLinearGroup.toPGL '' positiveDiagonal n := by
    rw [← hh]
    exact ⟨_,ht,rfl⟩
  obtain ⟨D,hD,heD⟩ := himem
  obtain ⟨H₀,rfl⟩ := ProjGenLinGroup.mk_surjective h
  have he : ProjGenLinGroup.mk (T * H₀) = ProjGenLinGroup.mk (H₀ * D.toGL) := by
    change ProjGenLinGroup.mk (T * H₀) = ProjGenLinGroup.mk H₀ * SpecialLinearGroup.toPGL D
    rw [heD,map_mul]
    group
  obtain ⟨r,hr⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
  let V := D.toGL * GeneralLinearGroup.scalar (Fin n) r⁻¹
  have hTV : T * H₀ = H₀ * V := by
    dsimp [V]
    rw [← mul_assoc,← hr,mul_assoc,← map_mul,mul_inv_cancel,map_one,mul_one]
  let H := B⁻¹ * H₀
  have hHV : diagonalUnits n z * H = H * V := by
    apply mul_left_cancel (a := B)
    calc B * (diagonalUnits n z * H) = T * H₀ := by
          rw [← mul_assoc,← hT,mul_assoc]
          simp [H]
      _ = H₀ * V := hTV
      _ = B * (H * V) := by simp [H,mul_assoc]
  let v : Fin n → ℝ := fun i => D.val i i * (r⁻¹).val
  have hV : V.val = Matrix.diagonal v := by
    ext i j
    change (D.val * Matrix.diagonal (fun _ : Fin n => (r⁻¹).val)) i j = Matrix.diagonal v i j
    rw [Matrix.mul_diagonal]
    by_cases hij : i = j
    · subst j; simp [v]
    · simp [Matrix.diagonal_apply_ne _ hij,hD.1 i j hij]
  have hz : Function.Injective z.val := by
    intro i j he
    have he' : Real.exp (i.val : ℝ) = Real.exp (j.val : ℝ) := by
      simpa [z,signedExpUnit,signValue,w] using he
    exact Fin.ext (Nat.cast_injective (Real.exp_injective he'))
  have hmat : Matrix.diagonal z.val * H.val = H.val * Matrix.diagonal v := by
    have hval := congrArg Units.val hHV
    change Matrix.diagonal z.val * H.val = H.val * V.val at hval
    rwa [hV] at hval
  obtain ⟨τ,c,hc⟩ := monomial_of_diagonal_intertwiner H z.val v hz hmat
  refine ⟨τ.trans σ,c,?_⟩
  congr 1
  have hH₀ : H₀ = B * H := by simp [H]
  rw [hH₀]
  apply Units.ext
  ext i j
  change (B.val * H.val) i j =
    ((realBasisGL hn b (τ.trans σ)).val * Matrix.diagonal c.val) i j
  rw [Matrix.mul_apply,Matrix.mul_diagonal]
  simp_rw [hc]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,realBasisGL_apply,
    Equiv.trans_apply]
  simp [B]

end PrimeDegreePackets.Adelic

end

end OAI
