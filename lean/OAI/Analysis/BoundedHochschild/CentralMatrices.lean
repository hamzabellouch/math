import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.TypeIIMatrices
import OAI.Analysis.BoundedHochschild.CentralRanks

namespace OAI

/-! Central matrix approximation of projections. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildCentralComparison
open BoundedHochschild HochschildComparison FinitePathMain HochschildMatrixSystems
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

namespace MatrixSystem
variable {n : ℕ} (E : HochschildMatrixSystems.MatrixSystem M n)

def conjugate (u : unitary M) : HochschildMatrixSystems.MatrixSystem M n where
  entry i j := (u:M)*E.entry i j*star (u:M)
  star_entry i j := by simp only [star_mul,star_star,E.star_entry,mul_assoc]
  entry_mul i j k l := by
    calc
      ((u:M)*E.entry i j*star (u:M))*((u:M)*E.entry k l*star (u:M)) =
          (u:M)*E.entry i j*(star (u:M)*(u:M))*E.entry k l*star (u:M) := by
            simp only [mul_assoc]
      _ = (u:M)*(E.entry i j*E.entry k l)*star (u:M) := by
        rw [Unitary.star_mul_self_of_mem u.prop,mul_one,mul_assoc (u:M)]
      _ = _ := by split_ifs with h <;> simp only [E.entry_mul,h,ite_true,ite_false,mul_zero,zero_mul]
  sum_diagonal := by
    rw [← Finset.sum_mul,← Finset.mul_sum,E.sum_diagonal,mul_one,Unitary.mul_star_self_of_mem u.prop]

omit [PartialOrder M] [StarOrderedRing M] in
lemma commute_colored_diagonal (z : Fin n → M) (hz : ∀ i, CentralProjection (z i))
    (a : M) (ha : ∀ i, Commute a (E.entry i i)) : Commute a (∑ i,z i*E.entry i i) := by
  apply Commute.sum_right
  intro i hi
  exact ((hz i).2 a).symm.mul_right (ha i)
end MatrixSystem

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in

theorem exists_central_matrix_projection_approx (h1 : τ 1=1) (hII : TypeII1 M)
    {p : M} (hp : IsStarProjection p) {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (E : HochschildMatrixSystems.MatrixSystem M n) (z : Fin n → M), 0<n ∧
      (∀ i, CentralProjection (z i)) ∧ IsStarProjection (∑ i,z i*E.entry i i) ∧
      (∑ i,z i*E.entry i i) ≤ p ∧ ‖τ.toPreGNS (p-∑ i,z i*E.entry i i)‖ < ε := by
  classical
  obtain ⟨n,hnR⟩ := exists_nat_gt ((ε^2)⁻¹)
  have hn : 0<n := by exact_mod_cast (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg ε)) hnR)
  have hnRpos : (0:ℝ)<n := by exact_mod_cast hn
  have hinv : (n:ℝ)⁻¹<ε^2 := (inv_lt_comm₀ hnRpos (sq_pos_of_pos hε)).mpr hnR
  obtain ⟨F⟩ := exists_matrixSystem_of_typeII1 e τ hτ htr hfaith hII n hn
  obtain ⟨R,hR⟩ := exists_central_rank τ htr e hτ hfaith F hp
  obtain ⟨u,hu,huf⟩ := PartialIso.unitary_extension e τ hτ htr hfaith R.val
  let E := MatrixSystem.conjugate F u
  have hs : (∑ i,R.color i*E.entry i i)=R.val.final := by
    rw [← huf,R.initial_eq,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    change R.color i*((u:M)*F.entry i i*star (u:M))=(u:M)*(R.color i*F.entry i i)*star (u:M)
    rw [← mul_assoc,← mul_assoc,(R.color_central i).2 (u:M) |>.eq,mul_assoc (u:M)]
  refine ⟨n,E,R.color,hn,R.color_central,hs ▸ R.val.final_proj,hs ▸ R.final_le,?_⟩
  rw [hs]
  have hproj := (R.val.final_proj.le_iff_sub hp).mp R.final_le
  have he : ‖τ.toPreGNS (p-R.val.final)‖^2=(τ (p-R.val.final)).re := by
    have hh := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS (p-R.val.final)))
    simpa only [PositiveLinearMap.ofPreGNS_toPreGNS,← Complex.ofReal_pow,Complex.ofReal_re,
      hproj.isSelfAdjoint.star_eq,hproj.isIdempotentElem.eq] using hh
  have hb : ‖τ.toPreGNS (p-R.val.final)‖^2 ≤ (n:ℝ)⁻¹ := by
    rw [he]
    have htt : (n:ℝ)*(τ (p-R.val.final)).re ≤ 1 := by simpa only [h1,Complex.one_re] using hR
    rw [← one_div (n:ℝ)]
    apply (le_div_iff₀ hnRpos).mpr
    nlinarith
  nlinarith [hb.trans_lt hinv,norm_nonneg (τ.toPreGNS (p-R.val.final))]

end HochschildCentralComparison

end

end OAI
