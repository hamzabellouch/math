import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.CenterCommutants

namespace OAI

/-! Matrix displacement and central energy estimates. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildCentralQuantization
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
  HochschildQuantization HochschildCentralComparison FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

include e in
lemma exists_colored_matrix_displacement
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hII : TypeII1 M)
    (a : M) (hacenter : CentrallyCentered τ a) (ha : 0<‖τ.toPreGNS a‖) :
    ∃ (m : ℕ) (F : MatrixSystem M m) (z : Fin m → M), 0 < m ∧
      (∀ i, CentralProjection (z i)) ∧ IsStarProjection (∑ i,z i*F.entry i i) ∧
      ‖τ.toPreGNS a‖/16 <
        ‖τ.toPreGNS ((∑ i,z i*F.entry i i)*a-a*(∑ i,z i*F.entry i i))‖ := by
  obtain ⟨p,hp,hpdisp⟩ := exists_central_projection_displacement e τ hτ h1 htr hfaith hacenter ha
  let t := ‖τ.toPreGNS a‖
  let ε : ℝ := t/(64*(‖a‖+1))
  have hε : 0<ε := div_pos ha (by positivity)
  obtain ⟨m,F,z,hm,hz,hq,_hqp,happrox⟩ := exists_central_matrix_projection_approx e τ hτ htr hfaith
    h1 hII hp hε
  refine ⟨m,F,z,hm,hz,hq,?_⟩
  let q := ∑ i,z i*F.entry i i
  have herr : ‖τ.toPreGNS (p*a-a*p)‖ ≤ ‖τ.toPreGNS (q*a-a*q)‖+2*‖a‖*ε := by
    calc
      _ = ‖τ.toPreGNS (q*a-a*q)+τ.toPreGNS ((p-q)*a-a*(p-q))‖ := by
        rw [← map_add]; congr 2; noncomm_ring
      _ ≤ ‖τ.toPreGNS (q*a-a*q)‖+‖τ.toPreGNS ((p-q)*a-a*(p-q))‖ := norm_add_le _ _
      _ ≤ ‖τ.toPreGNS (q*a-a*q)‖+2*‖a‖*ε :=
        add_le_add_right ((commutator_gns_le τ htr a (p-q)).trans
          (mul_le_mul_of_nonneg_left happrox.le (by positivity))) _
  have hsmall : 2*‖a‖*ε ≤ t/32 := by
    have heq : ε*(64*(‖a‖+1))=t := div_mul_cancel₀ _ (by positivity)
    nlinarith [hε.le]
  change t/16 < ‖τ.toPreGNS (q*a-a*q)‖
  change t/8 < _ at hpdisp
  linarith

end HochschildCentralQuantization

open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open BoundedHochschild HochschildRigidity HochschildSakai HochschildQuantization
  HochschildCentralQuantization FinitePathMain
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {n : ℕ} (E : MatrixSystem M n)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

include e in

theorem exists_central_energy_decreasing_extension
    (hn : 0<n) (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hII : TypeII1 M)
    (x : M) (hxcenter : CentrallyCentered τ x) (hx : 0<‖τ.toPreGNS (E.expectation x)‖) :
    ∃ (m : ℕ) (F : MatrixSystem E.commutant m), 0 < m ∧
      ‖τ.toPreGNS ((E.extend F).expectation x)‖^2 +
        (‖τ.toPreGNS (E.expectation x)‖/32)^2 <
          ‖τ.toPreGNS (E.expectation x)‖^2 := by
  classical
  let hL := mul_hasPreadjoint e
  let hR := mul_right_hasPreadjoint e
  obtain ⟨P,hPn,hP⟩ := exists_abstract_star_preadjoint e
  let eC := E.commutantPredualEquiv e hL hR P hP
  let ρ := E.commutantTrace τ
  let a : E.commutant := ⟨E.expectation x,E.commute_expectation x⟩
  have han : ‖ρ.toPreGNS a‖=‖τ.toPreGNS (E.expectation x)‖ := E.commutant_gns_norm τ a
  obtain ⟨m,F,z,hm,hz,hq,hdisp⟩ := exists_colored_matrix_displacement eC ρ
    (E.commutantTrace_normal e hL hR P hP τ hτ)
    (E.commutantTrace_one τ h1) (E.commutantTrace_tracial τ htr)
    (E.commutantTrace_faithful τ hfaith)
    (E.commutant_typeII1 e τ hn hτ htr hfaith hII) a
    (E.centrallyCentered_expectation τ htr (Nat.ne_of_gt hn) hxcenter) (han ▸ hx)
  refine ⟨m,F,hm,?_⟩
  let q : E.commutant := ∑ i,z i*F.entry i i
  let b : M := (E.extend F).expectation x
  have hbq : Commute b (q:M) := by
    change Commute b (E.commutant.subtype (∑ i,z i*F.entry i i))
    rw [map_sum]
    apply Commute.sum_right
    intro i hi
    rw [map_mul]
    exact ((E.central_commutant_coe (z i) (hz i).2 b).symm).mul_right
      ((E.extension_expectation_commutes F x).2 i i)
  have hqnorm : ‖(q:M)‖ ≤ 1 := hq.norm_le
  have hbound : ‖ρ.toPreGNS (q*a-a*q)‖ ≤ 2*‖τ.toPreGNS (E.expectation x-b)‖ := by
    rw [E.commutant_gns_norm τ]
    change ‖τ.toPreGNS ((q:M)*E.expectation x-E.expectation x*(q:M))‖ ≤ _
    have he : (q:M)*E.expectation x-E.expectation x*(q:M)=
        (q:M)*(E.expectation x-b)-(E.expectation x-b)*(q:M) := by
      have hh := hbq.eq
      noncomm_ring [hh]
    rw [he,map_sub]
    calc
      _ ≤ ‖τ.toPreGNS ((q:M)*(E.expectation x-b))‖+
          ‖τ.toPreGNS ((E.expectation x-b)*(q:M))‖ := norm_sub_le _ _
      _ ≤ ‖(q:M)‖*‖τ.toPreGNS (E.expectation x-b)‖+
          ‖(q:M)‖*‖τ.toPreGNS (E.expectation x-b)‖ :=
        add_le_add (preGNS_norm_mul_le τ _ _) (preGNS_norm_mul_right_le τ htr _ _)
      _ ≤ _ := by nlinarith [norm_nonneg (τ.toPreGNS (E.expectation x-b))]
  rw [han] at hdisp
  have hp := E.extension_pythagoras F τ htr (Nat.ne_of_gt hn) (Nat.ne_of_gt hm) x
  change ‖τ.toPreGNS (E.expectation x)‖^2=‖τ.toPreGNS b‖^2+
    ‖τ.toPreGNS (E.expectation x-b)‖^2 at hp
  have hstrict : ‖τ.toPreGNS (E.expectation x)‖/32 <
      ‖τ.toPreGNS (E.expectation x-b)‖ := by linarith
  have hs := sq_lt_sq₀ (by positivity : 0 ≤ ‖τ.toPreGNS (E.expectation x)‖/32)
    (norm_nonneg (τ.toPreGNS (E.expectation x-b)))
  change ‖τ.toPreGNS b‖^2+_ < _
  linarith [hs.mpr hstrict]

end MatrixSystem
end HochschildMatrixSystems

open Filter Topology
open scoped ComplexOrder
namespace HochschildCentralQuantization
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
  HochschildQuantization FinitePathMain
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {I : Type v} [Fintype I]

include e in

theorem exists_small_matrix_expectations
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hII : TypeII1 M)
    (x : I → M) (hx : ∀ i, CentrallyCentered τ (x i)) {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (E : MatrixSystem M n), 0<n ∧ ∀ i, ‖τ.toPreGNS (E.expectation (x i))‖<ε := by
  classical
  let S : Set ℝ := {b | ∃ (n : ℕ) (E : MatrixSystem M n), 0<n ∧ b=matrixEnergy τ x E}
  have hS : S.Nonempty := by
    obtain ⟨E⟩ := exists_matrixSystem_of_typeII1 e τ hτ htr hfaith hII 1 (by omega)
    exact ⟨matrixEnergy τ x E,1,E,by omega,rfl⟩
  have hSb : BddBelow S := ⟨0,by
    rintro b ⟨n,E,hn,rfl⟩
    exact matrixEnergy_nonneg τ x E⟩
  let δ : ℝ := (ε/32)^2
  have hδ : 0<δ := sq_pos_of_pos (div_pos hε (by norm_num))
  obtain ⟨b,hbS,hb⟩ := exists_lt_of_csInf_lt hS (lt_add_of_pos_right (sInf S) hδ)
  obtain ⟨n,E,hn,rfl⟩ := hbS
  refine ⟨n,E,hn,?_⟩
  intro i
  by_contra hi
  have hei : ε ≤ ‖τ.toPreGNS (E.expectation (x i))‖ := le_of_not_gt hi
  have hp : 0<‖τ.toPreGNS (E.expectation (x i))‖ := hε.trans_le hei
  obtain ⟨m,F,hm,hdrop⟩ := E.exists_central_energy_decreasing_extension e τ hn hτ h1 htr hfaith
    hII (x i) (hx i) hp
  have hd : δ ≤ (‖τ.toPreGNS (E.expectation (x i))‖/32)^2 := by
    dsimp [δ]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  have hd' := matrixEnergy_drop τ htr x E F (Nat.ne_of_gt hn) (Nat.ne_of_gt hm) i
    (lt_of_le_of_lt (add_le_add_right hd _) hdrop)
  have hnew : matrixEnergy τ x (E.extend F) ∈ S :=
    ⟨n*m,E.extend F,Nat.mul_pos hn hm,rfl⟩
  have hlo := csInf_le hSb hnew
  linarith

end HochschildCentralQuantization

end

end OAI
