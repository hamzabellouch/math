import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.Frames

namespace OAI

/-! Matrix systems and weak unitary powers in finite type-II algebras. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildMatrixSystems
open BoundedHochschild HochschildComparison FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in

theorem exists_matrixSystem_of_typeII1 (hII : TypeII1 M) (n : ℕ) (hn : 0<n) :
    Nonempty (MatrixSystem M n) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨v,hv⟩ := Frame.exists_full e τ hτ htr hfaith hII k
  refine ⟨⟨fun i j => (v.part i:M)*star (v.part j:M),?_,?_,?_⟩⟩
  · intro i j
    simp only [star_mul,star_star]
  · intro i j l m
    by_cases h : j=l
    · subst l
      rw [ite_eq_left rfl]
      calc
        ((v.part i:M)*star (v.part j:M))*((v.part j:M)*star (v.part m:M)) =
            (v.part i:M)*(v.part j).initial*star (v.part m:M) := by
              simp only [PartialIso.initial,mul_assoc]
        _ = (v.part i:M)*star (v.part m:M) := by
          rw [v.initial_eq,← v.initial_eq i,(v.part i).mul_initial]
    · rw [ite_eq_right h]
      calc
        ((v.part i:M)*star (v.part j:M))*((v.part l:M)*star (v.part m:M)) =
            (v.part i:M)*(star (v.part j:M)*(v.part l:M))*star (v.part m:M) := by
              simp only [mul_assoc]
        _ = 0 := by rw [PartialIso.star_mul_eq_zero_of_final_orthogonal (v.orthogonal j l h),mul_zero,zero_mul]
  · exact hv

end HochschildMatrixSystems

open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
open BoundedHochschild HochschildRigidity HochschildSakai FinitePathMain
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {I : Type v} [Fintype I]

include e in
theorem exists_unitary_weak_powers_of_typeII1
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hII : TypeII1 M)
    (a : I → M) (k : I → ℤ) (hk : ∀ i, k i ≠ 0) {ε : ℝ} (hε : 0<ε) :
    ∃ u : unitary M, ∀ i, ‖τ (a i*(u^(k i) : unitary M) : M)‖<ε := by
  classical
  let m : ℕ := 1+ ∑ i,(k i).natAbs
  have hm : 0 < m := by dsimp [m]; omega
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hkm (i : I) : (k i : ZMod m) ≠ 0 := by
    intro hz
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (k i) m).mp hz
    have hh := Int.natAbs_le_of_dvd_ne_zero hd (hk i)
    simp only [Int.natAbs_natCast] at hh
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
      Nat.zero_le (k j).natAbs) (Finset.mem_univ i)
    dsimp [m] at hh
    omega
  let B : ℝ := ∑ i,‖a i‖^2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hε2 : 0<ε^2 := sq_pos_of_pos hε
  obtain ⟨n,hnR⟩ := exists_nat_gt (B/ε^2)
  have hn : 0<n := by exact_mod_cast (lt_of_le_of_lt (div_nonneg hB hε2.le) hnR)
  have hnRpos : (0:ℝ)<n := by exact_mod_cast hn
  obtain ⟨E⟩ := exists_matrixSystem_of_typeII1 e τ hτ htr hfaith hII n hn
  obtain ⟨g,hg⟩ := E.exists_root_trace_energy τ h1 htr (Nat.ne_of_gt hn) a
    (fun i => (k i : ZMod m)) hkm
  refine ⟨E.rootUnitary g,fun i => ?_⟩
  have hsum : B/(n:ℝ)<ε^2 := by
    apply (div_lt_iff₀ hnRpos).mpr
    have hh := (div_lt_iff₀ hε2).mp hnR
    nlinarith
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
    sq_nonneg ‖τ (a j*E.diagonalRoot (k j : ZMod m) g)‖) (Finset.mem_univ i)
  have hh : ‖τ (a i*E.diagonalRoot (k i : ZMod m) g)‖^2<ε^2 := hi.trans_lt (hg.trans_lt hsum)
  change ‖τ (a i*((E.rootUnitary g)^(k i) : unitary M).val)‖<ε
  rw [E.rootUnitary_zpow]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hh

end HochschildMatrixSystems

end

end OAI
