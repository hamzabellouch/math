import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.RelativeCenter

namespace OAI

/-! Center-valued weak cancellation for unitary powers. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open BoundedHochschild HochschildCorners HochschildCentralQuantization HochschildRigidity
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {n : ℕ} (E : MatrixSystem M n)

def diagonalInflate (i : Fin n) : Corner (E.entry i i) (E.diagonal_proj i) →⋆ₐ[ℂ] M where
  toFun x := E.coefficient i i (x:M)
  map_zero' := E.coefficient_nil i i
  map_add' x y := by
    change E.coefficient i i ((x:M)+(y:M))=E.coefficient i i (x:M)+E.coefficient i i (y:M)
    simp only [coefficient,mul_add,add_mul,Finset.sum_add_distrib]
  map_one' := E.coefficient_diagonal_base i
  map_mul' x y := by
    rw [E.coefficient_mul]
    change E.coefficient i i ((x:M)*(y:M))=E.coefficient i i ((x:M)*E.entry i i*(y:M))
    rw [x.property.2]
  commutes' c := by
    change E.coefficient i i (c • E.entry i i)=algebraMap ℂ M c
    simp only [coefficient,mul_smul_comm,smul_mul_assoc,← Finset.smul_sum,E.entry_mul,
      ite_true,E.sum_diagonal,Algebra.algebraMap_eq_smul_one]
  map_star' x := (E.coefficient_star i i (x:M)).symm

omit [PartialOrder M] [StarOrderedRing M] in
lemma coefficient_compress (i : Fin n) (a : M) :
    E.coefficient i i (E.entry i i*a*E.entry i i)=E.coefficient i i a := by
  unfold coefficient
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_assoc,← mul_assoc,E.entry_mul,ite_eq_left rfl,mul_assoc,E.entry_mul,ite_eq_left rfl]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coefficient_diagonal_norm (i : Fin n) (a : M) : ‖E.coefficient i i a‖≤‖a‖ := by
  let p := E.entry i i
  let hp := E.diagonal_proj i
  let x : Corner p hp := ⟨p*a*p,compress_mem_corner hp a⟩
  have hh := NonUnitalStarAlgHom.norm_apply_le (E.diagonalInflate i) x
  change ‖E.coefficient i i (p*a*p)‖≤‖p*a*p‖ at hh
  rw [E.coefficient_compress] at hh
  have hn := hp.norm_le p
  exact hh.trans ((norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans
    (by calc
      ‖p‖*‖a‖*‖p‖ ≤ 1*‖a‖*1 := by gcongr
      _ = ‖a‖ := by ring)))

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma center_coefficient_diagonal (i : Fin n) (a : M) :
    centerExpectation e τ hτ htr hfaith (E.coefficient i i a)=
      (n:ℂ) • centerExpectation e τ hτ htr hfaith (a*E.entry i i) := by
  have ht (k : Fin n) : centerExpectation e τ hτ htr hfaith (E.entry k i*a*E.entry i k)=
      centerExpectation e τ hτ htr hfaith (a*E.entry i i) := by
    rw [centerExpectation_cyclic e τ hτ htr hfaith,← mul_assoc,E.entry_mul,ite_eq_left rfl,
      centerExpectation_cyclic e τ hτ htr hfaith]
  simp only [coefficient,map_sum,ht,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    Nat.cast_smul_eq_nsmul]

lemma center_diagonal_norm (hn : n≠0) (i : Fin n) (a : M) :
    ‖centerExpectation e τ hτ htr hfaith (a*E.entry i i)‖≤‖a‖/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh := (centerPart_norm e τ hτ htr hfaith (E.coefficient i i a)).trans (E.coefficient_diagonal_norm i a)
  change ‖centerExpectation e τ hτ htr hfaith (E.coefficient i i a)‖≤‖a‖ at hh
  rw [E.center_coefficient_diagonal e τ hτ htr hfaith,norm_smul,Complex.norm_natCast] at hh
  exact (le_div_iff₀ hnR).mpr (by nlinarith)

variable {m : ℕ} [NeZero m]

lemma center_root_parseval (a : M) (k : ZMod m) (hk : k≠0) :
    (∑ g : Fin n → ZMod m, ‖τ.toPreGNS (centerExpectation e τ hτ htr hfaith (a*E.diagonalRoot k g))‖^2)=
      (Fintype.card (Fin n → ZMod m):ℝ)*
        (∑ i,‖τ.toPreGNS (centerExpectation e τ hτ htr hfaith (a*E.entry i i))‖^2) := by
  have hh := HochschildRootPhase.character_parseval (fun i : Fin n => Pi.single i k)
    (single_frequency_injective k hk)
    (fun i => τ.toPreGNS (centerExpectation e τ hτ htr hfaith (a*E.entry i i)))
  simpa only [diagonalRoot,Finset.mul_sum,mul_smul_comm,map_sum,map_smul] using hh

lemma center_root_energy_bound (h1 : τ 1=1) (hn : n≠0)
    (a : M) (k : ZMod m) (hk : k≠0) :
    (∑ g : Fin n → ZMod m, ‖τ.toPreGNS (centerExpectation e τ hτ htr hfaith (a*E.diagonalRoot k g))‖^2) ≤
      (Fintype.card (Fin n → ZMod m):ℝ)*(‖a‖^2/(n:ℝ)) := by
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn
  have hb (i : Fin n) : ‖τ.toPreGNS (centerExpectation e τ hτ htr hfaith (a*E.entry i i))‖≤
      (n:ℝ)⁻¹*‖a‖ := by
    simpa only [div_eq_inv_mul] using (preGNS_norm_le τ h1 _).trans
      (E.center_diagonal_norm e τ hτ htr hfaith hn i a)
  rw [E.center_root_parseval e τ hτ htr hfaith a k hk]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ _i : Fin n,((n:ℝ)⁻¹*‖a‖)^2 := Finset.sum_le_sum (fun i hi =>
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (norm_nonneg _))).mpr (hb i))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

lemma exists_root_center_energy {I : Type*} [Fintype I]
    (h1 : τ 1=1) (hn : n≠0) (a : I → M) (k : I → ZMod m) (hk : ∀ i, k i≠0) :
    ∃ g : Fin n → ZMod m,
      (∑ i,‖τ.toPreGNS (centerExpectation e τ hτ htr hfaith (a i*E.diagonalRoot (k i) g))‖^2)≤
        (∑ i,‖a i‖^2)/(n:ℝ) := by
  classical
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset I)) =>
    E.center_root_energy_bound e τ hτ htr hfaith h1 hn (a i) (k i) (hk i))
  rw [Finset.sum_comm,← Finset.mul_sum,← Finset.sum_div] at hh
  by_contra hg
  push Not at hg
  have hstrict : (Fintype.card (Fin n → ZMod m):ℝ)*((∑ i,‖a i‖^2)/(n:ℝ)) <
      ∑ g : Fin n → ZMod m, ∑ i,‖τ.toPreGNS (centerExpectation e τ hτ htr hfaith (a i*E.diagonalRoot (k i) g))‖^2 := by
    rw [← nsmul_eq_mul,← Finset.card_univ,← Finset.sum_const]
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun _ _ => hg _)
  exact (not_lt_of_ge hh) hstrict

end MatrixSystem
end HochschildMatrixSystems

open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
open BoundedHochschild HochschildRigidity HochschildSakai FinitePathMain HochschildCentralQuantization
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {I : Type v} [Fintype I]

include e in
theorem exists_unitary_center_weak_powers
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hII : TypeII1 M)
    (a : I → M) (k : I → ℤ) (hk : ∀ i, k i ≠ 0) {ε : ℝ} (hε : 0<ε) :
    ∃ u : unitary M, ∀ i, ‖τ.toPreGNS (centerExpectation e τ hτ htr hfaith (a i*(u^(k i) : unitary M) : M))‖<ε := by
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
  obtain ⟨g,hg⟩ := E.exists_root_center_energy e τ hτ htr hfaith h1 (Nat.ne_of_gt hn) a
    (fun i => (k i : ZMod m)) hkm
  refine ⟨E.rootUnitary g,fun i => ?_⟩
  have hsum : B/(n:ℝ)<ε^2 := by
    apply (div_lt_iff₀ hnRpos).mpr
    have hh := (div_lt_iff₀ hε2).mp hnR
    nlinarith
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
    sq_nonneg ‖τ.toPreGNS (centerExpectation e τ hτ htr hfaith (a j*E.diagonalRoot (k j : ZMod m) g))‖) (Finset.mem_univ i)
  have hh : ‖τ.toPreGNS (centerExpectation e τ hτ htr hfaith (a i*E.diagonalRoot (k i : ZMod m) g))‖^2<ε^2 := hi.trans_lt (hg.trans_lt hsum)
  change ‖τ.toPreGNS (centerExpectation e τ hτ htr hfaith (a i*((E.rootUnitary g)^(k i) : unitary M).val))‖<ε
  rw [E.rootUnitary_zpow]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hh

end HochschildMatrixSystems

end

end OAI
