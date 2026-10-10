import OAI.NumberTheory.DirichletL.Detector.CentralRepeatedProduct
import OAI.NumberTheory.DirichletL.PrimeRows.RowPartition

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbeCentralRepeatedProduct
open ProbeRowReflectedAllocation ProbeRowRadicalConductor HeckeReciprocalGrowth HeckeDeletionBounds
local notation "O" => HeckeFamily.O

private lemma cost_power_identity (N L A R eps : ℝ) (hN : 0<N) (hL : 0<L) :
    N^A*N^R*L^2*(2*N^2*L^2)^eps=
      (2:ℝ)^eps*N^(A+R+2*eps)*L^(2+2*eps) := by
  have hp : (2*N^2*L^2)^eps=(2:ℝ)^eps*N^(2*eps)*L^(2*eps) := by
    rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) (by positivity)]
    rw [←Real.rpow_two N,←Real.rpow_two L,←Real.rpow_mul hN.le,←Real.rpow_mul hL.le]
  rw [hp]
  calc
    _ = (2:ℝ)^eps*(N^A*N^R*N^(2*eps))*(L^2*L^(2*eps)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hN,←Real.rpow_add hN,←Real.rpow_two L,←Real.rpow_add hL]

theorem central_rowCost_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (e eps : ℝ) (he : 0<e) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow) (a H : ℝ),51/100≤a → a≤1 → 0≤H →
      rowCost S hS u a e eps H≤
        C*rowNorm u^(a-1/2+12*e+4*eps)*(3+H)^(2+2*eps) := by
  let F : ℝ := fixedConductorConstant S
  have hF : 1≤F := by
    dsimp [F]
    exact_mod_cast fixedConductorConstant_pos S hS
  have hFp : 0<F := zero_lt_one.trans_le hF
  refine ⟨(2:ℝ)^eps*F^(1/2+12*e+4*eps),by positivity,?_⟩
  intro u a H ha ha1 hH
  let N : ℝ := F*rowNorm u
  let L : ℝ := 3+H
  let A : ℝ := a-1/2+6*e
  let R : ℝ := 6*e+2*eps
  have hn : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hN : 0<N := mul_pos hFp hn
  have hL : 0<L := by dsimp [L];linarith
  have hA : 0≤A := by dsimp [A];linarith
  have hR : 0≤R := by dsimp [R];positivity
  have hrad : ((radical (rowCharacter S hS u).modulus).absNorm:ℝ)≤N :=
    original_row_deletion_radical_le S hS u
  have hq : ((rowCharacter S hS u).modulus.absNorm:ℝ)≤N := original_row_conductor_le S hS u
  have hc : presentationComplexity (rowCharacter S hS u) H≤2*N^2*L^2 := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    rw [abs_of_nonneg hH]
    calc
      _ ≤ N*(2*N*L^2) := by
        apply mul_le_mul hrad _ (by positivity) hN.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) (sq_nonneg L)
      _ = _ := by ring
  have hrpow := Real.rpow_le_rpow (show (0:ℝ)≤(radical (rowCharacter S hS u).modulus).absNorm by positivity) hrad hR
  have hcpow := Real.rpow_le_rpow (show 0≤presentationComplexity (rowCharacter S hS u) H by
    unfold presentationComplexity HeckeLogarithmic.complexity;positivity) hc heps.le
  have hbound : rowCost S hS u a e eps H≤N^A*N^R*L^2*(2*N^2*L^2)^eps := by
    unfold rowCost
    apply mul_le_mul _ hcpow (Real.rpow_nonneg (by
      unfold presentationComplexity HeckeLogarithmic.complexity;positivity) _) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg L)
    exact mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg hN.le _)
  rw [cost_power_identity N L A R eps hN hL] at hbound
  have hexp : A+R+2*eps=a-1/2+12*e+4*eps := by dsimp [A,R];ring
  rw [hexp] at hbound
  apply hbound.trans
  dsimp only [N]
  rw [Real.mul_rpow hFp.le hn.le]
  have hf := Real.rpow_le_rpow_of_exponent_le hF
    (show a-1/2+12*e+4*eps≤1/2+12*e+4*eps by linarith)
  calc
    _ = ((2:ℝ)^eps*F^(a-1/2+12*e+4*eps))*rowNorm u^(a-1/2+12*e+4*eps)*L^(2+2*eps) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn.le _)
      exact mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg (by norm_num) _)

end SevenEighths.ProbeHighRowFamily

end

end OAI
