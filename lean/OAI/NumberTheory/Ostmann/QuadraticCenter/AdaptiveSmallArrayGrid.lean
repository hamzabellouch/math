import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveSmallArrayDefs
import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveSmallArrayScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem parameterGrid_lower_subset {lo B m : ℕ} (hlo : 1 ≤ lo) :
    parameterGrid lo B m ⊆ parameterGrid 1 B m := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hjlo,hjhi⟩ := Finset.mem_Icc.mp hj
  apply Finset.mem_image.mpr
  refine ⟨j,Finset.mem_Icc.mpr ⟨?_,hjhi⟩,rfl⟩
  exact (Nat.mul_le_mul_right m hlo).trans hjlo

theorem exists_near_adaptiveSmallBaseParameters {L Z M h : ℕ}
    (hL : 0 < L) (hZ : 0 < Z) (hM : M < 4*L) (hh : h < L)
    {θ R : ℝ} (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1)
    (hRlo : (L^6:ℕ) ≤ R) (hRhi : R ≤ (2*Z^13:ℕ)) :
    ∃ a ∈ adaptiveSmallBaseParameters L Z,
      a.modulusResidue=M ∧ a.phaseResidue=h ∧
      |θ-a.theta| ≤ 1/(Z^200:ℕ) ∧ |R-a.radius| ≤ 1/(Z^200:ℕ) := by
  classical
  have hm : 0 < Z^200 := pow_pos hZ 200
  obtain ⟨θ₀,ht,hθdist⟩ := exists_near_parameterGrid (lo:=0) (hi:=1) hm (by simpa using ht0) (by simpa using ht1)
  obtain ⟨R₀,hR,hRdist⟩ := exists_near_parameterGrid (lo:=L^6) (hi:=2*Z^13) hm hRlo hRhi
  have hlo : 1 ≤ L^6 := Nat.one_le_pow _ _ hL
  have hR' := parameterGrid_lower_subset hlo hR
  have hz : (θ₀,R₀) ∈ (parameterGrid 0 1 (Z^200)).product (parameterGrid 1 (2*Z^13) (Z^200)) :=
    Finset.mem_product.mpr ⟨ht,hR'⟩
  have ha : (⟨M,h,1,θ₀,R₀⟩:AdaptiveArrayParameters) ∈ adaptiveArrayParameters L Z := by
    apply Finset.mem_image.mpr
    refine ⟨((M,h),(1,(θ₀,R₀))),?_,rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hM,
      Finset.mem_range.mpr hh⟩,Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr
        ⟨le_rfl,Nat.one_le_pow _ _ hZ⟩,hz⟩⟩
  exact ⟨⟨M,h,1,θ₀,R₀⟩,Finset.mem_filter.mpr ⟨ha,rfl,(mem_parameterGrid_bounds hm hR).1⟩,
    rfl,rfl,hθdist,hRdist⟩

theorem adaptiveSmall_G_grid_error {L Z d s v : ℕ} (hL : Squarefree L)
    (hZ : 1 ≤ Z) (hLZ : L ≤ Z) (hC : adaptiveArrayConstant ≤ (Z:ℝ))
    (hd : d ∈ L.divisors) (hv : v ∈ L.divisors) (hs : s ∈ adaptiveSmallSupport L)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ)
    {R R' θ θ' : ℝ} (hR : 1 ≤ R) (hR' : 1 ≤ R')
    (hRB : R ≤ (2*Z^13:ℕ)) (hRB' : R' ≤ (2*Z^13:ℕ)) (h : ℝ)
    (ht : |θ-θ'| ≤ 1/(Z^200:ℕ)) (hr : |R-R'| ≤ 1/(Z^200:ℕ)) :
    ‖divisorQuadraticSumP d A mInv s v 1 R h θ-
      divisorQuadraticSumP d A mInv s v 1 R' h θ'‖ ≤ (Z:ℝ)^(-(80:ℝ)) := by
  have hsI := Finset.mem_Icc.mp (Finset.mem_filter.mp (adaptiveSmallSupport_subset hZ hLZ hs)).1
  apply (divisorQuadraticSumP_grid_error hZ (hL.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
    hsI.1 (Nat.pos_of_mem_divisors hv)
    ((Nat.le_of_dvd hL.ne_zero.bot_lt (Nat.dvd_of_mem_divisors hd)).trans hLZ)
    ((Nat.le_of_dvd hL.ne_zero.bot_lt (Nat.dvd_of_mem_divisors hv)).trans hLZ)
    hsI.2 A mInv 1 hR hR' hRB hRB' h ht hr).trans
  apply le_trans _ (adaptiveArray_error_le hZ hC)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast hZ) (by decide : 46 ≤ 48))
    adaptiveArrayConstant_pos.le

theorem exists_near_adaptiveOffEventParameters {L Z M : ℕ} (hL : Squarefree L)
    (hZ : 1 ≤ Z) (hLZ : L ≤ Z) (hC : adaptiveArrayConstant ≤ (Z:ℝ))
    (A : ∀ p : ℕ, Finset (ZMod p)) (h : ℤ) {θ R K : ℝ}
    (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1) (hRlo : (L^6:ℕ) ≤ R) (hRhi : R ≤ (2*Z^13:ℕ))
    (hK : 10 ≤ K) (hKlog : K ≤ Real.log (Z:ℝ))
    (hno : adaptiveNoSmallWitness L M A R h θ K) :
    ∃ a ∈ adaptiveOffEventParameters L Z A K,
      a.modulusResidue=M%(4*L) ∧ a.phaseResidue=adaptivePhaseResidue L h ∧
      |θ-a.theta| ≤ 1/(Z^200:ℕ) ∧ |R-a.radius| ≤ 1/(Z^200:ℕ) := by
  classical
  obtain ⟨a,ha,hMa,hha,hta,hRa⟩ := exists_near_adaptiveSmallBaseParameters hL.ne_zero.bot_lt (by omega)
    (Nat.mod_lt M (by have := hL.ne_zero.bot_lt; omega)) (adaptivePhaseResidue_lt hL.ne_zero.bot_lt h)
    ht0 ht1 hRlo hRhi
  have ha0 := (Finset.mem_filter.mp ha).1
  have hab := mem_adaptiveArrayParameters ha0 (by omega)
  have hRone : (1:ℝ) ≤ R := (show (1:ℝ) ≤ (L^6:ℕ) from by exact_mod_cast Nat.one_le_pow 6 L hL.ne_zero.bot_lt).trans hRlo
  refine ⟨a,Finset.mem_filter.mpr ⟨ha,?_⟩,hMa,hha,hta,hRa⟩
  intro s hs d hd v hv
  have hn := hno s hs d hd v hv
  rw [divisorQuadraticSumP_canonical_reduction hL hd] at hn
  have he := adaptiveSmall_G_grid_error hL hZ hLZ hC hd hv hs A
    (adaptiveInverse (M%(4*L)) d) hRone hab.2.2.2.2.2.2.1 hRhi hab.2.2.2.2.2.2.2
    (adaptivePhaseResidue L h) hta hRa
  have hsqrt : 1 ≤ Real.sqrt ((2:ℝ)^d.primeFactors.card) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  rw [hMa,hha]
  have hnorm := norm_le_norm_add_norm_sub
    (divisorQuadraticSumP d A (adaptiveInverse (M%(4*L)) d) s v 1 R (adaptivePhaseResidue L h) θ)
    (divisorQuadraticSumP d A (adaptiveInverse (M%(4*L)) d) s v 1 a.radius (adaptivePhaseResidue L h) a.theta)
  have habsorb := adaptive_small_mesh_absorb hZ hK hKlog
  have he0 := Real.rpow_nonneg (Nat.cast_nonneg Z) (-(80:ℝ))
  nlinarith [mul_le_mul_of_nonneg_left habsorb (Real.sqrt_nonneg ((2:ℝ)^d.primeFactors.card)),
    mul_le_mul_of_nonneg_right hsqrt he0]

end Ostmann.QuadraticCenter

end

end OAI
