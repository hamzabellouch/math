import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPolynomial

namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace SevenEighths.InverseInitialExcludedGeometry
open HeckeFamily InverseInitialExcludedPolynomial IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

def adjustedLength (Z r:ℝ)(j:Ideal O):ℝ:=r-Real.log (j.absNorm:ℝ)/Real.log Z

theorem adjusted_scale (Z r:ℝ)(hZ:1<Z){j:Ideal O}(hj:j≠0):
    Z^adjustedLength Z r j=Z^r/(j.absNorm:ℝ) := by
  have hjpos:0<(j.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj)
  have hzpos:=lt_trans zero_lt_one hZ
  rw [adjustedLength,Real.rpow_sub hzpos]
  congr 1
  rw [Real.rpow_def_of_pos hzpos]
  have hl:Real.log Z≠0:=(Real.log_pos hZ).ne'
  rw [mul_div_cancel₀ _ hl,Real.exp_log hjpos]

theorem divisor_norm_bounds {P j:Ideal O}(hP:P≠0)(hj:j∣P):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤(P.absNorm:ℝ) := by
  have hj0:=ne_zero_of_dvd_ne_zero hP hj
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP))
      (map_dvd Ideal.absNorm hj)

theorem adjustedLength_bounds (Z r η:ℝ)(hZ:1<Z){P j:Ideal O}
    (hP:P≠0)(hj:j∣P)(hlarge:Real.log (P.absNorm:ℝ)≤η*Real.log Z):
    r-η≤adjustedLength Z r j ∧ adjustedLength Z r j≤r := by
  obtain ⟨hn,hnP⟩:=divisor_norm_bounds hP hj
  have hl:0≤Real.log (j.absNorm:ℝ):=Real.log_nonneg hn
  have hu:Real.log (j.absNorm:ℝ)≤η*Real.log Z:=
    (Real.log_le_log (lt_of_lt_of_le zero_lt_one hn) hnP).trans hlarge
  have hd:Real.log (j.absNorm:ℝ)/Real.log Z≤η:=(div_le_iff₀ (Real.log_pos hZ)).mpr hu
  have hd0:0≤Real.log (j.absNorm:ℝ)/Real.log Z:=div_nonneg hl (Real.log_pos hZ).le
  dsimp [adjustedLength]
  constructor <;> linarith

theorem adjustedLength_eventually (P:Ideal O)(hP:P≠0)(η:ℝ)(hη:0<η):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀r:ℝ,∀j∈idealDivisors P,
      r-η≤adjustedLength Z r j ∧ adjustedLength Z r j≤r := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (P.absNorm:ℝ)/η))] with Z hZ hlog
  refine ⟨hZ,fun r j hj=>adjustedLength_bounds Z r η hZ hP ((mem_idealDivisors hP).mp hj) ?_⟩
  exact (div_le_iff₀ hη).mp hlog |>.trans_eq (mul_comm _ _)

theorem prime_coprime_of_norm_gt {P I:Ideal O}(hP:Prime P)(hI:I≠0)
    (hN:(I.absNorm:ℝ)<(P.absNorm:ℝ)):IsCoprime P I := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hIJ hJ
  have hmax:=(Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have heq:=hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hIJ
  have hd:P∣I:=Ideal.dvd_iff_le.mpr hIJ
  exact (not_le_of_gt hN) (divisor_norm_bounds hI hd).2

theorem live_prime_deleted_coefficient (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(V:ℝ→ℂ)(a Y:ℝ)(hY:0<Y)
    (hV:∀x,V x≠0→a≤x)(hlarge:((∏Q∈S,Q).absNorm:ℝ)<a*Y)
    (P:Ideal O)(hP:Prime P)(hvp:V ((P.absNorm:ℝ)/Y)≠0):
    idealCoeff (χ.excludePrimes S hS) P=idealCoeff χ P := by
  rw [deleted_coefficient_product,ite_eq_left]
  apply prime_coprime_of_norm_gt hP (prime_product_squarefree S hS).ne_zero
  exact hlarge.trans_le ((le_div_iff₀ hY).mp (hV _ hvp))

theorem prime_slot_unchanged (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(V:ℝ→ℂ)(a Y:ℝ)(hY:0<Y)
    (hV:∀x,V x≠0→a≤x)(hlarge:((∏Q∈S,Q).absNorm:ℝ)<a*Y)
    (P:Ideal O)(hP:Prime P):
    idealCoeff (χ.excludePrimes S hS) P*V ((P.absNorm:ℝ)/Y)=
      idealCoeff χ P*V ((P.absNorm:ℝ)/Y) := by
  by_cases hv:V ((P.absNorm:ℝ)/Y)=0
  · rw [hv,mul_zero,mul_zero]
  · rw [live_prime_deleted_coefficient χ S hS V a Y hY hV hlarge P hP hv]

end SevenEighths.InverseInitialExcludedGeometry

end

end OAI
