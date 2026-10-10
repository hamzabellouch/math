import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.PolygonCovarianceEnergy
import OAI.GroupTheory.SimpleAmenable.RandomFields.FiniteFieldConcentration
import OAI.GroupTheory.SimpleAmenable.Arithmetic.DyadicArithmetic

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceCovarianceLimit
open Classical Filter
open scoped Topology

noncomputable def sourceFlagMatrix {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ η κ : ℝ) (n : ℕ)
    (z y : FlagSite a m D v) : ℝ :=
  sourceDyadicWeight n*∑i∈sourceDyadicIndices n,
    flagAveragingMatrix χ ρ (sourceDyadicN n) ((2:ℝ)^i) η κ z y

theorem sourceFlagMatrix_covariance {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1) {K L ρ η κ : ℝ}
    (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
    (hL : 0≤L) (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ)
    (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|))
    (T : ℕ → Finset (FlagSite a m D v × FlagSite a m D v)) :
    Tendsto (fun n => ∑p∈T n,(sourceFlagMatrix χ ρ η κ n p.1 p.2-
      sourceFlagMatrix χ ρ η κ n (flagSiteAction hD g p.1) (flagSiteAction hD g p.2))^2)
      atTop (nhds 0) := by
  obtain ⟨R,C,hR,hC,he⟩ := flagMatrixDifference_dyadic_energy (v:=v) hD g χ hχ
    hK hcompact hL hρ hη hκ hLip
  have ht := sourceDyadicWeight_energy_tendsto.const_mul (4*C)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun n => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) _ ht
  filter_upwards [sourceDyadic_fine_eventually R hκ] with n hn
  have h := he (sourceDyadicN n) (sourceDyadicN_one_le n) (sourceDyadicIndices n) hn
    (sourceDyadicWeight n) (T n)
  simpa only [sourceFlagMatrix,flagMatrixDifference,Finset.sum_sub_distrib,mul_sub,mul_assoc] using h

end SourceCovarianceLimit

section SourceFieldConcentration
open Classical Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable def sourceActiveSites {a m D : ℕ} {v : ℝ×ℝ}
    (hD : 0<D) {K : ℝ} (hK : 0<K) (n : ℕ) : Finset (FlagSite a m D v) :=
  (flagSiteBox_finite hD (mul_pos (sourceDyadicN_pos n) hK)).toFinset

theorem sourceFlagMatrix_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {K : ℝ} (hK : 0<K)
    (hcompact : ∀x,K ≤ ‖x‖ → χ x=0) (ρ η κ : ℝ) (n : ℕ)
    (z y : FlagSite a m D v) (hz : z∉sourceActiveSites (v:=v) hD hK n) :
    sourceFlagMatrix χ ρ η κ n z y=0 := by
  have hnot : ¬z∈flagSiteBox (sourceDyadicN n*K) := by
    simpa only [sourceActiveSites,Set.Finite.mem_toFinset] using hz
  have hc : χ (scaledSiteConjugate (sourceDyadicN n) z)=0 := by
    apply hcompact
    by_contra hh
    have hh' : ‖scaledSiteConjugate (sourceDyadicN n) z‖<K := lt_of_not_ge hh
    have h₁ := norm_fst_le (scaledSiteConjugate (sourceDyadicN n) z)
    have h₂ := norm_snd_le (scaledSiteConjugate (sourceDyadicN n) z)
    simp only [scaledSiteConjugate,Real.norm_eq_abs,abs_div,abs_of_pos (sourceDyadicN_pos n)] at h₁ h₂
    apply hnot
    constructor
    · have h := (div_lt_iff₀ (sourceDyadicN_pos n)).mp (h₁.trans_lt hh'); nlinarith
    · have h := (div_lt_iff₀ (sourceDyadicN_pos n)).mp (h₂.trans_lt hh'); nlinarith
  simp only [sourceFlagMatrix,flagAveragingMatrix_cutoff_left χ _ _ _ _ _ z y hc,
    Finset.sum_const_zero,mul_zero]

theorem sourceActiveSites_card {a m D : ℕ} {v : ℝ×ℝ}
    (hD : 0<D) {K : ℝ} (hK : 0<K) (n : ℕ) :
    ((sourceActiveSites (a:=a) (m:=m) (v:=v) hD hK n).card:ℝ) ≤
      (m:ℝ)*(2*(D:ℝ)^2*K+2)^2*(sourceDyadicN n)^2 := by
  have hc := flagSiteBox_card_bound (a:=a) (m:=m) (v:=v) hD
    (mul_pos (sourceDyadicN_pos n) hK) (sourceActiveSites hD hK n)
    (fun z hz => (Set.Finite.mem_toFinset _).mp hz)
  have hN := sourceDyadicN_one_le n
  have hp : 2*(D:ℝ)^2*(sourceDyadicN n*K)+2 ≤ (2*(D:ℝ)^2*K+2)*sourceDyadicN n := by
    nlinarith
  calc
    _ ≤ (m:ℝ)*(2*(D:ℝ)^2*(sourceDyadicN n*K)+2)^2 := hc
    _ ≤ (m:ℝ)*((2*(D:ℝ)^2*K+2)*sourceDyadicN n)^2 := by gcongr
    _ = _ := by ring

theorem sourceDyadicWeight_eventually_sq_le_one :
    ∀ᶠn : ℕ in atTop,(sourceDyadicWeight n)^2 ≤ 1 := by
  filter_upwards [sourceDyadicWeight_energy_tendsto.eventually_lt_const zero_lt_one] with n hn
  rw [sourceDyadicIndices_card,Nat.cast_add,Nat.cast_one] at hn
  nlinarith [sq_nonneg (sourceDyadicWeight n),Nat.cast_nonneg (α:=ℝ) n]

theorem sourceFlagMatrix_concentration {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {K ρ η κ ε : ℝ} (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
    (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ) (hε : 0<ε)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : FlagSite a m D v → Ω → ℝ) (hind : iIndepFun X μ)
    (hm : ∀i,AEMeasurable (X i) μ) (hb : ∀i,∀ᵐω ∂μ,X i ω∈Set.Icc (-1:ℝ) 1)
    (hc : ∀i,∫ω,X i ω ∂μ=0) :
    Tendsto (fun n => μ.real {ω | ∃z : FlagSite a m D v,
      ε ≤ |∑y∈sourceActiveSites hD hK n,sourceFlagMatrix χ ρ η κ n z y*X y ω|})
        atTop (nhds 0) := by
  let C := 2*flagRowConstant D ρ η
  let A := (m:ℝ)*(2*(D:ℝ)^2*K+2)^2
  let c := ε^2/(2*C^2)
  have hC : 0<C := by dsimp [C,flagRowConstant]; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hc₀ : 0<c := by dsimp [c]; positivity
  have ht4 := tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ)<4 by norm_num)
  have ht : Tendsto (fun n : ℕ => 2*A*((4:ℝ)^n)^4*Real.exp (-c*(4:ℝ)^n)) atTop (nhds 0) := by
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4:ℝ) c hc₀).comp ht4
    have ht' := ht.const_mul (2*A)
    simpa only [Real.rpow_ofNat,mul_zero,mul_assoc,Function.comp_def] using ht'
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ ht
  filter_upwards [sourceDyadicWeight_eventually_sq_le_one] with n hw
  let S : Finset (FlagSite a m D v) := sourceActiveSites hD hK n
  have heq : {ω | ∃z : FlagSite a m D v,
      ε ≤ |∑y∈S,sourceFlagMatrix χ ρ η κ n z y*X y ω|} =
      {ω | ∃z∈S,ε ≤ |∑y∈S,sourceFlagMatrix χ ρ η κ n z y*X y ω|} := by
    ext ω
    constructor
    · rintro ⟨z,hz⟩
      refine ⟨z,?_,hz⟩
      by_contra hn
      have hzero (y : FlagSite a m D v) := sourceFlagMatrix_support hD χ hK hcompact ρ η κ n z y hn
      simp only [hzero,zero_mul,Finset.sum_const_zero,abs_zero] at hz
      exact (not_le.mpr hε) hz
    · rintro ⟨z,_,hz⟩; exact ⟨z,hz⟩
  have hrow (z : FlagSite a m D v) : ∑y∈S,(sourceFlagMatrix χ ρ η κ n z y)^2 ≤ C^2/(4:ℝ)^n := by
    have h := flagAveragingMatrix_dyadic_row_energy hD χ hχ hρ (sourceDyadicN_pos n) hη hκ
      (sourceDyadicIndices n) n (fun i hi => (Finset.mem_Icc.mp hi).1) (sourceDyadicWeight n) z S
    have hpow : ((2:ℝ)^n)^2=(4:ℝ)^n := by rw [← pow_mul,pow_mul']; norm_num
    calc
      _ ≤ (C*sourceDyadicWeight n/(2:ℝ)^n)^2 := h
      _ = C^2*(sourceDyadicWeight n)^2/(4:ℝ)^n := by rw [div_pow,mul_pow,hpow]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hw (sq_nonneg C)
  rw [heq]
  calc
    _ ≤ 2*(S.card:ℝ)*Real.exp (-ε^2/(2*(C^2/(4:ℝ)^n))) :=
      finite_matrix_noise_tail μ X hind hm hb hc S S (sourceFlagMatrix χ ρ η κ n)
        (by positivity) (fun z _ => hrow z) hε.le
    _ ≤ 2*(A*(sourceDyadicN n)^2)*Real.exp (-ε^2/(2*(C^2/(4:ℝ)^n))) := by
      gcongr
      exact sourceActiveSites_card hD hK n
    _ = _ := by
      have hexp : -ε^2/(2*(C^2/(4:ℝ)^n)) = -c*(4:ℝ)^n := by dsimp [c]; field_simp
      rw [hexp]
      have hpow : (sourceDyadicN n)^2=((4:ℝ)^n)^4 := by
        unfold sourceDyadicN
        rw [← pow_mul,← pow_mul]
        rw [show (4:ℝ)=2^2 by norm_num,← pow_mul]
        congr 1
        omega
      rw [hpow]
      ring

end SourceFieldConcentration

end SimpleAmenable
end
end

end OAI
