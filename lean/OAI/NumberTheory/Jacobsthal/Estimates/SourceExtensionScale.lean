import OAI.NumberTheory.Jacobsthal.Partitions.EffectiveCoordinateUnits
import OAI.NumberTheory.Jacobsthal.Primes.PrimeEventCounting

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open ErdosInverseBoxHeight ErdosInverseEuler

theorem sourceW_log_bounds : ∀ᶠ z : ℝ in atTop,
    1 < z ∧ 0 < Real.log z ∧ (Real.log z)^((1 : ℝ)/2) ≤ sourceW z ∧ sourceW z ≤ Real.log z := by
  have hs := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1/2)).bound zero_lt_one
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with z hh hLL hz
  have hL : 0 < Real.log z := Real.log_pos hz
  have hLL1 : 1 ≤ Real.log (Real.log z) := hLL
  have hLLpos : 0 < Real.log (Real.log z) := by linarith
  have hbound : (Real.log (Real.log z))^2 ≤ (Real.log z)^((1 : ℝ)/2) := by
    simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (sq_nonneg (Real.log (Real.log z))),
      abs_of_nonneg (Real.rpow_nonneg hL.le ((1 : ℝ)/2)),one_mul] using hh
  have heq : (Real.log z)^((1 : ℝ)/2)*(Real.log z)^((1 : ℝ)/2) = Real.log z := by
    rw [← Real.rpow_add hL]
    norm_num
  refine ⟨hz,hL,?_,?_⟩
  · apply (le_div_iff₀ (sq_pos_of_pos hLLpos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hL.le ((1 : ℝ)/2))]
  · exact div_le_self hL.le (by nlinarith)

theorem sourceW_le_power (alpha : ℝ) (ha : 0 < alpha) :
    ∀ᶠ z : ℝ in atTop,sourceW z ≤ z^alpha := by
  have hs := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) ha).bound zero_lt_one
  filter_upwards [sourceW_log_bounds,hs] with z hz hh
  have hlog : Real.log z ≤ z^alpha := by
    simpa only [Real.norm_eq_abs,Real.rpow_one,abs_of_pos hz.2.1,
      abs_of_nonneg (Real.rpow_nonneg (by linarith [hz.1] : 0 ≤ z) alpha),one_mul] using hh
  exact hz.2.2.2.trans hlog

theorem source_inverse_power_log_tendsto (t : ℝ) (ht : 12 < t) :
    Tendsto (fun z : ℝ => (Real.log z)^6*(sourceW z)^(-t)) atTop (𝓝 0) := by
  have heps : 0 < t/2-6 := by linarith
  have hT := (tendsto_rpow_neg_atTop heps).comp Real.tendsto_log_atTop
  have hnonneg : ∀ᶠ z : ℝ in atTop,0 ≤ (Real.log z)^6*(sourceW z)^(-t) := by
    filter_upwards [sourceW_log_bounds] with z hz
    have hWpos : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
    exact mul_nonneg (pow_nonneg hz.2.1.le 6) (Real.rpow_nonneg hWpos.le _)
  have hbound : ∀ᶠ z : ℝ in atTop,
      (Real.log z)^6*(sourceW z)^(-t) ≤ (Real.log z)^(-(t/2-6)) := by
    filter_upwards [sourceW_log_bounds] with z hz
    have hpow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hz.2.1 ((1 : ℝ)/2))
      hz.2.2.1 (show -t ≤ 0 by linarith)
    calc
      _ ≤ (Real.log z)^6*((Real.log z)^((1 : ℝ)/2))^(-t) :=
        mul_le_mul_of_nonneg_left hpow (pow_nonneg hz.2.1.le 6)
      _ = _ := by
        rw [← Real.rpow_mul hz.2.1.le,← Real.rpow_natCast (Real.log z) 6,← Real.rpow_add hz.2.1]
        congr 1
        norm_num
        ring
  exact squeeze_zero' hnonneg hbound hT

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceSmallModel
open ErdosInversePrimeBin ErdosInverseBoxHeight ErdosInverseSampleCost

theorem source_model_population (alpha xi : ℝ) (ha : 0 < alpha) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    ∀ᶠ z : ℝ in atTop,∀ R theta : ℝ,z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
      1 < R ∧ sourceW z ≤ R ∧ xi*R/(16*Real.log R) ≤ ((primeBin R theta).card : ℝ) := by
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (uniform_prime_bin_count (by positivity : 0 < xi/4))
  filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop R0,sourceW_le_power alpha ha]
    with z hz hW
  intro R theta hRlo htl htu
  have hc := hR0 R (hz.trans hRlo)
  have hRp : 0 < R := by linarith [hc.1]
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hc.1])
  refine ⟨by linarith [hc.1],hW.trans hRlo,?_⟩
  calc
    _ = (xi/4)*R/(4*Real.log R) := by ring
    _ ≤ theta*R/(4*Real.log R) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htl hRp.le) (by positivity)
    _ ≤ _ := (hc.2 theta htl (htu.trans hxi1)).1

end ErdosVarianceSmallModel

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open ErdosInverseBoxHeight ErdosInverseEuler

theorem source_rounding_log_tendsto (K alpha : ℝ) (h : ℕ) (hK : 0 ≤ K) (ha : 0 < alpha) :
    Tendsto (fun z : ℝ => (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*
      (2*(sourceW z)^K)^h/z^alpha) atTop (𝓝 0) := by
  have hcoef : 0 < (2 : ℝ)^h := by positivity
  have hs := (isLittleO_log_rpow_rpow_atTop (6+K*(h : ℝ)) (by positivity : 0 < alpha/4)).bound (inv_pos.mpr hcoef)
  have hbound : ∀ᶠ z : ℝ in atTop,
      (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/z^alpha ≤ z^(-(alpha/2)) := by
    filter_upwards [sourceW_log_bounds,smallModulus_source_power 1 1 zero_lt_one,
      sourceZ_le_rpow (alpha/4) (by positivity),hs] with z hz hM hZ hh
    have hzpos : 0 < z := by linarith [hz.1]
    have hWpos : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
    have hMbound : (smallModulus (sourceW z) : ℝ) ≤ z^(alpha/4) := by
      have hm : (smallModulus (sourceW z) : ℝ) ≤ sourceZ z := by simpa only [pow_one,Real.rpow_one] using hM
      exact hm.trans hZ.2
    have hlogbound : (2 : ℝ)^h*(Real.log z)^(6+K*(h : ℝ)) ≤ z^(alpha/4) := by
      have hsimp : (Real.log z)^(6+K*(h : ℝ)) ≤ ((2 : ℝ)^h)⁻¹*z^(alpha/4) := by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hz.2.1.le _),
          abs_of_nonneg (Real.rpow_nonneg hzpos.le _)] using hh
      have hm := mul_le_mul_of_nonneg_left hsimp hcoef.le
      have heq : (2 : ℝ)^h*(((2 : ℝ)^h)⁻¹*z^(alpha/4)) = z^(alpha/4) := by field_simp
      rwa [heq] at hm
    have hsmall : (Real.log z)^6*(2*(sourceW z)^K)^h ≤ z^(alpha/4) := by
      calc
        _ ≤ (Real.log z)^6*(2*(Real.log z)^K)^h :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hWpos.le hz.2.2.2 hK) (by norm_num)) h)
            (pow_nonneg hz.2.1.le 6)
        _ = (2 : ℝ)^h*(Real.log z)^(6+K*(h : ℝ)) := by
          rw [mul_pow,← Real.rpow_natCast ((Real.log z)^K) h,← Real.rpow_mul hz.2.1.le,
            ← Real.rpow_natCast (Real.log z) 6]
          norm_num only [Nat.cast_ofNat]
          calc
            _ = (2 : ℝ)^h*((Real.log z)^(6 : ℝ)*(Real.log z)^(K*(h : ℝ))) := by ring
            _ = _ := by rw [← Real.rpow_add hz.2.1]
        _ ≤ _ := hlogbound
    calc
      _ = (smallModulus (sourceW z) : ℝ)*((Real.log z)^6*(2*(sourceW z)^K)^h)/z^alpha := by ring
      _ ≤ z^(alpha/4)*z^(alpha/4)/z^alpha := by
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hzpos.le _)
        exact mul_le_mul hMbound hsmall (by positivity) (Real.rpow_nonneg hzpos.le _)
      _ = z^(-(alpha/2)) := by
        rw [← Real.rpow_add hzpos,← Real.rpow_sub hzpos]
        congr 1
        ring
  have hnonneg : ∀ᶠ z : ℝ in atTop,0 ≤
      (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/z^alpha := by
    filter_upwards [sourceW_log_bounds] with z hz
    have hzpos : 0 < z := by linarith [hz.1]
    have hWpos : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
    positivity
  exact squeeze_zero' hnonneg hbound (tendsto_rpow_neg_atTop (by positivity : 0 < alpha/2))

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open ErdosInverseBoxHeight ErdosInverseEuler

theorem source_cost_budget (aStar K alpha eps : ℝ) (h : ℕ) (hK : 0 ≤ K)
    (ha : 0 < alpha) (heps : 0 < eps) (hh : 12 < aStar*(h : ℝ)/2) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R U : ℝ,z^alpha ≤ R → 0 ≤ U → U ≤ (sourceW z)^K →
      (Real.log z)^6*(4*R*((sourceW z)^(-aStar/2))^h+
        (smallModulus (sourceW z) : ℝ)*(2*U)^h)/R ≤ eps := by
  have hmain := source_inverse_power_log_tendsto (aStar*(h : ℝ)/2) hh
  have hround := source_rounding_log_tendsto K alpha h hK ha
  have hsum : Tendsto (fun z : ℝ => 4*((Real.log z)^6*(sourceW z)^(-(aStar*(h : ℝ)/2)))+
      (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/z^alpha) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using (hmain.const_mul 4).add hround
  have hs := (tendsto_order.mp hsum).2 eps heps
  filter_upwards [hs,sourceW_log_bounds] with z hsumsmall hz
  refine ⟨hz.1,?_⟩
  intro R U hR hU hUtop
  have hzpos : 0 < z := by linarith [hz.1]
  have hWpos : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
  have hRpos : 0 < R := (Real.rpow_pos_of_pos hzpos alpha).trans_le hR
  have htau : ((sourceW z)^(-aStar/2))^h = (sourceW z)^(-(aStar*(h : ℝ)/2)) := by
    rw [← Real.rpow_natCast ((sourceW z)^(-aStar/2)) h,← Real.rpow_mul hWpos.le]
    congr 1
    ring
  have hURound : (2*U)^h ≤ (2*(sourceW z)^K)^h :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hUtop (by norm_num)) h
  have hroundle : (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*U)^h/R ≤
      (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/z^alpha := by
    calc
      _ ≤ (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/R :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hURound (by positivity)) hRpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hzpos _) hR
  calc
    _ = 4*((Real.log z)^6*(sourceW z)^(-(aStar*(h : ℝ)/2)))+
        (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*U)^h/R := by
      rw [htau]
      field_simp
    _ ≤ 4*((Real.log z)^6*(sourceW z)^(-(aStar*(h : ℝ)/2)))+
        (Real.log z)^6*(smallModulus (sourceW z) : ℝ)*(2*(sourceW z)^K)^h/z^alpha :=
      add_le_add le_rfl hroundle
    _ ≤ eps := hsumsmall.le

end ErdosInverseSampleCost

end

section

namespace ErdosVarianceSmallModel
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem atomWeight_totient (R xi w : ℝ) (H : ℕ) (C0 : ℤ) :
    atomWeight R xi w H C0 = (H : ℝ)/
      (((H*divisorModulus w H*coprimeModulus w H).totient : ℝ)*modelLength R xi (H : ℝ) (C0 : ℝ)) := by
  rw [pattern_totient]
  simp only [atomWeight,Nat.cast_mul]
  congr 1
  ring

theorem prime_bound_le_atom (R xi w : ℝ) (H : ℕ) (C0 : ℤ) (n : ℕ) (C : ℝ)
    (hR : 1 < R) (hxi : 0 < xi) (hH : 0 < H) (hC : 0 ≤ C)
    (hPopulation : xi*R/(16*Real.log R) ≤ (n : ℝ)) :
    C*primeWidth R xi (H : ℝ) (C0 : ℝ)/
      (((H*divisorModulus w H*coprimeModulus w H).totient : ℝ)*Real.log R) ≤
      (32*C*(n : ℝ))*atomWeight R xi w H C0 := by
  have hRp : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hM : 0 < H*divisorModulus w H*coprimeModulus w H :=
    Nat.mul_pos (Nat.mul_pos hH (divisorModulus_pos w H)) (coprimeModulus_pos w H)
  have hphi : (0 : ℝ) < (H*divisorModulus w H*coprimeModulus w H).totient := by
    exact_mod_cast Nat.totient_pos.mpr hM
  have hY : 0 < modelLength R xi (H : ℝ) (C0 : ℝ) := by
    dsimp [modelLength,interceptScale]
    positivity
  have hpop := (div_le_iff₀ (by positivity : 0 < 16*Real.log R)).mp hPopulation
  have harea := small_model_area R xi (H : ℝ) (C0 : ℝ) hRp hxi hHR
  have hpopH := mul_le_mul_of_nonneg_right hpop (show 0 ≤ 2*(H : ℝ) by positivity)
  have hwidth : primeWidth R xi (H : ℝ) (C0 : ℝ)*modelLength R xi (H : ℝ) (C0 : ℝ) ≤
      32*(n : ℝ)*Real.log R*(H : ℝ) := by nlinarith
  calc
    _ ≤ ((32*C*(n : ℝ))*(H : ℝ))/
        (((H*divisorModulus w H*coprimeModulus w H).totient : ℝ)*modelLength R xi (H : ℝ) (C0 : ℝ)) := by
      apply (div_le_div_iff₀ (mul_pos hphi hlog) (mul_pos hphi hY)).mpr
      have hh := mul_le_mul_of_nonneg_left hwidth
        (mul_nonneg hC (hphi.le))
      nlinarith
    _ = _ := by rw [atomWeight_totient];ring

theorem finite_model_domination (P : Finset ℕ) (R xi w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (hR : 1 < R) (hxi : 0 < xi) (hH : 0 < H) (hC0 : Int.gcd C0 (H : ℤ) = 1)
    (hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R)
    (C : ℝ) (hC : 0 ≤ C) (hPopulation : xi*R/(16*Real.log R) ≤ (P.card : ℝ))
    (hFibre : ∀ v ∈ modelUniverse R xi w H C0,
      ((primeFibre P w H C0 hw hP hlarge v).card : ℝ) ≤
        C*primeWidth R xi (H : ℝ) (C0 : ℝ)/
          (((H*divisorModulus w H*coprimeModulus w H).totient : ℝ)*Real.log R))
    (E : ModelPoint w H → Prop) :
    ((actualPrimeEvent P w H C0 hw hP hlarge E).card : ℝ)/(P.card : ℝ) ≤
      (32*C)*modelMass R xi w H C0 E := by
  have hRp : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hPpos : (0 : ℝ) < P.card := (by positivity : 0 < xi*R/(16*Real.log R)).trans_le hPopulation
  have hatom := prime_bound_le_atom R xi w H C0 P.card C hR hxi hH hC hPopulation
  apply (div_le_iff₀ hPpos).mpr
  calc
    _ = ∑ v ∈ (modelUniverse R xi w H C0).filter E,((primeFibre P w H C0 hw hP hlarge v).card : ℝ) := by
      rw [actualPrimeEvent_card_fibres P R xi w H C0 hw hP hlarge hRp hxi.le hH hC0 hbin E,Nat.cast_sum]
    _ ≤ ∑ _v ∈ (modelUniverse R xi w H C0).filter E,(32*C*(P.card : ℝ))*atomWeight R xi w H C0 := by
      apply Finset.sum_le_sum
      intro v hv
      exact (hFibre v (Finset.mem_filter.mp hv).1).trans hatom
    _ = ((32*C)*modelMass R xi w H C0 E)*(P.card : ℝ) := by
      rw [← Finset.mul_sum]
      change (32*C*(P.card : ℝ))*modelMass R xi w H C0 E = _
      ring

end ErdosVarianceSmallModel

end

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceSmallModel
open ErdosInversePrimeBin ErdosInverseBoxHeight ErdosInverseEuler

theorem source_prime_model_domination (alpha : ℝ) (ha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ xi : ℝ,0 < xi → xi ≤ 1 →
      ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (H : ℕ) (C0 : ℤ),
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi → 0 < H → Int.gcd C0 (H : ℤ) = 1 →
        (H : ℝ) ≤ R^((4 : ℝ)/5) → totalScale R (H : ℝ) (C0 : ℝ)/(H : ℝ) ≤ (sourceZ z)^12 →
        ∃ (hw : 0 ≤ sourceW z) (hP : ∀ p ∈ primeBin R theta,p.Prime)
          (hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ)),
        ∀ E : ModelPoint (sourceW z) H → Prop,
          ((actualPrimeEvent (primeBin R theta) (sourceW z) H C0 hw hP hlarge E).card : ℝ)/
            ((primeBin R theta).card : ℝ) ≤ C*modelMass R xi (sourceW z) H C0 E := by
  obtain ⟨C,hC,hFibres⟩ := source_residue_fibre_bound alpha ha
  refine ⟨32*C,by positivity,?_⟩
  intro xi hxi hxi1
  filter_upwards [hFibres xi hxi hxi1,source_model_population alpha xi ha hxi hxi1,
    sourceW_tendsto_atTop.eventually_ge_atTop 2] with z hFibre hPopulation hW
  intro R theta H C0 hRlo htl htu hH hC0 hHsmall hRatio
  have hpops := hPopulation R theta hRlo htl htu
  have hR : 0 < R := by linarith [hpops.1]
  have ht : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans htl
  let P := primeBin R theta
  have hP : ∀ p ∈ P,p.Prime := fun p hp => ((mem_primeBin hR.le ht p).mp hp).1
  have hlarge : ∀ p ∈ P,sourceW z < (p : ℝ) :=
    fun p hp => hpops.2.1.trans_lt ((mem_primeBin hR.le ht p).mp hp).2.1
  have hbin : ∀ p ∈ P,R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R := by
    intro p hp
    have hh := (mem_primeBin hR.le ht p).mp hp
    refine ⟨hh.2.1,?_⟩
    have htR := mul_le_mul_of_nonneg_right htu hR.le
    nlinarith [hh.2.2]
  have hw : 0 ≤ sourceW z := by linarith
  let : NeZero H := ⟨hH.ne'⟩
  refine ⟨hw,hP,hlarge,?_⟩
  intro E
  apply finite_model_domination P R xi (sourceW z) H C0 hw hP hlarge hpops.1 hxi hH hC0 hbin C hC.le hpops.2.2
  · intro v hv
    have hm := (mem_modelUniverse R xi (sourceW z) H C0 v).mp hv |>.2.2
    let M := H*divisorModulus (sourceW z) H*coprimeModulus (sourceW z) H
    have hM : 0 < M := Nat.mul_pos (Nat.mul_pos hH (divisorModulus_pos _ H)) (coprimeModulus_pos _ H)
    have hMbound : (M : ℝ) ≤ (H : ℝ)*(smallModulus (sourceW z) : ℝ) := by
      have hh := pattern_modulus_size (sourceW z) H
      have he : (M : ℝ) = (H : ℝ)*(smallModulus (sourceW z) : ℝ) := by exact_mod_cast hh
      exact he.le
    calc
      _ ≤ ((residueFibre P (H : ℝ) (C0 : ℝ) v.1 M
          (patternClass (sourceW z) H C0 hC0 v.1 hm v.2 : ℤ)).card : ℝ) := by
        exact_mod_cast primeFibre_card_le_residue P (sourceW z) H C0 hw hP hlarge hC0 v hm
      _ ≤ _ := hFibre.2 P R (H : ℝ) (C0 : ℝ) v.1 M
        (patternClass (sourceW z) H C0 hC0 v.1 hm v.2 : ℤ) hRlo (by exact_mod_cast hH) hM
        hHsmall hMbound hRatio (fun p hp => ⟨hP p hp,(hbin p hp).1,(hbin p hp).2⟩)

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem badPrimeProduct_extension_dvd (a : ℕ → ℤ) (r : ℚ) (q e : ℕ) (hq : q ≠ 0) :
    badPrimeProduct a r (q*e) ∣ badPrimeProduct a r q*e := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime
  · intro p hp
    obtain ⟨hpf,hnon⟩ := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hpf
    rcases hprime.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hpf) with hpq | hpe
    · have hpbad : p ∈ badPrimeFactors a r q := Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hprime,hpq,hq⟩,hnon⟩
      exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hpbad) e
    · exact dvd_mul_of_dvd_right hpe _

theorem effectiveModulus_extension_le (a : ℕ → ℕ) (r : ℚ) (q e : ℕ) (hq : 0 < q) (he : 0 < e) :
    effectiveModulus a r (q*e) ≤
      (r.den*badPrimeProduct (fun t => (a t : ℤ)) r q)*e := by
  have hh := Nat.le_of_dvd (Nat.mul_pos (badPrimeProduct_pos (fun t => (a t : ℤ)) r q) he)
    (badPrimeProduct_extension_dvd (fun t => (a t : ℤ)) r q e hq.ne')
  simpa only [effectiveModulus,Nat.mul_assoc] using Nat.mul_le_mul_left r.den hh

theorem effectiveModulus_height_of_extension (a : ℕ → ℕ) (r : ℚ) (q e : ℕ) (hq : 0 < q) (he : 0 < e)
    (R Z : ℝ) (hR : 0 ≤ R) (_hZ : 0 ≤ Z)
    (hparent : ((r.den*badPrimeProduct (fun t => (a t : ℤ)) r q : ℕ) : ℝ) ≤ R*Z^10)
    (heZ : (e : ℝ) ≤ Z) :
    (effectiveModulus a r (q*e) : ℝ) ≤ R*Z^11 := by
  calc
    _ ≤ ((r.den*badPrimeProduct (fun t => (a t : ℤ)) r q : ℕ) : ℝ)*(e : ℝ) := by
      exact_mod_cast effectiveModulus_extension_le a r q e hq he
    _ ≤ (R*Z^10)*Z := mul_le_mul hparent heZ (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end ErdosVarianceEffective

end

section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceEffective
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseSampleCost

theorem sourceW_power_subpower (A eps : ℝ) (hA : 0 ≤ A) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,(sourceW z)^A ≤ (sourceZ z)^eps := by
  filter_upwards [sourceW_log_bounds,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    exp_loglog_sq_le_sourceZ A eps hA heps] with z hz hLL hExp
  have hW : 0 < sourceW z := (Real.rpow_pos_of_pos hz.2.1 _).trans_le hz.2.2.1
  change 1 ≤ Real.log (Real.log z) at hLL
  have hLLsq : Real.log (Real.log z) ≤ (Real.log (Real.log z))^2 := by nlinarith
  calc
    _ ≤ (Real.log z)^A := Real.rpow_le_rpow hW.le hz.2.2.2 hA
    _ = Real.exp (A*Real.log (Real.log z)) := by rw [Real.rpow_def_of_pos hz.2.1];congr 1;ring
    _ ≤ Real.exp (A*(Real.log (Real.log z))^2) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hLLsq hA)
    _ ≤ _ := hExp

theorem extension_le_parent_power (Y p q e : ℕ) (hp : 0 < p) (hq : 0 < q) (he : 0 < e)
    (w C : ℝ) (hw : 1 < w) (hFinal : p*(q*e) ≤ Y)
    (hParent : Real.logb w ((Y : ℝ)/((p : ℝ)*q)) ≤ C) : (e : ℝ) ≤ w^C := by
  have hden : 0 < (p : ℝ)*q := by positivity
  have hY : 0 < Y := (Nat.mul_pos hp (Nat.mul_pos hq he)).trans_le hFinal
  have hratio : 0 < (Y : ℝ)/((p : ℝ)*q) := by positivity
  have hbound : (e : ℝ) ≤ (Y : ℝ)/((p : ℝ)*q) := by
    apply (le_div_iff₀ hden).mpr
    have hh : (p : ℝ)*((q : ℝ)*(e : ℝ)) ≤ (Y : ℝ) := by exact_mod_cast hFinal
    nlinarith
  exact hbound.trans ((Real.logb_le_iff_le_rpow hw hratio).mp hParent)

theorem source_extension_le_Z (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop,∀ p q e : ℕ,0 < p → 0 < q → 0 < e →
      p*(q*e) ≤ sourceY z →
      Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q)) ≤ C → (e : ℝ) ≤ sourceZ z := by
  filter_upwards [sourceW_power_subpower C 1 hC zero_lt_one,sourceW_tendsto_atTop.eventually_ge_atTop 2]
    with z hpower hW
  intro p q e hp hq he hFinal hParent
  have hh := extension_le_parent_power (sourceY z) p q e hp hq he (sourceW z) C (by linarith) hFinal hParent
  exact hh.trans (by simpa only [Real.rpow_one] using hpower)

end ErdosVarianceEffective

end

end Erdos970

end OAI
