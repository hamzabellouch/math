import Mathlib
import OAI.Analysis.VlasovMaxwell.Model
import OAI.Analysis.VlasovMaxwell.Geometry.DensitySecondMoment

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def dyadicBalanceConstant (α β : ℝ) : ℝ :=
  (1-((2:ℝ)^α)⁻¹)⁻¹+2^β/(1-((2:ℝ)^β)⁻¹)

lemma dyadicBalanceConstant_pos {α β : ℝ} (hα : 0<α) (hβ : 0<β) :
    0<dyadicBalanceConstant α β := by
  have ha : 0<1-((2:ℝ)^α)⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hα))
  have hb : 0<1-((2:ℝ)^β)⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hβ))
  unfold dyadicBalanceConstant
  positivity

lemma dyadic_power_min_summable {a b α β : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hα : 0<α) (hβ : 0<β) :
    Summable (fun k : ℤ => min (a*((2:ℝ)^k)^α) (b*((2:ℝ)^k)^(-β))) := by
  have hh := (geometric_min_summable_bound ha hb
    (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hα)
    (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hβ)).1
  convert hh using 1
  funext k
  rw [Real.rpow_zpow_comm (by norm_num : (0:ℝ)≤2),
    Real.rpow_zpow_comm (by norm_num : (0:ℝ)≤2),zpow_neg,
    Real.inv_rpow (zpow_pos (by norm_num : (0:ℝ)<2) k).le,
    Real.rpow_neg (zpow_pos (by norm_num : (0:ℝ)<2) k).le]

lemma truncated_dyadic_crossing {n f α : ℝ} (hn : 0<n) (hf : 0<f)
    (hα : 0<α) :
    Summable (fun j : ℕ => min (n*((2:ℝ)^j)^α) (f*((2:ℝ)^j)^(-1:ℝ))) ∧
    (∑' j : ℕ, min (n*((2:ℝ)^j)^α) (f*((2:ℝ)^j)^(-1:ℝ))) ≤
      min (2*f) (dyadicBalanceConstant α 1 * (n^(1/(α+1))*f^(α/(α+1)))) := by
  let g : ℤ→ℝ := fun k=>min (n*((2:ℝ)^k)^α) (f*((2:ℝ)^k)^(-1:ℝ))
  have hg : Summable g := dyadic_power_min_summable hn.le hf.le hα (by norm_num)
  have h0 (k : ℤ) : 0≤g k := le_min
    (mul_nonneg hn.le (Real.rpow_nonneg (zpow_pos (by norm_num : (0:ℝ)<2) k).le _))
    (mul_nonneg hf.le (Real.rpow_nonneg (zpow_pos (by norm_num : (0:ℝ)<2) k).le _))
  have hs : Summable (fun j : ℕ=>g j) := hg.comp_injective Int.ofNat_injective
  have he (j : ℕ) : g j=min (n*((2:ℝ)^j)^α) (f*((2:ℝ)^j)^(-1:ℝ)) := by
    simp only [g,zpow_natCast]
  simp_rw [he] at hs
  refine ⟨hs,le_min ?_ ?_⟩
  · have hb (j : ℕ) : min (n*((2:ℝ)^j)^α) (f*((2:ℝ)^j)^(-1:ℝ)) ≤ f*((2:ℝ)⁻¹)^j := by
      rw [inv_pow]
      exact (min_le_right _ _).trans_eq (by rw [Real.rpow_neg_one])
    have hfs : Summable (fun j : ℕ=>f*((2:ℝ)⁻¹)^j) :=
      (summable_geometric_of_abs_lt_one (by norm_num : |(2:ℝ)⁻¹|<1)).mul_left f
    have ht := hs.tsum_le_tsum hb hfs
    rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by norm_num : |(2:ℝ)⁻¹|<1)] at ht
    norm_num at ht
    linarith
  · have ht : (∑' j : ℕ,g j)≤∑' k : ℤ,g k :=
      Summable.tsum_le_tsum_of_inj Int.ofNat Int.ofNat_injective (fun k _=>h0 k) (fun _=>le_rfl)
        (hg.comp_injective Int.ofNat_injective) hg
    simp_rw [he] at ht
    exact ht.trans (dyadic_balance hn hf hα (by norm_num))

lemma crossing_normalisation {n D α : ℝ} (hn : 0<n) (hD : 0<D)
    (_hα : 0<α) :
    n^(1/(α+1))*(D^2/n)^(α/(α+1)) = D*(n/D)^((1-α)/(1+α)) := by
  rw [Real.div_rpow (sq_nonneg D) hn.le,←Real.rpow_natCast_mul hD.le]
  rw [Real.div_rpow hn.le hD.le]
  norm_num only [Nat.cast_ofNat]
  have he : 1/(α+1)-α/(α+1)=(1-α)/(1+α) := by ring
  have hnexp : n^(1/(α+1))/n^(α/(α+1))=n^((1-α)/(1+α)) := by
    rw [←Real.rpow_sub hn,he]
  rw [show n^(1/(α+1))*(D^((2:ℝ)*(α/(α+1)))/n^(α/(α+1)))=
    (n^(1/(α+1))/n^(α/(α+1)))*D^((2:ℝ)*(α/(α+1))) by ring,hnexp]
  have he' : (2:ℝ)*(α/(α+1))=1-(1-α)/(1+α) := by field_simp; ring
  rw [he',Real.rpow_sub hD,Real.rpow_one]
  ring

lemma truncated_crossing_normalised {n D α : ℝ} (hn : 0<n) (hD : 0<D)
    (hα : 0<α) :
    (∑' j : ℕ, min (n*((2:ℝ)^j)^α) ((D^2/n)*((2:ℝ)^j)^(-1:ℝ))) ≤
      (2+dyadicBalanceConstant α 1)*D*
        min ((n/D)^((1-α)/(1+α))) ((n/D)^(-1:ℝ)) := by
  have hf : 0<D^2/n := div_pos (sq_pos_of_pos hD) hn
  have hb := (truncated_dyadic_crossing hn hf hα).2
  have hC := dyadicBalanceConstant_pos hα (by norm_num : (0:ℝ)<1)
  have he : D^2/n=D*(n/D)^(-1:ℝ) := by
    rw [Real.rpow_neg_one,inv_div]
    ring
  have hnorm := crossing_normalisation hn hD hα
  rw [mul_min_of_nonneg _ _ (by positivity : 0≤(2+dyadicBalanceConstant α 1)*D)]
  apply le_min
  · have hh := hb.trans (min_le_right _ _)
    rw [hnorm] at hh
    have h0 : 0≤D*(n/D)^((1-α)/(1+α)) := by positivity
    calc
      _ ≤ dyadicBalanceConstant α 1*(D*(n/D)^((1-α)/(1+α))) := hh
      _ ≤ (2+dyadicBalanceConstant α 1)*(D*(n/D)^((1-α)/(1+α))) :=
        mul_le_mul_of_nonneg_right (by linarith) h0
      _ = _ := by ring
  · have hh := hb.trans (min_le_left _ _)
    calc
      _ ≤ 2*(D^2/n) := hh
      _ ≤ (2+dyadicBalanceConstant α 1)*(D^2/n) :=
        mul_le_mul_of_nonneg_right (by linarith) hf.le
      _ = _ := by rw [he]; ring

lemma angular_crossing_sum {x γ q : ℝ} (hx : 0<x) (hγ : 0<γ) (hq : 0<q) :
    Summable (fun k : ℤ=>min ((x*((2:ℝ)^k)^γ)^q) ((x*((2:ℝ)^k)^γ)^(-1:ℝ))) ∧
    (∑' k : ℤ,min ((x*((2:ℝ)^k)^γ)^q) ((x*((2:ℝ)^k)^γ)^(-1:ℝ))) ≤
      dyadicBalanceConstant (γ*q) γ := by
  have hgq : 0<γ*q := mul_pos hγ hq
  have he (k : ℤ) : min ((x*((2:ℝ)^k)^γ)^q) ((x*((2:ℝ)^k)^γ)^(-1:ℝ))=
      min (x^q*((2:ℝ)^k)^(γ*q)) (x^(-1:ℝ)*((2:ℝ)^k)^(-γ)) := by
    rw [Real.mul_rpow hx.le (Real.rpow_nonneg (zpow_pos (by norm_num : (0:ℝ)<2) k).le γ),
      Real.mul_rpow hx.le (Real.rpow_nonneg (zpow_pos (by norm_num : (0:ℝ)<2) k).le γ),
      ←Real.rpow_mul (zpow_pos (by norm_num : (0:ℝ)<2) k).le,
      ←Real.rpow_mul (zpow_pos (by norm_num : (0:ℝ)<2) k).le]
    simp only [mul_neg_one]
  simp_rw [he]
  refine ⟨dyadic_power_min_summable (Real.rpow_pos_of_pos hx _).le
    (Real.rpow_pos_of_pos hx _).le hgq hγ,?_⟩
  have hh := dyadic_balance (Real.rpow_pos_of_pos hx q) (Real.rpow_pos_of_pos hx (-1)) hgq hγ
  have heq : (x^q)^(γ/(γ*q+γ))*(x^(-1:ℝ))^((γ*q)/(γ*q+γ))=1 := by
    rw [←Real.rpow_mul hx.le,←Real.rpow_mul hx.le,←Real.rpow_add hx]
    rw [show q*(γ/(γ*q+γ))+(-1)*((γ*q)/(γ*q+γ))=0 by ring,Real.rpow_zero]
  simpa only [heq,mul_one,dyadicBalanceConstant] using hh

lemma two_level_crossing_sum {n D α γ : ℝ} (hn : 0<n) (hD : 0<D)
    (hα : 0<α) (hα1 : α<1) (hγ : 0<γ) :
    Summable (fun k : ℤ=>∑' j : ℕ,
      min ((n*((2:ℝ)^k)^γ)*((2:ℝ)^j)^α)
        ((D^2/(n*((2:ℝ)^k)^γ))*((2:ℝ)^j)^(-1:ℝ))) ∧
    (∑' k : ℤ,∑' j : ℕ,
      min ((n*((2:ℝ)^k)^γ)*((2:ℝ)^j)^α)
        ((D^2/(n*((2:ℝ)^k)^γ))*((2:ℝ)^j)^(-1:ℝ))) ≤
    (2+dyadicBalanceConstant α 1)*D*
      dyadicBalanceConstant (γ*((1-α)/(1+α))) γ := by
  let q : ℝ := (1-α)/(1+α)
  have hq : 0<q := div_pos (sub_pos.mpr hα1) (by linarith)
  have hC : 0<(2+dyadicBalanceConstant α 1)*D :=
    mul_pos (by linarith [dyadicBalanceConstant_pos hα (by norm_num : (0:ℝ)<1)]) hD
  let g : ℤ→ℝ := fun k=>∑' j : ℕ,
      min ((n*((2:ℝ)^k)^γ)*((2:ℝ)^j)^α)
        ((D^2/(n*((2:ℝ)^k)^γ))*((2:ℝ)^j)^(-1:ℝ))
  let f : ℤ→ℝ := fun k=>min (((n/D)*((2:ℝ)^k)^γ)^q)
      (((n/D)*((2:ℝ)^k)^γ)^(-1:ℝ))
  have ha := angular_crossing_sum (div_pos hn hD) hγ hq
  have hg0 (k : ℤ) : 0≤g k := by
    apply tsum_nonneg
    intro j
    apply le_min <;> positivity
  have hbound (k : ℤ) : g k≤(2+dyadicBalanceConstant α 1)*D*f k := by
    have hh := truncated_crossing_normalised
      (mul_pos hn (Real.rpow_pos_of_pos (zpow_pos (by norm_num : (0:ℝ)<2) k) γ)) hD hα
    have heq : n*((2:ℝ)^k)^γ/D=(n/D)*((2:ℝ)^k)^γ := by ring
    simpa only [g,f,q,heq] using hh
  have hfs : Summable (fun k=>(2+dyadicBalanceConstant α 1)*D*f k) :=
    ha.1.mul_left ((2+dyadicBalanceConstant α 1)*D)
  have hgs : Summable g := Summable.of_nonneg_of_le hg0 hbound hfs
  refine ⟨hgs,?_⟩
  change (∑' k,g k)≤_
  calc
    _ ≤ ∑' k,(2+dyadicBalanceConstant α 1)*D*f k := hgs.tsum_le_tsum hbound hfs
    _ = (2+dyadicBalanceConstant α 1)*D*(∑' k,f k) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left ha.2 hC.le

end RVM

end

end OAI
