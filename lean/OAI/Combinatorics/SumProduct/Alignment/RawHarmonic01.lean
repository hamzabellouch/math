import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.DyadicHarmonic01
import OAI.Combinatorics.SumProduct.Alignment.MicrocellScale01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section RawSuccessInlineScope9
noncomputable section
open scoped BigOperators
open Finset
namespace DyadicHarmonicBoundary
open UnitIntervalCounts MicrocellBoundary

theorem raw_bad_bound (X W t H R:ℕ) (hW:0<W) (hX:4*W≤X)
    (ht:0<t) (hH:0<H) (hR:R≤X) :
    badMass X (X^2) W t H R / mass X (X^2) W ≤
      168*(t:ℝ)*(R+W+1)/H+112*((R:ℝ)+W+1)/X := by
  have hxN:0<X:=by omega
  have hx:(0:ℝ)<X:=by exact_mod_cast hxN
  suffices hh:badMass X (X^2) W t H R / mass X (X^2) W ≤
      7*(24*(t:ℝ)*(R+W+1)/H+16*((R:ℝ)+W+1)/X) by
    convert hh using 1
    ring
  apply dyadic_transfer X W t H R hW hX _ (by positivity)
  intro k
  have hxy:X≤X*2^k:=by nlinarith [Nat.one_le_pow k 2 (by omega)]
  have hwy:4*W≤X*2^k:=hX.trans hxy
  have hry:R≤X*2^k:=hR.trans hxy
  have hm:0< mass (X*2^k) (X*2^k+X*2^k) W := by
    have hl:=dyadic_lower (X*2^k) W hW hwy
    have hw:(0:ℝ)<W:=by exact_mod_cast hW
    have htot:(0:ℝ)<W.totient:=by exact_mod_cast (Nat.totient_pos.mpr hW)
    exact lt_of_lt_of_le (by positivity) hl
  apply (div_le_iff₀ hm).mp
  rw [badMass_units,mass_units]
  have hh:=harmonic_bad_bound (X*2^k) W t H R hW hwy ht hH hry
  apply hh.trans
  apply add_le_add_right
  apply div_le_div_of_nonneg_left (by positivity) hx
  exact_mod_cast hxy

 

theorem raw_bad_bound_simple (X W t H R:ℕ) (hW:0<W) (hX:4*W≤X)
    (ht:0<t) (hH:0<H) (hWR:W≤R) (hR:R≤X) :
    badMass X (X^2) W t H R / mass X (X^2) W ≤
      504*(t:ℝ)*R/H+336*(R:ℝ)/X := by
  have hw:(W:ℝ)≤R:=by exact_mod_cast hWR
  have hr:(1:ℝ)≤R:=by exact_mod_cast (show 1≤R by omega)
  have hc:(R:ℝ)+W+1≤3*R:=by linarith
  calc
    _ ≤ 168*(t:ℝ)*(R+W+1)/H+112*((R:ℝ)+W+1)/X := raw_bad_bound X W t H R hW hX ht hH hR
    _ ≤ 168*(t:ℝ)*(3*R)/H+112*(3*(R:ℝ))/X := by gcongr
    _ = _ := by ring

open Filter Topology
 

theorem raw_bad_tendsto (X W t H R:ℕ→ℕ)
    (hscale:∀ᶠ n in atTop,0<W n ∧ 4*W n≤X n ∧ 0<t n ∧ 0<H n ∧ W n≤R n ∧ R n≤X n)
    (hHR:Tendsto (fun n=>(t n:ℝ)*R n/H n) atTop (𝓝 0))
    (hXR:Tendsto (fun n=>(R n:ℝ)/X n) atTop (𝓝 0)) :
    Tendsto (fun n=>badMass (X n) ((X n)^2) (W n) (t n) (H n) (R n) /
      mass (X n) ((X n)^2) (W n)) atTop (𝓝 0) := by
  have hh:Tendsto (fun n=>504*((t n:ℝ)*R n/H n)+336*((R n:ℝ)/X n)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using (hHR.const_mul 504).add (hXR.const_mul 336)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n=>div_nonneg
    (badMass_nonneg _ _ _ _ _ _) (mass_nonneg _ _ _))) ?_ hh
  filter_upwards [hscale] with n hn
  convert raw_bad_bound_simple (X n) (W n) (t n) (H n) (R n) hn.1 hn.2.1 hn.2.2.1
    hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2 using 1
  ring

end DyadicHarmonicBoundary
end
end RawSuccessInlineScope9

 

 

section RawSuccessInlineScope10
noncomputable section
open Filter Topology
namespace AdmissibleMicrocellBoundary
open MicrocellScale DyadicHarmonicBoundary

 
def earlierScale (M P:ℕ→ℕ) (n:ℕ) : ℝ := 2 + (M n:ℝ) + P n

lemma scale_one (M P:ℕ→ℕ) (n:ℕ) : 1≤earlierScale M P n := by
  unfold earlierScale
  have hM := Nat.cast_nonneg (α:=ℝ) (M n)
  have hP := Nat.cast_nonneg (α:=ℝ) (P n)
  linarith

lemma radius_four_modulus {M P H W:ℕ→ℕ}
    (hM:∀ᶠ n in atTop,0<M n ∧ W n≤M n)
    (hd:Dominates (fun n=>(H n:ℝ)) (earlierScale M P)) :
    ∀ᶠ n in atTop,4*W n≤radius (M n) (H n) := by
  have hh:=radius_dominates
    (by filter_upwards [hM] with n hn
        exact ⟨hn.1,by unfold earlierScale; linarith [Nat.cast_nonneg (α:=ℝ) (P n)]⟩)
    (Filter.Eventually.of_forall (scale_one M P)) hd 1 (by norm_num)
  filter_upwards [hM,hh.eventually_ge_atTop 4] with n hm hn
  rw [Real.rpow_one] at hn
  have hs:0<earlierScale M P n:=lt_of_lt_of_le (by norm_num) (scale_one M P n)
  have hn':4*earlierScale M P n≤radius (M n) (H n) := (le_div_iff₀ hs).mp hn
  have hw:(W n:ℝ)≤M n:=by exact_mod_cast hm.2
  have hm':(M n:ℝ)≤earlierScale M P n:=by unfold earlierScale; linarith [Nat.cast_nonneg (α:=ℝ) (P n)]
  have hh':4*(W n:ℝ)≤radius (M n) (H n):=by linarith
  exact_mod_cast hh'

 

theorem enlarged_rates {M P H X:ℕ→ℕ} (K:ℕ)
    (hM:∀ᶠ n in atTop,0<M n) (hH:∀ᶠ n in atTop,0<H n)
    (hd:Dominates (fun n=>(H n:ℝ)) (earlierScale M P))
    (hx:Dominates (fun n=>Real.log (X n:ℝ)) (fun n=>(H n:ℝ))) :
    Tendsto (fun n=>(P n:ℝ)^2*(K*radius (M n) (H n):ℕ)/H n) atTop (𝓝 0) ∧
    Tendsto (fun n=>(K*radius (M n) (H n):ℕ)/(X n:ℝ)) atTop (𝓝 0) := by
  have hb:=boundary_rate (t:=fun n=>(P n)^2) hM
    (Filter.Eventually.of_forall (scale_one M P))
    (Filter.Eventually.of_forall (fun n=>by
      simp only [Nat.cast_pow]
      have hp:(P n:ℝ)≤earlierScale M P n:=by unfold earlierScale; linarith [Nat.cast_nonneg (α:=ℝ) (M n)]
      exact pow_le_pow_left₀ (by positivity) hp 2)) hd
  have he:=endpoint_rate hM hH (by simpa only [Real.rpow_one] using hx 1 (by norm_num))
  constructor
  · convert hb.const_mul (K:ℝ) using 1 <;> simp only [Nat.cast_pow,Nat.cast_mul,mul_zero]
    try (funext n; ring)
  · convert he.const_mul (K:ℝ) using 1 <;> simp only [Nat.cast_mul,mul_zero]
    try (funext n; ring)

 

theorem uniform_raw_boundary {M P H X W:ℕ→ℕ} (K:ℕ) (hK:0<K)
    (hbase:∀ᶠ n in atTop,0<W n ∧ 0<M n ∧ W n≤M n ∧ 0<H n ∧ 0<X n)
    (hd:Dominates (fun n=>(H n:ℝ)) (earlierScale M P))
    (hx:Dominates (fun n=>Real.log (X n:ℝ)) (fun n=>(H n:ℝ))) :
    ∃ ε:ℕ→ℝ,Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n in atTop,∀ t:ℕ,0<t → t≤(P n)^2 →
        badMass (X n) ((X n)^2) (W n) t (H n) (K*radius (M n) (H n)) /
          mass (X n) ((X n)^2) (W n) ≤ ε n := by
  let R:ℕ→ℕ:=fun n=>K*radius (M n) (H n)
  have hM:∀ᶠ n in atTop,0<M n:=hbase.mono (fun _ h=>h.2.1)
  have hH:∀ᶠ n in atTop,0<H n:=hbase.mono (fun _ h=>h.2.2.2.1)
  obtain ⟨hb,he⟩:=enlarged_rates K hM hH hd hx
  have hr:∀ᶠ n in atTop,R n≤X n := by
    filter_upwards [hbase,he.eventually_lt_const (show (0:ℝ)<1 by norm_num)] with n hn hne
    have hxp:(0:ℝ)<X n:=by exact_mod_cast hn.2.2.2.2
    have hh':(R n:ℝ)<X n:=by simpa only [one_mul] using (div_lt_iff₀ hxp).mp hne
    exact_mod_cast hh'.le
  have hw:∀ᶠ n in atTop,4*W n≤R n := by
    have hfour:=radius_four_modulus (P:=P) (hbase.mono (fun _ h=>⟨h.2.1,h.2.2.1⟩)) hd
    filter_upwards [hfour] with n hn
    exact hn.trans (Nat.le_mul_of_pos_left _ hK)
  let ε:ℕ→ℝ:=fun n=>504*((P n:ℝ)^2*R n/H n)+336*((R n:ℝ)/X n)
  refine ⟨ε,?_,?_⟩
  · simpa only [ε,mul_zero,zero_add] using (hb.const_mul 504).add (he.const_mul 336)
  · filter_upwards [hbase,hr,hw] with n hn hrn hwn
    intro t ht htp
    have hwr:W n≤R n:=by omega
    have hxt:4*W n≤X n:=hwn.trans hrn
    have hb':=raw_bad_bound_simple (X n) (W n) t (H n) (R n) hn.1 hxt ht hn.2.2.2.1 hwr hrn
    apply hb'.trans
    dsimp only [ε]
    have htp':(t:ℝ)≤(P n:ℝ)^2:=by exact_mod_cast htp
    calc
      _ = 504*((t:ℝ)*R n/H n)+336*((R n:ℝ)/X n) := by ring
      _ ≤ _ := by gcongr

end AdmissibleMicrocellBoundary
end
end RawSuccessInlineScope10

 

 

section RawSuccessInlineScope11
noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators
namespace RawHarmonicProbability
attribute [local instance] Classical.propDecidable
open Finset DyadicHarmonicBoundary AdmissibleMicrocellBoundary MicrocellScale

 
def units (X W:ℕ) : Finset ℕ := (Ico X (X^2)).filter W.Coprime

lemma mass_units (X W:ℕ) : mass X (X^2) W=∑ p∈units X W,(p:ℝ)⁻¹ := by
  simp only [mass,units,sum_filter]

lemma units_pos {X W:ℕ} (hX:0<X) (p:units X W) : (0:ℝ)<(p.1:ℝ) := by
  exact_mod_cast hX.trans_le (mem_Ico.mp (mem_filter.mp p.2).1).1

lemma mass_pos (X W:ℕ) (hW:0<W) (hX:4*W≤X) : 0< mass X (X^2) W := by
  have ht:(0:ℝ)<W.totient:=by exact_mod_cast Nat.totient_pos.mpr hW
  have hw:(0:ℝ)<W:=by exact_mod_cast hW
  have hb:=dyadic_lower X W hW hX
  have hx2:2≤X:=by omega
  exact lt_of_lt_of_le (by positivity) (hb.trans (mass_mono (by nlinarith)))

lemma units_nonempty (X W:ℕ) (hW:0<W) (hX:4*W≤X) : (units X W).Nonempty := by
  have hh:=mass_pos X W hW hX
  rw [mass_units] at hh
  obtain ⟨p,hp,_⟩:=(sum_pos_iff_of_nonneg (fun _ _=>by positivity)).mp hh
  exact ⟨p,hp⟩

 

def law (X W:ℕ) (hW:0<W) (hX:4*W≤X) : ProbabilityMeasure ℕ := by
  letI : Nonempty (units X W) := (units_nonempty X W hW hX).coe_sort
  exact MicrocellProbability.weightedLaw (fun p:units X W=>(p.1:ℝ)⁻¹)
    (fun p=>inv_pos.mpr (units_pos (by omega) p)) Subtype.val

lemma law_apply (X W:ℕ) (hW:0<W) (hX:4*W≤X) (A:Set ℕ) :
    (law X W hW hX:Measure ℕ).real A =
      (∑ p∈Ico X (X^2),if W.Coprime p ∧ p∈A then (p:ℝ)⁻¹ else 0)/
        mass X (X^2) W := by
  classical
  let : Nonempty (units X W) := (units_nonempty X W hW hX).coe_sort
  rw [law,MicrocellProbability.weightedLaw_apply _ _ _ _ MeasurableSet.of_discrete]
  simp only [MicrocellHarmonic.weight]
  have hr:(∑ p:units X W,(p.1:ℝ)⁻¹)=mass X (X^2) W := by
    rw [sum_coe_sort (units X W) (fun p:ℕ=>(p:ℝ)⁻¹),←mass_units]
  rw [hr]
  rw [sum_coe_sort (units X W) (fun p:ℕ=>(p:ℝ)⁻¹ / mass X (X^2) W * (if p∈A then 1 else 0))]
  rw [units,sum_filter]
  rw [sum_div]
  apply sum_congr rfl
  intro p hp
  split_ifs <;> simp_all

lemma boundary_law (X W t H R:ℕ) (hW:0<W) (hX:4*W≤X) :
    (law X W hW hX:Measure ℕ).real {p|t*(p-R)/H≠t*(p+R)/H} =
      badMass X (X^2) W t H R / mass X (X^2) W := by
  rw [law_apply]
  simp only [badMass,Set.mem_ofPred_eq]
  congr 1
  apply sum_congr rfl
  intro p hp
  split_ifs <;> rfl

 

theorem finite_boundary_bound {J:Type*} [Fintype J]
    (X W H R:ℕ) (hW:0<W) (hX:4*W≤X) (t:J→ℕ) (ε:ℝ)
    (hb:∀ j,badMass X (X^2) W (t j) H R / mass X (X^2) W≤ε) :
    (law X W hW hX:Measure ℕ).real (⋃ j,{p|t j*(p-R)/H≠t j*(p+R)/H}) ≤
      Fintype.card J*ε := by
  calc
    _ ≤ ∑ j,(law X W hW hX:Measure ℕ).real {p|t j*(p-R)/H≠t j*(p+R)/H} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j:J,ε := sum_le_sum (fun j _=>by rw [boundary_law]; exact hb j)
    _ = _ := by simp

 

theorem admissible_finite_boundary {J:Type*} [Fintype J]
    {M P H X W:ℕ→ℕ} (K:ℕ) (hK:0<K)
    (hbase:∀ᶠ n in atTop,0<W n ∧ 0<M n ∧ W n≤M n ∧ 0<H n ∧ 0<X n)
    (hd:Dominates (fun n=>(H n:ℝ)) (earlierScale M P))
    (hx:Dominates (fun n=>Real.log (X n:ℝ)) (fun n=>(H n:ℝ))) :
    ∃ ε:ℕ→ℝ,Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n in atTop,∃ (hw:0<W n) (hX:4*W n≤X n),∀ t:J→ℕ,
      (∀ j,0<t j ∧ t j≤(P n)^2) →
      (law (X n) (W n) hw hX:Measure ℕ).real
        (⋃ j,{p|t j*(p-K*radius (M n) (H n))/H n ≠
          t j*(p+K*radius (M n) (H n))/H n}) ≤ ε n := by
  obtain ⟨ε,he,hb⟩:=uniform_raw_boundary K hK hbase hd hx
  have hf:=radius_four_modulus (P:=P) (hbase.mono (fun _ h=>⟨h.2.1,h.2.2.1⟩)) hd
  have hm:∀ᶠ n in atTop,0<M n:=hbase.mono (fun _ h=>h.2.1)
  have hh:∀ᶠ n in atTop,0<H n:=hbase.mono (fun _ h=>h.2.2.2.1)
  have hr:=endpoint_rate hm hh (by simpa only [Real.rpow_one] using hx 1 (by norm_num))
  refine ⟨fun n=>(Fintype.card J:ℝ)*ε n,?_,?_⟩
  · simpa only [mul_zero] using he.const_mul (Fintype.card J:ℝ)
  · filter_upwards [hbase,hb,hf,hr.eventually_lt_const (show (0:ℝ)<1 by norm_num)] with n hn hb hf hr
    have hxp:(0:ℝ)<X n:=by exact_mod_cast hn.2.2.2.2
    have hrx:radius (M n) (H n)≤X n:=by
      have hl:(radius (M n) (H n):ℝ)<X n:=by simpa using (div_lt_iff₀ hxp).mp hr
      exact_mod_cast hl.le
    refine ⟨hn.1,hf.trans hrx,fun t ht=>?_⟩
    exact finite_boundary_bound _ _ _ _ _ _ t _ (fun j=>hb (t j) (ht j).1 (ht j).2)

end RawHarmonicProbability

end
end RawSuccessInlineScope11
end

end OAI
