import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MicrocellSaturation01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section RawSuccessInlineScope16
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
end
end RawSuccessInlineScope16

 

 

section RawSuccessInlineScope17
noncomputable section
open Filter Topology
namespace MicrocellEarlierScale
open MicrocellScale AdmissibleMicrocellBoundary

 

theorem radius_dominates_square {M P H:ℕ→ℕ}
    (hM:∀ᶠ n in atTop,0<M n)
    (hd:Dominates (fun n=>(H n:ℝ)) (earlierScale M P)) :
    Dominates (fun n=>(radius (M n) (H n):ℝ)) (fun n=>(M n:ℝ)+(P n:ℝ)^2) := by
  have hm:∀ᶠ n in atTop,0<M n ∧ (M n:ℝ)≤earlierScale M P n := by
    filter_upwards [hM] with n hn
    refine ⟨hn,?_⟩
    unfold earlierScale
    linarith [Nat.cast_nonneg (α:=ℝ) (P n)]
  have hr:=radius_dominates hm (Filter.Eventually.of_forall (scale_one M P)) hd
  intro C hC
  have hh: Tendsto (fun n=>((radius (M n) (H n):ℝ)/(earlierScale M P n)^(2*C))/2^C) atTop atTop :=
    (hr (2*C) (by positivity)).atTop_div_const (Real.rpow_pos_of_pos (by norm_num) C)
  apply tendsto_atTop_mono' atTop _ hh
  filter_upwards [hM] with n hn
  let S:=earlierScale M P n
  let T:ℝ:=(M n:ℝ)+(P n:ℝ)^2
  have hS:1≤S:=scale_one M P n
  have hs:0<S:=by linarith
  have hm0:(0:ℝ)<M n:=by exact_mod_cast hn
  have ht:0<T:=by dsimp [T]; positivity
  have hp:(P n:ℝ)≤S:=by dsimp [S,earlierScale]; linarith [Nat.cast_nonneg (α:=ℝ) (M n)]
  have hm':(M n:ℝ)≤S:=by dsimp [S,earlierScale]; linarith [Nat.cast_nonneg (α:=ℝ) (P n)]
  have hT:T≤2*S^2 := by
    have hp2:(P n:ℝ)^2≤S^2:=pow_le_pow_left₀ (by positivity) hp 2
    dsimp [T]
    nlinarith
  have hpow:T^C≤(2:ℝ)^C*S^(2*C) := by
    calc
      _ ≤ (2*S^2)^C := Real.rpow_le_rpow ht.le hT hC.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg S),Real.rpow_mul hs.le 2 C,Real.rpow_two]
  change ((radius (M n) (H n):ℝ)/S^(2*C))/2^C ≤ (radius (M n) (H n):ℝ)/T^C
  calc
    _ = (radius (M n) (H n):ℝ)/(2^C*S^(2*C)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos ht C) hpow

lemma length_cast (M H:ℕ) : (length M H:ℝ)=(radius M H:ℝ)/(M:ℝ) := by
  exact Nat.cast_div_charZero (modulus_dvd M H)

 

theorem length_tendsto {M P H:ℕ→ℕ}
    (hM:∀ᶠ n in atTop,0<M n)
    (hd:Dominates (fun n=>(H n:ℝ)) (earlierScale M P)) :
    Tendsto (fun n=>length (M n) (H n)) atTop atTop := by
  have hm:∀ᶠ n in atTop,0<M n ∧ (M n:ℝ)≤earlierScale M P n := by
    filter_upwards [hM] with n hn
    refine ⟨hn,?_⟩
    unfold earlierScale
    linarith [Nat.cast_nonneg (α:=ℝ) (P n)]
  have hr:=radius_dominates hm (Filter.Eventually.of_forall (scale_one M P)) hd 1 (by norm_num)
  have hr':Tendsto (fun n=>(radius (M n) (H n):ℝ)/earlierScale M P n) atTop atTop := by
    simpa only [Real.rpow_one] using hr
  apply (tendsto_natCast_atTop_iff (R:=ℝ)).mp
  apply tendsto_atTop_mono' atTop _ hr'
  filter_upwards [hm] with n hn
  rw [length_cast]
  apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hn.1) hn.2

end MicrocellEarlierScale
end
end RawSuccessInlineScope17

 

 

section RawSuccessInlineScope18
noncomputable section
open scoped BigOperators
open Finset MeasureTheory Filter Topology
namespace AdmissibleRawSuccess
open MicrocellScale AdmissibleMicrocellBoundary MicrocellSaturation RawHarmonicProbability
attribute [local instance] Classical.propDecidable

 

theorem eventually_global {J : Type*} [Fintype J]
    {M P H X W : ℕ→ℕ} (c : ℝ) (hc : 0<c)
    (hbase : ∀ᶠ n in atTop,0<W n ∧ 0<M n ∧ W n∣M n ∧ 0<H n ∧ 0<X n)
    (hd : Dominates (fun n=>(H n:ℝ)) (earlierScale M P))
    (hx : Dominates (fun n=>Real.log (X n:ℝ)) (fun n=>(H n:ℝ))) :
    ∀ᶠ n in atTop,∃ (hw : 0<W n) (hX : 4*W n≤X n)
      (hN : 0<length (M n) (H n)),∀ (t:J→ℕ) (A:Set ℕ),
      (∀ j,0<t j ∧ t j≤(P n)^2) →
      (∀ i∈(units (X n) (W n)).image (label (radius (M n) (H n)) (M n)),
        good (X n) (radius (M n) (H n)) (H n) t i →
        letI : Nonempty (Fin (length (M n) (H n))) := Fin.pos_iff_nonempty.mp hN
        c/2<(MicrocellProbability.uniformLaw
          (fun b:Fin (length (M n) (H n)) =>
            MicrocellFibers.point (M n) (length (M n) (H n)*i.1) i.2 b):Measure ℕ).real A) →
      c/4 ≤ (law (X n) (W n) hw hX : Measure ℕ).real A := by
  have hbase' : ∀ᶠ n in atTop,0<W n ∧ 0<M n ∧ W n≤M n ∧ 0<H n ∧ 0<X n := by
    filter_upwards [hbase] with n hn
    exact ⟨hn.1,hn.2.1,Nat.le_of_dvd hn.2.1 hn.2.2.1,hn.2.2.2⟩
  have hM := hbase.mono (fun _ hn=>hn.2.1)
  have hH := hbase.mono (fun _ hn=>hn.2.2.2.1)
  obtain ⟨ε,hε,hbd⟩ := uniform_raw_boundary 2 (by decide) hbase' hd hx
  have hfour := radius_four_modulus (P:=P)
    (hbase'.mono (fun _ hn=>⟨hn.2.1,hn.2.2.1⟩)) hd
  have hR := endpoint_rate hM hH (by simpa only [Real.rpow_one] using hx 1 (by norm_num))
  have hL := MicrocellEarlierScale.length_tendsto hM hd
  have herror : Tendsto (fun n=>24*((radius (M n) (H n):ℝ)/X n)+
      (Fintype.card J:ℝ)*ε n) atTop (𝓝 0) := by
    simpa using (hR.const_mul 24).add (hε.const_mul (Fintype.card J:ℝ))
  filter_upwards [hbase,hfour,hbd,hL.eventually_ge_atTop 1,
    hR.eventually_lt_const (show (0:ℝ)<1 by norm_num),
    hR.eventually_le_const (show (0:ℝ)<c/6 by positivity),
    herror.eventually_le_const (show (0:ℝ)<1/4 by norm_num)] with n hn hfour hbd hL hRX hsmall herr
  have hxp : (0:ℝ)<X n := by exact_mod_cast hn.2.2.2.2
  have hRX' : radius (M n) (H n)≤X n := by
    have hh : (radius (M n) (H n):ℝ)<X n := by
      simpa only [one_mul] using (div_lt_iff₀ hxp).mp hRX
    exact_mod_cast hh.le
  have hX : 4*W n≤X n := hfour.trans hRX'
  have hN : 0<length (M n) (H n) := by omega
  have hlen : M n*length (M n) (H n)=radius (M n) (H n) :=
    Nat.mul_div_cancel' (modulus_dvd _ _)
  refine ⟨hn.1,hX,hN,?_⟩
  intro t A ht hs
  have hp := global_success (X n) (W n) (M n) (length (M n) (H n)) (H n)
    hn.1 hX hn.2.1 hN hn.2.2.1 t c (ε n) hc.le A
    (by simpa only [hlen] using hsmall)
    (by simpa only [hlen] using (fun j=>hbd (t j) (ht j).1 (ht j).2))
    (by simpa only [hlen] using hs)
  rw [hlen] at hp
  have hWR : (W n:ℝ)≤radius (M n) (H n) := by
    exact_mod_cast (show W n≤radius (M n) (H n) by omega)
  have hcost : (8*(radius (M n) (H n):ℝ)+16*W n)/X n ≤
      24*((radius (M n) (H n):ℝ)/X n) := by
    rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hxp.le
    linarith
  have hlo : (3/4:ℝ)≤1-(8*(radius (M n) (H n):ℝ)+16*W n)/X n-
        (Fintype.card J:ℝ)*ε n := by linarith
  have hh := mul_le_mul_of_nonneg_left hlo (show 0≤c/3 by positivity)
  linarith

end AdmissibleRawSuccess
end
end RawSuccessInlineScope18

 
end

section
noncomputable section
namespace ProductExposureLaw
open MeasureTheory Filter Topology
open scoped BigOperators
open HarmonicExposure RawHarmonicProbability DyadicHarmonicBoundary
attribute [local instance] Classical.propDecidable

def jointLaw {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) : Measure ((Fin m→ℕ)×ℕ) :=
  (Measure.pi (fun j=>(law (X j) W hW (hX j):Measure ℕ))).prod
    (law Xp W hW hXp:Measure ℕ)

instance jointLaw_probability {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) :
    IsProbabilityMeasure (jointLaw X Xp W hW hX hXp) := by
  unfold jointLaw
  infer_instance

def jointFiber {m : ℕ} (E : Set (Fin m→ℤ)) (X : Fin m→ℕ) (Xp W : ℕ)
    (S : Fin m→ℝ) (r : Fin m→ℤ) (L : ℤ) (Q Δ : ℝ) (a M : ℤ) :
    Finset ((Fin m→ℕ)×ℕ) :=
  ((rawTailFiber X W S r L).product (Finset.Ico Xp (Xp^2))).filter (fun z=>
    (fun j=>(z.1 j:ℤ))∈E ∧ M∣(z.2:ℤ)-a ∧
    Q≤(∏ j,(z.1 j:ℝ))*(z.2:ℝ) ∧ (∏ j,(z.1 j:ℝ))*(z.2:ℝ)<Q+Δ)

lemma law_singleton (X W : ℕ) (hW : 0<W) (hX : 4*W≤X) (p : ℕ) :
    (law X W hW hX:Measure ℕ).real {p} =
      (if p∈RawHarmonicProbability.units X W then (p:ℝ)⁻¹ else 0)/mass X (X^2) W := by
  rw [MicrocellConditional.law_apply_units]
  simp [MicrocellConditional.eventMass]

lemma joint_singleton_mem {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (S : Fin m→ℝ) (r : Fin m→ℤ) (L : ℤ) (t : Fin m→ℕ) (p : ℕ)
    (ht : t∈rawTailFiber X W S r L) (hp : p∈Finset.Ico Xp (Xp^2)) :
    (jointLaw X Xp W hW hX hXp).real {(t,p)} =
      ((∏ j,(t j:ℝ)⁻¹)*(if W.Coprime p then (p:ℝ)⁻¹ else 0)) /
        ((∏ j,mass (X j) ((X j)^2) W)*mass Xp (Xp^2) W) := by
  have hj (j : Fin m) :
      (law (X j) W hW (hX j):Measure ℕ).real {t j}=(t j:ℝ)⁻¹/mass (X j) ((X j)^2) W := by
    rw [law_singleton,ite_eq_left]
    obtain ⟨hi,hc,hs⟩ := Finset.mem_filter.mp (Fintype.mem_piFinset.mp ht j)
    exact Finset.mem_filter.mpr ⟨hi,hc⟩
  have hpp : (law Xp W hW hXp:Measure ℕ).real {p}=
      (if W.Coprime p then (p:ℝ)⁻¹ else 0)/mass Xp (Xp^2) W := by
    rw [law_singleton]
    simp only [RawHarmonicProbability.units,Finset.mem_filter,hp,true_and]
  have hpi : (Measure.pi (fun j=>(law (X j) W hW (hX j):Measure ℕ))).real {t} =
      ∏ j,(law (X j) W hW (hX j):Measure ℕ).real {t j} := by
    simp only [measureReal_def,Measure.pi_singleton,ENNReal.toReal_prod]
  rw [jointLaw,←Set.singleton_prod_singleton,measureReal_prod_prod,hpi,hpp]
  simp_rw [hj]
  rw [Finset.prod_div_distrib]
  ring

lemma joint_fiber_mass {m : ℕ} (E : Set (Fin m→ℤ)) (X : Fin m→ℕ) (Xp W : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (S : Fin m→ℝ) (r : Fin m→ℤ) (L : ℤ) (Q Δ : ℝ) (a M : ℤ) :
    (jointLaw X Xp W hW hX hXp).real (jointFiber E X Xp W S r L Q Δ a M : Set _) =
      literalFiberMass E X Xp W S r L Q Δ a M /
        ((∏ j,mass (X j) ((X j)^2) W)*mass Xp (Xp^2) W) := by
  rw [←sum_measureReal_singleton]
  unfold jointFiber literalFiberMass pivotFiber
  simp only [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product,
    Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hE : (fun j=>(t j:ℤ))∈E
  · simp only [hE,true_and,ite_true]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hb : M∣(p:ℤ)-a ∧ Q≤(∏ j,(t j:ℝ))*(p:ℝ) ∧
        (∏ j,(t j:ℝ))*(p:ℝ)<Q+Δ
    · simp only [hb]
      exact joint_singleton_mem X Xp W hW hX hXp S r L t p ht hp
    · simp [hb]
  · simp [hE]

 

theorem conditional_exact {m : ℕ} (E : Set (Fin m→ℤ)) (X : Fin m→ℕ) (Xp W : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (S : Fin m→ℝ) (r : Fin m→ℤ) (L : ℤ) (Q Δ : ℝ) (a M : ℤ) :
    (jointLaw X Xp W hW hX hXp).real (jointFiber E X Xp W S r L Q Δ a M : Set _) /
      (jointLaw X Xp W hW hX hXp).real (jointFiber Set.univ X Xp W S r L Q Δ a M : Set _) =
    literalFiberMass E X Xp W S r L Q Δ a M /
      literalFiberMass Set.univ X Xp W S r L Q Δ a M
 := by
  rw [joint_fiber_mass,joint_fiber_mass]
  have hN : (∏ j,mass (X j) ((X j)^2) W)*mass Xp (Xp^2) W≠0 := by
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun j _=>(mass_pos (X j) W hW (hX j)).ne')
    · exact (mass_pos Xp W hW hXp).ne'
  exact div_div_div_cancel_right₀ hN _ _

end ProductExposureLaw

end
end

end OAI
