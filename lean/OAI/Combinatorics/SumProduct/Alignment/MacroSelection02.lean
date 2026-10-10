import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MacroSelection01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
end

noncomputable section
namespace SourceMacroSelection
open ProductExposureLabels ProductExposureLaw RawHarmonicProbability
open MeasureTheory Filter Topology
open scoped BigOperators

lemma raw_coarse_bound {m : ℕ} (C H R Xp W : ℕ) (X : Fin m→ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (hH : 0<H) (hR : 0<R) (hRX : (C+1)*R≤Xp) (L M : ℤ)
    (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ t : Fin m→ℕ,(∀ j,t j∈units (X j) W) →
      DyadicHarmonicBoundary.badMass Xp (Xp^2) W (∏ j,t j) H ((C+1)*R) /
        DyadicHarmonicBoundary.mass Xp (Xp^2) W≤ε) :
    (jointLaw X Xp W hW hX hXp).real
      {z | ¬Stable C H R (expose L M (R:ℝ) z)}≤ε := by
  let μ : Measure (Fin m→ℕ) := Measure.pi (fun j=>(law (X j) W hW (hX j):Measure ℕ))
  let ν : Measure ℕ := law Xp W hW hXp
  have htail : ∀ᵐ t ∂μ,∀ j,t j∈units (X j) W := by
    apply ae_all_iff.mpr
    intro j
    exact (Measure.tendsto_eval_ae_ae (i:=j)).eventually (law_ae_units (X j) W hW (hX j))
  have hcond : ∀ᵐ t ∂μ,ν {p | ¬Stable C H R (expose L M (R:ℝ) (t,p))}≤ENNReal.ofReal ε := by
    filter_upwards [htail] with t ht
    have htp : ∀ j,0<t j := by
      intro j
      have hx:=hX j
      have htj:=(Finset.mem_Ico.mp (Finset.mem_filter.mp (ht j)).1).1
      omega
    have hh : ν.real {p | ¬Stable C H R (expose L M (R:ℝ) (t,p))}≤ε := by
      calc
        _ = ν.real ({p | ¬Stable C H R (expose L M (R:ℝ) (t,p))}∩(units Xp W:Set ℕ)) := by
          exact (MicrocellSaturation.law_restrict_units Xp W hW hXp _).symm
        _ ≤ ν.real {p | (∏ j,t j)*(p-(C+1)*R)/H≠(∏ j,t j)*(p+(C+1)*R)/H} := by
          refine measureReal_mono ?_ (by finiteness)
          intro p hp
          exact unstable_subset_boundary C H R hH hR L M (t,p) htp
            (hRX.trans (Finset.mem_Ico.mp (Finset.mem_filter.mp hp.2).1).1) hp.1
        _ = _ := boundary_law Xp W (∏ j,t j) H ((C+1)*R) hW hXp
        _ ≤ ε := hb t ht
    have he := (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
      (show (ν {p | ¬Stable C H R (expose L M (R:ℝ) (t,p))}).toReal≤(ENNReal.ofReal ε).toReal by
        simpa only [measureReal_def,ENNReal.toReal_ofReal hε] using hh)
    exact he
  have he : (μ.prod ν) {z | ¬Stable C H R (expose L M (R:ℝ) z)}≤ENNReal.ofReal ε := by
    rw [Measure.prod_apply MeasurableSet.of_discrete]
    calc
      _ ≤ ∫⁻ _t,ENNReal.ofReal ε ∂μ := lintegral_mono_ae hcond
      _ = _ := by simp [μ]
  change ((μ.prod ν) {z | ¬Stable C H R (expose L M (R:ℝ) z)}).toReal≤ε
  exact ENNReal.toReal_le_of_le_ofReal hε he

end SourceMacroSelection
end

noncomputable section
namespace SourceMacroSelection
open ProductExposureLabels ProductExposureLaw RawHarmonicProbability
open MicrocellScale AdmissibleMicrocellBoundary
open MeasureTheory Filter Topology
open scoped BigOperators
 

theorem source_macro_selection_decay {m : ℕ} (C : ℕ)
    (W M P H Xp : ℕ→ℕ) (X : ℕ→Fin m→ℕ) (L : ℕ→ℤ)
    (hW : ∀ n,0<W n) (hX : ∀ n j,4*W n≤X n j) (hXp : ∀ n,4*W n≤Xp n)
    (hbase : ∀ᶠ n in atTop,0<M n ∧ W n≤M n ∧ 0<H n)
    (hd : Dominates (fun n=>(H n:ℝ)) (earlierScale M P))
    (hx : Dominates (fun n=>Real.log (Xp n:ℝ)) (fun n=>(H n:ℝ)))
    (hprod : ∀ᶠ n in atTop,(∏ j : Fin m,(X n j)^2)≤(P n)^2) :
    Tendsto (fun n=>(jointLaw (X n) (Xp n) (W n) (hW n) (hX n) (hXp n)).real
      {z | ¬Stable C (H n) (radius (M n) (H n))
        (expose (L n) (M n:ℤ) (radius (M n) (H n):ℝ) z)}) atTop (𝓝 0)
 := by
  have hbase' : ∀ᶠ n in atTop,0<W n ∧ 0<M n ∧ W n≤M n ∧ 0<H n ∧ 0<Xp n := by
    filter_upwards [hbase] with n hn
    exact ⟨hW n,hn.1,hn.2.1,hn.2.2,lt_of_lt_of_le (by have:=hW n; omega) (hXp n)⟩
  obtain ⟨ε,hε,hbound⟩:=uniform_raw_boundary (C+1) (by omega) hbase' hd hx
  have hlimit : Tendsto (fun n=>max (ε n) 0) atTop (𝓝 0) := by
    simpa using hε.max (tendsto_const_nhds (x := (0:ℝ)))
  have hM : ∀ᶠ n in atTop,0<M n := hbase.mono (fun _ h=>h.1)
  have hH : ∀ᶠ n in atTop,0<H n := hbase.mono (fun _ h=>h.2.2)
  have hr := (enlarged_rates (C+1) hM hH hd hx).2
  have hRX : ∀ᶠ n in atTop,(C+1)*radius (M n) (H n)≤Xp n := by
    filter_upwards [hr.eventually_lt_const (show (0:ℝ)<1 by norm_num)] with n hn
    have hp : (0:ℝ)<Xp n := by have hw:=hW n;have hx:=hXp n;exact_mod_cast (show 0<Xp n by omega)
    have hh' : (((C+1)*radius (M n) (H n):ℕ):ℝ)<Xp n := by
      simpa only [one_mul] using (div_lt_iff₀ hp).mp hn
    exact_mod_cast hh'.le
  have hR := radius_four_modulus (P:=P) (hbase.mono (fun _ h=>⟨h.1,h.2.1⟩)) hd
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _=>measureReal_nonneg)) ?_ hlimit
  filter_upwards [hbase,hbound,hRX,hR,hprod] with n hbase hb hr hn hprod
  apply raw_coarse_bound C (H n) (radius (M n) (H n)) (Xp n) (W n) (X n)
    (hW n) (hX n) (hXp n) hbase.2.2 (by have:=hW n; omega) hr (L n) (M n:ℤ)
    (max (ε n) 0) (le_max_right _ _)
  intro t ht
  have htp : ∀ j,0<t j := by
    intro j
    have hx:=hX n j
    have hw:=hW n
    have htj:=(Finset.mem_Ico.mp (Finset.mem_filter.mp (ht j)).1).1
    omega
  have htbound : (∏ j,t j)≤(P n)^2 := by
    apply le_trans _ hprod
    apply Finset.prod_le_prod₀
    · intro j _
      exact Nat.zero_le _
    · intro j _
      exact (Finset.mem_Ico.mp (Finset.mem_filter.mp (ht j)).1).2.le
  exact (hb (∏ j,t j) (Finset.prod_pos (fun j _=>htp j)) htbound).trans (le_max_left _ _)

end SourceMacroSelection
end

noncomputable section
namespace SourceMacroSelection
open ProductExposureLabels ProductExposureLaw RawHarmonicProbability
open MicrocellScale AdmissibleMicrocellBoundary
open MeasureTheory Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private lemma tail_mass {m h a : ℕ} (perm : Fin (m+h)≃Fin a)
    (X : Fin a→ℕ) (Xp W : ℕ) (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (E : Set ((Fin m→ℕ)×ℕ)) :
    (jointLaw X Xp W hW hX hXp).real {z | ((fun j=>z.1 (perm (j.castAdd h))),z.2)∈E} =
    (jointLaw (fun j=>X (perm (j.castAdd h))) Xp W hW (fun _=>hX _) hXp).real E := by
  rw [joint_outside_disintegration perm X Xp W hW hX hXp]
  have hh (y : Fin h→ℕ) :
      {z | ((fun j=> (reassemble perm y z).1 (perm (j.castAdd h))),(reassemble perm y z).2)∈E}=E := by
    ext z
    simp [reassemble]
  simp_rw [Set.mem_ofPred_eq,hh]
  rw [←Finset.sum_mul,outside_weights_sum,one_mul]
 

theorem source_joint_macro_decay {T : Type} [Fintype T] {a : ℕ}
    (m h : T→ℕ) (perm : ∀ t,Fin (m t+h t)≃Fin a) (C : T→ℕ)
    (W M P H Xp : ℕ→ℕ) (X : ℕ→Fin a→ℕ) (L : ℕ→ℤ)
    (hW : ∀ N,0<W N) (hX : ∀ N j,4*W N≤X N j) (hXp : ∀ N,4*W N≤Xp N)
    (hbase : ∀ᶠ N in atTop,0<M N ∧ W N≤M N ∧ 0<H N)
    (hd : Dominates (fun N=>(H N:ℝ)) (earlierScale M P))
    (hx : Dominates (fun N=>Real.log (Xp N:ℝ)) (fun N=>(H N:ℝ)))
    (hprod : ∀ t,∀ᶠ N in atTop,(∏ j : Fin (m t),(X N (perm t (j.castAdd (h t))))^2)≤(P N)^2) :
    Tendsto (fun N=>(jointLaw (X N) (Xp N) (W N) (hW N) (hX N) (hXp N)).real
      {z | ∃ t,¬Stable (C t) (H N) (radius (M N) (H N))
        (expose (L N) (M N:ℤ) (radius (M N) (H N):ℝ)
          ((fun j : Fin (m t)=>z.1 (perm t (j.castAdd (h t)))),z.2))}) atTop (𝓝 0)

 := by
  let E : ℕ→T→Set ((Fin a→ℕ)×ℕ):=fun N t=>
    {z | ¬Stable (C t) (H N) (radius (M N) (H N))
      (expose (L N) (M N:ℤ) (radius (M N) (H N):ℝ)
        ((fun j : Fin (m t)=>z.1 (perm t (j.castAdd (h t)))),z.2))}
  have he (t : T) : Tendsto (fun N=>(jointLaw (X N) (Xp N) (W N) (hW N) (hX N) (hXp N)).real (E N t))
      atTop (𝓝 0) := by
    have hm:=source_macro_selection_decay (C t) W M P H Xp
      (fun N j=>X N (perm t (j.castAdd (h t)))) L hW (fun N j=>hX N _) hXp hbase hd hx (hprod t)
    apply hm.congr
    intro N
    exact (tail_mass (perm t) (X N) (Xp N) (W N) (hW N) (hX N) (hXp N) _).symm
  have hsum : Tendsto (fun N=>∑ t,(jointLaw (X N) (Xp N) (W N) (hW N) (hX N) (hXp N)).real (E N t))
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun t _=>he t)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _=>measureReal_nonneg)) ?_ hsum
  apply Filter.Eventually.of_forall
  intro N
  have hset : {z | ∃ t,¬Stable (C t) (H N) (radius (M N) (H N))
      (expose (L N) (M N:ℤ) (radius (M N) (H N):ℝ)
        ((fun j : Fin (m t)=>z.1 (perm t (j.castAdd (h t)))),z.2))}=⋃ t,E N t := by
    ext z
    simp [E]
  rw [hset]
  exact measureReal_iUnion_fintype_le _

end SourceMacroSelection
end

noncomputable section
open Filter Topology
open scoped BigOperators
namespace AdmissibleArrayScales
open MicrocellScale AdmissibleMicrocellBoundary MicrocellEarlierScale
 

theorem source_array_scales {m : ℕ} (M P H Xp : ℕ→ℕ)
    (X : ℕ→Fin m→ℕ) (Q L : ℕ→ℝ)
    (hbase : ∀ᶠ n in atTop,0<M n ∧ 0<P n ∧ 0<H n)
    (hd : Dominates (fun n=>(H n:ℝ)) (earlierScale M P))
    (hx : Dominates (fun n=>Real.log (Xp n:ℝ)) (fun n=>(H n:ℝ)))
    (hX : ∀ᶠ n in atTop,(∀ j,X n j≤P n) ∧ (∏ j : Fin m,(X n j:ℝ)^2)≤(P n:ℝ)^2)
    (hQ : ∀ᶠ n in atTop,0≤Q n ∧ Q n≤(M n:ℝ)*(P n:ℝ)^2)
    (hL : ∀ᶠ n in atTop,0≤L n ∧ L n≤(M n:ℝ)^2) :
    (∀ᶠ n in atTop,0<radius (M n) (H n)) ∧
    Tendsto (fun n=>(radius (M n) (H n):ℝ)/(Xp n:ℝ)) atTop (𝓝 0) ∧
    (∀ a : ℝ,0<a →Tendsto (fun n=>((radius (M n) (H n):ℝ)/(M n:ℝ))/
      (1+∑ j : Fin m,(X n j:ℝ)^2)^a) atTop atTop) ∧
    Tendsto (fun n=>(Q n+(∏ j : Fin m,(X n j:ℝ)^2)*L n)/
      (radius (M n) (H n):ℝ)) atTop (𝓝 0)
 := by
  have hM : ∀ᶠ n in atTop,0<M n := hbase.mono (fun _ h=>h.1)
  have hH : ∀ᶠ n in atTop,0<H n := hbase.mono (fun _ h=>h.2.2)
  let T : ℕ→ℝ := fun n=>(M n:ℝ)+(P n:ℝ)^2
  have hT : ∀ᶠ n in atTop,1≤T n := by
    filter_upwards [hM] with n hn
    have hm : (1:ℝ)≤M n := by exact_mod_cast hn
    dsimp [T]
    nlinarith
  have hr := radius_dominates_square hM hd
  have hR : ∀ᶠ n in atTop,0<radius (M n) (H n) := by
    filter_upwards [hT,(hr 1 zero_lt_one).eventually_ge_atTop 1] with n ht hh
    change 1≤(radius (M n) (H n):ℝ)/(T n)^1 at hh
    rw [Real.rpow_one] at hh
    have hp : 0<T n := by linarith
    have hh' := (le_div_iff₀ hp).mp hh
    have hp' : (0:ℝ)<radius (M n) (H n) := by linarith
    exact_mod_cast hp'
  refine ⟨hR,?_,?_,?_⟩
  · simpa using (enlarged_rates 1 hM hH hd hx).2
  · intro a ha
    have hc : (0:ℝ)<((m:ℝ)+1)^a := Real.rpow_pos_of_pos (by positivity) a
    have hh := (hr (a+1) (by linarith)).atTop_div_const hc
    apply tendsto_atTop_mono' atTop ?_ hh
    filter_upwards [hT,hM,hX] with n ht hm hx
    have ht0 : 0<T n := by linarith
    have hm0 : (0:ℝ)<M n := by exact_mod_cast hm
    have hmT : (M n:ℝ)≤T n := by dsimp [T]; nlinarith
    have hpT : (P n:ℝ)^2≤T n := by dsimp [T]; linarith [Nat.cast_nonneg (α:=ℝ) (M n)]
    have hsum : (∑ j : Fin m,(X n j:ℝ)^2)≤(m:ℝ)*(P n:ℝ)^2 := by
      calc
        _ ≤ ∑ _j : Fin m,(P n:ℝ)^2 := by
          apply Finset.sum_le_sum
          intro j _
          exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hx.1 j) 2
        _ = _ := by simp
    let S : ℝ := 1+∑ j : Fin m,(X n j:ℝ)^2
    have hs0 : 0<S := by dsimp [S]; positivity
    have hsT : S≤((m:ℝ)+1)*T n := by
      dsimp [S]
      have hh := mul_le_mul_of_nonneg_left hpT (Nat.cast_nonneg (α:=ℝ) m)
      nlinarith
    have hpow : S^a≤((m:ℝ)+1)^a*(T n)^a := by
      calc
        _ ≤ (((m:ℝ)+1)*T n)^a := Real.rpow_le_rpow hs0.le hsT ha.le
        _ = _ := Real.mul_rpow (by positivity) ht0.le
    have hden : (M n:ℝ)*S^a≤((m:ℝ)+1)^a*(T n)^(a+1) := by
      calc
        _ ≤ T n*(((m:ℝ)+1)^a*(T n)^a) := mul_le_mul hmT hpow (Real.rpow_nonneg hs0.le _) ht0.le
        _ = _ := by rw [Real.rpow_add ht0,Real.rpow_one]; ring
    change ((radius (M n) (H n):ℝ)/(T n)^(a+1))/((m:ℝ)+1)^a ≤
      ((radius (M n) (H n):ℝ)/(M n:ℝ))/S^a
    rw [div_div,div_div]
    rw [mul_comm ((T n)^(a+1))]
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hm0 (Real.rpow_pos_of_pos hs0 _)) hden
  · have hh : Tendsto (fun n=>(T n)^3/(radius (M n) (H n):ℝ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,inv_div,Real.rpow_natCast] using
        tendsto_inv_atTop_zero.comp (hr (3:ℕ) (by norm_num))
    apply squeeze_zero' ?_ ?_ (by simpa using hh.const_mul 2)
    · filter_upwards [hQ,hL] with n hq hl
      exact div_nonneg (add_nonneg hq.1 (mul_nonneg (Finset.prod_nonneg (fun j _=>sq_nonneg _)) hl.1)) (by positivity)
    · filter_upwards [hT,hX,hQ,hL] with n ht hx hq hl
      have hmn : (0:ℝ)≤M n := by positivity
      have hmT : (M n:ℝ)≤T n := by dsimp [T]; nlinarith
      have hpT : (P n:ℝ)^2≤T n := by dsimp [T]; linarith [Nat.cast_nonneg (α:=ℝ) (M n)]
      have ht0 : 0≤T n := by linarith
      have hb1 : Q n≤(T n)^2 := by
        calc
          _ ≤ (M n:ℝ)*(P n:ℝ)^2 := hq.2
          _ ≤ T n*T n := mul_le_mul hmT hpT (sq_nonneg _) ht0
          _ = _ := by ring
      have hb2 : (∏ j : Fin m,(X n j:ℝ)^2)*L n≤(T n)^3 := by
        calc
          _ ≤ (P n:ℝ)^2*(M n:ℝ)^2 := mul_le_mul hx.2 hl.2 hl.1 (sq_nonneg _)
          _ ≤ T n*(T n)^2 := mul_le_mul hpT (pow_le_pow_left₀ hmn hmT 2) (sq_nonneg _) ht0
          _ = _ := by ring
      have ht23 : (T n)^2≤(T n)^3 := by nlinarith [sq_nonneg (T n),mul_nonneg (sq_nonneg (T n)) (sub_nonneg.mpr ht)]
      calc
        _ ≤ (2*(T n)^3)/(radius (M n) (H n):ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
        _ = _ := by ring

end AdmissibleArrayScales

end
end

end OAI
