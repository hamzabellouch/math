import Mathlib
import OAI.Analysis.PathSelection.TaylorCutoffs
import OAI.Analysis.PathSelection.UniformFamilies

namespace OAI

/-! Weighted words and holomorphic finite-clock and Puiseux tuple composition. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Complex
namespace DegeneratingTrees.Clock

lemma weighted_truncation_words (S : Finset ℝ) (b : ℝ → ℂ → ℂ)
    (h : ℕ → ℂ → ℂ) (N : ℕ) (z : ℂ) :
    (∑ n ∈ Finset.range (N+1),h n z*(∑ β ∈ S,Complex.exp ((β:ℂ)*z)*b β z)^n) =
      ∑ w ∈ wordsUpTo S N,h w.length z*wordTerm b w z := by
  classical
  simp_rw [power_truncation_words,Finset.mul_sum]
  calc
    _ = ∑ n ∈ Finset.range (N+1),∑ w ∈ wordsOfLength S n,h w.length z*wordTerm b w z := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro w hw
      rw [(mem_wordsOfLength.mp hw).1]
    _ = _ := by
      symm
      apply Finset.sum_biUnion
      intro n hn m hm hne
      apply Finset.disjoint_left.mpr
      intro w hwn hwm
      exact hne ((mem_wordsOfLength.mp hwn).1.symm.trans (mem_wordsOfLength.mp hwm).1)

variable {E : Set ℝ} {δ : ℝ} (hδ : 0 < δ) (hE : ∀ β ∈ E, β ≤ -δ)
  (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite)

def weightedCoefficient (b : ℝ → ℂ → ℂ) (h : ℕ → ℂ → ℂ) (β : ℝ) (z : ℂ) : ℂ :=
  ∑ w ∈ (wordFiber_finite hδ hE hEl β).toFinset,h w.length z*wordCoefficient b w z

lemma weighted_coefficient_truncation (b : ℝ → ℂ → ℂ) (h : ℕ → ℂ → ℂ)
    (B : ℝ) (z : ℂ) :
    (∑ β ∈ (wordSupport_finite hδ hE hEl B).toFinset,
      Complex.exp ((β:ℂ)*z)*weightedCoefficient hδ hE hEl b h β z) =
      ∑ w ∈ (wordCut_finite hδ hE hEl B).toFinset,h w.length z*wordTerm b w z := by
  classical
  let S := (wordSupport_finite hδ hE hEl B).toFinset
  let T := (wordCut_finite hδ hE hEl B).toFinset
  have hmaps : ∀ w ∈ T,w.sum ∈ S := by
    intro w hw
    have hh := (wordCut_finite hδ hE hEl B).mem_toFinset.mp hw
    exact (wordSupport_finite hδ hE hEl B).mem_toFinset.mpr ⟨⟨w,hh.1,rfl⟩,hh.2⟩
  calc
    _ = ∑ β ∈ S,∑ w ∈ T with w.sum=β,h w.length z*wordTerm b w z := by
      apply Finset.sum_congr rfl
      intro β hβ
      have hB : B ≤ β := ((wordSupport_finite hδ hE hEl B).mem_toFinset.mp hβ).2
      have he : (wordFiber_finite hδ hE hEl β).toFinset = T.filter (fun w => w.sum=β) := by
        ext w
        simp only [Set.Finite.mem_toFinset,Finset.mem_filter,T,wordFiber,wordCut,mem_ofPred_eq]
        constructor
        · intro hw
          exact ⟨⟨hw.1,by simpa only [hw.2] using hB⟩,hw.2⟩
        · intro hw
          exact ⟨hw.1.1,hw.2⟩
      rw [weightedCoefficient,he,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      simp only [wordTerm,(Finset.mem_filter.mp hw).2]
      ring
    _ = _ := Finset.sum_fiberwise_of_maps_to hmaps _

lemma weighted_split (b : ℝ → ℂ → ℂ) (h : ℕ → ℂ → ℂ) {B : ℝ} {N : ℕ}
    (hN : -δ*((N:ℝ)+1) < B) (z : ℂ) :
    (∑ n ∈ Finset.range (N+1),h n z*(∑ β ∈ (hEl B).toFinset,Complex.exp ((β:ℂ)*z)*b β z)^n) =
    (∑ β ∈ (wordSupport_finite hδ hE hEl B).toFinset,
      Complex.exp ((β:ℂ)*z)*weightedCoefficient hδ hE hEl b h β z) +
      ∑ w ∈ (wordsUpTo (hEl B).toFinset N).filter (fun w => w.sum < B),h w.length z*wordTerm b w z := by
  classical
  rw [weighted_truncation_words,weighted_coefficient_truncation,
    ←words_high hδ hE hEl hN]
  symm
  simpa only [not_le] using Finset.sum_filter_add_sum_filter_not
    (wordsUpTo (hEl B).toFinset N) (fun w => B ≤ w.sum)
      (fun w => h w.length z*wordTerm b w z)

lemma weightedCoefficient_slow {b : ℝ → ℂ → ℂ} (hb : ∀ β ∈ E,SectorSlow (b β))
    {h : ℕ → ℂ → ℂ} (hh : ∀ n,SectorSlow (h n)) (β : ℝ) :
    SectorSlow (weightedCoefficient hδ hE hEl b h β) := by
  apply SectorSlow.sum
  intro w hw
  exact (hh _).mul (wordCoefficient_slow hb ((wordFiber_finite hδ hE hEl β).mem_toFinset.mp hw).1)

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma ExpSmall.analytic_comp_difference {g : ℂ → ℂ} {d : ℂ}
    (hg : AnalyticAt ℂ g d) {f h : ℂ → ℂ}
    (hf : Tendsto f sectorInfinity (𝓝 d)) (hh : Tendsto h sectorInfinity (𝓝 d))
    {B : ℝ} (he : ExpSmall B (fun z => f z-h z)) :
    ExpSmall B (fun z => g (f z)-g (h z)) := by
  obtain ⟨a,ha,he⟩ := he
  exact ⟨a,ha,(hg.hasStrictFDerivAt.isBigO_sub.comp_tendsto (hf.prodMk_nhds hh)).trans he⟩

lemma SectorSlow.of_tendsto {f : ℂ → ℂ} {d : ℂ}
    (hf : Tendsto f sectorInfinity (𝓝 d)) : SectorSlow f := by
  intro ε hε
  exact (ExpBound.of_tendsto hf).mono hε.le

 

theorem SectorExpansion.holomorphic_comp_negative {f : ℂ → ℂ} {E : Set ℝ}
    {b : ℝ → ℂ → ℂ} (hf : SectorExpansion f E b) {δ : ℝ} (hδ : 0<δ)
    (hE : ∀ β∈E,β≤-δ) (hb : ∀ β∈E,SectorSlow (b β))
    {a g : ℂ → ℂ} {d : ℂ} (ha : Tendsto a sectorInfinity (𝓝 d))
    (haa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ a z) (hg : AnalyticAt ℂ g d) :
    ∃ c : ℕ → ℂ → ℂ,(∀ n,AnalyticAt ℂ (c n) d) ∧
      SectorExpansion (fun z => g (a z+f z)) (wordSupport E)
        (weightedCoefficient hδ hE hf.finite_above b (fun n z => c n (a z))) := by
  classical
  obtain ⟨c,hc,hTaylor⟩ := TaylorCutoff.analytic_moving_taylor hg
  refine ⟨c,hc,?_⟩
  have hneg := hf.negative_bound hδ hE
  have hft := hneg.tendsto_zero (by linarith : -δ/2<0)
  have hat : Tendsto (fun z => a z+f z) sectorInfinity (𝓝 d) := by
    simpa only [add_zero] using ha.add hft
  have hct : ∀ n,Tendsto (fun z => c n (a z)) sectorInfinity (𝓝 (c n d)) :=
    fun n => (hc n).continuousAt.tendsto.comp ha
  apply SectorExpansion.of_expSmall (wordSupport_bddAbove hδ.le hE)
    (wordSupport_finite hδ hE hf.finite_above)
  · filter_upwards [hf.eventually_analytic,haa,hat.eventually hg.eventually_analyticAt] with z hf ha hg
    exact hg.comp (f := fun z => a z+f z) (ha.add hf)
  · intro B
    let S := (hf.finite_above B).toFinset
    let P : ℂ → ℂ := fun z => ∑ β ∈ S,Complex.exp ((β:ℂ)*z)*b β z
    have hP : ExpBound (-δ/2) P := truncation_negative_bound hδ hE hb B (hf.finite_above B)
    have hPt := hP.tendsto_zero (by linarith : -δ/2<0)
    have haPt : Tendsto (fun z => a z+P z) sectorInfinity (𝓝 d) := by
      simpa only [add_zero] using ha.add hPt
    have hdiff : ExpSmall B (fun z => g (a z+f z)-g (a z+P z)) := by
      apply ExpSmall.analytic_comp_difference hg hat haPt
      simpa only [add_sub_add_left_eq_sub] using hf.expSmall_remainder B
    obtain ⟨N,hN⟩ := exists_nat_gt (-2*B/δ)
    have hN' : -δ/2*((N:ℝ)+1) < B := by
      have hh := (div_lt_iff₀ hδ).mp hN
      nlinarith
    have hN'' : -δ*((N:ℝ)+1) < B := by
      have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
      nlinarith
    have herr : ExpSmall B (fun z => g (a z+P z)-
        ∑ n ∈ Finset.range (N+1),c n (a z)*P z^n) := by
      refine ⟨-δ/2*((N:ℝ)+1),hN',?_⟩
      have h := hTaylor a P (δ/2) ha (by linarith) (by simpa only [neg_div] using hP) (N+1)
      simpa only [neg_div,Nat.cast_add,Nat.cast_one] using h
    let T := (wordsUpTo S N).filter (fun w => w.sum < B)
    have hlow : ExpSmall B (fun z => ∑ w ∈ T,c w.length (a z)*wordTerm b w z) := by
      apply ExpSmall.sum
      intro w hw
      have hm := (mem_wordsUpTo.mp (Finset.mem_filter.mp hw).1).2
      have hwE : w∈exponentWords E := fun β hβ =>
        ((hf.finite_above B).mem_toFinset.mp (hm β hβ)).1
      have h := ((SectorSlow.of_tendsto (hct w.length)).mul
        (wordCoefficient_slow hb hwE)).expSmall (Finset.mem_filter.mp hw).2
      convert h using 1
      funext z
      dsimp only [wordTerm]
      ring
    convert (hdiff.add herr).add hlow using 1
    funext z
    have he := weighted_split hδ hE hf.finite_above b (fun n z => c n (a z)) hN'' z
    change (∑ n ∈ Finset.range (N+1),c n (a z)*P z^n) = _ at he
    rw [he]
    dsimp [T,S]
    ring

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma Puiseux.uniform {f : ℝ → ℂ} (hf : Puiseux f) : UniformPuiseux f := by
  obtain ⟨n,hn,m,F,hF,he⟩ := hf
  refine ⟨n,hn,m,F,hF,?_⟩
  simpa only [←Complex.ofReal_zpow,Complex.real_smul,smul_eq_mul] using he

lemma SectorExpansion.uniform {F : ℂ → ℂ} {A : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hF : SectorExpansion F A b) : UniformSectorExpansion F A b := by
  refine ⟨hF.bounded_above,hF.finite_above,?_⟩
  intro B
  simpa only [smul_eq_mul] using hF.remainders B

lemma ClockGerm.uniform {xs : List (ℝ → ℝ)} {f : ℝ → ℂ}
    (hf : ClockGerm xs f) : UniformClockGerm xs f := by
  induction xs generalizing f with
  | nil => exact Puiseux.uniform hf
  | cons X xs ih =>
    obtain ⟨F,A,b,hF,hb,he⟩ := hf
    exact ⟨F,A,b,hF.uniform,fun β hβ => ⟨ih (hb β hβ).1,(hb β hβ).2⟩,he⟩

lemma Puiseux.analytic_comp_finite {f : ℝ → ℂ} (hf : Puiseux f) {d : ℂ}
    (hlim : Tendsto f atTop (𝓝 d)) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g d) :
    Puiseux (fun t => g (f t)) := by
  by_cases hz : f =ᶠ[atTop] fun _ => 0
  · apply (puiseux_const (g 0)).congr
    filter_upwards [hz] with t ht
    rw [ht]
  obtain ⟨n,hn,m,F,hF,hF0,he⟩ := hf.uniform.normalize hz
  have hm := UniformPuiseux.finite_limit_nonnegative hlim hn hF hF0 he
  let k := m.toNat
  have hkm : (k:ℤ)=m := Int.toNat_of_nonneg hm
  let H : ℂ → ℂ := fun v => v^k*F v
  have hH : AnalyticAt ℂ H 0 := (analyticAt_id.pow k).mul hF
  have heH : f =ᶠ[atTop] fun t => H (rootCoord n t) := by
    simpa only [H,←zpow_natCast,hkm,smul_eq_mul] using he
  have hd : H 0=d := tendsto_nhds_unique (hH.continuousAt.tendsto.comp
    (rootCoord_complex_tendsto_zero hn)) (hlim.congr' heH)
  refine ⟨n,hn,0,fun v => g (H v),?_,?_⟩
  · exact (hd ▸ hg).comp hH
  · filter_upwards [heH] with t ht
    simp only [zpow_zero,one_smul,ht]

 

theorem ClockGerm.analytic_comp_finite {xs : List (ℝ → ℝ)}
    (hvalid : ValidClocks xs) {f : ℝ → ℂ} (hf : ClockGerm xs f) {d : ℂ}
    (hlim : Tendsto f atTop (𝓝 d)) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g d) :
    ClockGerm xs (fun t => g (f t)) := by
  classical
  induction xs generalizing f g d with
  | nil => exact Puiseux.analytic_comp_finite hf hlim hg
  | cons X xs ih =>
    obtain ⟨K,hK⟩ := hvalid.sectorData
    obtain ⟨F,⟨E,b,hF,hb⟩,he⟩ := hK.expansion_iff.mp hf
    have hXt := hvalid.2.2.1
    have hXc := (hvalid.2.1.real_eventually_analytic hvalid.1).mono
      (fun _ h => h.continuousAt)
    have hreal : Tendsto (fun t : ℝ => F (t:ℂ)) atTop (𝓝 d) :=
      tendsto_of_comp_clock hXt hXc (hlim.congr' he)
    let D := nonzeroRaySupport E b
    have htrim : SectorExpansion F D b := hF.trim_zero (fun β hβ => hK.lower.analytic (hb β hβ))
    have hDb : ∀ β∈D,b β∈K := fun β hβ => hb β hβ.1
    have hnonpos : ∀ β∈D,β≤0 := by
      intro β hβ
      by_contra h
      exact hβ.2 (hF.positive_coeff_zero_of_limit hK.lower hb hreal hβ.1 (lt_of_not_ge h))
    have hgo : ∀ (a r : ℂ → ℂ) (A : Set ℝ) (c : ℝ → ℂ → ℂ),
        a∈K → SectorExpansion r A c → (∀ β∈A,c β∈K) →
        (∀ β∈A,β<0) → (∀ z,F z=a z+r z) → ExpansionOver K (fun z => g (F z)) := by
      intro a r A c ham hr hc hneg heq
      obtain ⟨δ,hδ,hgap⟩ := strict_negative_support_gap hr.finite_above hneg
      have hr0 := (hr.negative_bound hδ hgap).tendsto_zero (by linarith : -δ/2<0)
      have har : Tendsto (fun t : ℝ => a (t:ℂ)) atTop (𝓝 d) := by
        have h := hreal.sub (hr0.comp tendsto_real_sectorInfinity)
        simp only [sub_zero] at h
        convert h using 1
        funext t
        simp only [heq,Function.comp_apply,add_sub_cancel_right]
      have halim : Tendsto (fun t => a (X t:ℂ)) atTop (𝓝 d) := har.comp hXt
      have halower := (hK.membership a).mp ham
      have ha : Tendsto a sectorInfinity (𝓝 d) :=
        halower.1.uniform.model_limit hvalid halower.2 EventuallyEq.rfl halim
      obtain ⟨q,hq,hcomp⟩ := hr.holomorphic_comp_negative hδ hgap
        (fun β hβ => hK.lower.slow (hc β hβ)) ha halower.2 hg
      have hqm : ∀ n,(fun z => q n (a z))∈K := by
        intro n
        apply (hK.membership _).mpr
        refine ⟨ih hvalid.1 halower.1 halim (hq n),?_⟩
        filter_upwards [halower.2,ha.eventually (hq n).eventually_analyticAt] with z haz hqz
        exact hqz.comp (f := a) haz
      have hmem : ∀ β,weightedCoefficient hδ hgap hr.finite_above c (fun n z => q n (a z)) β∈K := by
        intro β
        apply hK.lower.finset_sum_mem
        intro w hw
        exact hK.lower.mul_mem (hqm w.length) (hK.lower.word_mem hc
          ((wordFiber_finite hδ hgap hr.finite_above β).mem_toFinset.mp hw).1)
      exact (show ExpansionOver K (fun z => g (a z+r z)) from
        ⟨wordSupport A,_,hcomp,fun β _ => hmem β⟩).congr
        (Eventually.of_forall (fun z => by change g (a z+r z)=g (F z); rw [heq]))
    have hcomp : ExpansionOver K (fun z => g (F z)) := by
      by_cases h0 : (0:ℝ)∈D
      · have hr := htrim.erase h0 (hK.lower.analytic (hDb 0 h0)) (hK.lower.slow (hDb 0 h0))
        simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul] at hr
        apply hgo (b 0) (fun z => F z-b 0 z) (D\{0}) b (hDb 0 h0) hr
          (fun β hβ => hDb β hβ.1)
        · intro β hβ
          exact lt_of_le_of_ne (hnonpos β hβ.1) hβ.2
        · intro z; ring
      · apply hgo (fun _ => 0) F D b (hK.lower.const_mem 0) htrim hDb
        · intro β hβ
          exact lt_of_le_of_ne (hnonpos β hβ) (fun h => h0 (h ▸ hβ))
        · intro z; simp
    exact hK.expansion_iff.mpr ⟨fun z => g (F z),hcomp,he.mono (fun t ht => congrArg g ht)⟩

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

lemma Puiseux.finite_representation {f : ℝ → ℂ} (hf : Puiseux f)
    {d : ℂ} (hlim : Tendsto f atTop (𝓝 d)) :
    ∃ n : ℕ,0<n ∧ ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ F 0=d ∧
      f =ᶠ[atTop] fun t => F (rootCoord n t) := by
  by_cases hz : f =ᶠ[atTop] fun _ => 0
  · have hd : d=0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hz.symm)
    exact ⟨1,by omega,fun _ => 0,analyticAt_const,hd.symm,hz⟩
  obtain ⟨n,hn,m,F,hF,hF0,he⟩ := hf.uniform.normalize hz
  have hm := UniformPuiseux.finite_limit_nonnegative hlim hn hF hF0 he
  let H : ℂ → ℂ := fun v => v^m.toNat*F v
  have hkm : (m.toNat:ℤ)=m := Int.toNat_of_nonneg hm
  have hH : AnalyticAt ℂ H 0 := (analyticAt_id.pow _).mul hF
  have heH : f =ᶠ[atTop] fun t => H (rootCoord n t) := by
    simpa only [H,←zpow_natCast,hkm,smul_eq_mul] using he
  refine ⟨n,hn,H,hH,?_,heH⟩
  exact tendsto_nhds_unique (hH.continuousAt.tendsto.comp
    (rootCoord_complex_tendsto_zero hn)) (hlim.congr' heH)

lemma finite_representation_refine {n k : ℕ} (hn : 0<n) (hk : 0<k)
    {f : ℝ → ℂ} {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 0) (he : f =ᶠ[atTop] fun t => G (rootCoord n t)) :
    AnalyticAt ℂ (fun z => G (z^k)) 0 ∧
      f =ᶠ[atTop] fun t => G ((rootCoord (n*k) t:ℂ)^k) := by
  refine ⟨?_,?_⟩
  · have hG' : AnalyticAt ℂ G ((0:ℂ)^k) := by simpa [zero_pow hk.ne'] using hG
    exact hG'.comp (f := fun z : ℂ => z^k) (analyticAt_id.pow k)
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with t ht hpos
  rw [ht,←rootCoord_pow hn hk hpos,Complex.ofReal_pow]

lemma puiseux_tuple_finite_representation {k : ℕ} (f : Fin k → ℝ → ℂ)
    (d : Fin k → ℂ) (hf : ∀ i,Puiseux (f i))
    (hlim : ∀ i,Tendsto (f i) atTop (𝓝 (d i))) :
    ∃ n : ℕ,0<n ∧ ∃ F : ℂ → (Fin k → ℂ),AnalyticAt ℂ F 0 ∧ F 0=d ∧
      (fun t i => f i t) =ᶠ[atTop] fun t => F (rootCoord n t) := by
  induction k with
  | zero =>
    refine ⟨1,by omega,fun _ => d,analyticAt_const,rfl,Eventually.of_forall ?_⟩
    intro t
    ext i
    exact Fin.elim0 i
  | succ k ih =>
    obtain ⟨n,hn,G,hG,hGd,heG⟩ := (hf 0).finite_representation (hlim 0)
    obtain ⟨r,hr,H,hH,hHd,heH⟩ := ih (fun i => f i.succ) (fun i => d i.succ)
      (fun i => hf i.succ) (fun i => hlim i.succ)
    let J : ℂ → Fin (k+1) → ℂ := fun z => Fin.cons (G (z^r)) (H (z^n))
    have hGr : AnalyticAt ℂ (fun z => G (z^r)) 0 :=
      (finite_representation_refine hn hr hG heG).1
    have hHn : AnalyticAt ℂ (fun z => H (z^n)) 0 := by
      have hH' : AnalyticAt ℂ H ((0:ℂ)^n) := by simpa [zero_pow hn.ne'] using hH
      exact hH'.comp (f := fun z : ℂ => z^n) (analyticAt_id.pow n)
    refine ⟨n*r,Nat.mul_pos hn hr,J,?_,?_,?_⟩
    · apply analyticAt_pi_iff.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hGr
      · exact (analyticAt_pi_iff.mp hHn j)
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [J,Fin.cons_zero,zero_pow hr.ne'] using hGd
      · simpa only [J,Fin.cons_succ,zero_pow hn.ne'] using congrFun hHd j
    · filter_upwards [heG,heH,eventually_gt_atTop (0:ℝ)] with t ht hht hpos
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change f 0 t=G ((rootCoord (n*r) t:ℂ)^r)
        rw [ht,←rootCoord_pow hn hr hpos,Complex.ofReal_pow]
      · change f _ t=H ((rootCoord (n*r) t:ℂ)^n) j
        have h := congrFun hht j
        rw [h,←rootCoord_pow hr hn hpos,Complex.ofReal_pow,Nat.mul_comm r n]

 

theorem Puiseux.analytic_comp_tuple_finite {k : ℕ} {f : Fin k → ℝ → ℂ}
    (hf : ∀ i,Puiseux (f i)) {d : Fin k → ℂ}
    (hlim : ∀ i,Tendsto (f i) atTop (𝓝 (d i)))
    {g : (Fin k → ℂ) → ℂ} (hg : AnalyticAt ℂ g d) :
    Puiseux (fun t => g (fun i => f i t)) := by
  obtain ⟨n,hn,F,hF,hFd,he⟩ := puiseux_tuple_finite_representation f d hf hlim
  refine ⟨n,hn,0,fun z => g (F z),?_,?_⟩
  · exact (hFd ▸ hg).comp hF
  · filter_upwards [he] with t ht
    simp only [zpow_zero,one_smul,ht]

end DegeneratingTrees.Clock
end

end OAI
