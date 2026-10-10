import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.GaugeBounds
import OAI.Probability.SLEGauge.RadiusComparison

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory Set Filter Topology
namespace SLEExactGauge.MomentBatches

 
def moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L : Ω → ℝ)
    (n : ℕ) : ℝ := ∫ ω, (L ω)^n ∂P

lemma mean_pow_le_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (L : Ω → ℝ) (hL : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (h1 : Integrable L P) (n : ℕ) (hn : Integrable (fun ω => (L ω)^n) P) :
    (moment P L 1)^n ≤ moment P L n := by
  simpa only [moment,pow_one] using
    (convexOn_pow (𝕜 := ℝ) n).map_integral_le (by fun_prop) isClosed_Ici hL h1 hn

 
def cutoff (m : ℕ → ℝ) (n : ℕ) : ℝ := 4*m (n+1)/m n

 
def multiplicity (m : ℕ → ℝ) (n : ℕ) (k : ℤ) : ℕ :=
  if (2:ℝ)^k ≤ cutoff m n then ⌊(4:ℝ)^n*((2:ℝ)^k)^n/m n⌋₊ else 0

lemma multiplicity_bounds {m : ℕ → ℝ} {n : ℕ} {k : ℤ}
    (hn : 0 < n) (hm1 : 0 < m 1) (hmn : 0 < m n) (hJ : (m 1)^n ≤ m n)
    (hk : multiplicity m n k ≠ 0) : m 1/4 ≤ (2:ℝ)^k ∧ (2:ℝ)^k ≤ cutoff m n := by
  unfold multiplicity at hk
  split_ifs at hk with hcut
  · have hw : 1 ≤ (4:ℝ)^n*((2:ℝ)^k)^n/m n :=
      Nat.floor_pos.mp (Nat.pos_of_ne_zero hk)
    have hp : (m 1)^n ≤ (4*(2:ℝ)^k)^n := by
      rw [mul_pow]
      exact hJ.trans (by simpa only [one_mul] using (le_div_iff₀ hmn).mp hw)
    have hml := (pow_le_pow_iff_left₀ hm1.le (by positivity) hn.ne').mp hp
    exact ⟨by linarith,hcut⟩
  · exact (hk rfl).elim

lemma finite_multiplicity_support {m : ℕ → ℝ} {n : ℕ}
    (hn : 0 < n) (hm1 : 0 < m 1) (hmn : 0 < m n) (hmnext : 0 < m (n+1))
    (hJ : (m 1)^n ≤ m n) : {k : ℤ | multiplicity m n k ≠ 0}.Finite := by
  obtain ⟨l,hl,hl'⟩ := exists_mem_Ico_zpow (show 0 < m 1/4 by positivity) (by norm_num : (1:ℝ) < 2)
  obtain ⟨u,hu,hu'⟩ := exists_mem_Ico_zpow
    (show 0 < cutoff m n by unfold cutoff; positivity) (by norm_num : (1:ℝ) < 2)
  refine (finite_Icc l u).subset ?_
  intro k hk
  have hb := multiplicity_bounds hn hm1 hmn hJ hk
  refine ⟨(zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp (hl.trans hb.1),?_⟩
  have hlt : k < u+1 := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp
    (hb.2.trans_lt hu')
  omega

 

def support (m : ℕ → ℝ) (n : ℕ) : Finset ℤ := by
  classical
  exact if h : {k : ℤ | multiplicity m n k ≠ 0}.Finite then h.toFinset else ∅

lemma mem_support {m : ℕ → ℝ} {n : ℕ}
    (hfin : {k : ℤ | multiplicity m n k ≠ 0}.Finite) (k : ℤ) :
    k∈support m n ↔ multiplicity m n k ≠ 0 := by
  simp only [support,dite_eq_left hfin,Finite.mem_toFinset,mem_ofPred_eq]

 

def noncleanup (m : ℕ → ℝ) (n : ℕ) : List ℝ :=
  ((support m n).sort (· ≤ ·)).flatMap (fun k => List.replicate (multiplicity m n k) ((2:ℝ)^k))

def batch (m : ℕ → ℝ) (n : ℕ) : List ℝ := noncleanup m n ++ [(n:ℝ)]

lemma batch_length_pos (m : ℕ → ℝ) (n : ℕ) : 0 < (batch m n).length := by
  simp [batch]

lemma batch_entry_lower {m : ℕ → ℝ} {n : ℕ}
    (hn : 0 < n) (hm1 : 0 < m 1) (hmn : 0 < m n) (hJ : (m 1)^n ≤ m n)
    {b : ℝ} (hb : b∈batch m n) : min 1 (m 1/4) ≤ b := by
  simp only [batch,List.mem_append,List.mem_singleton] at hb
  rcases hb with hb | rfl
  · obtain ⟨k,hks,hkb⟩ := List.mem_flatMap.mp hb
    obtain ⟨hk,rfl⟩ := List.mem_replicate.mp hkb
    exact (min_le_right _ _).trans (multiplicity_bounds hn hm1 hmn hJ hk).1
  · exact (min_le_left _ _).trans (by exact_mod_cast hn)

 
lemma batch_cleanup (m : ℕ → ℝ) (n : ℕ) :
    (batch m n)[(noncleanup m n).length]'(by simp [batch])=(n:ℝ) := by
  simp [batch,List.getElem_append_right]

 

def badLevels (v : ℕ → ℝ) (M : ℝ) : Set ℕ := {j | 1 ≤ j ∧ v j ≤ 3*M/4}

lemma finite_badLevels {v : ℕ → ℝ} {M : ℝ} (hM : 0 < M)
    (hv : Tendsto v atTop (𝓝 M)) : (badLevels v M).Finite := by
  have hev : ∀ᶠ j in atTop, 3*M/4 < v j := hv.eventually_const_lt (by linarith)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine (finite_Iio N).subset ?_
  intro j hj
  change j < N
  by_contra! hh
  exact (not_lt_of_ge hj.2) (hN j hh)

 

def level (v : ℕ → ℝ) (M : ℝ) : ℕ := by
  classical
  exact 1 + if h : (badLevels v M).Finite then h.toFinset.card else 0

lemma level_pos (v : ℕ → ℝ) (M : ℝ) : 0 < level v M := by
  unfold level
  omega

lemma level_moment_gt {v : ℕ → ℝ} {M : ℝ} (hM : 0 < M) (hv : Monotone v)
    (hlim : Tendsto v atTop (𝓝 M)) : 3*M/4 < v (level v M) := by
  classical
  have hfin := finite_badLevels hM hlim
  by_contra! hh
  have hsub : Finset.Icc 1 (level v M) ⊆ hfin.toFinset := by
    intro j hj
    rw [Finite.mem_toFinset]
    have hj' := Finset.mem_Icc.mp hj
    exact ⟨hj'.1,(hv hj'.2).trans hh⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  simp only [level,dite_eq_left hfin] at hcard
  omega

 
abbrev EntryIndex (m : ℕ → ℝ) := Σ n : {n : ℕ // 0 < n}, Fin (batch m n.1).length

instance (m : ℕ → ℝ) : Nonempty (EntryIndex m) :=
  ⟨⟨⟨1,by norm_num⟩,⟨0,batch_length_pos m 1⟩⟩⟩

def threshold (m : ℕ → ℝ) (i : EntryIndex m) : ℝ := (batch m i.1.1)[i.2.1]

 

def radius (m : ℕ → ℝ) (a : ℝ) (ell : ℕ → ℕ) (i : EntryIndex m) : ℝ :=
  Real.exp (-((i.1.1:ℝ)^2)-2*a*(i.2.1:ℝ)*((ell i.1.1:ℝ)+(i.1.1:ℝ)))

lemma radius_pos (m : ℕ → ℝ) (a : ℝ) (ell : ℕ → ℕ) (i : EntryIndex m) :
    0 < radius m a ell i := Real.exp_pos _

lemma radius_le (m : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a) (ell : ℕ → ℕ) (i : EntryIndex m) :
    radius m a ell i ≤ Real.exp (-((i.1.1:ℝ)^2)) := by
  unfold radius
  apply Real.exp_le_exp.mpr
  have : 0 ≤ 2*a*(i.2.1:ℝ)*((ell i.1.1:ℝ)+(i.1.1:ℝ)) := by positivity
  linarith

def cleanupIndex (m : ℕ → ℝ) (n : ℕ) (hn : 0 < n) : EntryIndex m :=
  ⟨⟨n,hn⟩,⟨(noncleanup m n).length,by simp [batch]⟩⟩

lemma cleanup_threshold (m : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    threshold m (cleanupIndex m n hn)=(n:ℝ) := batch_cleanup m n

lemma cleanup_cost_small (m : ℕ → ℝ) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (ell : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ i : EntryIndex m, threshold m i * (radius m a ell i)^d < ε := by
  have hlim : Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-d*(n:ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 d hd).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    change Tendsto (fun n : ℕ => (n:ℝ)^(1:ℝ)*Real.exp (-d*(n:ℝ))) atTop (𝓝 0) at h
    simpa only [Real.rpow_one] using h
  obtain ⟨n,hn,hnε⟩ := ((eventually_ge_atTop 1).and (hlim.eventually_lt_const hε)).exists
  have hnp : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hρ : (radius m a ell (cleanupIndex m n hnp))^d ≤ Real.exp (-d*(n:ℝ)) := by
    calc
      (radius m a ell (cleanupIndex m n hnp))^d ≤ (Real.exp (-((n:ℝ)^2)))^d :=
        Real.rpow_le_rpow (radius_pos m a ell _).le (radius_le m ha ell _) hd.le
      _ = Real.exp (-((n:ℝ)^2)*d) := (Real.exp_mul _ _).symm
      _ ≤ Real.exp (-d*(n:ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hd.le (show (n:ℝ) ≤ (n:ℝ)^2 by nlinarith |> sub_nonneg.mpr)]
  refine ⟨cleanupIndex m n hnp,?_⟩
  rw [cleanup_threshold]
  exact (mul_le_mul_of_nonneg_left hρ (Nat.cast_nonneg n)).trans_lt hnε

 
def momentGauge (m : ℕ → ℝ) (a d : ℝ) (ell : ℕ → ℕ) : ℝ → ℝ :=
  QuadraticGauge.gauge d (threshold m) (radius m a ell)

 

theorem momentGauge_admissible (m : ℕ → ℝ) (hm : ∀ n, 0 < n → 0 < m n)
    (hJ : ∀ n, 0 < n → (m 1)^n ≤ m n) {a d : ℝ}
    (ha : 0 ≤ a) (hd : 0 < d) (hd2 : d ≤ 2) (ell : ℕ → ℕ) :
    Target.IsHausdorffGauge (momentGauge m a d ell) := by
  have hm1 := hm 1 Nat.zero_lt_one
  have hc : 0 < min 1 (m 1/4) := lt_min zero_lt_one (by positivity)
  have hb (i : EntryIndex m) : min 1 (m 1/4) ≤ threshold m i :=
    batch_entry_lower i.1.2 (hm 1 Nat.zero_lt_one) (hm _ i.1.2) (hJ _ i.1.2)
      (List.getElem_mem i.2.2)
  exact QuadraticGauge.isHausdorffGauge (fun i => hc.le.trans (hb i))
    (radius_pos m a ell) hd.le hd2 hc hb (cleanup_cost_small m ha hd ell)

lemma momentGauge_doubling (m : ℕ → ℝ) (hm : ∀ n, 0 < n → 0 < m n)
    (hJ : ∀ n, 0 < n → (m 1)^n ≤ m n) (a d : ℝ) (ell : ℕ → ℕ)
    {C r : ℝ} (hC : 1 ≤ C) : momentGauge m a d ell (C*r) ≤ C^2*momentGauge m a d ell r := by
  have hm1 := hm 1 Nat.zero_lt_one
  have hc : 0 ≤ min 1 (m 1/4) := le_min zero_le_one (by positivity)
  have hb (i : EntryIndex m) : 0 ≤ threshold m i := hc.trans
    (batch_entry_lower i.1.2 (hm 1 Nat.zero_lt_one) (hm _ i.1.2) (hJ _ i.1.2)
      (List.getElem_mem i.2.2))
  exact QuadraticGauge.gauge_scale hb (radius_pos m a ell) hC

end SLEExactGauge.MomentBatches
end
end
 

 
section
 

noncomputable section
open Set Filter Topology
namespace SLEExactGauge.MomentBatches

lemma dyadic_predecessor (n : ℕ) (k : ℤ) :
    ((2:ℝ)^(k-1))^n = (1/2:ℝ)^n * ((2:ℝ)^k)^n := by
  rw [zpow_sub₀ (by norm_num : (2:ℝ)≠0),zpow_one,div_pow,div_pow,one_pow]
  ring

lemma dyadic_sum_le (n : ℕ) (hn : 0 < n) (S : Finset ℤ) (K : ℤ)
    (hK : ∀ k∈S, k ≤ K) :
    (∑ k∈S, ((2:ℝ)^k)^n) ≤ ((2:ℝ)^K)^n/(1-(1/2:ℝ)^n) := by
  have hq : (1/2:ℝ)^n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'
  have hden : 0 < 1-(1/2:ℝ)^n := sub_pos.mpr hq
  induction S using Finset.induction_on_max generalizing K with
  | empty => simp only [Finset.sum_empty]; positivity
  | insert a S hmax ih =>
    have haS : a∉S := by intro ha; exact lt_irrefl a (hmax a ha)
    rw [Finset.sum_insert haS]
    have hs := ih (a-1) (fun k hk => by have := hmax k hk; omega)
    have hstep : ((2:ℝ)^a)^n + ((2:ℝ)^(a-1))^n/(1-(1/2:ℝ)^n) =
        ((2:ℝ)^a)^n/(1-(1/2:ℝ)^n) := by
      rw [dyadic_predecessor]
      field_simp
      ring
    calc
      ((2:ℝ)^a)^n + ∑ k∈S, ((2:ℝ)^k)^n ≤
        ((2:ℝ)^a)^n + ((2:ℝ)^(a-1))^n/(1-(1/2:ℝ)^n) := add_le_add le_rfl hs
      _ = ((2:ℝ)^a)^n/(1-(1/2:ℝ)^n) := hstep
      _ ≤ ((2:ℝ)^K)^n/(1-(1/2:ℝ)^n) := by
        apply div_le_div_of_nonneg_right _ hden.le
        apply pow_le_pow_left₀ (by positivity)
        exact zpow_le_zpow_right₀ (by norm_num) (hK a (Finset.mem_insert_self _ _))

 

lemma dyadic_sum_below (n : ℕ) (hn : 0 < n) (S : Finset ℤ) (x : ℝ) (hx : 0 ≤ x) :
    (∑ k∈S with (2:ℝ)^k ≤ x, ((2:ℝ)^k)^n) ≤ x^n/(1-(1/2:ℝ)^n) := by
  classical
  rcases hx.eq_or_lt with rfl | hxp
  · simp only [show ∀ k : ℤ, ¬(2:ℝ)^k≤0 from fun k => not_le_of_gt (by positivity),
      Finset.filter_false,Finset.sum_empty,zero_pow hn.ne',zero_div,le_refl]
  · obtain ⟨K,hKlo,hKhi⟩ := exists_mem_Ico_zpow hxp (by norm_num : (1:ℝ)<2)
    have hb : ∀ k∈S.filter (fun k => (2:ℝ)^k ≤ x), k ≤ K := by
      intro k hk
      have hkle := (Finset.mem_filter.mp hk).2
      have hlt : k < K+1 := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp
        (hkle.trans_lt hKhi)
      omega
    calc
      (∑ k∈S with (2:ℝ)^k ≤ x, ((2:ℝ)^k)^n) ≤ ((2:ℝ)^K)^n/(1-(1/2:ℝ)^n) :=
        dyadic_sum_le n hn _ K hb
      _ ≤ x^n/(1-(1/2:ℝ)^n) := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hKlo n)
        (by have := pow_lt_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1) hn.ne'; linarith)

lemma multiplicity_le_weight {m : ℕ → ℝ} {n : ℕ} (hm : 0 < m n) (k : ℤ) :
    (multiplicity m n k:ℝ) ≤ (4:ℝ)^n*((2:ℝ)^k)^n/m n := by
  unfold multiplicity
  split_ifs
  · exact Nat.floor_le (by positivity)
  · simp only [Nat.cast_zero]
    positivity

 
def counts (m : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k∈support m n, if (2:ℝ)^k ≤ x then (multiplicity m n k:ℝ) else 0

lemma counts_nonneg (m : ℕ → ℝ) (n : ℕ) (x : ℝ) : 0 ≤ counts m n x := by
  unfold counts
  exact Finset.sum_nonneg (fun k hk => by split_ifs <;> positivity)

lemma counts_eq_sum_filter (m : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    counts m n x = ∑ k∈support m n with (2:ℝ)^k ≤ x, (multiplicity m n k:ℝ) := by
  classical
  exact (Finset.sum_filter (s := support m n) (fun k => (2:ℝ)^k≤x) (fun k => (multiplicity m n k:ℝ))).symm

lemma counts_upper {m : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (hmn : 0 < m n)
    {x : ℝ} (hx : 0 ≤ x) :
    counts m n x ≤ ((4:ℝ)^n/m n) * (x^n/(1-(1/2:ℝ)^n)) := by
  classical
  rw [counts_eq_sum_filter]
  calc
    (∑ k∈support m n with (2:ℝ)^k ≤ x, (multiplicity m n k:ℝ)) ≤
        ∑ k∈support m n with (2:ℝ)^k ≤ x, ((4:ℝ)^n/m n)*((2:ℝ)^k)^n := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [div_mul_eq_mul_div] using multiplicity_le_weight hmn k
    _ = ((4:ℝ)^n/m n) * (∑ k∈support m n with (2:ℝ)^k ≤ x, ((2:ℝ)^k)^n) := by
      rw [Finset.mul_sum]
    _ ≤ ((4:ℝ)^n/m n) * (x^n/(1-(1/2:ℝ)^n)) :=
      mul_le_mul_of_nonneg_left (dyadic_sum_below n hn _ x hx) (by positivity)

lemma multiplicity_le_counts {m : ℕ → ℝ} {n : ℕ}
    (hfin : {k : ℤ | multiplicity m n k≠0}.Finite) (k : ℤ) {x : ℝ} (hkx : (2:ℝ)^k ≤ x) :
    (multiplicity m n k:ℝ) ≤ counts m n x := by
  classical
  by_cases hk : multiplicity m n k=0
  · simpa only [hk,Nat.cast_zero] using counts_nonneg m n x
  · calc
      (multiplicity m n k:ℝ) = (if (2:ℝ)^k ≤ x then (multiplicity m n k:ℝ) else 0) := by rw [ite_eq_left hkx]
      _ ≤ ∑ j∈support m n, if (2:ℝ)^j ≤ x then (multiplicity m n j:ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if (2:ℝ)^j≤x then (multiplicity m n j:ℝ) else 0)
          (fun j hj => by split_ifs <;> positivity) ((mem_support hfin k).mpr hk)

 

lemma counts_lower {m : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (hmn : 0 < m n)
    (hfin : {k : ℤ | multiplicity m n k≠0}.Finite)
    {x : ℝ} (hx : 0 ≤ x) (hcut : x ≤ cutoff m n) :
    (2:ℝ)^n*x^n/m n-1 ≤ counts m n x := by
  rcases hx.eq_or_lt with rfl | hxp
  · simp only [zero_pow hn.ne',mul_zero,zero_div,zero_sub]
    exact (by norm_num : (-1:ℝ)≤0).trans (counts_nonneg m n 0)
  · obtain ⟨k,hkx,hxk⟩ := exists_mem_Ico_zpow hxp (by norm_num : (1:ℝ)<2)
    have hx2 : x ≤ 2*(2:ℝ)^k := by
      rw [zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one] at hxk
      linarith
    have hpow : (2:ℝ)^n*x^n ≤ (4:ℝ)^n*((2:ℝ)^k)^n := by
      rw [← mul_pow,← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    have hw : (2:ℝ)^n*x^n/m n-1 ≤ (multiplicity m n k:ℝ) := by
      rw [multiplicity,ite_eq_left (hkx.trans hcut)]
      have hf := Nat.lt_floor_add_one ((4:ℝ)^n*((2:ℝ)^k)^n/m n)
      have hdiv := div_le_div_of_nonneg_right hpow hmn.le
      linarith
    exact hw.trans (multiplicity_le_counts hfin k hkx)

 

lemma finite_entries_before (m : ℕ → ℝ) (N : ℕ) :
    {i : EntryIndex m | i.1.1 < N}.Finite := by
  have hf (n : ℕ) : {i : EntryIndex m | i.1.1=n}.Finite := by
    by_cases hn : 0 < n
    · have him : {i : EntryIndex m | i.1.1=n} ⊆
        range (fun k : Fin (batch m n).length => (⟨⟨n,hn⟩,k⟩ : EntryIndex m)) := by
        rintro ⟨⟨j,hj⟩,k⟩ h
        change j=n at h
        subst j
        exact ⟨k,rfl⟩
      exact (finite_range _).subset him
    · have he : {i : EntryIndex m | i.1.1=n} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hn (hi ▸ i.1.2)
      rw [he]
      exact finite_empty
  have hunion : (⋃ n : Fin N, {i : EntryIndex m | i.1.1=n.1}).Finite := finite_iUnion (fun n => hf n.1)
  apply hunion.subset
  intro i hi
  exact mem_iUnion.mpr ⟨⟨i.1.1,hi⟩,rfl⟩

theorem momentGauge_finite_exclusions (m : ℕ → ℝ)
    (hm : ∀ n, 0 < n → 0 < m n) (hJ : ∀ n, 0 < n → (m 1)^n ≤ m n)
    (a d : ℝ) (ell : ℕ → ℕ) (n₀ : ℕ) (F : ℝ → ℝ) (M C : ℝ)
    (hF : ∀ r, 0 < r → 0 ≤ F r ∧ F r ≤ M)
    (hbound : ∀ i : EntryIndex m, n₀ ≤ i.1.1 → ∀ r, 0 < r →
      F r ≤ C*QuadraticGauge.entry d (threshold m i) (radius m a ell i) r) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ r, 0 < r → F r ≤ C'*momentGauge m a d ell r := by
  have hm1 := hm 1 Nat.zero_lt_one
  have hc : 0 < min 1 (m 1/4) := lt_min zero_lt_one (by positivity)
  have hb (i : EntryIndex m) : 0 < threshold m i := hc.trans_le
    (batch_entry_lower i.1.2 hm1 (hm _ i.1.2) (hJ _ i.1.2) (List.getElem_mem i.2.2))
  apply QuadraticGauge.finite_exclusions d (threshold m) (radius m a ell) hb
    (radius_pos m a ell) (finite_entries_before m n₀).toFinset F M C hF
  intro i hi
  apply hbound i
  exact le_of_not_gt (by simpa only [Finite.mem_toFinset,mem_ofPred_eq] using hi)

end SLEExactGauge.MomentBatches
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Topology
namespace SLEExactGauge.MomentBatches

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma integrable_counts (m : ℕ → ℝ) (n : ℕ) {X : Ω → ℝ} (hX : Measurable X) :
    Integrable (fun ω => counts m n (X ω)) P := by
  apply integrable_finsetSum
  intro k hk
  exact (integrable_const (multiplicity m n k:ℝ)).indicator (measurableSet_le measurable_const hX)

lemma integral_counts (m : ℕ → ℝ) (n : ℕ) {X : Ω → ℝ} (hX : Measurable X) :
    (∫ ω, counts m n (X ω) ∂P) =
      ∑ k∈support m n, (multiplicity m n k:ℝ)*P.real {ω | (2:ℝ)^k ≤ X ω} := by
  rw [show (fun ω => counts m n (X ω)) =
    (fun ω => ∑ k∈support m n, {ω | (2:ℝ)^k ≤ X ω}.indicator
      (fun _ => (multiplicity m n k:ℝ)) ω) from rfl]
  rw [integral_finsetSum _ (fun k hk => (integrable_const (multiplicity m n k:ℝ)).indicator
    (measurableSet_le measurable_const hX))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_indicator_const _ (measurableSet_le measurable_const hX),smul_eq_mul,mul_comm]

 

theorem upper_tail_finite (L : Ω → ℝ) (hL : Measurable L) (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (n : ℕ) (hn : 0 < n) (hLn : Integrable (fun ω => (L ω)^n) P)
    (hmn : 0 < moment P L n) :
    (∑ k∈support (moment P L) n, (multiplicity (moment P L) n k:ℝ)*
      P.real {ω | 16*(2:ℝ)^k ≤ L ω}) ≤ (4:ℝ)^n/(16:ℝ)^n/(1-(1/2:ℝ)^n) := by
  let m := moment P L
  let C := ((4:ℝ)^n/m n)/(16:ℝ)^n/(1-(1/2:ℝ)^n)
  have hmaj : (fun ω => counts m n (L ω/16)) ≤ᵐ[P] (fun ω => C*(L ω)^n) := by
    filter_upwards [hL0] with ω hω
    calc
      counts m n (L ω/16) ≤ ((4:ℝ)^n/m n)*((L ω/16)^n/(1-(1/2:ℝ)^n)) :=
        counts_upper hn hmn (by positivity)
      _ = C*(L ω)^n := by dsimp only [C]; rw [div_pow]; ring
  have hI := integral_mono_ae (integrable_counts P m n (hL.div_const 16)) (hLn.const_mul C) hmaj
  rw [integral_counts P m n (hL.div_const 16),integral_const_mul] at hI
  have hsets (k : ℤ) : {ω | (2:ℝ)^k ≤ L ω/16} = {ω | 16*(2:ℝ)^k ≤ L ω} := by
    ext ω
    simp only [mem_ofPred_eq,le_div_iff₀ (by norm_num : (0:ℝ)<16),mul_comm]
  simp_rw [hsets] at hI
  have he : C*(∫ ω,(L ω)^n∂P) = (4:ℝ)^n/(16:ℝ)^n/(1-(1/2:ℝ)^n) := by
    change (((4:ℝ)^n/m n)/(16:ℝ)^n/(1-(1/2:ℝ)^n))*m n = _
    field_simp [show m n ≠ 0 from hmn.ne']
  exact he ▸ hI

lemma sum_eq_tsum_multiplicity {m : ℕ → ℝ} {n : ℕ}
    (hfin : {k : ℤ | multiplicity m n k≠0}.Finite) (p : ℤ → ℝ) :
    (∑ k∈support m n, (multiplicity m n k:ℝ)*p k) =
      ∑' k : ℤ, (multiplicity m n k:ℝ)*p k := by
  symm
  apply tsum_eq_sum
  intro k hk
  have hn : multiplicity m n k=0 := not_not.mp (by rwa [mem_support hfin] at hk)
  simp only [hn,Nat.cast_zero,zero_mul]

 

lemma moment_sequence_properties (L : Ω → ℝ) (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (hint : ∀ n, Integrable (fun ω => (L ω)^n) P) (hmean : 0 < moment P L 1) :
    (∀ n, 0 < n → 0 < moment P L n) ∧
    (∀ n, 0 < n → (moment P L 1)^n ≤ moment P L n) := by
  have hJ (n : ℕ) : (moment P L 1)^n ≤ moment P L n :=
    mean_pow_le_moment P L hL0 (by simpa only [pow_one] using hint 1) n (hint n)
  exact ⟨fun n hn => (pow_pos hmean n).trans_le (hJ n),fun n hn => hJ n⟩

theorem upper_tail (L : Ω → ℝ) (hL : Measurable L) (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (hint : ∀ n, Integrable (fun ω => (L ω)^n) P) (hmean : 0 < moment P L 1)
    (n : ℕ) (hn : 0 < n) :
    (∑' k : ℤ, (multiplicity (moment P L) n k:ℝ)*P.real {ω | 16*(2:ℝ)^k ≤ L ω}) ≤
      (4:ℝ)^n/(16:ℝ)^n/(1-(1/2:ℝ)^n) := by
  obtain ⟨hm,hJ⟩ := moment_sequence_properties P L hL0 hint hmean
  rw [← sum_eq_tsum_multiplicity
    (finite_multiplicity_support hn hmean (hm n hn) (hm (n+1) (by omega)) (hJ n hn))]
  exact upper_tail_finite P L hL hL0 n hn (hint n) (hm n hn)

 

omit [IsProbabilityMeasure P] in
lemma truncated_moment_lower [IsProbabilityMeasure P] (L Y : Ω → ℝ) (hY : Measurable Y)
    (hYL : ∀ᵐ ω ∂P, 0 ≤ Y ω ∧ Y ω ≤ L ω) (n : ℕ)
    (hLn : Integrable (fun ω => (L ω)^(n+1)) P)
    (hYn : Integrable (fun ω => (Y ω)^n) P)
    (hmn : 0 < moment P L n) (hmnext : 0 < moment P L (n+1))
    (happrox : 3*moment P L n/4 ≤ moment P Y n) :
    moment P L n/2 ≤
      ∫ ω, {ω | Y ω ≤ cutoff (moment P L) n}.indicator (fun ω => (Y ω)^n) ω ∂P := by
  let T := cutoff (moment P L) n
  let G := {ω | Y ω ≤ T}
  have hT : 0 < T := by dsimp [T,cutoff]; positivity
  have hG : MeasurableSet G := measurableSet_le hY measurable_const
  have hpoint : (fun ω => (Y ω)^n) ≤ᵐ[P]
      (fun ω => G.indicator (fun ω => (Y ω)^n) ω + (L ω)^(n+1)/T) := by
    filter_upwards [hYL] with ω hω
    have hL0 : 0 ≤ L ω := hω.1.trans hω.2
    by_cases hg : ω∈G
    · rw [indicator_of_mem hg]
      exact le_add_of_nonneg_right (by positivity)
    · rw [indicator_of_notMem hg,zero_add]
      apply (le_div_iff₀ hT).mpr
      calc
        (Y ω)^n*T ≤ (Y ω)^n*Y ω :=
          mul_le_mul_of_nonneg_left (le_of_not_ge hg) (pow_nonneg hω.1 _)
        _ = (Y ω)^(n+1) := (pow_succ _ _).symm
        _ ≤ (L ω)^(n+1) := pow_le_pow_left₀ hω.1 hω.2 _
  have hI := integral_mono_ae hYn ((hYn.indicator hG).add (hLn.div_const T)) hpoint
  simp only [Pi.add_apply] at hI
  rw [integral_add (hYn.indicator hG) (hLn.div_const T),integral_div] at hI
  have he : (∫ ω,(L ω)^(n+1)∂P)/T = moment P L n/4 := by
    change moment P L (n+1)/(4*moment P L (n+1)/moment P L n) = _
    field_simp [hmn.ne', hmnext.ne']
  rw [he] at hI
  change moment P Y n ≤ _ at hI
  change moment P L n/2 ≤ ∫ ω,G.indicator (fun ω => (Y ω)^n) ω∂P
  linarith

 

theorem success_strong (L Y : Ω → ℝ) (hY : Measurable Y)
    (hYL : ∀ᵐ ω ∂P, 0 ≤ Y ω ∧ Y ω ≤ L ω) (n : ℕ) (hn : 0 < n)
    (hLn : Integrable (fun ω => (L ω)^(n+1)) P)
    (hYn : Integrable (fun ω => (Y ω)^n) P)
    (hmn : 0 < moment P L n) (hmnext : 0 < moment P L (n+1))
    (hfin : {k : ℤ | multiplicity (moment P L) n k≠0}.Finite)
    (happrox : 3*moment P L n/4 ≤ moment P Y n) :
    (2:ℝ)^n/2-1 ≤ ∑ k∈support (moment P L) n, (multiplicity (moment P L) n k:ℝ)*
      P.real {ω | (2:ℝ)^k ≤ Y ω} := by
  let m := moment P L
  let G := {ω | Y ω ≤ cutoff m n}
  let f := G.indicator (fun ω => (Y ω)^n)
  let D := (2:ℝ)^n/m n
  have hG : MeasurableSet G := measurableSet_le hY measurable_const
  have hD : 0 ≤ D := by dsimp [D,m]; positivity
  have hpoint : (fun ω => D*f ω-1) ≤ᵐ[P] (fun ω => counts m n (Y ω)) := by
    filter_upwards [hYL] with ω hω
    by_cases hg : ω∈G
    · have he : f ω = (Y ω)^n := indicator_of_mem hg _
      rw [he]
      simpa only [D,div_mul_eq_mul_div] using counts_lower hn hmn hfin hω.1 hg
    · have he : f ω=0 := indicator_of_notMem hg _
      rw [he,mul_zero,zero_sub]
      exact (by norm_num : (-1:ℝ)≤0).trans (counts_nonneg m n (Y ω))
  have hI := integral_mono_ae (((hYn.indicator hG).const_mul D).sub (integrable_const 1))
    (integrable_counts P m n hY) hpoint
  simp only [Pi.sub_apply] at hI
  rw [integral_sub ((hYn.indicator hG).const_mul D) (integrable_const 1),
    integral_const_mul,integral_const,probReal_univ,one_smul,integral_counts P m n hY] at hI
  have htr := truncated_moment_lower P L Y hY hYL n hLn hYn hmn hmnext happrox
  have hmul := mul_le_mul_of_nonneg_left htr hD
  have he : D*(m n/2) = (2:ℝ)^n/2 := by dsimp [D]; field_simp [show m n ≠ 0 from hmn.ne']
  rw [he] at hmul
  exact (sub_le_sub_right hmul 1).trans hI

lemma success_numerics (n : ℕ) (hn : 3 ≤ n) :
    (2:ℝ)^(n-2)-1/(2*(1-(1/2:ℝ)^n)) ≤ (2:ℝ)^n/2-1 ∧
    (2:ℝ)^n/8 ≤ (2:ℝ)^(n-2)-1/(2*(1-(1/2:ℝ)^n)) := by
  have hlow : (8:ℝ) ≤ 2^n := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn
    norm_num at hp ⊢
    exact hp
  have hq : (1/2:ℝ)^n ≤ 1/2 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
      (show 1 ≤ n by omega)
  have hden : 1 ≤ 2*(1-(1/2:ℝ)^n) := by linarith
  have hsub0 : 0 ≤ 1/(2*(1-(1/2:ℝ)^n)) := by positivity
  have hsub1 : 1/(2*(1-(1/2:ℝ)^n)) ≤ 1 := (div_le_one (by linarith)).mpr hden
  have hpow : (2:ℝ)^(n-2) = (2:ℝ)^n/4 := by
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
    rw [hj,Nat.add_sub_cancel_left,pow_add]
    norm_num
  rw [hpow]
  constructor <;> linarith

 

theorem success (L Y : Ω → ℝ) (hY : Measurable Y)
    (hYL : ∀ᵐ ω ∂P, 0 ≤ Y ω ∧ Y ω ≤ L ω)
    (hint : ∀ n, Integrable (fun ω => (L ω)^n) P) (hmean : 0 < moment P L 1)
    (n : ℕ) (hn : 3 ≤ n) (hYn : Integrable (fun ω => (Y ω)^n) P)
    (happrox : 3*moment P L n/4 ≤ moment P Y n) :
    (2:ℝ)^(n-2)-1/(2*(1-(1/2:ℝ)^n)) ≤
      (∑' k : ℤ, (multiplicity (moment P L) n k:ℝ)*P.real {ω | (2:ℝ)^k ≤ Y ω}) ∧
    (2:ℝ)^n/8 ≤ (2:ℝ)^(n-2)-1/(2*(1-(1/2:ℝ)^n)) := by
  have hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω := hYL.mono (fun ω hω => hω.1.trans hω.2)
  obtain ⟨hm,hJ⟩ := moment_sequence_properties P L hL0 hint hmean
  have hnp : 0 < n := by omega
  have hfin := finite_multiplicity_support hnp hmean (hm n hnp) (hm (n+1) (by omega)) (hJ n hnp)
  have hb := success_strong P L Y hY hYL n hnp (hint (n+1)) hYn
    (hm n hnp) (hm (n+1) (by omega)) hfin happrox
  rw [sum_eq_tsum_multiplicity hfin] at hb
  exact ⟨(success_numerics n hn).1.trans hb,(success_numerics n hn).2⟩

end SLEExactGauge.MomentBatches
end
end

end OAI
