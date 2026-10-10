import Mathlib
import OAI.Analysis.PathSelection.SectorBounds

namespace OAI

/-! Discrete and logarithmic loss pullbacks, summable majorants and derivative transfer. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology
namespace DegeneratingTrees

lemma summable_comp_four {w : ℕ → ℝ} (hw : Summable w) {k : ℕ → ℕ}
    (hk : ∀ j : ℕ,j<4 → StrictMono (fun n => k (4*n+j))) :
    Summable (fun n => w (k n)) := by
  have hs (j : ℕ) (hj : j<4) : Summable (fun n => w (k (4*n+j))) :=
    hw.comp_injective (hk j hj).injective
  apply Summable.even_add_odd
  · apply Summable.even_add_odd
    · simpa only [show ∀ n : ℕ,2*(2*n)=4*n+0 by omega] using hs 0 (by omega)
    · convert hs 2 (by omega) using 1
      ext n
      congr 2
      omega
  · apply Summable.even_add_odd
    · convert hs 1 (by omega) using 1
      ext n
      congr 2
      omega
    · convert hs 3 (by omega) using 1
      ext n
      congr 2
      omega

lemma dyadic_span_bound {ω : ℝ → ℝ} {n₀ : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n,0≤w n)
    (hb : ∀ n r,(2:ℝ)^(n+n₀)<r → r<2^(n+n₀+2) → ω r≤w n)
    (k q : ℕ) {s : ℝ} (hsl : (2:ℝ)^(k+n₀+1 ) ≤ s)
    (hsu : s<(2:ℝ)^(k+n₀+q+1)) :
    ω s≤∑ j∈Finset.range q,w (k+j) := by
  obtain ⟨j,hjl,hju⟩ := dyadic_shell (show (0:ℝ)<2^(k+n₀+1) by positivity) hsl
  have hjq : j<q := by
    have hh : (2:ℝ)^(k+n₀+1+j)<2^(k+n₀+q+1) := by
      simpa only [pow_add] using hjl.trans_lt hsu
    exact (by have := (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hh; omega)
  have hl : (2:ℝ)^(k+j+n₀)<s := by
    have hh : (2:ℝ)^(k+j+n₀)<2^(k+n₀+1)*2^j := by
      rw [←pow_add]
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    exact hh.trans_le hjl
  have hu : s<(2:ℝ)^(k+j+n₀+2) := by
    convert hju using 1
    simp only [pow_add]
    ring
  exact (hb (k+j) s hl hu).trans
    (Finset.single_le_sum (fun i _ => hw (k+i)) (Finset.mem_range.mpr hjq))

 

lemma admissible_max_of_shell_bounds {v : ℝ → ℝ} {N : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n,0≤w n) (hs : Summable w)
    (hb : ∀ n r,(2:ℝ)^(n+N)<r → r<2^(n+N+2) → v r≤w n) :
    AdmissibleAngularLoss (fun r => max (baseLoss r) (v r)) := by
  obtain ⟨hp,M,a,ha,has,hab⟩ := admissible_baseLoss
  refine ⟨?_,M+N,fun n => a (n+N)+w (n+M),?_,?_,?_⟩
  · filter_upwards [hp] with r hr
    exact ⟨hr.1.trans_le (le_max_left _ _),hr.2.trans (le_max_left _ _)⟩
  · intro n
    exact add_nonneg (ha _) (hw _)
  · exact ((summable_nat_add_iff N).mpr has).add ((summable_nat_add_iff M).mpr hs)
  · intro n r hl hu
    have h1 := hab (n+N) r (by convert hl using 1; congr 1; omega)
      (by convert hu using 1; congr 1; omega)
    have h2 := hb (n+M) r (by convert hl using 1; congr 1; omega)
      (by convert hu using 1; congr 1; omega)
    exact max_le (h1.trans (le_add_of_nonneg_right (hw _)))
      (h2.trans (le_add_of_nonneg_left (ha _)))

 

lemma admissible_pullback_of_shell_control {ω f : ℝ → ℝ} {n₀ N q : ℕ}
    {w : ℕ → ℝ} (hw : ∀ n,0≤w n) (hs : Summable w)
    (hb : ∀ n r,(2:ℝ)^(n+n₀)<r → r<2^(n+n₀+2) → ω r≤w n)
    (k : ℕ → ℕ) (hk : ∀ j : ℕ,j<4 → StrictMono (fun n => k (4*n+j)))
    (hmap : ∀ n r,(2:ℝ)^(n+N)<r → r<2^(n+N+2) →
      (2:ℝ)^(k n+n₀+1)≤f r ∧ f r<2^(k n+n₀+q+1)) :
    AdmissibleAngularLoss (fun r => max (baseLoss r) (ω (f r))) := by
  have hsum (S : Finset ℕ) : Summable (fun n => ∑ j∈S,w (k n+j)) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      have hh : Summable (fun n => w (k n+j)) :=
        summable_comp_four ((summable_nat_add_iff j).mpr hs) hk
      simpa only [Finset.sum_insert hj] using hh.add ih
  apply admissible_max_of_shell_bounds (N := N)
    (w := fun n => ∑ j∈Finset.range q,w (k n+j))
    (fun n => Finset.sum_nonneg (fun j _ => hw _)) (hsum _)
  intro n r hl hu
  exact dyadic_span_bound hw hb (k n) q (hmap n r hl hu).1 (hmap n r hl hu).2

end DegeneratingTrees

 

 

open Set Filter Topology
namespace DegeneratingTrees

lemma summable_comp_mod {w : ℕ → ℝ} (hw₀ : ∀ n,0 ≤ w n) (hw : Summable w)
    {k : ℕ → ℕ} {m : ℕ} (hm : 0  <  m)
    (hk : ∀ j : ℕ,j < m → StrictMono (fun n => k (m*n+j))) :
    Summable (fun n => w (k n)) := by
  let : NeZero m := ⟨hm.ne'⟩
  let e : ℕ ≃ Fin m × ℕ := (Nat.divModEquiv m).trans (Equiv.prodComm _ _)
  have hs : Summable (fun p : Fin m × ℕ => w (k (p.2*m+p.1))) := by
    apply (summable_prod_of_nonneg (fun p => hw₀ _)).mpr
    refine ⟨?_,Summable.of_finite⟩
    intro j
    simpa only [Function.comp_def,Nat.mul_comm] using hw.comp_injective (hk j j.isLt).injective
  have hh := hs.comp_injective e.injective
  have he (n : ℕ) : (e n).2*m+(e n).1=n := Nat.div_add_mod' n m
  simpa only [Function.comp_def,he] using hh

lemma summable_shell_window {w : ℕ → ℝ} (hw₀ : ∀ n,0 ≤ w n) (hw : Summable w)
    {k : ℕ → ℕ} {m : ℕ} (hm : 0  <  m)
    (hk : ∀ j : ℕ,j < m → StrictMono (fun n => k (m*n+j))) (q : ℕ) :
    Summable (fun n => ∑ j∈Finset.range q,w (k n+j)) := by
  classical
  have hh (S : Finset ℕ) : Summable (fun n => ∑ j∈S,w (k n+j)) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      have h := summable_comp_mod (fun n => hw₀ (n+j)) ((summable_nat_add_iff j).mpr hw) hm hk
      simpa only [Finset.sum_insert hj] using h.add ih
  exact hh _

end DegeneratingTrees

 

 

 

open Set Filter Topology
namespace DegeneratingTrees

theorem log_scale_shell_control {ψ : ℝ → ℝ} {A c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hψ : ∀ x y : ℝ,A ≤ x → x ≤ y →
      c*(y-x) ≤ ψ y-ψ x ∧ ψ y-ψ x ≤ C*(y-x)) (n₀ : ℕ) :
    ∃ N m q : ℕ,∃ k : ℕ → ℕ,0 < m ∧
      (∀ j : ℕ,j < m → StrictMono (fun n => k (m*n+j))) ∧
      ∀ n r,(2:ℝ)^(n+N) < r → r < 2^(n+N+2) →
        (2:ℝ)^(k n+n₀+1) ≤ (2:ℝ)^(ψ (Real.logb 2 r)) ∧
        (2:ℝ)^(ψ (Real.logb 2 r)) < 2^(k n+n₀+q+1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (Max.max A (A+((n₀:ℝ)+2-ψ A)/c))
  have hNA : A ≤ (N:ℝ) := le_of_lt ((le_max_left _ _).trans_lt hN)
  have hNψ : (n₀:ℝ)+2 < ψ (N:ℝ) := by
    have h := (hψ A (N:ℝ) le_rfl hNA).1
    have ht := (le_max_right _ _).trans_lt hN
    have ht' : ((n₀:ℝ)+2-ψ A)/c < (N:ℝ)-A := by linarith
    have ht'' := (div_lt_iff₀ hc).mp ht'
    nlinarith
  have hbase (n : ℕ) : (n₀:ℝ)+2 < ψ ((n+N:ℕ):ℝ) := by
    have hn : (N:ℝ) ≤ ((n+N:ℕ):ℝ) := by norm_num
    have h := (hψ (N:ℝ) ((n+N:ℕ):ℝ) hNA hn).1
    nlinarith
  obtain ⟨m,hm⟩ := exists_nat_gt ((2:ℝ)/c)
  have hm0 : 0 < m := by
    have hh : (0:ℝ) < (m:ℝ) := (by positivity : (0:ℝ) < 2/c).trans hm
    exact_mod_cast hh
  have hcm : 2 < c*(m:ℝ) := by have hh := (div_lt_iff₀ hc).mp hm; nlinarith
  obtain ⟨q,hq⟩ := exists_nat_gt (2*C+1)
  let k : ℕ → ℕ := fun n => ⌊ψ ((n+N:ℕ):ℝ)⌋₊-n₀-1
  have hid (n : ℕ) : k n+n₀+1=⌊ψ ((n+N:ℕ):ℝ)⌋₊ := by
    have hn : n₀+1 ≤ ⌊ψ ((n+N:ℕ):ℝ)⌋₊ := by
      apply Nat.le_floor
      have := hbase n
      norm_num only [Nat.cast_add,Nat.cast_one] at this ⊢
      nlinarith
    dsimp [k]
    omega
  have hk : ∀ j : ℕ,j < m → StrictMono (fun n => k (m*n+j)) := by
    intro j hj
    apply strictMono_nat_of_lt_succ
    intro n
    let x : ℝ := ((m*n+j+N:ℕ):ℝ)
    let y : ℝ := ((m*(n+1)+j+N:ℕ):ℝ)
    have hxA : A ≤ x := le_trans hNA (by dsimp [x]; exact_mod_cast (Nat.le_add_left N (m*n+j)))
    have hxy : y-x=(m:ℝ) := by dsimp [y,x]; push_cast; ring
    have hh := (hψ x y hxA (by linarith)).1
    have hxp : 0 ≤ ψ x := by
      have hh := hbase (m*n+j)
      exact (show (0:ℝ) ≤ (n₀:ℝ)+2 by positivity).trans hh.le
    have hfloorx := Nat.floor_le hxp
    have hfloory := Nat.lt_floor_add_one (ψ y)
    have hfl : ⌊ψ x⌋₊ < ⌊ψ y⌋₊ := by
      have hh' : (⌊ψ x⌋₊:ℝ) < (⌊ψ y⌋₊:ℝ) := by nlinarith
      exact_mod_cast hh'
    have hidx := hid (m*n+j)
    have hidy := hid (m*(n+1)+j)
    dsimp [x,y] at hfl
    omega
  refine ⟨N,m,q,k,hm0,hk,?_⟩
  intro n r hrl hru
  have hrl0 : (0:ℝ) < 2^(n+N) := by positivity
  have hr0 : 0 < r := hrl0.trans hrl
  have hlogl : ((n+N:ℕ):ℝ) < Real.logb 2 r := by
    have hh := Real.logb_lt_logb (by norm_num : (1:ℝ) < 2) hrl0 hrl
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2),mul_one] using hh
  have hlogu : Real.logb 2 r < ((n+N:ℕ):ℝ)+2 := by
    have hh := Real.logb_lt_logb (by norm_num : (1:ℝ) < 2) hr0 hru
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2),mul_one,Nat.cast_add,Nat.cast_ofNat] using hh
  have hNA' : A ≤ ((n+N:ℕ):ℝ) := le_trans hNA (by norm_num)
  have hh := hψ ((n+N:ℕ):ℝ) (Real.logb 2 r) hNA' hlogl.le
  have hfloor := Nat.floor_le (show 0 ≤ ψ ((n+N:ℕ):ℝ) by
    exact (show (0:ℝ) ≤ (n₀:ℝ)+2 by positivity).trans (hbase n).le)
  have hfloor' := Nat.lt_floor_add_one (ψ ((n+N:ℕ):ℝ))
  constructor
  · rw [←Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    rw [hid]
    nlinarith
  · rw [←Real.rpow_natCast]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
    have he : k n+n₀+q+1=⌊ψ ((n+N:ℕ):ℝ)⌋₊+q := by have := hid n; omega
    rw [he]
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hfloor' hh hlogu hlogl ⊢
    nlinarith

end DegeneratingTrees

 

 

 

open Set Filter Topology
namespace DegeneratingTrees

lemma summable_strict_majorant {w : ℕ → ℝ} (hw : ∀ n,0≤w n) (hs : Summable w) :
    ∃ v : ℕ → ℝ,(∀ n,0≤v n) ∧ Summable v ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ n in atTop,w n≤ε*v n := by
  let T : ℕ → ℝ := fun n => ∑' k : ℕ,w (k+n)
  have hTpos (n : ℕ) : 0≤T n := tsum_nonneg (fun k => hw _)
  have hTrec (n : ℕ) : T n=w n+T (n+1) := by
    have hh := ((summable_nat_add_iff n).mpr hs).tsum_eq_zero_add
    simpa only [T,zero_add,Nat.add_assoc,show 1+n=n+1 by omega] using hh
  have hTlim : Tendsto T atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := ∑' k,w k)).sub hs.hasSum.tendsto_sum_nat
    simp only [sub_self] at hh
    apply hh.congr
    intro n
    have ht := hs.sum_add_tsum_nat_add n
    dsimp [T]
    linarith
  let v : ℕ → ℝ := fun n => Real.sqrt (T n)-Real.sqrt (T (n+1))
  have hvpos (n : ℕ) : 0≤v n := by
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    linarith [hTrec n,hw n]
  have hvs : Summable v := by
    apply summable_of_sum_range_le hvpos (c := Real.sqrt (T 0))
    intro n
    dsimp [v]
    rw [Finset.sum_range_sub']
    exact sub_le_self _ (Real.sqrt_nonneg _)
  have hfac (n : ℕ) : w n=(Real.sqrt (T n)+Real.sqrt (T (n+1)))*v n := by
    dsimp [v]
    nlinarith [Real.sq_sqrt (hTpos n),Real.sq_sqrt (hTpos (n+1)),hTrec n]
  have hlim : Tendsto (fun n => Real.sqrt (T n)+Real.sqrt (T (n+1))) atTop (𝓝 0) := by
    have hh := (Real.continuous_sqrt.continuousAt.tendsto.comp hTlim).add
      (Real.continuous_sqrt.continuousAt.tendsto.comp (hTlim.comp (tendsto_add_atTop_nat 1)))
    simpa only [Real.sqrt_zero,add_zero,Function.comp_def] using hh
  refine ⟨v,hvpos,hvs,?_⟩
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  rw [hfac]
  exact mul_le_mul_of_nonneg_right hn.le (hvpos n)

end DegeneratingTrees

 

 

 

open Set Filter Topology
namespace DegeneratingTrees

 

theorem AdmissibleAngularLoss.pullback_log_scale {ω ψ : ℝ → ℝ}
    (hω : AdmissibleAngularLoss ω) {A : ℝ}
    (hψ : ∀ x y : ℝ,A≤x → x≤y →
      (y-x)/2≤ψ y-ψ x ∧ ψ y-ψ x≤2*(y-x)) :
    AdmissibleAngularLoss (fun r => Max.max (baseLoss r) (ω ((2:ℝ)^(ψ (Real.logb 2 r))))) := by
  obtain ⟨hp,n₀,w,hw,hs,hb⟩ := hω
  obtain ⟨N,hN⟩ := exists_nat_gt (Max.max A (A+2*((n₀:ℝ)+2-ψ A)))
  have hNA : A≤(N:ℝ) := le_of_lt ((le_max_left _ _).trans_lt hN)
  have hNψ : (n₀:ℝ)+2<ψ (N:ℝ) := by
    have h := (hψ A (N:ℝ) le_rfl hNA).1
    have ht := (le_max_right _ _).trans_lt hN
    linarith
  have hbase (n : ℕ) : (n₀:ℝ)+2<ψ ((n+N:ℕ):ℝ) := by
    have hn : (N:ℝ)≤((n+N:ℕ):ℝ) := by norm_num
    have h := (hψ (N:ℝ) ((n+N:ℕ):ℝ) hNA hn).1
    linarith
  let k : ℕ → ℕ := fun n => ⌊ψ ((n+N:ℕ):ℝ)⌋₊-n₀-1
  have hid (n : ℕ) : k n+n₀+1=⌊ψ ((n+N:ℕ):ℝ)⌋₊ := by
    have hn : n₀+1≤⌊ψ ((n+N:ℕ):ℝ)⌋₊ := by
      apply Nat.le_floor
      have := hbase n
      norm_num only [Nat.cast_add,Nat.cast_one] at this ⊢
      linarith
    dsimp [k]
    omega
  have hk : ∀ j : ℕ,j<4 → StrictMono (fun n => k (4*n+j)) := by
    intro j hj
    apply strictMono_nat_of_lt_succ
    intro n
    let x : ℝ := ((4*n+j+N:ℕ):ℝ)
    let y : ℝ := ((4*(n+1)+j+N:ℕ):ℝ)
    have hxA : A≤x := le_trans hNA (by dsimp [x]; exact_mod_cast (Nat.le_add_left N (4*n+j)))
    have hxy : y-x=4 := by dsimp [y,x]; push_cast; ring
    have hh := (hψ x y hxA (by linarith)).1
    have hxp : 0≤ψ x := by
      have hh := hbase (4*n+j)
      exact (show (0:ℝ)≤(n₀:ℝ)+2 by positivity).trans hh.le
    have hfloorx := Nat.floor_le hxp
    have hfloory := Nat.lt_floor_add_one (ψ y)
    have hfl : ⌊ψ x⌋₊<⌊ψ y⌋₊ := by
      have hh' : (⌊ψ x⌋₊:ℝ)<(⌊ψ y⌋₊:ℝ) := by linarith
      exact_mod_cast hh'
    have hidx := hid (4*n+j)
    have hidy := hid (4*(n+1)+j)
    dsimp [x,y] at hfl
    omega
  apply admissible_pullback_of_shell_control (N := N) (q := 5) hw hs hb k hk
  intro n r hrl hru
  have hrl0 : (0:ℝ)<2^(n+N) := by positivity
  have hr0 : 0<r := hrl0.trans hrl
  have hlogl : ((n+N:ℕ):ℝ)<Real.logb 2 r := by
    have hh := Real.logb_lt_logb (by norm_num : (1:ℝ)<2) hrl0 hrl
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] using hh
  have hlogu : Real.logb 2 r<((n+N:ℕ):ℝ)+2 := by
    have hh := Real.logb_lt_logb (by norm_num : (1:ℝ)<2) hr0 hru
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one,Nat.cast_add,Nat.cast_ofNat] using hh
  have hNA' : A≤((n+N:ℕ):ℝ) := le_trans hNA (by norm_num)
  have hh := hψ ((n+N:ℕ):ℝ) (Real.logb 2 r) hNA' hlogl.le
  have hfloor := Nat.floor_le (show 0≤ψ ((n+N:ℕ):ℝ) by
    exact (show (0:ℝ)≤(n₀:ℝ)+2 by positivity).trans (hbase n).le)
  have hfloor' := Nat.lt_floor_add_one (ψ ((n+N:ℕ):ℝ))
  constructor
  · rw [←Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    rw [hid]
    linarith
  · rw [←Real.rpow_natCast]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2)
    have he : k n+n₀+5+1=⌊ψ ((n+N:ℕ):ℝ)⌋₊+5 := by have := hid n; omega
    rw [he]
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hfloor' hh hlogu hlogl ⊢
    linarith

end DegeneratingTrees

 

 

 

open Set Filter Topology
namespace DegeneratingTrees

def dyadicLossIndex (N : ℕ) (r : ℝ) : ℕ := ⌊Real.logb 2 r⌋₊-N-1

lemma tendsto_dyadicLossIndex (N : ℕ) : Tendsto (dyadicLossIndex N) atTop atTop :=
  (tendsto_sub_atTop_nat 1).comp ((tendsto_sub_atTop_nat N).comp
    (tendsto_nat_floor_atTop.comp (Real.tendsto_logb_atTop (by norm_num : (1:ℝ)<2))))

lemma dyadicLossIndex_shell (N : ℕ) : ∀ᶠ r : ℝ in atTop,
    (2:ℝ)^(dyadicLossIndex N r+N)<r ∧ r<2^(dyadicLossIndex N r+N+2) := by
  filter_upwards [(Real.tendsto_logb_atTop (by norm_num : (1:ℝ)<2)).eventually
    (eventually_ge_atTop ((N:ℝ)+1)),eventually_gt_atTop (0:ℝ)] with r hl hr
  have hfl : N+1≤⌊Real.logb 2 r⌋₊ := Nat.le_floor (by exact_mod_cast hl)
  have hid : dyadicLossIndex N r+N+1=⌊Real.logb 2 r⌋₊ := by dsimp [dyadicLossIndex]; omega
  have hlog : 0≤Real.logb 2 r := (by positivity : (0:ℝ)≤(N:ℝ)+1).trans hl
  have hfloor := Nat.floor_le hlog
  have hfloor' := Nat.lt_floor_add_one (Real.logb 2 r)
  have he : r=(2:ℝ)^(Real.logb 2 r) := (Real.rpow_logb (by norm_num) (by norm_num) hr).symm
  constructor
  · conv_rhs => rw [he]
    rw [←Real.rpow_natCast]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2)
    have hh : ((dyadicLossIndex N r+N:ℕ):ℝ)+1=(⌊Real.logb 2 r⌋₊:ℝ) := by exact_mod_cast hid
    linarith
  · conv_lhs => rw [he]
    rw [←Real.rpow_natCast]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2)
    have hh : dyadicLossIndex N r+N+2=⌊Real.logb 2 r⌋₊+1 := by omega
    rw [hh]
    simpa only [Nat.cast_add,Nat.cast_one] using hfloor'

lemma admissible_dyadic_step {v : ℕ → ℝ} (hv : ∀ n,0≤v n) (hs : Summable v) (N : ℕ) :
    AdmissibleAngularLoss (fun r => max (baseLoss r) (v (dyadicLossIndex N r))) := by
  have hsum : Summable (fun n => v (n+1)+v (n+2)) :=
    ((summable_nat_add_iff 1).mpr hs).add ((summable_nat_add_iff 2).mpr hs)
  apply admissible_max_of_shell_bounds (N := N+2)
    (w := fun n => v (n+1)+v (n+2)) (fun n => add_nonneg (hv _) (hv _)) hsum
  intro n r hl hu
  have hp : (0:ℝ)<2^(n+(N+2)) := by positivity
  have hr : 0<r := hp.trans hl
  have hlogl : ((n+(N+2):ℕ):ℝ)<Real.logb 2 r := by
    have hh := Real.logb_lt_logb (by norm_num : (1:ℝ)<2) hp hl
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] using hh
  have hlogu : Real.logb 2 r<((n+(N+2)+2:ℕ):ℝ) := by
    have hh := Real.logb_lt_logb (by norm_num : (1:ℝ)<2) hr hu
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] using hh
  have hfloorl : n+(N+2)≤⌊Real.logb 2 r⌋₊ := Nat.le_floor hlogl.le
  have hflooru : ⌊Real.logb 2 r⌋₊<n+(N+2)+2 :=
    (Nat.floor_lt ((Nat.cast_nonneg _).trans hlogl.le)).mpr hlogu
  have hid : dyadicLossIndex N r=n+1 ∨ dyadicLossIndex N r=n+2 := by
    dsimp [dyadicLossIndex]
    omega
  rcases hid with h | h
  · rw [h]; exact le_add_of_nonneg_right (hv _)
  · rw [h]; exact le_add_of_nonneg_left (hv _)

theorem admissible_strict_absorption {e : ℝ → ℝ} {w : ℕ → ℝ} {N : ℕ}
    (hw : ∀ n,0≤w n) (hs : Summable w)
    (hb : ∀ n r,(2:ℝ)^(n+N)<r → r<2^(n+N+2) → |e r|≤w n) :
    ∃ ω : ℝ → ℝ,AdmissibleAngularLoss ω ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ r in atTop,|e r|≤ε*ω r := by
  obtain ⟨v,hv,hvs,hlittle⟩ := summable_strict_majorant hw hs
  refine ⟨fun r => max (baseLoss r) (v (dyadicLossIndex N r)),admissible_dyadic_step hv hvs N,?_⟩
  intro ε hε
  filter_upwards [dyadicLossIndex_shell N,(tendsto_dyadicLossIndex N).eventually (hlittle ε hε)] with r hr hvw
  exact (hb _ r hr.1 hr.2).trans (hvw.trans
    (mul_le_mul_of_nonneg_left (le_max_right _ _) hε.le))

end DegeneratingTrees

 

 

 

open Set Filter Topology
namespace DegeneratingTrees

lemma logarithmic_clock_slopes {ψ : ℝ → ℝ}
    (ha : ∀ᶠ x in atTop,DifferentiableAt ℝ ψ x)
    (hd : Tendsto (deriv ψ) atTop (𝓝 1)) :
    ∃ A : ℝ,∀ x y : ℝ,A≤x → x≤y →
      (y-x)/2≤ψ y-ψ x ∧ ψ y-ψ x≤2*(y-x) := by
  have hnear : ∀ᶠ x in atTop,‖deriv ψ x-1‖≤(1:ℝ)/2 := by
    filter_upwards [(Metric.tendsto_nhds.mp hd) (1/2) (by norm_num)] with x hx
    exact le_of_lt (by simpa only [dist_eq_norm] using hx)
  obtain ⟨A,hA⟩ := eventually_atTop.mp (ha.and hnear)
  refine ⟨A,?_⟩
  intro x y hx hxy
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t => ψ t-t) (f' := fun t => deriv ψ t-1) (a := x) (b := y)
    (fun t ht => ((hA t (hx.trans ht.1)).1.hasDerivAt.sub (hasDerivAt_id t)).hasDerivWithinAt)
    (fun t ht => (hA t (hx.trans ht.1)).2) y ⟨hxy,le_rfl⟩
  rw [Real.norm_eq_abs,abs_le] at hh
  constructor <;> linarith [hh.1,hh.2]

theorem AdmissibleAngularLoss.pullback_log_derivative {ω ψ : ℝ → ℝ}
    (hω : AdmissibleAngularLoss ω)
    (ha : ∀ᶠ x in atTop,DifferentiableAt ℝ ψ x)
    (hd : Tendsto (deriv ψ) atTop (𝓝 1)) :
    AdmissibleAngularLoss (fun r => Max.max (baseLoss r) (ω ((2:ℝ)^(ψ (Real.logb 2 r))))) := by
  obtain ⟨A,hA⟩ := logarithmic_clock_slopes ha hd
  exact hω.pullback_log_scale hA

end DegeneratingTrees

 

 

 

open Set Filter Topology
namespace DegeneratingTrees

lemma logarithmic_clock_slopes_pos {ψ : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (ha : ∀ᶠ x in atTop,DifferentiableAt ℝ ψ x)
    (hd : Tendsto (deriv ψ) atTop (𝓝 b)) :
    ∃ A : ℝ,∀ x y : ℝ,A ≤ x → x ≤ y →
      (b/2)*(y-x) ≤ ψ y-ψ x ∧ ψ y-ψ x ≤ (2*b)*(y-x) := by
  have hnear : ∀ᶠ x in atTop,‖deriv ψ x-b‖ ≤ b/2 := by
    filter_upwards [(Metric.tendsto_nhds.mp hd) (b/2) (by positivity)] with x hx
    exact le_of_lt (by simpa only [dist_eq_norm] using hx)
  obtain ⟨A,hA⟩ := eventually_atTop.mp (ha.and hnear)
  refine ⟨A,?_⟩
  intro x y hx hxy
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t => ψ t-b*t) (f' := fun t => deriv ψ t-b) (a := x) (b := y)
    (fun t ht => ((hA t (hx.trans ht.1)).1.hasDerivAt.sub (hasDerivAt_const_mul b)).hasDerivWithinAt)
    (fun t ht => (hA t (hx.trans ht.1)).2) y ⟨hxy,le_rfl⟩
  rw [Real.norm_eq_abs,abs_le] at hh
  constructor <;> nlinarith [hh.1,hh.2]

lemma unit_to_dyadic_shells {e : ℝ → ℝ} {w : ℕ → ℝ} {n₀ : ℕ}
    (hb : ∀ n t,((n+n₀:ℕ):ℝ) ≤ t → t ≤ ((n+n₀:ℕ):ℝ)+2 → |e t| ≤ w n) :
    ∀ n r,(2:ℝ)^(n+n₀) < r → r < 2^(n+n₀+2) → |e (Real.logb 2 r)| ≤ w n := by
  intro n r hl hu
  have hl₀ : (0:ℝ) < 2^(n+n₀) := by positivity
  have hr : 0 < r := hl₀.trans hl
  apply hb
  · have hh := Real.logb_lt_logb (by norm_num : (1:ℝ) < 2) hl₀ hl
    exact le_of_lt (by simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2),mul_one] using hh)
  · have hh := Real.logb_lt_logb (by norm_num : (1:ℝ) < 2) hr hu
    exact le_of_lt (by simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2),mul_one,Nat.cast_add,Nat.cast_ofNat] using hh)

theorem strict_loss_from_unit_shells {e ψ : ℝ → ℝ} {w : ℕ → ℝ} {n₀ : ℕ}
    (hw : ∀ n,0 ≤ w n) (hs : Summable w)
    (hb : ∀ n t,((n+n₀:ℕ):ℝ) ≤ t → t ≤ ((n+n₀:ℕ):ℝ)+2 → |e t| ≤ w n)
    {b : ℝ} (hb₀ : 0 < b)
    (ha : ∀ᶠ x in atTop,DifferentiableAt ℝ ψ x)
    (hd : Tendsto (deriv ψ) atTop (𝓝 b)) :
    ∃ ω : ℝ → ℝ,AdmissibleAngularLoss ω ∧
      ∀ ε : ℝ,0 < ε → ∀ᶠ r in atTop,|e (ψ (Real.logb 2 r))| ≤ ε*ω r := by
  obtain ⟨A,hA⟩ := logarithmic_clock_slopes_pos hb₀ ha hd
  obtain ⟨N,m,q,k,hm,hk,hmap⟩ := log_scale_shell_control (by positivity : 0 < b/2)
    (by positivity : 0 < 2*b) hA n₀
  apply admissible_strict_absorption (N := N) (w := fun n => ∑ j∈Finset.range q,w (k n+j))
    (fun n => Finset.sum_nonneg (fun j _ => hw _)) (summable_shell_window hw hs hm hk q)
  intro n r hl hu
  have hh := dyadic_span_bound hw (unit_to_dyadic_shells hb) (k n) q
    (hmap n r hl hu).1 (hmap n r hl hu).2
  simpa only [Real.logb_rpow (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ)≠1)] using hh

end DegeneratingTrees
end

end OAI
