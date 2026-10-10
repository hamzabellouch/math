import OAI.Probability.FKMaps.RadialBridge

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

/-- Durations followed by a terminal first-hitting segment. -/
def segments {m : ℕ} (d b : Fin m → ℕ) : List (ℕ×ℕ) :=
  List.ofFn (fun i => (d i,b i))

lemma segments_cons {m : ℕ} (d b : Fin (m+1) → ℕ) :
    segments d b=(d 0,b 0)::segments (Fin.tail d) (Fin.tail b) := by
  simp [segments,List.ofFn_succ,Fin.tail_def]

lemma traceSize_segments {m : ℕ} (R : ℕ) (d b : Fin m → ℕ) :
    traceSize R (segments d b)=(∑ i,d i)+R := by
  rw [traceSize_eq_sum]
  simp [segments,List.sum_ofFn]

def normalizedTrace {m : ℕ} (a R : ℕ) (d b : Fin m → ℕ) : ℝ :=
  traceKilledWeight a (R+1) (segments d b) /
    pathMass ((∑ i,d i)+R+1) (firstHit a)

lemma normalizedTrace_cons {m : ℕ} (a R : ℕ) (d b : Fin (m+1) → ℕ)
    (h : pathMass ((∑ i,Fin.tail d i)+R+1) (firstHit (b 0))≠0) :
    normalizedTrace a R d b=
      (killed (d 0) a (b 0)*pathMass ((∑ i,Fin.tail d i)+R+1) (firstHit (b 0)) /
        pathMass (d 0+((∑ i,Fin.tail d i)+R)+1) (firstHit a))*
      normalizedTrace (b 0) R (Fin.tail d) (Fin.tail b) := by
  simp only [normalizedTrace,segments_cons,traceKilledWeight]
  rw [Fin.sum_univ_succ d]
  change killed (d 0) a (b 0)*traceKilledWeight (b 0) (R+1)
    (segments (Fin.tail d) (Fin.tail b)) /
    pathMass (d 0+(∑ i,Fin.tail d i)+R+1) (firstHit a)=_
  rw [show d 0+(∑ i,Fin.tail d i)+R+1=d 0+((∑ i,Fin.tail d i)+R)+1 by omega]
  field_simp

/-- Macroscopic bridge parameters expressed directly in successive durations. -/
def remaining {m : ℕ} (s : Fin m → ℝ) (r : ℝ) (i : Fin m) : ℝ :=
  r+∑ j∈Finset.univ.filter (fun j : Fin m => i<j),s j

def durationRatio {m : ℕ} (s : Fin m → ℝ) (r : ℝ) (i : Fin m) : ℝ :=
  remaining s r i/(s i+remaining s r i)

def durationVariance {m : ℕ} (s : Fin m → ℝ) (r : ℝ) (i : Fin m) : ℝ :=
  s i*remaining s r i/(s i+remaining s r i)

lemma remaining_zero {m : ℕ} (s : Fin (m+1) → ℝ) (r : ℝ) :
    remaining s r 0=(∑ i,Fin.tail s i)+r := by
  simp only [remaining,Finset.sum_filter,Fin.sum_univ_succ,lt_self_iff_false,ite_false,
    Fin.succ_pos,ite_true,zero_add]
  rw [add_comm]
  rfl

lemma remaining_succ {m : ℕ} (s : Fin (m+1) → ℝ) (r : ℝ) (i : Fin m) :
    remaining s r i.succ=remaining (Fin.tail s) r i := by
  simp only [remaining,Finset.sum_filter,Fin.sum_univ_succ,Fin.not_lt_zero,ite_false,
    Fin.succ_lt_succ_iff,zero_add]
  rfl

lemma remaining_pos {m : ℕ} (s : Fin m → ℝ) {r : ℝ} (hr : 0<r)
    (hs : ∀ i,0<s i) (i : Fin m) : 0<remaining s r i := by
  unfold remaining
  exact add_pos_of_pos_of_nonneg hr (Finset.sum_nonneg (fun j _ => (hs j).le))

lemma sum_ratio_tendsto {m : ℕ} {d : ℕ → Fin m → ℕ} {T : ℕ → ℕ}
    {s : Fin m → ℝ} (hd : ∀ i,Tendsto (fun n => (d n i:ℝ)/(T n:ℝ)) atTop (𝓝 (s i))) :
    Tendsto (fun n => ((∑ i,d n i:ℕ):ℝ)/(T n:ℝ)) atTop (𝓝 (∑ i,s i)) := by
  have hh := tendsto_finsetSum Finset.univ (fun i _ => hd i)
  simpa only [Nat.cast_sum,Finset.sum_div] using hh

lemma even_int_cast {n : ℕ} (h : Even n) : Even (n:ℤ) := by exact_mod_cast h

lemma even_int_terminal {n b : ℕ} (hn : Even n) (hb : Even b) :
    Even (((n+1:ℕ):ℤ)+((b:ℤ)+1)) := by
  have h := (even_int_cast hn).add (even_int_cast hb)
  have he : (((n+1:ℕ):ℤ)+((b:ℤ)+1))=((n:ℤ)+(b:ℤ))+2 := by push_cast; ring
  rw [he]
  exact h.add (by norm_num : Even (2:ℤ))


lemma firstHit_eventually_ne_zero {R T a : ℕ → ℕ} {t x : ℝ}
    (ht : 0<t) (hx : 0<x) (hR : Tendsto R atTop atTop)
    (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => ((R n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t))
    (hRe : ∀ n,Even (R n)) (hae : ∀ n,Even (a n))
    (ha : Tendsto (fun n => (a n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 x)) :
    ∀ᶠ n in atTop,pathMass (R n+1) (firstHit (a n))≠0 := by
  have hh := firstHit_scaled_limit ht hR hT hr
    (Filter.Eventually.of_forall (fun n => even_int_terminal (hRe n) (hae n))) ha
  have hp := hh.eventually (eventually_ne_nhds (hitHeat_pos ht hx).ne')
  filter_upwards [hp] with n hn
  exact fun h => hn (by simp only [h,mul_zero])


lemma pathMass_nonneg (N : ℕ) (P : Path N → Prop) : 0≤pathMass N P := by
  unfold pathMass
  positivity

lemma chainDensity_ne_top (m : ℕ) (z : ℝ) (a t x : Fin m → ℝ) :
    Radial.chainDensity z a t x≠∞ := by
  induction m generalizing z with
  | zero => exact ENNReal.one_ne_top
  | succ m ih =>
    apply ENNReal.mul_ne_top _ (ih _ _ _ _)
    unfold Radial.transition Set.indicator
    split_ifs <;> simp

/-- Interior-start conditioned trace densities from the exact killed kernels. -/
lemma scaledTrace_limit_positive (m : ℕ) {d b : ℕ → Fin m → ℕ} {R T a : ℕ → ℕ}
    {s x : Fin m → ℝ} {r z : ℝ}
    (hr : 0<r) (hz : 0<z) (hs : ∀ i,0<s i) (hx : ∀ i,0<x i)
    (hR : Tendsto R atTop atTop) (hT : Tendsto T atTop atTop)
    (hd : ∀ i,Tendsto (fun n => d n i) atTop atTop)
    (hrR : Tendsto (fun n => ((R n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 r))
    (hrd : ∀ i,Tendsto (fun n => (d n i:ℝ)/(T n:ℝ)) atTop (𝓝 (s i)))
    (hRe : ∀ n,Even (R n)) (hde : ∀ n i,Even (d n i))
    (hae : ∀ n,Even (a n)) (hbe : ∀ n i,Even (b n i))
    (ha : Tendsto (fun n => (a n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 z))
    (hb : ∀ i,Tendsto (fun n => (b n i:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 (x i))) :
    Tendsto (fun n => ENNReal.ofReal ((Real.sqrt (T n:ℝ)/2)^m*
      normalizedTrace (a n) (R n) (d n) (b n))) atTop
      (𝓝 (Radial.chainDensity z (durationRatio s r) (durationVariance s r) x)) := by
  induction m generalizing R T a r z with
  | zero =>
    have hne := firstHit_eventually_ne_zero hr hz hR hT hrR hRe hae ha
    apply tendsto_const_nhds.congr'
    filter_upwards [hne] with n hn
    have he : (∑ i : Fin 0,d n i)=0 := Fin.sum_univ_zero _
    simp only [normalizedTrace]
    rw [he,Nat.zero_add]
    simp only [segments,List.ofFn_zero,traceKilledWeight,pow_zero,one_mul,div_self hn,ENNReal.ofReal_one,Radial.chainDensity]
  | succ m ih =>
    let R' : ℕ → ℕ := fun n => (∑ i,Fin.tail (d n) i)+R n
    let t : ℝ := (∑ i,Fin.tail s i)+r
    have ht : 0<t := add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => (hs i.succ).le)) hr
    have hR' : Tendsto R' atTop atTop := tendsto_atTop_mono (fun n => Nat.le_add_left _ _) hR
    have hrR' : Tendsto (fun n => ((R' n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t) := by
      convert (sum_ratio_tendsto (fun i => hrd i.succ)).add hrR using 1 <;>
      simp [R',t,Nat.cast_add,add_div,add_assoc,Fin.tail_def]
    have hRe' (n : ℕ) : Even (R' n) :=
      (Finset.even_sum (fun i : Fin m => Fin.tail (d n) i) (fun i _ => hde n i.succ)).add (hRe n)
    have hk := conditioned_kernel_limit (hs 0) ht hz (hd 0) hR' hT (hrd 0) hrR'
      (Filter.Eventually.of_forall (fun n => ((even_int_cast (hde n 0)).add
        (even_int_cast (hbe n 0))).sub (even_int_cast (hae n))))
      (Filter.Eventually.of_forall (fun n => even_int_terminal (hRe' n) (hbe n 0)))
      (Filter.Eventually.of_forall (fun n => even_int_terminal ((hde n 0).add (hRe' n)) (hae n)))
      ha (hb 0)
    have hh := ih hr (hx 0) (fun i => hs i.succ) (fun i => hx i.succ) hR hT
      (fun i => hd i.succ) hrR (fun i => hrd i.succ) hRe (fun n i => hde n i.succ)
      (fun n => hbe n 0) (fun n i => hbe n i.succ) (hb 0) (fun i => hb i.succ)
    have hne := firstHit_eventually_ne_zero ht (hx 0) hR' hT hrR' hRe' (fun n => hbe n 0) (hb 0)
    have hlim := ENNReal.Tendsto.mul (ENNReal.continuous_ofReal.tendsto _ |>.comp hk)
      (Or.inr (chainDensity_ne_top _ _ _ _ _)) hh (Or.inr ENNReal.ofReal_ne_top)
    have hcoef : |t/(s 0+t)|=t/(s 0+t) := abs_of_pos (div_pos ht (add_pos (hs 0) ht))
    have htarget : Radial.transition (durationVariance s r 0)
        (|durationRatio s r 0| *z) (x 0)=
        ENNReal.ofReal (radialHeat (s 0*t/(s 0+t)) (t/(s 0+t)*z) (x 0)) := by
      rw [Radial.transition,indicator_of_mem (show x 0∈Ioi (0:ℝ) from hx 0)]
      simp only [durationVariance,durationRatio,remaining_zero]
      rw [hcoef]
    have heta : Fin.tail (durationRatio s r)=durationRatio (Fin.tail s) r := by
      funext i
      simp only [Fin.tail_def,durationRatio,remaining_succ]
    have hetv : Fin.tail (durationVariance s r)=durationVariance (Fin.tail s) r := by
      funext i
      simp only [Fin.tail_def,durationVariance,remaining_succ]
    change Tendsto _ atTop (𝓝 (Radial.transition (durationVariance s r 0)
      (|durationRatio s r 0| *z) (x 0)*
      Radial.chainDensity (x 0) (Fin.tail (durationRatio s r)) (Fin.tail (durationVariance s r)) (Fin.tail x)))
    rw [htarget,heta,hetv]
    apply hlim.congr'
    filter_upwards [hne] with n hn
    rw [normalizedTrace_cons _ _ _ _ hn,pow_succ]
    simp only [Function.comp_apply]
    rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity)
      (div_nonneg (mul_nonneg (killed_nonneg _ _ _) (pathMass_nonneg _ _)) (pathMass_nonneg _ _)))]
    congr 1
    simp only [R']
    simp +unfoldPartialApp only [Fin.tail_def]
    ring

/-- Entrance-start trace densities, including the singular zero-radius initial law. -/
lemma scaledTrace_limit_zero (m : ℕ) {d b : ℕ → Fin m → ℕ} {R T : ℕ → ℕ}
    {s x : Fin m → ℝ} {r : ℝ}
    (hr : 0<r) (hs : ∀ i,0<s i) (hx : ∀ i,0<x i)
    (hR : Tendsto R atTop atTop) (hT : Tendsto T atTop atTop)
    (hd : ∀ i,Tendsto (fun n => d n i) atTop atTop)
    (hrR : Tendsto (fun n => ((R n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 r))
    (hrd : ∀ i,Tendsto (fun n => (d n i:ℝ)/(T n:ℝ)) atTop (𝓝 (s i)))
    (hRe : ∀ n,Even (R n)) (hde : ∀ n i,Even (d n i))
    (hbe : ∀ n i,Even (b n i))
    (hb : ∀ i,Tendsto (fun n => (b n i:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 (x i))) :
    Tendsto (fun n => ENNReal.ofReal ((Real.sqrt (T n:ℝ)/2)^m*
      normalizedTrace 0 (R n) (d n) (b n))) atTop
      (𝓝 (Radial.chainDensity 0 (durationRatio s r) (durationVariance s r) x)) := by
  cases m with
  | zero =>
    have hl := firstHit_zero_scaled_limit hr hR hT hrR
      (Filter.Eventually.of_forall (fun n => by
        simpa using even_int_terminal (hRe n) (by norm_num : Even 0)))
    have hp : 0<2/r*heat r 0 := mul_pos (div_pos (by norm_num) hr) (heat_pos hr 0)
    have hne : ∀ᶠ n in atTop,pathMass (R n+1) (firstHit 0)≠0 := by
      filter_upwards [hl.eventually (eventually_ne_nhds hp.ne')] with n hn
      exact fun h => hn (by simp only [h,mul_zero])
    apply tendsto_const_nhds.congr'
    filter_upwards [hne] with n hn
    have he : (∑ i : Fin 0,d n i)=0 := Fin.sum_univ_zero _
    simp only [normalizedTrace]
    rw [he,Nat.zero_add]
    simp only [segments,List.ofFn_zero,traceKilledWeight,pow_zero,one_mul,div_self hn,ENNReal.ofReal_one,Radial.chainDensity]
  | succ m =>
    let R' : ℕ → ℕ := fun n => (∑ i,Fin.tail (d n) i)+R n
    let t : ℝ := (∑ i,Fin.tail s i)+r
    have ht : 0<t := add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => (hs i.succ).le)) hr
    have hR' : Tendsto R' atTop atTop := tendsto_atTop_mono (fun n => Nat.le_add_left _ _) hR
    have hrR' : Tendsto (fun n => ((R' n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t) := by
      convert (sum_ratio_tendsto (fun i => hrd i.succ)).add hrR using 1 <;>
      simp [R',t,Nat.cast_add,add_div,add_assoc,Fin.tail_def]
    have hRe' (n : ℕ) : Even (R' n) :=
      (Finset.even_sum (fun i : Fin m => Fin.tail (d n) i) (fun i _ => hde n i.succ)).add (hRe n)
    have hk := entrance_conditioned_limit (hs 0) ht (hd 0) hR' hT (hrd 0) hrR'
      (Filter.Eventually.of_forall (fun n => (even_int_cast (hde n 0)).add
        (even_int_cast (hbe n 0))))
      (Filter.Eventually.of_forall (fun n => even_int_terminal (hRe' n) (hbe n 0)))
      (Filter.Eventually.of_forall (fun n => by
        simpa using even_int_terminal ((hde n 0).add (hRe' n)) (by norm_num : Even 0)))
      (hb 0)
    have hh := scaledTrace_limit_positive m hr (hx 0) (fun i => hs i.succ) (fun i => hx i.succ) hR hT
      (fun i => hd i.succ) hrR (fun i => hrd i.succ) hRe (fun n i => hde n i.succ)
      (fun n => hbe n 0) (fun n i => hbe n i.succ) (hb 0) (fun i => hb i.succ)
    have hne := firstHit_eventually_ne_zero ht (hx 0) hR' hT hrR' hRe' (fun n => hbe n 0) (hb 0)
    have hlim := ENNReal.Tendsto.mul (ENNReal.continuous_ofReal.tendsto _ |>.comp hk)
      (Or.inr (chainDensity_ne_top _ _ _ _ _)) hh (Or.inr ENNReal.ofReal_ne_top)
    have htarget : Radial.transition (durationVariance s r 0)
        (|durationRatio s r 0| *0) (x 0)=
        ENNReal.ofReal (radialHeat (s 0*t/(s 0+t)) 0 (x 0)) := by
      rw [Radial.transition,indicator_of_mem (show x 0∈Ioi (0:ℝ) from hx 0)]
      simp only [durationVariance,durationRatio,remaining_zero]
      simp only [mul_zero]
      rfl
    have heta : Fin.tail (durationRatio s r)=durationRatio (Fin.tail s) r := by
      funext i
      simp only [Fin.tail_def,durationRatio,remaining_succ]
    have hetv : Fin.tail (durationVariance s r)=durationVariance (Fin.tail s) r := by
      funext i
      simp only [Fin.tail_def,durationVariance,remaining_succ]
    change Tendsto _ atTop (𝓝 (Radial.transition (durationVariance s r 0)
      (|durationRatio s r 0| *0) (x 0)*
      Radial.chainDensity (x 0) (Fin.tail (durationRatio s r)) (Fin.tail (durationVariance s r)) (Fin.tail x)))
    rw [htarget,heta,hetv]
    apply hlim.congr'
    filter_upwards [hne] with n hn
    rw [normalizedTrace_cons _ _ _ _ hn,pow_succ]
    simp only [Function.comp_apply]
    rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity)
      (div_nonneg (mul_nonneg (killed_nonneg _ _ _) (pathMass_nonneg _ _)) (pathMass_nonneg _ _)))]
    congr 1
    simp only [R']
    simp +unfoldPartialApp only [Fin.tail_def]
    ring

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma sum_differences_nat {m : ℕ} (g : Fin (m+1) → ℕ) (hg : Monotone g) :
    (∑ i : Fin m,(g i.succ-g i.castSucc))=g (Fin.last m)-g 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have hh := ih (Fin.tail g) (hg.comp (fun _ _ h => Fin.succ_le_succ_iff.mpr h))
    simp only [Fin.tail_def,Fin.succ_castSucc] at hh
    rw [hh]
    have h0 := hg (show (0:Fin (m+2))≤(0:Fin (m+1)).succ by exact Fin.zero_le _)
    have h1 := hg (Fin.le_last ((0:Fin (m+1)).succ))
    change (g (Fin.succ 0)-g 0)+(g (Fin.last (m+1))-g (Fin.succ 0))=
      g (Fin.last (m+1))-g 0
    change g 0≤g (Fin.succ 0) at h0
    change g (Fin.succ 0)≤g (Fin.last (m+1)) at h1
    omega

lemma located_differences {m : ℕ} (g : Fin (m+1) → ℕ) (hg : Monotone g)
    (b : Fin m → ℕ) :
    located (segments (fun i => g i.succ-g i.castSucc) b)=
      List.ofFn (fun i => (g i.succ-g 0,b i)) := by
  induction m with
  | zero => simp [segments,located]
  | succ m ih =>
    rw [segments_cons,located]
    have hh := ih (Fin.tail g) (hg.comp (fun _ _ h => Fin.succ_le_succ_iff.mpr h)) (Fin.tail b)
    simp +unfoldPartialApp only [Fin.tail_def,Fin.succ_castSucc] at hh ⊢
    rw [hh,List.ofFn_succ,List.map_ofFn]
    congr 1
    congr 1
    funext i
    have h0 := hg (show (0:Fin (m+2))≤(0:Fin (m+1)).succ by exact Fin.zero_le _)
    have h1 := hg (show (0 : Fin (m+1)).succ ≤ i.succ.succ from Fin.succ_le_succ_iff.mpr (Fin.zero_le _))
    simp only [Function.comp_apply,Fin.castSucc_zero]
    congr 1
    omega

lemma sum_gridDurations {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) :
    (∑ i,gridDurations u n i)=evenGrid n (u (Fin.last m)) := by
  have hh := sum_differences_nat (fun i => evenGrid n (u i))
    (fun _ _ h => evenGrid_mono n (hu h))
  simpa only [gridDurations,h0,(show ((0:unitInterval):ℝ)=0 from rfl),evenGrid_zero,Nat.sub_zero] using hh

lemma grid_total {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) :
    (∑ i,gridDurations u n i)+gridRemainder u n+1=2*n+1 := by
  rw [sum_gridDurations u hu h0,gridRemainder]
  have h := evenGrid_le n (u (Fin.last m)).property.2
  omega

lemma grid_observed {N m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) (b : Fin m → ℕ) (d : Path N) :
    observed 0 (segments (gridDurations u n) b) d↔
      ∀ i,pathSum d (evenGrid n (u i.succ))=(b i:ℤ) := by
  have hh := located_differences (fun i => evenGrid n (u i))
    (fun _ _ h => evenGrid_mono n (hu h)) b
  unfold observed
  rw [show located (segments (gridDurations u n) b)=_ from hh]
  simp only [h0,(show ((0:unitInterval):ℝ)=0 from rfl),evenGrid_zero,Nat.sub_zero,List.mem_ofFn,
    forall_exists_index,forall_apply_eq_imp_iff,Int.natCast_zero,zero_add]

lemma gridRemainder_ratio {m : ℕ} (u : Fin (m+1) → unitInterval) :
    Tendsto (fun n => ((gridRemainder u n:ℝ)+1)/((2*n+1:ℕ):ℝ)) atTop
      (𝓝 (1-(u (Fin.last m):ℝ))) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).sub (evenGrid_ratio (u (Fin.last m)) (u (Fin.last m)).property.1)
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro n
  dsimp only [gridRemainder]
  rw [Nat.cast_sub (evenGrid_le n (u (Fin.last m)).property.2)]
  have hp : ((2*n+1:ℕ):ℝ)≠0 := by positivity
  field_simp
  push_cast
  ring

lemma nat_atTop_of_ratio {A B : ℕ → ℕ} {r : ℝ} (hr : 0<r)
    (hB : Tendsto B atTop atTop)
    (h : Tendsto (fun n => (A n:ℝ)/(B n:ℝ)) atTop (𝓝 r)) :
    Tendsto A atTop atTop := by
  have hB' : Tendsto (fun n => (B n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hB
  have hm := Filter.Tendsto.pos_mul_atTop hr h hB'
  have hB0 : ∀ᶠ n in atTop,(B n:ℝ)≠0 := (hB'.eventually_gt_atTop 0).mono (fun _ h => h.ne')
  have hh : Tendsto (fun n => (A n:ℝ)) atTop atTop := hm.congr' (by
    filter_upwards [hB0] with n hn
    exact div_mul_cancel₀ _ hn)
  exact tendsto_natCast_atTop_iff.mp hh

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open TreeCoding

def bridgeRatio (a b : unitInterval) : ℝ := (1-(b:ℝ))/(1-(a:ℝ))
def bridgeVariance (a b : unitInterval) : ℝ := ((b:ℝ)-(a:ℝ))*(1-(b:ℝ))/(1-(a:ℝ))
def bridgeResidual {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (a b : unitInterval) (ω : Ω) : ℝ :=
  bridgeAt B b ω-bridgeRatio a b*bridgeAt B a ω

lemma bridgeRatio_pos {a b : unitInterval} (hab : a<b) (hb : (b:ℝ)<1) :
    0<bridgeRatio a b := by
  have ha : (a:ℝ)<1 := lt_trans hab hb
  exact div_pos (sub_pos.mpr hb) (sub_pos.mpr ha)

lemma bridgeVariance_pos {a b : unitInterval} (hab : a<b) (hb : (b:ℝ)<1) :
    0<bridgeVariance a b := by
  have ha : (a:ℝ)<1 := lt_trans hab hb
  exact div_pos (mul_pos (sub_pos.mpr hab) (sub_pos.mpr hb)) (sub_pos.mpr ha)

lemma bridgeResidual_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsGaussianProcess (fun p : unitInterval×unitInterval => bridgeResidual B p.1 p.2) P := by
  classical
  apply (bridgeAt_gaussian hB).of_isGaussianProcess
  intro p
  refine ⟨{p.1,p.2},
    { toFun x := x ⟨p.2,by simp⟩-bridgeRatio p.1 p.2*x ⟨p.1,by simp⟩
      map_add' x y := by simp only [Pi.add_apply]; ring
      map_smul' c x := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring},?_⟩
  intro ω
  rfl

lemma integral_bridgeResidual {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a b : unitInterval) :
    P[bridgeResidual B a b]=0 := by
  have hg := bridgeAt_gaussian hB
  unfold bridgeResidual
  rw [integral_sub (hg.hasGaussianLaw_eval _).integrable
    ((hg.hasGaussianLaw_eval _).integrable.const_mul _),integral_const_mul]
  simp only [integral_bridgeAt hB,mul_zero,sub_zero]

lemma covariance_bridgeResidual_earlier {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {s a b : unitInterval} (hsa : s≤a) (hab : a≤b) (ha : (a:ℝ)<1) :
    cov[bridgeResidual B a b,bridgeAt B s;P]=0 := by
  have hg := bridgeAt_gaussian hB
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  unfold bridgeResidual
  rw [covariance_fun_sub_left (hg.hasGaussianLaw_eval _).memLp_two
    ((hg.hasGaussianLaw_eval _).memLp_two.const_mul _) (hg.hasGaussianLaw_eval _).memLp_two,
    covariance_const_mul_left,covariance_bridgeAt hB,covariance_bridgeAt hB]
  change bbCov (b:ℝ) (s:ℝ)-bridgeRatio a b*bbCov (a:ℝ) (s:ℝ)=0
  rw [bbCov,bbCov,min_eq_right (show (s:ℝ)≤b from hsa.trans hab),min_eq_right (show (s:ℝ)≤a from hsa)]
  unfold bridgeRatio
  have ha0 : 1-(a:ℝ)≠0 := ne_of_gt (sub_pos.mpr ha)
  field_simp
  ring

lemma variance_bridgeResidual {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {a b : unitInterval} (hab : a≤b) (ha : (a:ℝ)<1) :
    Var[bridgeResidual B a b;P]=bridgeVariance a b := by
  have hg := bridgeAt_gaussian hB
  have hr := (bridgeResidual_gaussian hB).hasGaussianLaw_eval (a,b)
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [← covariance_self hr.aemeasurable]
  change cov[bridgeResidual B a b,fun ω => bridgeAt B b ω-bridgeRatio a b*bridgeAt B a ω;P]=_
  rw [covariance_fun_sub_right hr.memLp_two (hg.hasGaussianLaw_eval _).memLp_two
    ((hg.hasGaussianLaw_eval _).memLp_two.const_mul _),covariance_const_mul_right,
    covariance_bridgeResidual_earlier hB le_rfl hab ha,mul_zero,sub_zero]
  unfold bridgeResidual
  rw [covariance_fun_sub_left (hg.hasGaussianLaw_eval _).memLp_two
    ((hg.hasGaussianLaw_eval _).memLp_two.const_mul _) (hg.hasGaussianLaw_eval _).memLp_two,
    covariance_const_mul_left,covariance_bridgeAt hB,covariance_bridgeAt hB]
  change bbCov (b:ℝ) (b:ℝ)-bridgeRatio a b*bbCov (a:ℝ) (b:ℝ)=_
  rw [bbCov,bbCov,min_self,min_eq_left (show (a:ℝ)≤b from hab)]
  unfold bridgeRatio bridgeVariance
  have ha0 : 1-(a:ℝ)≠0 := ne_of_gt (sub_pos.mpr ha)
  field_simp
  ring

lemma bridgeResidual_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {a b : unitInterval} (hab : a<b) (hb : (b:ℝ)<1) :
    HasLaw (bridgeResidual B a b) (gaussianReal 0 (bridgeVariance a b).toNNReal) P := by
  have hr := (bridgeResidual_gaussian hB).hasGaussianLaw_eval (a,b)
  refine ⟨hr.aemeasurable,?_⟩
  rw [hr.map_eq_gaussianReal,integral_bridgeResidual hB,
    variance_bridgeResidual hB hab.le (lt_trans hab hb)]

/-- The standardized regression innovations at arbitrary increasing interior times. -/
def innovation {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (i : Fin m) (ω : Ω) : ℝ :=
  (Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹*
    bridgeResidual B (u i.castSucc) (u i.succ) ω

lemma innovation_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u)
    (h1 : ∀ i,(u i:ℝ)<1) (i : Fin m) :
    HasLaw (innovation B u i) (gaussianReal 0 1) P := by
  have hij := hu i.castSucc_lt_succ
  have hv := bridgeVariance_pos hij (h1 _)
  have hh := gaussianReal_const_mul (bridgeResidual_hasLaw hB hij (h1 _))
    ((Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹)
  have hvar : NNReal.mk ((Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹^2)
      (sq_nonneg _)*(bridgeVariance (u i.castSucc) (u i.succ)).toNNReal=1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_one,NNReal.coe_mul,NNReal.coe_mk,Real.coe_toNNReal _ hv.le,
      inv_pow,Real.sq_sqrt hv.le]
    exact inv_mul_cancel₀ hv.ne'
  change HasLaw (fun ω => (Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹*
    bridgeResidual B (u i.castSucc) (u i.succ) ω) (gaussianReal 0 1) P
  simpa only [mul_zero,hvar] using hh

lemma innovations_independent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u) (h1 : ∀ i,(u i:ℝ)<1) :
    iIndepFun (innovation B u) P := by
  classical
  have hg := bridgeAt_gaussian hB
  let L : ({x // x∈(Finset.univ : Finset (Fin (m+1)))} → ℝ) →L[ℝ] (Fin m → ℝ) :=
    { toFun x i := (Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹*
        (x ⟨i.succ,by simp⟩-bridgeRatio (u i.castSucc) (u i.succ)*x ⟨i.castSucc,by simp⟩)
      map_add' x y := by ext i; simp only [Pi.add_apply]; ring
      map_smul' c x := by ext i; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring }
  have hjoint : HasGaussianLaw (fun ω i => innovation B u i ω) P :=
    ((hg.comp_right u).hasGaussianLaw Finset.univ).map L
  apply hjoint.iIndepFun_of_covariance_eq_zero
  intro i j hij
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hh (i j : Fin m) (hij : i<j) :
      cov[innovation B u j,innovation B u i;P]=0 := by
    have hr := (bridgeResidual_gaussian hB).hasGaussianLaw_eval (u j.castSucc,u j.succ)
    unfold innovation
    rw [covariance_const_mul_left,covariance_const_mul_right]
    have he : cov[bridgeResidual B (u j.castSucc) (u j.succ),
        bridgeResidual B (u i.castSucc) (u i.succ);P]=0 := by
      change cov[bridgeResidual B (u j.castSucc) (u j.succ),
        fun ω => bridgeAt B (u i.succ) ω-bridgeRatio (u i.castSucc) (u i.succ)*bridgeAt B (u i.castSucc) ω;P]=0
      rw [covariance_fun_sub_right hr.memLp_two (hg.hasGaussianLaw_eval _).memLp_two
        ((hg.hasGaussianLaw_eval _).memLp_two.const_mul _),covariance_const_mul_right,
        covariance_bridgeResidual_earlier hB (hu.monotone (by exact_mod_cast hij))
          (hu.monotone j.castSucc_lt_succ.le) (h1 _),
        covariance_bridgeResidual_earlier hB (hu.monotone (by exact_mod_cast hij.le))
          (hu.monotone j.castSucc_lt_succ.le) (h1 _)]
      ring
    rw [he,mul_zero,mul_zero]
  rcases lt_or_gt_of_ne hij with h|h
  · rw [covariance_comm]; exact hh i j h
  · exact hh j i h

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open TreeCoding

lemma innovations_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u) (h1 : ∀ i,(u i:ℝ)<1) :
    HasGaussianLaw (fun ω i => innovation B u i ω) P :=
  (innovations_independent hB u hu h1).hasGaussianLaw
    (fun i => (innovation_hasLaw hB u hu h1 i).hasGaussianLaw)

lemma independent_innovations {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ}
    (hB : iIndepFun (fun i ω t => B i t ω) P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) :
    iIndepFun (fun k ω i => innovation (B k) u i ω) P := by
  let f : (ℝ≥0 → ℝ) → (Fin m → ℝ) := fun x i =>
    (Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹*
      (x ⟨(u i.succ:ℝ),(u i.succ).property.1⟩-(u i.succ:ℝ)*x 1-
       bridgeRatio (u i.castSucc) (u i.succ)*
       (x ⟨(u i.castSucc:ℝ),(u i.castSucc).property.1⟩-(u i.castSucc:ℝ)*x 1))
  have hf : Measurable f := by fun_prop
  exact hB.comp (fun _ => f) (fun _ => hf)

/-- Regression innovations are independent not only in time but across the three
source Brownian coordinates; no radial-process theorem is taken as an assumption. -/
theorem vector_innovations_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ k,IsPreBrownianReal (B k) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u) (h1 : ∀ i,(u i:ℝ)<1) :
    HasLaw (fun ω i => (toLp 2 (fun k => innovation (B k) u i ω) : Space))
      (Measure.pi (fun _ : Fin m => stdGaussian Space)) P := by
  have hrows := independent_innovations hI u
  have hrowg := hrows.hasGaussianLaw (fun k => innovations_gaussian (hB k) u hu h1)
  let L : (Fin 3 → Fin m → ℝ) →L[ℝ] (Fin m → Fin 3 → ℝ) :=
    { toFun x i k := x k i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hg : HasGaussianLaw (fun ω i k => innovation (B k) u i ω) P := hrowg.map L
  have hin (k : Fin 3) := innovations_independent (hB k) u hu h1
  have hl (k : Fin 3) (i : Fin m) := innovation_hasLaw (hB k) u hu h1 i
  have hcol : iIndepFun (fun i ω k => innovation (B k) u i ω) P := by
    apply hg.iIndepFun_of_covariance_eval
    intro i j hij k l
    apply IndepFun.covariance_eq_zero _ (hl k i).hasGaussianLaw.memLp_two
      (hl l j).hasGaussianLaw.memLp_two
    by_cases hkl : k=l
    · subst l
      exact (hin k).indepFun hij
    · exact (hrows.indepFun hkl).comp (measurable_pi_apply i) (measurable_pi_apply j)
  have hlcol (i : Fin m) :
      HasLaw (fun ω => (toLp 2 (fun k => innovation (B k) u i ω) : Space)) (stdGaussian Space) P := by
    have hi := hrows.comp (fun _ x => x i) (fun _ => measurable_pi_apply i)
    have hr := hi.hasLaw_pi (fun k => hl k i)
    have hs : HasLaw (toLp 2 : (Fin 3 → ℝ) → Space) (stdGaussian Space)
        (Measure.pi (fun _ => gaussianReal 0 1)) :=
      ⟨(by fun_prop),map_pi_eq_stdGaussian⟩
    exact hs.comp hr
  exact (hcol.comp (fun _ => (toLp 2 : (Fin 3 → ℝ) → Space)) (by fun_prop)).hasLaw_pi hlcol

/-- Reconstruction of a chronological chain from its standardized innovations. -/
lemma chain_reconstruct (m : ℕ) (x : Fin (m+1) → Space) (a t : Fin m → ℝ)
    (ht : ∀ i,0<t i) :
    chain (x 0) a t (fun i => (Real.sqrt (t i))⁻¹ • (x i.succ-a i • x i.castSucc)) =
      Fin.tail x := by
  induction m with
  | zero => exact Subsingleton.elim _ _
  | succ m ih =>
    have ht0 : Real.sqrt (t 0)≠0 := ne_of_gt (Real.sqrt_pos.mpr (ht 0))
    have hw : a 0 • x 0+Real.sqrt (t 0) •
        ((Real.sqrt (t 0))⁻¹ • (x (Fin.succ 0)-a 0 • x 0))=x (Fin.succ 0) := by
      rw [smul_smul,mul_inv_cancel₀ ht0,one_smul,add_sub_cancel]
    have hh := ih (Fin.tail x) (Fin.tail a) (Fin.tail t) (fun i => ht i.succ)
    apply funext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hw
    · change chain (a 0 • x 0+Real.sqrt (t 0) •
          ((Real.sqrt (t 0))⁻¹ • (x (Fin.succ 0)-a 0 • x 0)))
        (Fin.tail a) (Fin.tail t) _ j=(Fin.tail (Fin.tail x)) j
      rw [hw]
      exact congrFun hh j

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open TreeCoding SimpleWalk

def bridgeVector {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) (u : unitInterval) (ω : Ω) : Space :=
  toLp 2 (fun k => bridgeAt (B k) u ω)

def bridgeDensity {m : ℕ} (u : Fin (m+1) → unitInterval) (x : Fin m → ℝ) : ℝ≥0∞ :=
  chainDensity 0 (fun i => bridgeRatio (u i.castSucc) (u i.succ))
    (fun i => bridgeVariance (u i.castSucc) (u i.succ)) x

lemma vector_residual {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (i : Fin m) (ω : Ω) :
    (Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹ •
      (bridgeVector B (u i.succ) ω-bridgeRatio (u i.castSucc) (u i.succ) •
        bridgeVector B (u i.castSucc) ω)=
      toLp 2 (fun k => innovation (B k) u i ω) := by
  ext k
  rfl

lemma norm_bridgeVector {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ)
    (u : unitInterval) (ω : Ω) : ‖bridgeVector B u ω‖=standardExcursion B ω u := by
  have h := EuclideanSpace.real_norm_sq_eq (bridgeVector B u ω)
  change ‖bridgeVector B u ω‖ ^ 2 = ∑ k : Fin 3, (bridgeAt (B k) u ω)^2 at h
  have hs : 0≤∑ k : Fin 3,(bridgeAt (B k) u ω)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [standardExcursion]
  change ‖bridgeVector B u ω‖=Real.sqrt (∑ k : Fin 3,(bridgeAt (B k) u ω)^2)
  have he := Real.sq_sqrt hs
  nlinarith [norm_nonneg (bridgeVector B u ω),Real.sqrt_nonneg (∑ k : Fin 3,(bridgeAt (B k) u ω)^2)]

/-- Exact finite-dimensional density of the source standard excursion (the norm
of three independent bridges), at every increasing collection of interior times. -/
theorem lintegral_standardExcursion {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ k,IsPreBrownianReal (B k) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u)
    (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1)
    (F : (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω,F (fun i => standardExcursion B ω (u i.succ)) ∂P)=
      ∫⁻ x,F x*bridgeDensity u x := by
  let a : Fin m → ℝ := fun i => bridgeRatio (u i.castSucc) (u i.succ)
  let t : Fin m → ℝ := fun i => bridgeVariance (u i.castSucc) (u i.succ)
  have ht (i : Fin m) : 0<t i := bridgeVariance_pos (hu i.castSucc_lt_succ) (h1 _)
  have hl := vector_innovations_law hB hI u hu h1
  have he : ∀ᵐ ω ∂P,chain 0 a t (fun i => toLp 2 (fun k => innovation (B k) u i ω))=
      fun i => bridgeVector B (u i.succ) ω := by
    have hz : ∀ᵐ ω ∂P,∀ k,B k 0 ω=0 := ae_all_iff.mpr (fun k => (hB k).eval_zero_ae_eq_zero)
    filter_upwards [hz] with ω hω
    have hx : bridgeVector B (u 0) ω=0 := by
      rw [h0]
      ext k
      change B k (0:ℝ≥0) ω - (0:ℝ) * B k 1 ω = 0
      rw [hω k]
      ring
    have hh := chain_reconstruct m (fun i => bridgeVector B (u i) ω) a t ht
    rw [hx] at hh
    apply funext
    intro i
    simpa only [a,t,vector_residual,Fin.tail_def] using congrFun hh i
  have hFn : Measurable (fun z : Fin m → Space => F (fun i => ‖chain 0 a t z i‖)) := by
    have hc : Measurable (chain 0 a t) := ((continuous_chain m a t).comp
      (show Continuous (fun z : Fin m → Space => ((0:Space),z)) from by fun_prop)).measurable
    exact hF.comp (by fun_prop)
  calc
    _=(∫⁻ ω,F (fun i => ‖chain 0 a t (fun j => toLp 2 (fun k => innovation (B k) u j ω)) i‖) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω]
      simp only [norm_bridgeVector]
    _=∫⁻ z,F (fun i => ‖chain 0 a t z i‖) ∂Measure.pi (fun _ => stdGaussian Space) :=
      hl.lintegral_comp hFn.aemeasurable
    _=_ := by simpa only [norm_zero,bridgeDensity,a,t] using lintegral_chain m 0 a t ht F hF

lemma measurable_bridgeDensity {m : ℕ} (u : Fin (m+1) → unitInterval) :
    Measurable (bridgeDensity u) :=
  (measurable_chainDensity m _ _).comp
    (show Measurable (fun x : Fin m → ℝ => ((0:ℝ),x)) from by fun_prop)

end FKCRT.Radial
end

end OAI
