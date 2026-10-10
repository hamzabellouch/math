import Mathlib
import OAI.Probability.ParisiFinite.TerminalThird

namespace OAI

/-! Nnwidth. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Function
open scoped Topology NNReal ENNReal
namespace ParisiFinite

 
def nnwidth : Schedule → ℝ≥0
  | [] => 0
  | (_,d)::ls => d+nnwidth ls

lemma coe_nnwidth (ls : Schedule) : (nnwidth ls : ℝ) = width ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [nnwidth,width,ih]

@[simp] lemma nnwidth_append (ls rs : Schedule) :
    nnwidth (ls++rs) = nnwidth ls+nnwidth rs := by
  induction ls with
  | nil => simp [nnwidth]
  | cons l ls ih => simp [nnwidth,ih,add_assoc]

 

def scheduleValue : Schedule → ℝ≥0 → ℝ≥0
  | [],_ => 0
  | (a,d)::ls,t => if t < d then a else scheduleValue ls (t-d)

@[simp] lemma scheduleValue_zero_cons (a : ℝ≥0) (ls : Schedule) (t : ℝ≥0) :
    scheduleValue ((a,0)::ls) t = scheduleValue ls t := by
  simp [scheduleValue]

@[simp] lemma scheduleValue_cons_shift (a d : ℝ≥0) (ls : Schedule) (t : ℝ≥0) :
    scheduleValue ((a,d)::ls) (d+t) = scheduleValue ls t := by
  simp [scheduleValue,not_lt.mpr (show d ≤ d+t from le_add_of_nonneg_right zero_le)]

lemma scheduleValue_split_shift (a d e : ℝ≥0) (hde : d ≤ e)
    (ls : Schedule) (t : ℝ≥0) :
    scheduleValue ((a,e)::ls) (d+t) = scheduleValue ((a,e-d)::ls) t := by
  have he : d+(e-d)=e := add_tsub_cancel_of_le hde
  have hc : d+t < e ↔ t < e-d := by
    exact lt_tsub_iff_left.symm
  simp only [scheduleValue,hc]
  split_ifs with ht
  · rfl
  · congr 1
    calc (d+t)-e = (d+t)-(d+(e-d)) := by rw [he]
         _ = t-(e-d) := add_tsub_add_eq_tsub_left _ _ _

lemma scheduleValue_append_left (ls rs : Schedule) (t : ℝ≥0)
    (ht : t < nnwidth ls) : scheduleValue (ls++rs) t = scheduleValue ls t := by
  induction ls generalizing t with
  | nil => simp [nnwidth] at ht
  | cons l ls ih =>
    simp only [nnwidth] at ht
    simp only [List.cons_append,scheduleValue]
    split_ifs with htd
    · rfl
    · apply ih
      exact (tsub_lt_iff_left (le_of_not_gt htd)).mpr ht

lemma scheduleValue_append_right (ls rs : Schedule) (t : ℝ≥0) :
    scheduleValue (ls++rs) (nnwidth ls+t) = scheduleValue rs t := by
  induction ls with
  | nil => simp [nnwidth]
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    simp only [nnwidth,List.cons_append,add_assoc,scheduleValue_cons_shift,ih]

@[simp] lemma evolve_zero_cons (a : ℝ≥0) (ls : Schedule) (f : ℝ → ℝ) :
    evolve ((a,0)::ls) f = evolve ls f := by
  funext x
  simp [evolve]

lemma evolve_of_nnwidth_zero (ls : Schedule) (hls : nnwidth ls=0) (f : ℝ → ℝ) :
    evolve ls f=f := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    have hh : l.2=0 ∧ nnwidth ls=0 := add_eq_zero.mp hls
    obtain ⟨a,d⟩ := l
    simp only at hh
    rw [hh.1,evolve_zero_cons,ih hh.2]

 

lemma evolve_le_of_scheduleValue_le {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (ls rs : Schedule) (hw : nnwidth ls=nnwidth rs)
    (hle : ∀ t, t < nnwidth ls → scheduleValue ls t ≤ scheduleValue rs t) (x : ℝ) :
    evolve ls f x  ≤  evolve rs f x := by
  cases ls with
  | nil =>
    rw [evolve_of_nnwidth_zero rs hw.symm f]
    exact le_rfl
  | cons l ls =>
    obtain ⟨a,d⟩ := l
    cases rs with
    | nil =>
      rw [evolve_of_nnwidth_zero ((a,d)::ls) hw f]
      exact le_rfl
    | cons r rs =>
      obtain ⟨b,e⟩ := r
      by_cases hd : d=0
      · subst d
        rw [evolve_zero_cons]
        apply evolve_le_of_scheduleValue_le hf ls ((b,e)::rs) (by simpa [nnwidth] using hw)
        intro t ht
        simpa using hle t (by simpa [nnwidth] using ht)
      by_cases he : e=0
      · subst e
        rw [evolve_zero_cons]
        apply evolve_le_of_scheduleValue_le hf ((a,d)::ls) rs (by simpa [nnwidth] using hw)
        intro t ht
        simpa using hle t ht
      have hd' : 0 < d := pos_iff_ne_zero.mpr hd
      have he' : 0 < e := pos_iff_ne_zero.mpr he
      have hab : a ≤ b := by
        have hh := hle 0 (by simp only [nnwidth]; positivity)
        simpa only [scheduleValue,hd',he',↓reduceIte] using hh
      by_cases hde : d ≤ e
      · let rr : Schedule := (b,e-d)::rs
        have hw' : nnwidth ls=nnwidth rr := by
          dsimp only [nnwidth] at hw ⊢
          dsimp only [rr,nnwidth]
          apply (add_left_cancel (a := d))
          rw [← add_assoc,add_tsub_cancel_of_le hde]
          exact hw
        have hm : ∀ y,evolve ls f y  ≤  evolve rr f y := by
          intro y
          apply evolve_le_of_scheduleValue_le hf ls rr hw'
          intro t ht
          have ht' : d+t < nnwidth ((a,d)::ls) := by
            simpa only [nnwidth] using add_lt_add_right ht d
          have hh := hle (d+t) ht'
          simpa only [scheduleValue_cons_shift,scheduleValue_split_shift _ _ _ hde,rr] using hh
        have hs : evolve ((b,e)::rs) f = step b (Real.sqrt d) (evolve rr f) := by
          have hh := evolve_split hf b d (e-d) rs
          rw [add_tsub_cancel_of_le hde] at hh
          exact hh.symm
        rw [hs]
        change step a (Real.sqrt d) (evolve ls f) x ≤ _
        exact (step_parameter_mono (evolve_lipschitz hf ls) a.coe_nonneg (by exact_mod_cast hab)
          (Real.sqrt d) x).trans
          (step_le_of_le (evolve_lipschitz hf ls) (evolve_lipschitz hf rr) b.coe_nonneg
            (Real.sqrt d) x hm)
      · have hed : e ≤ d := le_of_not_ge hde
        let ll : Schedule := (a,d-e)::ls
        have hw' : nnwidth ll=nnwidth rs := by
          dsimp only [nnwidth] at hw
          dsimp only [ll,nnwidth]
          apply (add_left_cancel (a := e))
          rw [← add_assoc,add_tsub_cancel_of_le hed]
          exact hw
        have hm : ∀ y,evolve ll f y ≤ evolve rs f y := by
          intro y
          apply evolve_le_of_scheduleValue_le hf ll rs hw'
          intro t ht
          have ht' : e+t < nnwidth ((a,d)::ls) := by
            have hh := add_lt_add_right ht e
            simpa only [ll,nnwidth,← add_assoc,add_tsub_cancel_of_le hed] using hh
          have hh := hle (e+t) ht'
          simpa only [scheduleValue_cons_shift,scheduleValue_split_shift _ _ _ hed,ll] using hh
        have hs : evolve ((a,d)::ls) f = step a (Real.sqrt e) (evolve ll f) := by
          have hh := evolve_split hf a e (d-e) ls
          rw [add_tsub_cancel_of_le hed] at hh
          exact hh.symm
        rw [hs]
        change _ ≤ step b (Real.sqrt e) (evolve rs f) x
        exact (step_parameter_mono (evolve_lipschitz hf ll) a.coe_nonneg (by exact_mod_cast hab)
          (Real.sqrt e) x).trans
          (step_le_of_le (evolve_lipschitz hf ll) (evolve_lipschitz hf rs) b.coe_nonneg
            (Real.sqrt e) x hm)
termination_by ls.length+rs.length

lemma dyadicSchedule_nnwidth (γ : ℝ≥0 → ℝ≥0) (u : Bool) (t d : ℝ≥0) (n : ℕ) :
    nnwidth (dyadicSchedule γ u t d n) = d := by
  apply NNReal.coe_injective
  rw [coe_nnwidth,dyadicSchedule_width]

lemma dyadicSchedule_value_bounds {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ)
    (t d : ℝ≥0) (n : ℕ) {s : ℝ≥0} (hs : s < d) :
    scheduleValue (dyadicSchedule γ false t d n) s ≤ γ (t+s) ∧
    γ (t+s) ≤ scheduleValue (dyadicSchedule γ true t d n) s := by
  induction n generalizing t d s with
  | zero =>
    simp only [dyadicSchedule,Bool.false_eq_true,↓reduceIte,scheduleValue,hs]
    exact ⟨hγ (le_add_of_nonneg_right zero_le),hγ (add_le_add_right hs.le t)⟩
  | succ n ih =>
    simp only [dyadicSchedule]
    by_cases hsd : s < d/2
    · rw [scheduleValue_append_left _ _ s (by rwa [dyadicSchedule_nnwidth]),
        scheduleValue_append_left _ _ s (by rwa [dyadicSchedule_nnwidth])]
      exact ih t (d/2) hsd
    · have hd : d/2 ≤ s := le_of_not_gt hsd
      have he : d/2+(s-d/2)=s := add_tsub_cancel_of_le hd
      have ht : s-d/2 < d/2 := by
        apply (tsub_lt_iff_left hd).mpr
        simpa only [add_halves] using hs
      have hlo := scheduleValue_append_right
        (dyadicSchedule γ false t (d/2) n)
        (dyadicSchedule γ false (t+d/2) (d/2) n) (s-d/2)
      have hhi := scheduleValue_append_right
        (dyadicSchedule γ true t (d/2) n)
        (dyadicSchedule γ true (t+d/2) (d/2) n) (s-d/2)
      rw [dyadicSchedule_nnwidth,he] at hlo hhi
      rw [hlo,hhi]
      simpa only [add_assoc,he] using ih (t+d/2) (d/2) ht

lemma dyadicSchedule_append_value_bounds {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ)
    (t d e : ℝ≥0) (n : ℕ) {s : ℝ≥0} (hs : s < d+e) :
    scheduleValue (dyadicSchedule γ false t d n ++ dyadicSchedule γ false (t+d) e n) s ≤ γ (t+s) ∧
    γ (t+s) ≤ scheduleValue (dyadicSchedule γ true t d n ++ dyadicSchedule γ true (t+d) e n) s := by
  by_cases hsd : s < d
  · rw [scheduleValue_append_left _ _ s (by rwa [dyadicSchedule_nnwidth]),
      scheduleValue_append_left _ _ s (by rwa [dyadicSchedule_nnwidth])]
    exact dyadicSchedule_value_bounds hγ t d n hsd
  · have hd : d ≤ s := le_of_not_gt hsd
    have he : d+(s-d)=s := add_tsub_cancel_of_le hd
    have ht : s-d < e := (tsub_lt_iff_left hd).mpr hs
    have hlo := scheduleValue_append_right
      (dyadicSchedule γ false t d n) (dyadicSchedule γ false (t+d) e n) (s-d)
    have hhi := scheduleValue_append_right
      (dyadicSchedule γ true t d n) (dyadicSchedule γ true (t+d) e n) (s-d)
    rw [dyadicSchedule_nnwidth,he] at hlo hhi
    rw [hlo,hhi]
    simpa only [add_assoc,he] using dyadicSchedule_value_bounds hγ (t+d) e n ht

lemma dyadicEvolution_high_grid_bound {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ} (hb : ∀ t,(γ t:ℝ) ≤ β)
    (t d : ℝ≥0) (n : ℕ) (x : ℝ) :
    |evolve (dyadicSchedule γ true t d n) f x-dyadicEvolution γ t d f x| ≤
      2*gaussianSmallError β (Real.sqrt (dyadicMesh d n)) := by
  have hlo : evolve (dyadicSchedule γ false t d n) f x ≤ dyadicEvolution γ t d f x :=
    le_ciSup (dyadic_low_bddAbove hf hγ t d x) n
  have hhi : dyadicEvolution γ t d f x ≤ evolve (dyadicSchedule γ true t d n) f x := by
    apply le_of_tendsto (dyadic_high_tendsto hf hγ hb t d x)
    filter_upwards [eventually_ge_atTop n] with k hk
    exact dyadic_high_antitone hf hγ t d x hk
  have he := abs_le.mp (dyadicSchedule_grid_error hb t d n hf x)
  rw [abs_of_nonneg (sub_nonneg.mpr hhi)]
  linarith

lemma dyadicEvolution_dyadic_grid_bound {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ} (hb : ∀ t,(γ t:ℝ) ≤ β)
    (u : Bool) (t d : ℝ≥0) (n : ℕ) (x : ℝ) :
    |evolve (dyadicSchedule γ u t d n) f x-dyadicEvolution γ t d f x| ≤
      2*gaussianSmallError β (Real.sqrt (dyadicMesh d n)) := by
  cases u
  · exact dyadicEvolution_grid_bound hf hγ hb t d n x
  · exact dyadicEvolution_high_grid_bound hf hγ hb t d n x

lemma dyadic_tendsto {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ} (hb : ∀ t,(γ t:ℝ) ≤ β)
    (u : Bool) (t d : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => evolve (dyadicSchedule γ u t d n) f x) atTop
      (𝓝 (dyadicEvolution γ t d f x)) := by
  cases u
  · exact dyadic_low_tendsto hf hγ t d x
  · exact dyadic_high_tendsto hf hγ hb t d x

lemma dyadic_append_tendsto {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ} (hb : ∀ t,(γ t:ℝ) ≤ β)
    (u : Bool) (t d e : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => evolve (dyadicSchedule γ u t d n ++ dyadicSchedule γ u (t+d) e n) f x) atTop
      (𝓝 (dyadicEvolution γ t d (dyadicEvolution γ (t+d) e f) x)) := by
  let g := dyadicEvolution γ (t+d) e f
  have hg : LipschitzWith 1 g := dyadicEvolution_lipschitz hf hγ _ _
  have hleft := dyadic_tendsto hg hγ hb u t d x
  have he : Tendsto (fun n => 2*gaussianSmallError β (Real.sqrt (dyadicMesh e n))) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (gaussianSmallError_dyadic_tendsto β e).const_mul 2
  have hbnd (n : ℕ) : |evolve (dyadicSchedule γ u t d n ++ dyadicSchedule γ u (t+d) e n) f x-
      evolve (dyadicSchedule γ u t d n) g x| ≤
        2*gaussianSmallError β (Real.sqrt (dyadicMesh e n)) := by
    rw [evolve_append]
    exact evolve_stable (evolve_lipschitz hf _) hg _ _
      (fun y => dyadicEvolution_dyadic_grid_bound hf hγ hb u (t+d) e n y) x
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using hleft.sub he)
    (by simpa only [add_zero] using hleft.add he)
  · intro n; have hh := (abs_le.mp (hbnd n)).1; linarith
  · intro n; have hh := (abs_le.mp (hbnd n)).2; linarith

 

lemma dyadicEvolution_DPP {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ} (hb : ∀ t,(γ t:ℝ) ≤ β)
    (t d e : ℝ≥0) (x : ℝ) :
    dyadicEvolution γ t (d+e) f x =
      dyadicEvolution γ t d (dyadicEvolution γ (t+d) e f) x := by
  apply le_antisymm
  · apply le_of_tendsto_of_tendsto (dyadic_low_tendsto hf hγ t (d+e) x)
      (dyadic_append_tendsto hf hγ hb true t d e x)
    apply Eventually.of_forall
    intro n
    apply evolve_le_of_scheduleValue_le hf
    · simp only [nnwidth_append,dyadicSchedule_nnwidth]
    · intro s hs
      rw [dyadicSchedule_nnwidth] at hs
      exact (dyadicSchedule_value_bounds hγ t (d+e) n hs).1.trans
        (dyadicSchedule_append_value_bounds hγ t d e n hs).2
  · apply le_of_tendsto_of_tendsto (dyadic_append_tendsto hf hγ hb false t d e x)
      (dyadic_high_tendsto hf hγ hb t (d+e) x)
    apply Eventually.of_forall
    intro n
    apply evolve_le_of_scheduleValue_le hf
    · simp only [nnwidth_append,dyadicSchedule_nnwidth]
    · intro s hs
      rw [nnwidth_append,dyadicSchedule_nnwidth,dyadicSchedule_nnwidth] at hs
      exact (dyadicSchedule_append_value_bounds hγ t d e n hs).1.trans
        (dyadicSchedule_value_bounds hγ t (d+e) n hs).2

lemma field_DPP (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β)
    {t s : ℝ≥0} (hts : t ≤ s) (hs : s ≤ 1) (x : ℝ) :
    field β γ t x = dyadicEvolution γ t (s-t) (field β γ s) x := by
  have he : (s-t)+(1-s)=1-t := by
    rw [add_comm,tsub_add_tsub_cancel hs hts]
  have hh := dyadicEvolution_DPP (terminal_lipschitz hβ) hγ
    (fun u => by exact_mod_cast hb u) t (s-t) (1-s) x
  rw [he,add_tsub_cancel_of_le hts] at hh
  exact hh

lemma recursion_prefix_time_bound (β : ℝ≥0) (hβ : 0 < β) (ls rs : Schedule)
    (ha : ∀ l ∈ ls ++ rs,l.1 ≤ β) (x : ℝ) :
    0 ≤ recursion β (ls ++ rs) x-recursion β rs x ∧
      recursion β (ls ++ rs) x-recursion β rs x ≤ (β:ℝ)*width ls/2 := by
  induction ls with
  | nil => simp [width]
  | cons l ls ih =>
    have ht : ∀ k ∈ ls ++ rs,k.1 ≤ β := fun k hk => ha k (List.mem_cons_of_mem _ hk)
    have hb := step_curvature_time_bound (smoothRecursion_hasParisiCurvature β hβ (ls ++ rs) ht)
      l.1.coe_nonneg (by exact_mod_cast ha l (List.mem_cons_self)) (Real.sqrt l.2) (Real.sqrt_nonneg _) x
    rw [smoothRecursion_val,Real.sq_sqrt l.2.coe_nonneg] at hb
    have hh := ih ht
    change 0 ≤ step l.1 (Real.sqrt l.2) (recursion β (ls ++ rs)) x-recursion β rs x ∧
      step l.1 (Real.sqrt l.2) (recursion β (ls ++ rs)) x-recursion β rs x ≤ (β:ℝ)*width (l::ls)/2
    have hw : width (l::ls)=(l.2:ℝ)+width ls := by simp [width]
    rw [hw]
    constructor <;> nlinarith [hb.1,hb.2,hh.1,hh.2]

 

lemma field_time_bound (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β)
    {t s : ℝ≥0} (hts : t ≤ s) (hs : s ≤ 1) (x : ℝ) :
    0 ≤ field β γ t x-field β γ s x ∧
      field β γ t x-field β γ s x ≤ (β:ℝ)*(s-t:ℝ≥0)/2 := by
  have he : (s-t)+(1-s)=1-t := by rw [add_comm,tsub_add_tsub_cancel hs hts]
  have hfull := dyadic_append_tendsto (f := terminal (β : ℝ)) (terminal_lipschitz hβ) hγ
    (fun u => by exact_mod_cast hb u) false t (s-t) (1-s) x
  have heq : dyadicEvolution γ t (s-t) (dyadicEvolution γ (t+(s-t)) (1-s) (terminal β)) x =
      field β γ t x := by
    have hh := dyadicEvolution_DPP (f := terminal (β : ℝ)) (terminal_lipschitz hβ) hγ
      (fun u => by exact_mod_cast hb u) t (s-t) (1-s) x
    rw [he] at hh
    exact hh.symm
  rw [heq,add_tsub_cancel_of_le hts] at hfull
  have hr := dyadic_low_tendsto (terminal_lipschitz hβ) hγ s (1-s) x
  change Tendsto _ _ (𝓝 (field β γ s x)) at hr
  have hlim := hfull.sub hr
  have hbounds (n : ℕ) :
      0 ≤ evolve (dyadicSchedule γ false t (s-t) n ++ dyadicSchedule γ false s (1-s) n) (terminal β) x -
        evolve (dyadicSchedule γ false s (1-s) n) (terminal β) x ∧
      evolve (dyadicSchedule γ false t (s-t) n ++ dyadicSchedule γ false s (1-s) n) (terminal β) x -
        evolve (dyadicSchedule γ false s (1-s) n) (terminal β) x ≤ (β:ℝ)*(s-t:ℝ≥0)/2 := by
    have hh := recursion_prefix_time_bound β hβ
      (dyadicSchedule γ false t (s-t) n) (dyadicSchedule γ false s (1-s) n) (by
        intro l hl
        rcases List.mem_append.mp hl with h|h
        · exact dyadicSchedule_coeff_bound hb false t (s-t) n l h
        · exact dyadicSchedule_coeff_bound hb false s (1-s) n l h) x
    rwa [recursion_eq_evolve,recursion_eq_evolve,dyadicSchedule_width] at hh
  exact ⟨ge_of_tendsto hlim (Eventually.of_forall fun n => (hbounds n).1),
    le_of_tendsto hlim (Eventually.of_forall fun n => (hbounds n).2)⟩

lemma field_time_abs_bound (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β)
    {t s : ℝ≥0} (ht : t ≤ 1) (hs : s ≤ 1) (x : ℝ) :
    |field β γ t x-field β γ s x| ≤ (β:ℝ)/2*|(t:ℝ)-s| := by
  rcases le_total t s with hts|hst
  · have hh := field_time_bound β hβ hγ hb hts hs x
    rw [abs_of_nonneg hh.1,abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hts))]
    rw [NNReal.coe_sub hts] at hh
    nlinarith [hh.2]
  · have hh := field_time_bound β hβ hγ hb hst ht x
    rw [abs_sub_comm,abs_of_nonneg hh.1,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hst))]
    rw [NNReal.coe_sub hst] at hh
    nlinarith [hh.2]

lemma field_joint_lipschitz (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) :
    LipschitzWith (β/2+1) (fun q : OrderPoint × ℝ => field β γ (Real.toNNReal q.1) q.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hut : Real.toNNReal (u.1:ℝ) ≤ 1 := Real.toNNReal_le_one.mpr u.1.property.2
  have hvt : Real.toNNReal (v.1:ℝ) ≤ 1 := Real.toNNReal_le_one.mpr v.1.property.2
  have ht := field_time_abs_bound β hβ hγ hb hut hvt u.2
  rw [Real.coe_toNNReal _ u.1.property.1,Real.coe_toNNReal _ v.1.property.1] at ht
  have hx := (dyadicEvolution_lipschitz (terminal_lipschitz hβ) hγ
    (Real.toNNReal v.1) (1-Real.toNNReal v.1)).dist_le_mul u.2 v.2
  change dist (field β γ _ u.2) (field β γ _ v.2) ≤ _ at hx
  norm_num only [NNReal.coe_one,one_mul] at hx
  rw [Real.dist_eq] at hx ⊢
  have htri := abs_sub_le (field β γ (Real.toNNReal u.1) u.2)
    (field β γ (Real.toNNReal v.1) u.2) (field β γ (Real.toNNReal v.1) v.2)
  have htu : |(u.1:ℝ)-v.1| ≤ dist u v := by
    change dist u.1 v.1 ≤ dist u v
    exact le_max_left _ _
  have hxu : dist u.2 v.2 ≤ dist u v := le_max_right _ _
  simp only [NNReal.coe_add,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one]
  nlinarith [mul_le_mul_of_nonneg_left htu (show 0 ≤ (β:ℝ)/2 by positivity)]

lemma continuous_field_joint (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) :
    Continuous (fun q : OrderPoint × ℝ => field β γ (Real.toNNReal q.1) q.2) :=
  (field_joint_lipschitz β hβ hγ hb).continuous

lemma field_taylor_error (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β)
    (t : ℝ≥0) (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    |field β γ t (x+h)-field β γ t x-h*fieldGradient β γ t x| ≤ (β:ℝ)*h^2 := by
  have hv (y : ℝ) : Tendsto
      (fun n => (smoothRecursion β hβ (dyadicSchedule γ false t (1-t) n)).val y)
      atTop (𝓝 (field β γ t y)) := by
    simpa only [smoothRecursion_val,recursion_eq_evolve,field,NNReal.toReal] using
      dyadic_low_tendsto (terminal_lipschitz hβ) hγ t (1-t) y
  have hm := fieldGradient_dyadic_tendsto β hβ hγ hb t x
  apply le_of_tendsto (((hv (x+h)).sub (hv x)).sub (hm.const_mul h) |>.abs)
  exact Eventually.of_forall fun n => curvature_taylor_error
    (smoothRecursion_hasParisiCurvature β hβ _ (dyadicSchedule_coeff_bound hb false t (1-t) n)) x hh

lemma field_slope_error (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β)
    (t : ℝ≥0) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    |(field β γ t (x+h)-field β γ t x)/h-fieldGradient β γ t x| ≤ (β:ℝ)*h := by
  rw [div_sub' hh.ne',abs_div,abs_of_pos hh]
  apply (div_le_iff₀ hh).mpr
  simpa only [pow_two,mul_assoc] using field_taylor_error β hβ hγ hb t x hh.le

 

lemma continuous_fieldGradient_joint (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) :
    Continuous (fun q : OrderPoint × ℝ => fieldGradient β γ (Real.toNNReal q.1) q.2) := by
  let ε (n : ℕ) : ℝ := 1/(n+1 : ℕ)
  let F (n : ℕ) (q : OrderPoint × ℝ) : ℝ :=
    (field β γ (Real.toNNReal q.1) (q.2+ε n)-field β γ (Real.toNNReal q.1) q.2)/ε n
  have he (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have ht : Tendsto (fun n => (β:ℝ)*ε n) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using SKCavity.tendsto_succ_reciprocal.const_mul (β:ℝ)
  have hu : TendstoUniformly F (fun q : OrderPoint × ℝ =>
      fieldGradient β γ (Real.toNNReal q.1) q.2) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn q
    rw [Real.dist_eq,abs_sub_comm]
    exact (field_slope_error β hβ hγ hb (Real.toNNReal q.1) q.2 (he n)).trans_lt hn
  apply hu.continuous
  apply Eventually.frequently
  apply Eventually.of_forall
  intro n
  have hc := continuous_field_joint β hβ hγ hb
  exact ((hc.comp (continuous_fst.prodMk (continuous_snd.add_const (ε n)))).sub hc).div_const (ε n)

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite

def fieldCurvature (β : ℝ≥0) (γ : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ → ℝ :=
  deriv (fieldGradient β γ t)

lemma fieldGradient_dyadic_uniform (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (t : ℝ≥0) :
    TendstoUniformly (fun n => (smoothRecursion β hβ (dyadicSchedule γ false t (1-t) n)).d1)
      (fieldGradient β γ t) atTop := by
  obtain ⟨m,hd,_,_,hu⟩ := dyadicEvolution_terminal_gradient β hβ hγ hb t (1-t)
  have he : fieldGradient β γ t=m := funext (fun x => (hd x).deriv)
  rw [he]
  exact hu

lemma fieldCurvature_exists (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (t : ℝ≥0) :
    TendstoUniformly (fun n => (smoothRecursion β hβ (dyadicSchedule γ false t (1-t) n)).d2)
      (fieldCurvature β γ t) atTop ∧
    (∀ x,HasDerivAt (fieldGradient β γ t) (fieldCurvature β γ t x) x) ∧
    LipschitzWith (5*β^2) (fieldCurvature β γ t) := by
  have hl (n : ℕ) : LipschitzWith (5*β^2)
      (smoothRecursion β hβ (dyadicSchedule γ false t (1-t) n)).d2 :=
    recursion_curvature_lipschitz β hβ _ (ordered_lower (γ t).coe_nonneg
      (ordered_upper (show (γ (t+(1-t)):ℝ)≤β by exact_mod_cast hb _)
        (dyadicSchedule_ordered hγ false t (1-t) n)))
  obtain ⟨g,hu,hd,hg⟩ := exists_uniform_derivative_lipschitz_limit
    (fun n => (smoothRecursion β hβ (dyadicSchedule γ false t (1-t) n)).hasD2) hl
    (fieldGradient_dyadic_uniform β hβ hγ hb t)
  have he : fieldCurvature β γ t=g := funext (fun x => (hd x).deriv)
  rw [he]
  exact ⟨hu,hd,hg⟩

lemma hasDerivAt_fieldGradient (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (t : ℝ≥0) (x : ℝ) :
    HasDerivAt (fieldGradient β γ t) (fieldCurvature β γ t x) x :=
  (fieldCurvature_exists β hβ hγ hb t).2.1 x

lemma fieldCurvature_lipschitz (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (t : ℝ≥0) :
    LipschitzWith (5*β^2) (fieldCurvature β γ t) :=
  (fieldCurvature_exists β hβ hγ hb t).2.2

lemma fieldCurvature_dyadic_tendsto (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (t : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => (smoothRecursion β hβ (dyadicSchedule γ false t (1-t) n)).d2 x)
      atTop (𝓝 (fieldCurvature β γ t x)) :=
  (fieldCurvature_exists β hβ hγ hb t).1.tendsto_at x

lemma fieldCurvature_bounds (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (t : ℝ≥0) (x : ℝ) :
    0<fieldCurvature β γ t x ∧ fieldCurvature β γ t x≤(β:ℝ)*(1-fieldGradient β γ t x^2) := by
  have ht := fieldCurvature_dyadic_tendsto β hβ hγ hb t x
  constructor
  · apply (curvatureFloor_pos β hβ x).trans_le
    apply ge_of_tendsto ht
    exact Eventually.of_forall fun n => finite_curvature_floor β hβ _
      (dyadicSchedule_coeff_bound hb false t (1-t) n)
      (by rw [dyadicSchedule_width];exact_mod_cast (tsub_le_self : 1-t≤(1:ℝ≥0))) le_rfl
  · apply le_of_tendsto_of_tendsto ht
      (((fieldGradient_dyadic_tendsto β hβ hγ hb t x).pow 2).const_sub 1 |>.const_mul (β:ℝ))
    exact Eventually.of_forall fun n => (smoothRecursion_hasParisiCurvature β hβ _
      (dyadicSchedule_coeff_bound hb false t (1-t) n)).2 x |>.2

lemma fieldCurvature_abs (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (t : ℝ≥0) (x : ℝ) :
    |fieldCurvature β γ t x|≤β := by
  obtain ⟨hp,hu⟩ := fieldCurvature_bounds β hβ hγ hb t x
  rw [abs_of_pos hp]
  nlinarith [mul_nonneg β.coe_nonneg (sq_nonneg (fieldGradient β γ t x))]

lemma fieldGradient_slope_error (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (t : ℝ≥0) (x : ℝ) {h : ℝ} (hh : 0<h) :
    |(fieldGradient β γ t (x+h)-fieldGradient β γ t x)/h-fieldCurvature β γ t x|≤5*(β:ℝ)^2*h := by
  rw [div_sub' hh.ne',abs_div,abs_of_pos hh]
  apply (div_le_iff₀ hh).mpr
  simpa only [NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow,pow_two,mul_assoc] using
    taylor_error_of_derivative_lipschitz (hasDerivAt_fieldGradient β hβ hγ hb t)
      (fieldCurvature_lipschitz β hβ hγ hb t) x hh.le

lemma continuous_fieldCurvature_joint (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β) :
    Continuous (fun q : OrderPoint × ℝ => fieldCurvature β γ (Real.toNNReal q.1) q.2) := by
  let ε (n : ℕ) : ℝ := 1/(n+1 : ℕ)
  let F (n : ℕ) (q : OrderPoint × ℝ) : ℝ :=
    (fieldGradient β γ (Real.toNNReal q.1) (q.2+ε n)-fieldGradient β γ (Real.toNNReal q.1) q.2)/ε n
  have he (n : ℕ) : 0<ε n := by dsimp [ε];positivity
  have ht : Tendsto (fun n => 5*(β:ℝ)^2*ε n) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using SKCavity.tendsto_succ_reciprocal.const_mul (5*(β:ℝ)^2)
  have hu : TendstoUniformly F (fun q : OrderPoint × ℝ =>
      fieldCurvature β γ (Real.toNNReal q.1) q.2) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn q
    rw [Real.dist_eq,abs_sub_comm]
    exact (fieldGradient_slope_error β hβ hγ hb (Real.toNNReal q.1) q.2 (he n)).trans_lt hn
  apply hu.continuous
  apply Eventually.frequently
  apply Eventually.of_forall
  intro n
  have hc := continuous_fieldGradient_joint β hβ hγ hb
  exact ((hc.comp (continuous_fst.prodMk (continuous_snd.add_const (ε n)))).sub hc).div_const (ε n)

end ParisiFinite

end

end OAI
