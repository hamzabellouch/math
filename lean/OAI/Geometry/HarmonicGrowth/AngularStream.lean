import OAI.Geometry.HarmonicGrowth.InsertedWord
import OAI.Geometry.HarmonicGrowth.Profiles

namespace OAI

noncomputable section


namespace HarmonicCounterexample.CausalConstruction
open Filter Set
open scoped Topology ContDiff

variable {P E : Type*}

/-- Prefixes contain genuine future zero controls, rather than the base point
of an endpoint chart (whose control word need not vanish). -/
def prefixes (zero : P) (choose : ℕ → (ℕ → P) → P) : ℕ → ℕ → P
  | 0 => fun _ => zero
  | n+1 => Function.update (prefixes zero choose n) n (choose n (prefixes zero choose n))

def limitChoice (zero : P) (choose : ℕ → (ℕ → P) → P) (j : ℕ) : P :=
  choose j (prefixes zero choose j)

lemma prefixes_zero {zero : P} {choose : ℕ → (ℕ → P) → P} {n j : ℕ} (h : n ≤ j) :
    prefixes zero choose n j=zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [prefixes,Function.update_of_ne (by omega : j ≠ n)]
      exact ih (by omega)

lemma prefixes_stable {zero : P} {choose : ℕ → (ℕ → P) → P} {n j : ℕ} (h : j < n) :
    prefixes zero choose n j=limitChoice zero choose j := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hj : j=n
      · subst j; simp [prefixes,limitChoice]
      · rw [prefixes,Function.update_of_ne hj]
        exact ih (by omega)

/-- Pure dependent choice in chronological order. The predicate may depend on
all past controls, but never on a fictitious future control. -/
theorem causal_choice (zero : P) (admissible : Set P)
    (good : ℕ → (ℕ → P) → P → Prop)
    (produce : ∀ j s,(∀ i < j,s i ∈ admissible) → (∀ i,j ≤ i → s i=zero) →
      ∃ x ∈ admissible,good j s x) :
    ∃ s : ℕ → P,(∀ j,s j ∈ admissible) ∧
      ∀ j,good j (fun i => if i < j then s i else zero) (s j) := by
  classical
  let choose (j : ℕ) (s : ℕ → P) : P :=
    if h : (∀ i < j,s i ∈ admissible) ∧ (∀ i,j ≤ i → s i=zero)
      then (produce j s h.1 h.2).choose else zero
  have hg : ∀ j,limitChoice zero choose j ∈ admissible ∧
      good j (prefixes zero choose j) (limitChoice zero choose j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      have hp : ∀ i < j,prefixes zero choose j i ∈ admissible := by
        intro i hi
        rw [prefixes_stable hi]
        exact (ih i hi).1
      have hz : ∀ i,j ≤ i → prefixes zero choose j i=zero := fun i hi => prefixes_zero hi
      have he : limitChoice zero choose j=(produce j (prefixes zero choose j) hp hz).choose := by
        change (if h : (∀ i < j,prefixes zero choose j i ∈ admissible) ∧
            (∀ i,j ≤ i → prefixes zero choose j i=zero)
          then (produce j (prefixes zero choose j) h.1 h.2).choose else zero)=_
        rw [dite_eq_left ⟨hp,hz⟩]
      rw [he]
      exact (produce j (prefixes zero choose j) hp hz).choose_spec
  refine ⟨limitChoice zero choose,fun j => (hg j).1,?_⟩
  intro j
  have he : prefixes zero choose j=(fun i => if i < j then limitChoice zero choose i else zero) := by
    funext i
    split_ifs with hi
    · exact prefixes_stable hi
    · exact prefixes_zero (by omega)
  rw [← he]
  exact (hg j).2

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
open Schedule

/-- Vector-valued local finiteness for the fixed polynomial schedule. -/
theorem smooth_escaping_sum {f : ℕ → ℝ → E} (hf : ∀ j,ContDiff ℝ ∞ (f j))
    (hz : ∀ j t,t ≤ time j → f j t=0) :
    ContDiff ℝ ∞ (fun t => ∑' j,f j t) := by
  apply contDiff_iff_contDiffAt.2
  intro t
  obtain ⟨N,hN⟩ := eventually_atTop.1 (time_atTop.eventually_gt_atTop (t+1))
  apply (ContDiffAt.sum (s:=Finset.range N) (fun j _ => (hf j).contDiffAt)).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (show t<t+1 by linarith)] with u hu
  apply tsum_eq_sum
  intro j hj
  have hj' : N ≤ j := by simpa only [Finset.mem_range,not_lt] using hj
  exact hz j u (by linarith [hN j hj'])

omit [NormedSpace ℝ E] in
/-- At every actual time in a period there is exactly one possible increment.
Both endpoints have zero increments, so this holds on closed periods. -/
lemma sum_period {f : ℕ → ℝ → E}
    (hz0 : ∀ j t,t ≤ time j → f j t=0)
    (hz1 : ∀ j t,time (j+1) ≤ t → f j t=0)
    {j : ℕ} {t : ℝ} (hlo : time j ≤ t) (hhi : t ≤ time (j+1)) :
    (∑' i,f i t)=f j t := by
  apply tsum_eq_single j
  intro i hi
  rcases lt_or_gt_of_ne hi with hij | hij
  · exact hz1 i t ((time_strictMono.monotone hij).trans hlo)
  · exact hz0 i t (hhi.trans (time_strictMono.monotone hij))

omit [NormedSpace ℝ E] in
lemma sum_initial {f : ℕ → ℝ → E}
    (hz0 : ∀ j t,t ≤ time j → f j t=0) {t : ℝ} (ht : t ≤ time 0) :
    (∑' i,f i t)=0 := by
  have he : (fun i => f i t)=(fun _ => (0:E)) := by
    funext j
    exact hz0 j t (ht.trans (time_strictMono.monotone (Nat.zero_le j)))
  rw [he,tsum_zero]

omit [NormedSpace ℝ E] in
/-- A future insertion cannot change a previous time, regardless of the
infinite tail of controls. This is the causality needed by regular ODEs. -/
lemma sum_causal {f g : ℕ → ℝ → E} {j : ℕ}
    (hf : ∀ i t,t ≤ time i → f i t=0)
    (hg : ∀ i t,t ≤ time i → g i t=0)
    (he : ∀ i < j,f i=g i) {t : ℝ} (ht : t ≤ time j) :
    (∑' i,f i t)=(∑' i,g i t) := by
  apply tsum_congr
  intro i
  by_cases hi : i<j
  · rw [he i hi]
  · have hti : t ≤ time i := ht.trans (time_strictMono.monotone (by omega))
    rw [hf i t hti,hg i t hti]

end HarmonicCounterexample.CausalConstruction

end

noncomputable section


namespace HarmonicCounterexample.AngularStream
open Set Schedule Pulses FiniteControl.SmoothWord
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- The fixed diagonal leg; initially and during every pulse it is round. -/
def base (qstar : ℝ) (j0 : ℕ) : ℝ → ℝ := Pulses.profile (fun _ _ => 0) qstar j0

lemma base_smooth (qstar : ℝ) (j0 : ℕ) : ContDiff ℝ ∞ (base qstar j0) :=
  Pulses.profile_smooth (fun _ => contDiff_const) (by simp) qstar j0

lemma base_initial {qstar t : ℝ} {j0 : ℕ} (ht : t ≤ time j0) : base qstar j0 t=1 :=
  Pulses.profile_initial (by simp) ht

lemma base_pulse {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j)
    (hlo : time j ≤ t) (hhi : t ≤ time j+pulse j) : base qstar j0 t=1 := by
  have h := Pulses.profile_pulse (z:=fun _ _ => 0) (qstar:=qstar) (by simp) (by simp) hj hlo hhi
  simpa [base] using h

lemma base_range {qstar : ℝ} (hq : 1 ≤ qstar) (j0 : ℕ) (t : ℝ) :
    base qstar j0 t ∈ Icc 1 qstar := by
  by_cases ht : t ≤ time j0
  · rw [base_initial ht];exact ⟨le_rfl,hq⟩
  · obtain ⟨j,hj,hlo,hhi⟩ := GlobalGrowth.grid_bracket time_atTop j0 (le_of_not_ge ht)
    have h := Pulses.profile_bounds_on_period (z:=fun _ _ => 0) (M:=0) (by simp) (by simp)
      (by simp) hq hj hlo hhi
    simpa [base] using h

/-- Actual angular increment of a period, zero on both open round collars. -/
def increment (r : ℝ) (b : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ) (j : ℕ) (t : ℝ) : E :=
  nonlinearBergerWord r b D (s j) (pulse j) ((t-time j)/pulse j)-b

lemma increment_before (r : ℝ) (b : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ)
    {j : ℕ} {t : ℝ} (ht : t ≤ time j) : increment r b D s j t=0 := by
  have hu : (t-time j)/pulse j ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ht) (pulse_pos j).le
  rw [increment,nonlinearBergerWord_round_before r b D (s j) (pulse j) _
    (lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (duration_pos n).le hu) (by norm_num)),sub_self]

lemma increment_after (r : ℝ) (b : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ)
    {j : ℕ} {t : ℝ} (ht : time j+pulse j ≤ t) : increment r b D s j t=0 := by
  have hu : 1 ≤ (t-time j)/pulse j := (le_div_iff₀ (pulse_pos j)).2 (by linarith)
  have hu' : duration n ≤ duration n*((t-time j)/pulse j) := by
    simpa using mul_le_mul_of_nonneg_left hu (duration_pos n).le
  rw [increment,nonlinearBergerWord_round_after r b D (s j) (pulse j) _
    (lt_of_lt_of_le (by simp [duration]) hu'),sub_self]

lemma increment_zero (r : ℝ) (b : E) (D : Fin n → E) {s : ℕ → Fin n → ℝ}
    {j : ℕ} (hj : s j=0) (t : ℝ) : increment r b D s j t=0 := by
  have he : packetStretch (s j) (pulse j) ((t-time j)/pulse j)=(fun _ => 1) := by
    funext i;simp [packetStretch,hj]
  simp only [increment,nonlinearBergerWord,he,nonlinearPacket_round,sub_self]

def activeIncrement (r : ℝ) (b : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ) (j0 j : ℕ) : ℝ → E :=
  if j0 ≤ j then increment r b D s j else 0

lemma active_before (r : ℝ) (b : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ) (j0 j : ℕ)
    (t : ℝ) (ht : t ≤ time j) : activeIncrement r b D s j0 j t=0 := by
  dsimp [activeIncrement];split_ifs
  · exact increment_before r b D s ht
  · rfl

lemma active_after (r : ℝ) (b : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ) (j0 j : ℕ)
    (t : ℝ) (ht : time (j+1) ≤ t) : activeIncrement r b D s j0 j t=0 := by
  dsimp [activeIncrement];split_ifs
  · apply increment_after r b D s
    rw [time_succ] at ht
    linarith [pulse_pos j,dwell_pos j]
  · rfl

/-- Simultaneously smooth infinite angular coefficient. No angular selector is
used in its definition, so discontinuous labels cannot spoil regularity. -/
def angular (r : ℝ) (b D0 : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ)
    (qstar : ℝ) (j0 : ℕ) (t : ℝ) : E :=
  PulseTaylor.angular r b D0 (base qstar j0 t)+∑' j,activeIncrement r b D s j0 j t

lemma angular_smooth (r : ℝ) (b D0 : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ)
    {qstar : ℝ} (hq : 1 ≤ qstar) (j0 : ℕ)
    (hpos : ∀ j,j0 ≤ j → ∀ t i,packetStretch (s j) (pulse j) t i ≠ 0) :
    ContDiff ℝ ∞ (angular r b D0 D s qstar j0) := by
  have hb : ContDiff ℝ ∞ (fun t => PulseTaylor.angular r b D0 (base qstar j0 t)) := by
    have h1 := (base_smooth qstar j0).rpow_const_of_ne (p:=r) (fun t =>
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (base_range hq j0 t).1)))
    have h2 := (base_smooth qstar j0).rpow_const_of_ne (p:=r-1) (fun t =>
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (base_range hq j0 t).1)))
    exact (h1.smul contDiff_const).add ((h1.sub h2).smul contDiff_const)
  apply hb.add (CausalConstruction.smooth_escaping_sum ?_ (active_before r b D s j0))
  intro j
  dsimp [activeIncrement]
  split_ifs with hj
  · exact ((nonlinearBergerWord_smooth r b D (s j) (pulse j) (fun i t => hpos j hj t i)).comp
      ((contDiff_id.sub contDiff_const).div_const _)).sub contDiff_const
  · exact contDiff_const

lemma angular_initial (r : ℝ) (b D0 : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ)
    {qstar t : ℝ} {j0 : ℕ} (ht : t ≤ time j0) : angular r b D0 D s qstar j0 t=b := by
  have he : (fun j => activeIncrement r b D s j0 j t)=(fun _ => (0:E)) := by
    funext j
    dsimp [activeIncrement]
    split_ifs with hj
    · exact increment_before r b D s (ht.trans (time_strictMono.monotone hj))
    · rfl
  simp only [angular,base_initial ht,PulseTaylor.angular_one,he,tsum_zero,add_zero]

lemma angular_period (r : ℝ) (b D0 : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ)
    {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j) (hlo : time j ≤ t) (hhi : t ≤ time (j+1)) :
    angular r b D0 D s qstar j0 t=
      PulseTaylor.angular r b D0 (base qstar j0 t)+increment r b D s j t := by
  rw [angular,CausalConstruction.sum_period (active_before r b D s j0)
    (active_after r b D s j0) hlo hhi]
  simp only [activeIncrement,ite_eq_left hj]

lemma angular_pulse (r : ℝ) (b D0 : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ)
    {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j) (hlo : time j ≤ t) (hhi : t ≤ time j+pulse j) :
    angular r b D0 D s qstar j0 t=nonlinearBergerWord r b D (s j) (pulse j) ((t-time j)/pulse j) := by
  rw [angular_period r b D0 D s hj hlo (by rw [time_succ];linarith [pulse_pos j,dwell_pos j]),
    base_pulse hj hlo hhi,PulseTaylor.angular_one,increment]
  abel

lemma angular_leg (r : ℝ) (b D0 : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ)
    {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j) (hlo : time j+pulse j ≤ t) (hhi : t ≤ time (j+1)) :
    angular r b D0 D s qstar j0 t=PulseTaylor.angular r b D0 (base qstar j0 t) := by
  rw [angular_period r b D0 D s hj (by linarith [pulse_pos j]) hhi,
    increment_after r b D s hlo,add_zero]

lemma angular_causal (r : ℝ) (b D0 : E) (D : Fin n → E) {s s' : ℕ → Fin n → ℝ}
    (qstar : ℝ) (j0 : ℕ) {j : ℕ} (he : ∀ i < j,s i=s' i) {t : ℝ} (ht : t ≤ time j) :
    angular r b D0 D s qstar j0 t=angular r b D0 D s' qstar j0 t := by
  unfold angular
  congr 1
  apply CausalConstruction.sum_causal (active_before r b D s j0) (active_before r b D s' j0) ?_ ht
  intro i hi
  funext u
  dsimp [activeIncrement]
  split_ifs <;> simp [increment,he i hi]

end HarmonicCounterexample.AngularStream

end

noncomputable section


namespace HarmonicCounterexample.AngularStream
open Set Filter Schedule Pulses FiniteControl.SmoothWord
open scoped ContDiff Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

lemma active_summable (r : ℝ) (b : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ)
    (j0 : ℕ) (t : ℝ) : Summable (fun j => activeIncrement r b D s j0 j t) := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 (time_atTop.eventually_ge_atTop t)
  apply summable_of_ne_finset_zero (s:=Finset.range N)
  intro j hj
  apply active_before r b D s j0 j t
  exact hN j (by simpa only [Finset.mem_range,not_lt] using hj)

/-- Updating a previously zero pulse is exactly the actual smooth insertion,
not merely equality of an ideal packet. -/
lemma angular_update (r : ℝ) (b D0 : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ)
    (x : Fin n → ℝ) (qstar : ℝ) {j0 j : ℕ} (hj : j0 ≤ j) (hz : s j=0) (t : ℝ) :
    angular r b D0 D (Function.update s j x) qstar j0 t=
      angular r b D0 D s qstar j0 t+
        (nonlinearBergerWord r b D x (pulse j) ((t-time j)/pulse j)-b) := by
  classical
  have he : (fun i => if i=j then 0 else activeIncrement r b D (Function.update s j x) j0 i t)=
      (fun i => if i=j then 0 else activeIncrement r b D s j0 i t) := by
    funext i
    split_ifs with hi
    · rfl
    · dsimp [activeIncrement];split_ifs <;> simp [increment,Function.update_of_ne hi]
  have hz' : activeIncrement r b D s j0 j t=0 := by
    dsimp [activeIncrement];rw [ite_eq_left hj];exact increment_zero r b D hz t
  rw [angular,angular,(active_summable r b D (Function.update s j x) j0 t).tsum_eq_add_tsum_ite j,
    (active_summable r b D s j0 t).tsum_eq_add_tsum_ite j,he,hz',zero_add]
  simp only [activeIncrement,ite_eq_left hj,increment,Function.update_self]
  abel

lemma coefficient_update (r : ℝ) (b D0 : E) (D : Fin n → E) (s : ℕ → Fin n → ℝ)
    (x : Fin n → ℝ) (qstar : ℝ) (α : ℝ → ℝ) {j0 j : ℕ} (hj : j0 ≤ j) (hz : s j=0) :
    (fun t => α t • angular r b D0 D (Function.update s j x) qstar j0 t)=
      insertWord (fun t => α t • angular r b D0 D s qstar j0 t) α r b D x (time j) (pulse j) := by
  funext t
  rw [angular_update r b D0 D s x qstar hj hz t,smul_add]
  rfl

def direction (D0 : E) (D : Fin n → E) : Option (Fin n) → E
  | none => D0
  | some i => D i

lemma angular_representation [NeZero n] (r : ℝ) (b D0 : E) (D : Fin n → E)
    (s : ℕ → Fin n → ℝ) {qstar : ℝ} (hq : 1 ≤ qstar) (j0 : ℕ)
    (hpos : ∀ j,j0 ≤ j → ∀ t i,packetStretch (s j) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2))
    (t : ℝ) : ∃ (d : Option (Fin n)), ∃ q ∈ Icc (1/2:ℝ) (qstar+1/2),
      angular r b D0 D s qstar j0 t=PulseTaylor.angular r b (direction D0 D d) q := by
  by_cases ht : t ≤ time j0
  · refine ⟨none,1,⟨by norm_num,by linarith⟩,?_⟩
    rw [angular_initial r b D0 D s ht,PulseTaylor.angular_one]
  · obtain ⟨j,hj,hlo,hhi⟩ := GlobalGrowth.grid_bracket time_atTop j0 (le_of_not_ge ht)
    by_cases htp : t ≤ time j+pulse j
    · obtain ⟨d,hd,_⟩ := exists_unit_round_gap_selector n
      let u := (t-time j)/pulse j
      refine ⟨some (d u),packetStretch (s j) (pulse j) u (d u),?_,?_⟩
      · have hh := hpos j hj u (d u)
        exact ⟨hh.1,hh.2.trans (by linarith)⟩
      · rw [angular_pulse r b D0 D s hj hlo htp,
          nonlinearBergerWord_selected r b D (s j) (pulse j) u (d u) (fun i hi => (hd u i hi).1),
          packetStretch_selected (s j) (pulse j) u (d u) (fun i hi => (hd u i hi).1)]
        rfl
    · refine ⟨none,base qstar j0 t,?_,?_⟩
      · have hh := base_range hq j0 t
        exact ⟨(by norm_num : (1/2:ℝ) ≤ 1).trans hh.1,hh.2.trans (by linarith)⟩
      · exact angular_leg r b D0 D s hj (le_of_not_ge htp) hhi

/-- An actual all-time coefficient bound chosen before the entire sequence of
controls and the starting index. Uniformity is compactness of one fixed angular
family, not a bound on a posteriori chosen histories. -/
theorem angular_uniform_bound [NeZero n] (r : ℝ) (b D0 : E) (D : Fin n → E)
    {qstar : ℝ} (hq : 1 ≤ qstar) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (s : ℕ → Fin n → ℝ) (j0 : ℕ),
      (∀ j,j0 ≤ j → ∀ t i,packetStretch (s j) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2)) →
      ∀ t,‖angular r b D0 D s qstar j0 t‖ ≤ C := by
  classical
  have hc (d : Option (Fin n)) : ContinuousOn (PulseTaylor.angular r b (direction D0 D d))
      (Icc (1/2:ℝ) (qstar+1/2)) := by
    apply ContinuousOn.add
    · exact (continuousOn_id.rpow_const (fun t ht => Or.inl (by change t ≠ 0;linarith [ht.1]))).smul continuousOn_const
    · exact ((continuousOn_id.rpow_const (fun t ht => Or.inl (by change t ≠ 0;linarith [ht.1]))).sub
        (continuousOn_id.rpow_const (fun t ht => Or.inl (by change t ≠ 0;linarith [ht.1])))).smul continuousOn_const
  choose C hC using fun d => isCompact_Icc.exists_bound_of_continuousOn (hc d)
  let M := ∑ d : Option (Fin n),max (C d) 0
  have hM : 0 ≤ M := Finset.sum_nonneg (fun d _ => le_max_right _ _)
  refine ⟨M,hM,fun s j0 hpos t => ?_⟩
  obtain ⟨d,q,hq',he⟩ := angular_representation r b D0 D s hq j0 hpos t
  rw [he]
  exact (hC d q hq').trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun i _ => le_max_right (C i) 0) (Finset.mem_univ d)))

end HarmonicCounterexample.AngularStream

end

noncomputable section


namespace HarmonicCounterexample.AngularStream
open Set Schedule Pulses FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} [NeZero n]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

lemma angular_nonnegative (r B : ℝ) (D0 : E →L[ℝ] E) (D : Fin n → E →L[ℝ] E)
    (s : ℕ → Fin n → ℝ) {qstar : ℝ} (hq : 1 ≤ qstar) (j0 : ℕ)
    (hpos : ∀ j,j0 ≤ j → ∀ t i,packetStretch (s j) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2))
    (hD : ∀ d x,inner ℝ x (direction D0 D d x) ≤ 0)
    (hBD : ∀ d x,-(B*‖x‖^2) ≤ inner ℝ x (direction D0 D d x))
    (t : ℝ) (x : E) :
    0 ≤ inner ℝ x (angular r (B • (1:E →L[ℝ] E)) D0 D s qstar j0 t x) := by
  obtain ⟨d,q,hq',he⟩ := angular_representation r (B • (1:E →L[ℝ] E)) D0 D s hq j0 hpos t
  rw [he]
  exact berger_angular_nonneg r B q (direction D0 D d) (by linarith [hq'.1]) (hD d) (hBD d) x

lemma angular_symmetric (r B : ℝ) (D0 : E →L[ℝ] E) (D : Fin n → E →L[ℝ] E)
    (s : ℕ → Fin n → ℝ) {qstar : ℝ} (hq : 1 ≤ qstar) (j0 : ℕ)
    (hpos : ∀ j,j0 ≤ j → ∀ t i,packetStretch (s j) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2))
    (hD : ∀ d x y,inner ℝ (direction D0 D d x) y=inner ℝ x (direction D0 D d y))
    (t : ℝ) (x y : E) :
    inner ℝ (angular r (B • (1:E →L[ℝ] E)) D0 D s qstar j0 t x) y=
      inner ℝ x (angular r (B • (1:E →L[ℝ] E)) D0 D s qstar j0 t y) := by
  obtain ⟨d,q,_,he⟩ := angular_representation r (B • (1:E →L[ℝ] E)) D0 D s hq j0 hpos t
  rw [he]
  simp only [PulseTaylor.angular,add_apply,smul_apply,
    one_apply_eq_self,inner_add_left,inner_add_right,real_inner_smul_left,
    inner_smul_right,hD d x y]

omit [NeZero n] in
lemma angular_zero_pulse (r : ℝ) (b D0 : E →L[ℝ] E) (D : Fin n → E →L[ℝ] E)
    (s : ℕ → Fin n → ℝ) {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j) (hz : s j=0)
    (hlo : time j ≤ t) (hhi : t ≤ time j+pulse j) : angular r b D0 D s qstar j0 t=b := by
  rw [angular_period r b D0 D s hj hlo (by rw [time_succ];linarith [pulse_pos j,dwell_pos j]),
    base_pulse hj hlo hhi,PulseTaylor.angular_one,increment_zero r b D hz t,add_zero]

omit [NeZero n] in
/-- The preceding round rest is round even for the first active period, whose
entire previous history is round. This uniformity is essential for recursion. -/
lemma angular_rest (r : ℝ) (b D0 : E →L[ℝ] E) (D : Fin n → E →L[ℝ] E)
    (s : ℕ → Fin n → ℝ) {qstar t : ℝ} {j0 j : ℕ}
    (hlo : time j+3*pulse j+dwell j ≤ t) (hhi : t ≤ time (j+1)) :
    angular r b D0 D s qstar j0 t=b := by
  by_cases hj : j0 ≤ j
  · rw [angular_leg r b D0 D s hj (by linarith [pulse_pos j,dwell_pos j]) hhi]
    have hb : base qstar j0 t=1 := Pulses.profile_rest (by simp) (by simp) hj hlo hhi
    rw [hb,PulseTaylor.angular_one]
  · apply angular_initial r b D0 D s
    exact hhi.trans (time_strictMono.monotone (by omega))

end HarmonicCounterexample.AngularStream

end

end OAI
