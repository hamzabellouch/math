import OAI.Probability.SATVariance.OccupationBounds

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_tsum.{u_1} {α : Type u_1} [Fintype α] (f : α → ℕ → ℝ)
    (hf : ∀ a, Summable (f a)) :
    favg (fun a => ∑' m, f a m) = ∑' m, favg (fun a => f a m) := by
  unfold favg
  rw [← Summable.tsum_finsetSum (fun a _ => hf a), tsum_div_const]

lemma lifetime_mono {u s : ℕ} (hsu : s ≤ u) {S T : Finset (Assignment u)} (hST : S ⊆ T) :
    lifetime u s S ≤ lifetime u s T := by
  exact Summable.tsum_le_tsum (survival_mono hST) (survival_summable hsu S)
    (survival_summable hsu T)

lemma lifetime_bellman {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) :
    lifetime u s S = alive u S + clauseStep u s (lifetime u s) S := by
  unfold clauseStep
  simp_rw [lifetime]
  rw [favg_tsum _ (fun _ => survival_summable hsu _)]
  have hs := survival_summable hsu S
  rw [tsum_eq_zero_add' (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h))]
  congr 1
  congr 1
  funext m
  change (clauseStep u s)^[m+1] (alive u) S = _
  rw [Function.iterate_succ_apply']
  rfl

lemma alive_le_lifetime {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) :
    alive u S ≤ lifetime u s S := by
  rw [lifetime_bellman hsu]
  exact le_add_of_nonneg_right (favg_nonneg fun _ => lifetime_nonneg _ _ _)

def markovSum.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ) (f : X → ℝ) : ℕ → X → ℝ
  | 0 => fun _ => 0
  | m+1 => fun x => f x + P 0 (markovSum (fun i => P (i+1)) f m) x

lemma markovSum_mono.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ)
    (hP : ∀ i, Monotone (P i)) {f g : X → ℝ} (hfg : f ≤ g) (m : ℕ) :
    markovSum P f m ≤ markovSum P g m := by
  induction m generalizing P with
  | zero => exact le_rfl
  | succ m ih =>
    intro x
    exact add_le_add (hfg x) (hP 0 (ih _ (fun i => hP (i+1))) x)

lemma markovSum_potential.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ)
    (hP : ∀ i, Monotone (P i))
    (hPc : ∀ i f c, P i (fun x => f x+c) = fun x => P i f x+c)
    (f τ : X → ℝ) (hτ : ∀ x, 0 ≤ τ x) (z : ℕ → ℝ)
    (hdrift : ∀ i x, f x + P i τ x ≤ τ x + z i) (m : ℕ) (x : X) :
    markovSum P f m x ≤ τ x + ∑ i ∈ Finset.range m, z i := by
  induction m generalizing P z x with
  | zero => simpa [markovSum] using hτ x
  | succ m ih =>
    have hi := hP 0 (fun y => ih (fun i => P (i+1)) (fun i => hP (i+1))
      (fun i => hPc (i+1)) (fun i => z (i+1)) (fun i => hdrift (i+1)) y)
    rw [hPc] at hi
    calc
      markovSum P f (m+1) x ≤ f x +
          (P 0 τ x + ∑ i ∈ Finset.range m, z (i+1)) := by
        change f x + P 0 (markovSum (fun i => P (i+1)) f m) x ≤ _
        linarith [hi x]
      _ ≤ τ x + z 0 + ∑ i ∈ Finset.range m, z (i+1) := by linarith [hdrift 0 x]
      _ = _ := by rw [Finset.sum_range_succ']; ring

lemma markovSum_level.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ)
    (hP : ∀ i, Monotone (P i))
    (hPc : ∀ i f c, P i (fun x => f x+c) = fun x => P i f x+c)
    (hPconst : ∀ i c, P i (fun _ => c) = fun _ => c)
    (f τ : X → ℝ) (hτ : ∀ x, 0 ≤ τ x) (z : ℕ → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hdrift : ∀ i x, f x + P i τ x ≤ τ x + z i)
    (e : X → ℝ) (hef : e ≤ f) {C : ℝ} (hC : 0 ≤ C)
    (hlevel : ∀ x, e x ≠ 0 → τ x ≤ C) (m : ℕ) (x : X) :
    markovSum P e m x ≤ C + ∑ i ∈ Finset.range m, z i := by
  induction m generalizing P z x with
  | zero => simpa [markovSum] using hC
  | succ m ih =>
    by_cases he : e x = 0
    · have hi := hP 0 (fun y => ih (fun i => P (i+1)) (fun i => hP (i+1))
        (fun i => hPc (i+1)) (fun i => hPconst (i+1)) (fun i => z (i+1))
        (fun i => hz (i+1)) (fun i => hdrift (i+1)) y)
      rw [hPconst] at hi
      change e x + _ ≤ _
      rw [he, zero_add, Finset.sum_range_succ']
      linarith [hi x, hz 0]
    · exact (markovSum_mono P hP hef (m+1) x).trans
        ((markovSum_potential P hP hPc f τ hτ z hdrift (m+1) x).trans
          (by linarith [hlevel x he]))

def scheduledStep (u k : ℕ) (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ)
    (f : Finset (Assignment u) → ℝ) (S : Finset (Assignment u)) : ℝ :=
  if ordinary i then clauseStep u k f S else f (S ∩ mask i)

lemma scheduledStep_mono (u k : ℕ) (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ) :
    Monotone (scheduledStep u k ordinary mask i) := by
  intro f g h S
  unfold scheduledStep
  split
  · exact clauseStep_mono u k h S
  · exact h _

lemma scheduledStep_const {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ) (c : ℝ) :
    scheduledStep u k ordinary mask i (fun _ => c) = fun _ => c := by
  funext S
  unfold scheduledStep
  split
  · exact congrFun (clauseStep_const hku c) S
  · rfl

lemma scheduledStep_add_const {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ)
    (f : Finset (Assignment u) → ℝ) (c : ℝ) :
    scheduledStep u k ordinary mask i (fun S => f S+c) =
      fun S => scheduledStep u k ordinary mask i f S+c := by
  funext S
  unfold scheduledStep
  split
  · exact congrFun (clauseStep_add_const hku f c) S
  · rfl

lemma scheduledStep_drift {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ) (S : Finset (Assignment u)) :
    alive u S + scheduledStep u k ordinary mask i (lifetime u k) S ≤
      lifetime u k S + if ordinary i then 0 else 1 := by
  unfold scheduledStep
  split
  · simpa using (lifetime_bellman hku S).ge
  · have ht := lifetime_mono hku (Finset.inter_subset_left : S ∩ mask i ⊆ S)
    have hf := alive_le_one u S
    linarith

lemma scheduled_occupation {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (L : ℕ) (S : Finset (Assignment u))
    {a : ℝ} (ha : 0 < a) :
    markovSum (scheduledStep u (r+1) ordinary mask)
      (fun T => if T.Nonempty ∧ a ≤ blockKill u r T d then 1 else 0) L S ≤
      lifetimeC (r+1) * (d : ℝ)^(lifetimeBeta (r+1)) * a^(-lifetimeBeta (r+1)) +
        ∑ i ∈ Finset.range L, if ordinary i then (0 : ℝ) else 1 := by
  apply markovSum_level _ (scheduledStep_mono u (r+1) ordinary mask)
    (scheduledStep_add_const hru ordinary mask) (scheduledStep_const hru ordinary mask)
    (alive u) (lifetime u (r+1)) (lifetime_nonneg _ _) _
    (fun _ => by split <;> norm_num) (scheduledStep_drift hru ordinary mask)
  · intro T
    by_cases hT : T.Nonempty
    · simp only [alive, ite_eq_left hT]
      split <;> norm_num
    · simp [alive, hT]
  · exact mul_nonneg (mul_nonneg (lifetimeC_pos (by omega : 1 ≤ r)).le
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg ha.le _)
  · intro T hT
    have hTa : a ≤ blockKill u r T d := by
      split_ifs at hT with h
      · exact h.2
      · exact (hT rfl).elim
    exact lifetime_level hr hru hd T ha hTa

lemma markovSum_const.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ)
    (hPc : ∀ i c, P i (fun _ => c) = fun _ => c) (c : ℝ) (m : ℕ) :
    markovSum P (fun _ => c) m = fun _ => m*c := by
  induction m generalizing P with
  | zero => funext x; simp [markovSum]
  | succ m ih =>
    funext x
    simp only [markovSum, ih _ (fun i => hPc (i+1)), hPc]
    push_cast
    ring

lemma scheduled_occupation_le_length {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (e : Finset (Assignment u) → ℝ)
    (he : ∀ S, e S ≤ 1) (L : ℕ) (S : Finset (Assignment u)) :
    markovSum (scheduledStep u k ordinary mask) e L S ≤ L := by
  have hm := markovSum_mono _ (scheduledStep_mono u k ordinary mask) he L S
  rw [markovSum_const _ (scheduledStep_const hku ordinary mask) 1] at hm
  simpa using hm

lemma tailIndicator_antitone (x : ℝ) :
    Antitone (fun a : ℝ => if a ≤ x then (1 : ℝ) else 0) := by
  intro a b hab
  dsimp only
  by_cases hb : b ≤ x
  · simp [hb, hab.trans hb]
  · simp only [ite_eq_right hb]
    split <;> norm_num

lemma integral_tailIndicator {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (∫ a in (0 : ℝ)..1, if a ≤ x then (1 : ℝ) else 0) = x := by
  have h := intervalIntegral.integral_indicator (μ := volume)
    (f := fun _ : ℝ => (1 : ℝ)) (show x ∈ Set.Icc 0 1 from ⟨hx, hx1⟩)
  simpa [Set.indicator, intervalIntegral.integral_const] using h

lemma favg_integral.{u_1} {α : Type u_1} [Fintype α] (f : α → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ x, IntervalIntegrable (f x) volume a b) :
    favg (fun x => ∫ t in a..b, f x t) = ∫ t in a..b, favg (fun x => f x t) := by
  unfold favg
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum (fun x _ => hf x)]

lemma scheduledStep_antitone {u k : ℕ}
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ)
    (f : ℝ → Finset (Assignment u) → ℝ) (hf : ∀ S, Antitone (fun a => f a S))
    (S : Finset (Assignment u)) :
    Antitone (fun a => scheduledStep u k ordinary mask i (f a) S) := by
  intro a b hab
  exact scheduledStep_mono u k ordinary mask i (fun T => hf T hab) S

lemma scheduledStep_integral {u k : ℕ}
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ)
    (f : ℝ → Finset (Assignment u) → ℝ) (hf : ∀ S, Antitone (fun a => f a S))
    (S : Finset (Assignment u)) (a b : ℝ) :
    scheduledStep u k ordinary mask i (fun T => ∫ t in a..b, f t T) S =
      ∫ t in a..b, scheduledStep u k ordinary mask i (f t) S := by
  unfold scheduledStep
  split
  · simpa only [clauseStep] using favg_integral
      (fun c : Clause u k => fun t => f t (S.filter (Satisfies c)))
      (fun c => (hf _).intervalIntegrable)
  · rfl

lemma scheduledSum_antitone {u k : ℕ}
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u))
    (f : ℝ → Finset (Assignment u) → ℝ) (hf : ∀ S, Antitone (fun a => f a S))
    (L : ℕ) (S : Finset (Assignment u)) :
    Antitone (fun a => markovSum (scheduledStep u k ordinary mask) (f a) L S) := by
  intro a b hab
  exact markovSum_mono _ (scheduledStep_mono u k ordinary mask) (fun T => hf T hab) L S

lemma scheduledSum_integral {u k : ℕ}
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u))
    (f : ℝ → Finset (Assignment u) → ℝ) (hf : ∀ S, Antitone (fun a => f a S))
    (L : ℕ) (S : Finset (Assignment u)) (a b : ℝ) :
    markovSum (scheduledStep u k ordinary mask) (fun T => ∫ t in a..b, f t T) L S =
      ∫ t in a..b, markovSum (scheduledStep u k ordinary mask) (f t) L S := by
  induction L generalizing ordinary mask S with
  | zero => simp [markovSum]
  | succ L ih =>
    change (∫ t in a..b, f t S) + scheduledStep u k ordinary mask 0
      (markovSum (scheduledStep u k (fun i => ordinary (i+1)) (fun i => mask (i+1)))
        (fun T => ∫ t in a..b, f t T) L) S = _
    have he : markovSum (scheduledStep u k (fun i => ordinary (i+1)) (fun i => mask (i+1)))
        (fun T => ∫ t in a..b, f t T) L =
        fun T => ∫ t in a..b, markovSum
          (scheduledStep u k (fun i => ordinary (i+1)) (fun i => mask (i+1))) (f t) L T := by
      funext T
      exact ih _ _ T
    rw [he, scheduledStep_integral _ _ _ _
      (fun T => scheduledSum_antitone _ _ f hf L T)]
    exact (intervalIntegral.integral_add (hf S).intervalIntegrable
      (scheduledStep_antitone _ _ _ _
        (fun T => scheduledSum_antitone _ _ f hf L T) S).intervalIntegrable).symm

lemma scheduled_layercake {u k : ℕ}
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (f : Finset (Assignment u) → ℝ)
    (hf : ∀ S, 0 ≤ f S) (hf1 : ∀ S, f S ≤ 1)
    (L : ℕ) (S : Finset (Assignment u)) :
    markovSum (scheduledStep u k ordinary mask) f L S =
      ∫ a in (0 : ℝ)..1, markovSum (scheduledStep u k ordinary mask)
        (fun T => if a ≤ f T then 1 else 0) L S := by
  have he : f = fun T => ∫ a in (0 : ℝ)..1, if a ≤ f T then (1 : ℝ) else 0 := by
    funext T
    exact (integral_tailIndicator (hf T) (hf1 T)).symm
  conv_lhs => rw [he]
  exact scheduledSum_integral _ _ _ (fun T => tailIndicator_antitone (f T)) L S 0 1

lemma scheduled_reward_tail {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (f : Finset (Assignment u) → ℝ)
    (hfempty : f ∅ = 0) {θ Q : ℝ}
    (hθ : 0 ≤ θ) (hQ : 0 ≤ Q)
    (hprod : ∀ S, lifetime u k S * (f S)^θ ≤ Q) (L : ℕ)
    (S : Finset (Assignment u)) {a : ℝ} (ha : 0 < a) :
    markovSum (scheduledStep u k ordinary mask)
      (fun T => if a ≤ f T then 1 else 0) L S ≤ Q*a^(-θ) +
        ∑ i ∈ Finset.range L, if ordinary i then (0 : ℝ) else 1 := by
  apply markovSum_level _ (scheduledStep_mono u k ordinary mask)
    (scheduledStep_add_const hku ordinary mask) (scheduledStep_const hku ordinary mask)
    (alive u) (lifetime u k) (lifetime_nonneg _ _) _
    (fun _ => by split <;> norm_num) (scheduledStep_drift hku ordinary mask)
  · intro T
    dsimp only
    by_cases hT : T.Nonempty
    · simp only [alive, ite_eq_left hT]
      split <;> norm_num
    · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      subst T
      simp [alive, hfempty, not_le.mpr ha]
  · exact mul_nonneg hQ (Real.rpow_nonneg ha.le _)
  · intro T hT
    have hTa : a ≤ f T := by
      split_ifs at hT with h
      · exact h
      · exact (hT rfl).elim
    have hp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le hTa hθ)
      (lifetime_nonneg u k T)
    rw [Real.rpow_neg ha.le, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos ha _)).2 (hp.trans (hprod T))

lemma scheduled_reward_tail_bound {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (f : Finset (Assignment u) → ℝ)
    (hfempty : f ∅ = 0) {θ Q Z : ℝ} (hθ : 0 ≤ θ) (hQ : 0 ≤ Q) (hZ : 0 ≤ Z)
    (hprod : ∀ S, lifetime u k S * (f S)^θ ≤ Q) (L : ℕ)
    (hcount : (∑ i ∈ Finset.range L, if ordinary i then (0 : ℝ) else 1) ≤ Z)
    (S : Finset (Assignment u)) {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    markovSum (scheduledStep u k ordinary mask)
      (fun T => if a ≤ f T then 1 else 0) L S ≤ (Q+Z+1)*a^(-θ) := by
  have hp : 1 ≤ a^(-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    ha.1 ha.2.le (neg_nonpos.mpr hθ)
  have ht := scheduled_reward_tail hku ordinary mask f hfempty hθ hQ hprod L S ha.1
  nlinarith [mul_nonneg hZ (sub_nonneg.mpr hp)]

lemma scheduled_reward_integrated_subcritical {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (f : Finset (Assignment u) → ℝ)
    (hfempty : f ∅ = 0) (hf : ∀ S, 0 ≤ f S) (hf1 : ∀ S, f S ≤ 1)
    {θ Q Z : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hQ : 0 ≤ Q) (hZ : 0 ≤ Z)
    (hprod : ∀ S, lifetime u k S * (f S)^θ ≤ Q) (L : ℕ)
    (hcount : (∑ i ∈ Finset.range L, if ordinary i then (0 : ℝ) else 1) ≤ Z)
    (S : Finset (Assignment u)) :
    markovSum (scheduledStep u k ordinary mask) f L S ≤ (Q+Z+1)/(1-θ) := by
  rw [scheduled_layercake ordinary mask f hf hf1 L S]
  apply integrated_tail_subcritical
    (scheduledSum_antitone ordinary mask _ (fun T => tailIndicator_antitone (f T)) L S) hθ1
  intro a ha
  exact scheduled_reward_tail_bound hku ordinary mask f hfempty hθ hQ hZ hprod L hcount S ha

lemma scheduled_reward_integrated_critical {u k : ℕ} (hku : k ≤ u)
    (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (f : Finset (Assignment u) → ℝ)
    (hfempty : f ∅ = 0) (hf : ∀ S, 0 ≤ f S) (hf1 : ∀ S, f S ≤ 1)
    {Q Z : ℝ} (hQ : 0 ≤ Q) (hZ : 0 ≤ Z)
    (hprod : ∀ S, lifetime u k S * f S ≤ Q) {L : ℕ} (hL : 1 ≤ L)
    (hcount : (∑ i ∈ Finset.range L, if ordinary i then (0 : ℝ) else 1) ≤ Z)
    (S : Finset (Assignment u)) :
    markovSum (scheduledStep u k ordinary mask) f L S ≤ (Q+Z+1)*(1+Real.log L) := by
  rw [scheduled_layercake ordinary mask f hf hf1 L S]
  apply integrated_tail_critical
    (scheduledSum_antitone ordinary mask _ (fun T => tailIndicator_antitone (f T)) L S)
    (by linarith) (by exact_mod_cast hL)
  · intro a
    exact scheduled_occupation_le_length hku ordinary mask _
      (fun T => by split <;> norm_num) L S
  · intro a ha
    have ht := scheduled_reward_tail_bound hku ordinary mask f hfempty
      (by norm_num : (0 : ℝ) ≤ 1) hQ hZ (by simpa using hprod) L hcount S ha
    simpa [Real.rpow_neg_one, div_eq_mul_inv] using ht

def occupationGamma (k : ℕ) : ℝ := (k : ℝ)-lifetimeBeta k

lemma occupationGamma_succ {r : ℕ} (hr : 2 ≤ r) :
    occupationGamma (r+1) = lifetimeBeta (r+1) * ((r-1 : ℕ) : ℝ) := by
  rw [occupationGamma, lifetimeBeta_succ (by omega), Nat.cast_add, Nat.cast_one,
    Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  have hr₀ : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  field_simp

lemma occupationGamma_pos {r : ℕ} (hr : 2 ≤ r) : 0 < occupationGamma (r+1) := by
  rw [occupationGamma_succ hr, lifetimeBeta_succ (by omega)]
  have h : (0 : ℝ) < ((r-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < r-1)
  positivity

def occupationReward (u r d : ℕ) (S : Finset (Assignment u)) : ℝ :=
  if S.Nonempty then (blockKill u r S d)^(occupationGamma (r+1)) else 0

lemma occupationReward_nonneg (u r d : ℕ) (S : Finset (Assignment u)) :
    0 ≤ occupationReward u r d S := by
  unfold occupationReward
  split
  · exact Real.rpow_nonneg (blockKill_nonneg _ _ _ _) _
  · rfl

lemma occupationReward_le_one {u r : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (d : ℕ) (S : Finset (Assignment u)) : occupationReward u r d S ≤ 1 := by
  unfold occupationReward
  split
  · exact Real.rpow_le_one (blockKill_nonneg _ _ _ _) (blockKill_le_one (by omega) _ _)
      (occupationGamma_pos hr).le
  · norm_num

lemma occupationReward_product {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    (S : Finset (Assignment u)) :
    lifetime u (r+1) S * (occupationReward u r d S)^(((r-1 : ℕ) : ℝ)⁻¹) ≤
      lifetimeC (r+1) * (d : ℝ)^(lifetimeBeta (r+1)) := by
  have hθ : (0 : ℝ) < (((r-1 : ℕ) : ℝ)⁻¹) := by
    exact inv_pos.mpr (by exact_mod_cast (by omega : 0 < r-1))
  unfold occupationReward
  split
  · rw [← Real.rpow_mul (blockKill_nonneg _ _ _ _), occupationGamma_succ hr,
      mul_inv_cancel_right₀ (by exact_mod_cast (by omega : r-1 ≠ 0) : ((r-1 : ℕ) : ℝ) ≠ 0)]
    exact lifetime_product hr hru hd S
  · rw [Real.zero_rpow hθ.ne', mul_zero]
    exact mul_nonneg (lifetimeC_pos (by omega : 1 ≤ r)).le (Real.rpow_nonneg (by positivity) _)

end RandomKSAT

end

end OAI
