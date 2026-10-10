import OAI.Probability.SATVariance.HiddenTests

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma markovSum_projection.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
    (P : ℕ → (X → ℝ) → X → ℝ) (Q : ℕ → (Y → ℝ) → Y → ℝ)
    (π : X → Y) (hπ : ∀ i f x, P i (fun y => f (π y)) x = Q i f (π x))
    (f : Y → ℝ) (M : ℕ) (x : X) :
    markovSum P (fun y => f (π y)) M x = markovSum Q f M (π x) := by
  induction M generalizing P Q x with
  | zero => rfl
  | succ M ih =>
    simp only [markovSum]
    have he : markovSum (fun i => P (i+1)) (fun y => f (π y)) M =
        fun y => markovSum (fun i => Q (i+1)) f M (π y) := by
      funext y
      exact ih _ _ (fun i => hπ (i+1)) y
    rw [he, hπ]

lemma rootSum_projection {u k : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (f : Finset (Assignment u) → ℝ) (M : ℕ) (S : PairState u k) :
    markovSum (uniformStep (pairEvolution a env)) (fun T => f (fibre a T)) M S =
      markovSum (scheduledStep u k (fun i => rootSize (env i).1 = 0)
        (fun i => dataMask (env i) a)) f M (fibre a S) :=
  markovSum_projection _ _ _ (pairEvolution_fibre_operator hku a env) f M S

lemma fibre_univ {u k : ℕ} (a : Assignment k) :
    fibre (u := u) a Finset.univ = Finset.univ := by ext b; simp [fibre]

lemma rootSum_test_bound {u k M d : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (J : Finset (Fin k))
    (hJ : ∀ j ∈ J, Available a (fun i : Fin M => env i) j)
    (hd : ∀ m j, (testIndices a (fun i : Fin M => env i) m j).card ≤ d)
    (w : Finset (Assignment u) → ℝ) (hw : ∀ S, 0 ≤ w S) :
    markovSum (uniformStep (pairEvolution a env))
      (fun T => forcedReward a T * w (fibre a T)) M Finset.univ ≤
    markovSum (scheduledStep u k (fun i => rootSize (env i).1 = 0)
      (fun i => dataMask (env i) a))
      (fun S => w S * (alive u S * blockKill u (k-1) S d ^ J.card)) M Finset.univ := by
  let := clause_nonempty u k hku
  let := clause_nonempty u (k-1) (by omega)
  rw [← fibre_univ (u := u) a, ← rootSum_projection hku]
  rw [← rootRewards_avg hku, ← rootRewards_avg hku]
  rw [favg_noiseWord, favg_noiseWord]
  apply favg_mono
  intro o
  unfold dataRewards
  rw [favg_sum, favg_sum]
  apply Finset.sum_le_sum
  intro m _
  simp only [fibre_pairPrefix_refresh]
  have he : favg (fun ys : Fin k → Fin M → Clause u (k-1) =>
      forcedReward a (pairPrefix Finset.univ
        (fun i => refreshData a (env i) (o i,fun j => ys j i)) m.val) *
        w (fibrePrefix a (fun i : Fin M => env i) o m.val)) =
      w (fibrePrefix a (fun i : Fin M => env i) o m.val) *
      favg (fun ys : Fin k → Fin M → Clause u (k-1) =>
        forcedReward a (pairPrefix Finset.univ
          (fun i => refreshData a (env i) (o i,fun j => ys j i)) m.val)) := by
    simp_rw [mul_comm _ (w _)]
    exact favg_mul _ _
  rw [he, favg_const]
  exact mul_le_mul_of_nonneg_left (forcedPrefix_probability hku a _ o m.val J hJ (hd _)) (hw _)

def incidentSet {u k M : ℕ} (env : Fin M → RootData u k) : Finset (Fin M) :=
  Finset.univ.filter fun i => rootSize (env i).1 ≠ 0

def collisionSet {u k M : ℕ} (env : Fin M → RootData u k) : Finset (Fin M) :=
  Finset.univ.filter fun i => 2 ≤ rootSize (env i).1

lemma testIndices_card_le {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (m : ℕ) (j : Fin k) : (testIndices a env m j).card ≤ (incidentSet env).card := by
  apply Finset.card_le_card
  intro i hi
  have hh := (Finset.mem_filter.mp hi).2.2.1
  simp [incidentSet, hh]

lemma incidentSet_sum {u k : ℕ} (env : ℕ → RootData u k) (M : ℕ) :
    (∑ i ∈ Finset.range M, if rootSize (env i).1 = 0 then (0 : ℝ) else 1) =
      ((incidentSet (fun i : Fin M => env i)).card : ℝ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [incidentSet, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

lemma available_of_no_collision {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (hV : (collisionSet env).card = 0) (j : Fin k) : Available a env j := by
  intro i hi
  have hm : i ∈ collisionSet env := by simp [collisionSet, hi]
  rw [Finset.card_eq_zero.mp hV] at hm
  exact (Finset.notMem_empty i hm).elim

lemma uniqueTrue_injective {k : ℕ} (t : RootType k) (a : Assignment k) {i j : Fin k}
    (hi : UniqueTrue t a i) (hj : UniqueTrue t a j) : i = j := by
  by_contra h
  exact hj.2 i h hi.1

lemma available_except_one {u k M : ℕ} (hk : 1 ≤ k) (a : Assignment k)
    (env : Fin M → RootData u k) (hV : (collisionSet env).card ≤ 1) :
    ∃ j₀ : Fin k, ∀ j, j ≠ j₀ → Available a env j := by
  by_cases hbad : ∃ j : Fin k, ¬ Available a env j
  · obtain ⟨j₀,hj₀⟩ := hbad
    refine ⟨j₀,fun j hj i hi hij => ?_⟩
    obtain ⟨i₀,hi₀,hij₀⟩ : ∃ i, 2 ≤ rootSize (env i).1 ∧ UniqueTrue (env i).1 a j₀ := by
      simp only [Available] at hj₀
      push Not at hj₀
      exact hj₀
    have he : i = i₀ := Finset.card_le_one.mp hV i
      (by simp [collisionSet, hi]) i₀ (by simp [collisionSet, hi₀])
    subst i₀
    exact hj (uniqueTrue_injective _ _ hij hij₀)
  · refine ⟨⟨0, by omega⟩, fun j _ => ?_⟩
    by_contra hj
    exact hbad ⟨j,hj⟩

lemma lifetimeBeta_bounds {r : ℕ} (hr : 2 ≤ r) :
    1 ≤ lifetimeBeta (r+1) ∧ lifetimeBeta (r+1) ≤ (r : ℝ) ∧
      2*lifetimeBeta (r+1) ≤ 3 := by
  rw [lifetimeBeta_succ (by omega)]
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hi : (0 : ℝ) ≤ (r : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hj : (r : ℝ)⁻¹ ≤ 1/2 := by
    apply (inv_le_iff_one_le_mul₀ (by positivity)).2
    linarith
  constructor
  · linarith
  constructor <;> linarith

def deletionQ (k d : ℕ) : ℝ := (lifetimeC k+1)*(d : ℝ)^(lifetimeBeta k)

lemma deletionQ_nonneg {r d : ℕ} (hr : 2 ≤ r) : 0 ≤ deletionQ (r+1) d := by
  unfold deletionQ
  exact mul_nonneg (by linarith [lifetimeC_pos (by omega : 1 ≤ r)])
    (Real.rpow_nonneg (by positivity) _)

lemma lifetime_weight_product {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d) (S : Finset (Assignment u)) :
    (lifetime u (r+1) S+Z) * (blockKill u r S d)^(lifetimeBeta (r+1)) ≤ deletionQ (r+1) d := by
  have hb := lifetimeBeta_bounds hr
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (d : ℝ) ≤ (d : ℝ)^(lifetimeBeta (r+1)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hd1 hb.1
  have hq := Real.rpow_le_one (blockKill_nonneg u r S d) (blockKill_le_one (by omega) S d)
    (by linarith : 0 ≤ lifetimeBeta (r+1))
  have ht := lifetime_product hr hru hd S
  unfold deletionQ
  nlinarith [mul_nonneg hZ (sub_nonneg.mpr hq)]

lemma weighted_all_tests {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d) (S : Finset (Assignment u)) :
    (lifetime u (r+1) S+Z) * (alive u S * blockKill u r S d ^ (r+1)) ≤
      deletionQ (r+1) d * occupationReward u r d S := by
  by_cases hS : S.Nonempty
  · simp only [alive, occupationReward, ite_eq_left hS, one_mul]
    by_cases hq : blockKill u r S d = 0
    · simp only [hq, zero_pow (by omega : r+1 ≠ 0), mul_zero]
      exact mul_nonneg (deletionQ_nonneg hr) (Real.rpow_nonneg (by norm_num) _)
    · have hqp : 0 < blockKill u r S d := lt_of_le_of_ne (blockKill_nonneg _ _ _ _) (Ne.symm hq)
      have he : (blockKill u r S d)^(r+1) =
          (blockKill u r S d)^(lifetimeBeta (r+1)) * (blockKill u r S d)^(occupationGamma (r+1)) := by
        rw [← Real.rpow_add hqp, occupationGamma]
        simp only [add_sub_cancel, Real.rpow_natCast]
      rw [he, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (lifetime_weight_product hr hru hd hZ hZd S)
        (Real.rpow_nonneg hqp.le _)
  · simp [alive, occupationReward, hS]

lemma weighted_all_but_one_test {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d) (S : Finset (Assignment u)) :
    (lifetime u (r+1) S+Z) * (alive u S * blockKill u r S d ^ r) ≤ deletionQ (r+1) d := by
  by_cases hS : S.Nonempty
  · simp only [alive, ite_eq_left hS, one_mul]
    by_cases hq : blockKill u r S d = 0
    · simpa only [hq, zero_pow (by omega : r ≠ 0), mul_zero] using deletionQ_nonneg (d := d) hr
    · have hqp : 0 < blockKill u r S d := lt_of_le_of_ne (blockKill_nonneg _ _ _ _) (Ne.symm hq)
      have hpow : (blockKill u r S d)^r ≤ (blockKill u r S d)^(lifetimeBeta (r+1)) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge hqp (blockKill_le_one (by omega) S d)
          (lifetimeBeta_bounds hr).2.1
      exact (mul_le_mul_of_nonneg_left hpow (add_nonneg (lifetime_nonneg _ _ _) hZ)).trans
        (lifetime_weight_product hr hru hd hZ hZd S)
  · simp only [alive, ite_eq_right hS, zero_mul, mul_zero]
    exact deletionQ_nonneg hr

lemma scheduledStep_mul (u k : ℕ) (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ) (c : ℝ) (f : Finset (Assignment u) → ℝ) :
    scheduledStep u k ordinary mask i (fun S => c*f S) =
      fun S => c*scheduledStep u k ordinary mask i f S := by
  funext S
  unfold scheduledStep
  split
  · exact favg_mul c _
  · rfl

lemma rootRewards_square_test_bound {u k M d : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (J : Finset (Fin k))
    (hJ : ∀ j ∈ J, Available a (fun i : Fin M => env i) j)
    (hd : ∀ m j, (testIndices a (fun i : Fin M => env i) m j).card ≤ d)
    {Z : ℝ} (hZ : 0 ≤ Z)
    (hcount : ((incidentSet (fun i : Fin M => env i)).card : ℝ) ≤ Z) :
    favg (fun z : Fin M → RefreshNoise u k =>
      (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i)))^2) ≤
      2*markovSum (scheduledStep u k (fun i => rootSize (env i).1 = 0)
        (fun i => dataMask (env i) a))
        (fun S => (lifetime u k S+Z)*(alive u S * blockKill u (k-1) S d ^ J.card)) M Finset.univ := by
  have hh := rootPath_square hku a env M (Z := Z) (by rw [incidentSet_sum]; exact hcount) (Finset.univ : PairState u k)
  simp_rw [rootPath_eq_rewards] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (rootSum_test_bound hku a env J hJ hd (fun S : Finset (Assignment u) => lifetime u k S+Z)
      (fun S => add_nonneg (lifetime_nonneg _ _ _) hZ)) (by norm_num))

def durationLog (k M : ℕ) : ℝ := if k = 3 then 1+Real.log (M+1) else 1

lemma durationLog_one_le (k M : ℕ) : 1 ≤ durationLog k M := by
  unfold durationLog
  split
  · have h : (1 : ℝ) ≤ M+1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
    linarith [Real.log_nonneg h]
  · rfl

lemma integrated_occupationReward {u r d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u) (hd : 1 ≤ d)
    (ordinary : ℕ → Prop) [DecidablePred ordinary] (mask : ℕ → Finset (Assignment u))
    (M : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d)
    (hcount : (∑ i ∈ Finset.range M, if ordinary i then (0 : ℝ) else 1) ≤ Z)
    (S : Finset (Assignment u)) :
    markovSum (scheduledStep u (r+1) ordinary mask) (occupationReward u r d) M S ≤
      4*deletionQ (r+1) d * durationLog (r+1) M := by
  let Q := lifetimeC (r+1)*(d : ℝ)^(lifetimeBeta (r+1))
  have hQ : 0 ≤ Q := mul_nonneg (lifetimeC_pos (by omega : 1 ≤ r)).le (Real.rpow_nonneg (by positivity) _)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (d : ℝ) ≤ (d : ℝ)^(lifetimeBeta (r+1)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hd1 (lifetimeBeta_bounds hr).1
  have hbound : Q+Z+1 ≤ 2*deletionQ (r+1) d := by
    dsimp only [Q, deletionQ]
    have hc := lifetimeC_pos (by omega : 1 ≤ r)
    nlinarith [Real.rpow_nonneg (x := (d : ℝ)) (by positivity) (lifetimeBeta (r+1))]
  have he : occupationReward u r d ∅ = 0 := by simp [occupationReward]
  by_cases hr2 : r = 2
  · subst r
    by_cases hM : M = 0
    · subst M
      simp only [markovSum]
      exact mul_nonneg (mul_nonneg (by norm_num) (deletionQ_nonneg (by omega)))
        (le_trans (by norm_num) (durationLog_one_le _ _))
    · have hp (T : Finset (Assignment u)) : lifetime u 3 T * occupationReward u 2 d T ≤ Q := by
        simpa using occupationReward_product (by omega : 2 ≤ 2) hru hd T
      have hh := scheduled_reward_integrated_critical hru ordinary mask (occupationReward u 2 d)
        he (occupationReward_nonneg _ _ _) (occupationReward_le_one (by omega) hru d)
        hQ hZ hp (by omega : 1 ≤ M) hcount S
      have hlog := Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) (by norm_num : (M : ℝ) ≤ M+1)
      have hpos : 0 ≤ 1+Real.log (M : ℝ) := by
        have h := Real.log_nonneg (show (1 : ℝ) ≤ (M : ℝ) by exact_mod_cast (by omega : 1 ≤ M))
        linarith
      simp only [durationLog, show 2+1=3 from rfl, ↓reduceIte]
      have hbprod := mul_le_mul_of_nonneg_right hbound hpos
      nlinarith [mul_nonneg (deletionQ_nonneg (d := d) (by omega : 2 ≤ 2))
        (sub_nonneg.mpr hlog), mul_nonneg (deletionQ_nonneg (d := d) (by omega : 2 ≤ 2)) hpos]
  · have hr3 : 3 ≤ r := by omega
    have hθ : 0 ≤ (((r-1 : ℕ) : ℝ)⁻¹) := by positivity
    have hθ2 : (((r-1 : ℕ) : ℝ)⁻¹) ≤ 1/2 := by
      apply (inv_le_iff_one_le_mul₀ (by exact_mod_cast (by omega : 0 < r-1))).2
      have h : (2 : ℝ) ≤ (r-1 : ℕ) := by exact_mod_cast (by omega : 2 ≤ r-1)
      linarith
    have hθ1 : (((r-1 : ℕ) : ℝ)⁻¹) < 1 := by linarith
    have hh := scheduled_reward_integrated_subcritical hru ordinary mask (occupationReward u r d)
      he (occupationReward_nonneg _ _ _) (occupationReward_le_one hr hru d)
      hθ hθ1 hQ hZ (occupationReward_product hr hru hd) M hcount S
    have hdiv : (Q+Z+1)/(1-(((r-1 : ℕ) : ℝ)⁻¹)) ≤ 2*(Q+Z+1) := by
      apply (div_le_iff₀ (by linarith)).2
      nlinarith
    simp only [durationLog, ite_eq_right (by omega : r+1 ≠ 3), mul_one]
    exact hh.trans (hdiv.trans (by linarith))

lemma rootRewards_square_no_collision {u r M d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (hd : 1 ≤ d) (a : Assignment (r+1)) (env : ℕ → RootData u (r+1))
    (hV : (collisionSet (fun i : Fin M => env i)).card = 0)
    {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d)
    (hcount : ((incidentSet (fun i : Fin M => env i)).card : ℝ) ≤ Z) :
    favg (fun z : Fin M → RefreshNoise u (r+1) =>
      (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i)))^2) ≤
      8*(deletionQ (r+1) d)^2*durationLog (r+1) M := by
  have htests (m) (j : Fin (r+1)) :
      (testIndices a (fun i : Fin M => env i) m j).card ≤ d := by
    have hh := testIndices_card_le a (fun i : Fin M => env i) m j
    have hh' : ((incidentSet (fun i : Fin M => env i)).card : ℝ) ≤ d := hcount.trans hZd
    exact hh.trans (by exact_mod_cast hh')
  have hh := rootRewards_square_test_bound hru a env Finset.univ
    (fun j _ => available_of_no_collision a _ hV j) htests hZ hcount
  simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at hh
  have hm := markovSum_mono _
    (scheduledStep_mono u (r+1) (fun i => rootSize (env i).1 = 0) (fun i => dataMask (env i) a))
    (weighted_all_tests hr hru hd hZ hZd) M (Finset.univ : Finset (Assignment u))
  rw [markovSum_mul _ (scheduledStep_mul _ _ _ _)] at hm
  have ho := integrated_occupationReward hr hru hd (fun i => rootSize (env i).1 = 0)
    (fun i => dataMask (env i) a) M hZ hZd (by rw [incidentSet_sum]; exact hcount) Finset.univ
  have hp := mul_le_mul_of_nonneg_left ho (deletionQ_nonneg (d := d) hr)
  nlinarith

lemma rootRewards_square_one_collision {u r M d : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (hd : 1 ≤ d) (a : Assignment (r+1)) (env : ℕ → RootData u (r+1))
    (hV : (collisionSet (fun i : Fin M => env i)).card ≤ 1)
    {Z : ℝ} (hZ : 0 ≤ Z) (hZd : Z ≤ d)
    (hcount : ((incidentSet (fun i : Fin M => env i)).card : ℝ) ≤ Z) :
    favg (fun z : Fin M → RefreshNoise u (r+1) =>
      (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i)))^2) ≤
      2*M*deletionQ (r+1) d := by
  obtain ⟨j₀,hj₀⟩ := available_except_one (by omega : 1 ≤ r+1) a _ hV
  have htests (m) (j : Fin (r+1)) :
      (testIndices a (fun i : Fin M => env i) m j).card ≤ d := by
    have hh := testIndices_card_le a (fun i : Fin M => env i) m j
    have hh' : ((incidentSet (fun i : Fin M => env i)).card : ℝ) ≤ d := hcount.trans hZd
    exact hh.trans (by exact_mod_cast hh')
  have hh := rootRewards_square_test_bound hru a env (Finset.univ.erase j₀)
    (fun j hj => hj₀ j (Finset.mem_erase.mp hj).1) htests hZ hcount
  have hc : (Finset.univ.erase j₀).card = r := by simp
  rw [hc] at hh
  simp only [Nat.add_sub_cancel] at hh
  have hm := markovSum_mono _
    (scheduledStep_mono u (r+1) (fun i => rootSize (env i).1 = 0) (fun i => dataMask (env i) a))
    (weighted_all_but_one_test hr hru hd hZ hZd) M (Finset.univ : Finset (Assignment u))
  rw [markovSum_const _ (scheduledStep_const hru _ _)] at hm
  nlinarith

lemma dataRewards_nonneg {u k M : ℕ} (a : Assignment k) (S : PairState u k)
    (ps : Fin M → RootData u k) : 0 ≤ dataRewards (forcedReward a) S ps :=
  Finset.sum_nonneg fun _ _ => forcedReward_nonneg _ _

lemma dataRewards_le_length {u k M : ℕ} (a : Assignment k) (S : PairState u k)
    (ps : Fin M → RootData u k) : dataRewards (forcedReward a) S ps ≤ M := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) (fun i _ => forcedReward_le_one a (pairPrefix S ps i.val))
  simpa [dataRewards] using hh

lemma rootRewards_square_conditioned {u r M : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (a : Assignment (r+1)) (env : ℕ → RootData u (r+1)) :
    let Z := (incidentSet (fun i : Fin M => env i)).card
    let V : ℝ := (collisionSet (fun i : Fin M => env i)).card
    let Q := deletionQ (r+1) (max 1 Z)
    favg (fun z : Fin M → RefreshNoise u (r+1) =>
      (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i)))^2) ≤
      8*Q^2*durationLog (r+1) M + 2*M*Q*V + (M : ℝ)^2*V*(V-1) := by
  dsimp only
  let Z := (incidentSet (fun i : Fin M => env i)).card
  let V := (collisionSet (fun i : Fin M => env i)).card
  let Q := deletionQ (r+1) (max 1 Z)
  have hQ : 0 ≤ Q := deletionQ_nonneg hr
  have hZF : (Z : ℝ) ≤ (max 1 Z : ℕ) := by exact_mod_cast le_max_right 1 Z
  have hterm : 0 ≤ 8*Q^2*durationLog (r+1) M := by
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (le_trans (by norm_num) (durationLog_one_le _ _))
  change _ ≤ 8*Q^2*durationLog (r+1) M+2*M*Q*(V : ℝ)+(M : ℝ)^2*V*(V-1)
  by_cases hV : V = 0
  · have hh := rootRewards_square_no_collision hr hru (le_max_left 1 Z) a env hV
      (Nat.cast_nonneg Z) hZF (le_refl (Z : ℝ))
    simpa only [hV, Nat.cast_zero, mul_zero, zero_mul, add_zero] using hh
  by_cases hV1 : V ≤ 1
  · have he : V = 1 := by omega
    have hh := rootRewards_square_one_collision hr hru (le_max_left 1 Z) a env hV1
      (Nat.cast_nonneg Z) hZF (le_refl (Z : ℝ))
    simp only [he, Nat.cast_one, mul_one, sub_self, mul_zero, add_zero]
    exact hh.trans (le_add_of_nonneg_left hterm)
  · have hv : (2 : ℝ) ≤ V := by exact_mod_cast (by omega : 2 ≤ V)
    have htriv : favg (fun z : Fin M → RefreshNoise u (r+1) =>
        (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (env i) (z i)))^2) ≤ (M : ℝ)^2 := by
      let := clause_nonempty u (r+1) hru
      let := clause_nonempty u ((r+1)-1) (by omega)
      exact (favg_mono (fun z => pow_le_pow_left₀ (dataRewards_nonneg a _ _) (dataRewards_le_length a _ _) 2)).trans_eq (favg_const _)
    have hfac : 1 ≤ (V : ℝ)*(V-1) := by nlinarith
    have hmfac := mul_le_mul_of_nonneg_left hfac (sq_nonneg (M : ℝ))
    have hmQ : 0 ≤ 2*M*Q*(V : ℝ) := by positivity
    nlinarith

lemma deletionQ_poly_bound {r Z : ℕ} (hr : 2 ≤ r) :
    deletionQ (r+1) (max 1 Z) ≤ (lifetimeC (r+1)+1)*(1+(Z : ℝ))^2 := by
  unfold deletionQ
  have hb := lifetimeBeta_bounds hr
  have hd : (1 : ℝ) ≤ (max 1 Z : ℕ) := by exact_mod_cast le_max_left 1 Z
  have hd' : ((max 1 Z : ℕ) : ℝ) ≤ 1+(Z : ℝ) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) Z]) (by linarith)
  have hp := Real.rpow_le_rpow_of_exponent_le hd (show lifetimeBeta (r+1) ≤ (2 : ℝ) by linarith)
  change _ ≤ ((max 1 Z : ℕ) : ℝ)^((2 : ℕ) : ℝ) at hp
  rw [Real.rpow_natCast] at hp
  apply mul_le_mul_of_nonneg_left (hp.trans (pow_le_pow_left₀ (by positivity) hd' 2))
  linarith [lifetimeC_pos (by omega : 1 ≤ r)]

lemma deletionQ_sq_poly_bound {r Z : ℕ} (hr : 2 ≤ r) :
    (deletionQ (r+1) (max 1 Z))^2 ≤ (lifetimeC (r+1)+1)^2*(1+(Z : ℝ))^3 := by
  unfold deletionQ
  rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
  have hb := lifetimeBeta_bounds hr
  have hd : (1 : ℝ) ≤ (max 1 Z : ℕ) := by exact_mod_cast le_max_left 1 Z
  have hd' : ((max 1 Z : ℕ) : ℝ) ≤ 1+(Z : ℝ) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) Z]) (by linarith)
  have hp := Real.rpow_le_rpow_of_exponent_le hd (show lifetimeBeta (r+1)* (2 : ℝ) ≤ (3 : ℝ) by linarith)
  change _ ≤ ((max 1 Z : ℕ) : ℝ)^((3 : ℕ) : ℝ) at hp
  rw [Real.rpow_natCast] at hp
  exact mul_le_mul_of_nonneg_left (hp.trans (pow_le_pow_left₀ (by positivity) hd' 3)) (sq_nonneg _)

end RandomKSAT

end

end OAI
