import OAI.Probability.SATVariance.FiberRefresh

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

abbrev RootData (u k : ℕ) := (t : RootType k) × Clause u (k-rootSize t)

abbrev PairState (u k : ℕ) := Finset (Assignment k × Assignment u)

def DataSatisfies {u k : ℕ} (p : RootData u k) (x : Assignment k × Assignment u) : Prop :=
  RootSatisfies p.1 x.1 ∨ Satisfies p.2 x.2

def dataStep {u k : ℕ} (p : RootData u k) (S : PairState u k) : PairState u k :=
  S.filter (DataSatisfies p)

def fibre {u k : ℕ} (a : Assignment k) (S : PairState u k) : Finset (Assignment u) :=
  Finset.univ.filter fun b => (a,b) ∈ S

def dataMask {u k : ℕ} (p : RootData u k) (a : Assignment k) : Finset (Assignment u) :=
  Finset.univ.filter fun b => DataSatisfies p (a,b)

lemma fibre_dataStep {u k : ℕ} (p : RootData u k) (a : Assignment k) (S : PairState u k) :
    fibre a (dataStep p S) = fibre a S ∩ dataMask p a := by
  ext b
  simp [fibre, dataStep, dataMask]

lemma rootSatisfies_zero {k : ℕ} (t : RootType k) (h : rootSize t = 0) (a : Assignment k) :
    ¬ RootSatisfies t a := by
  rintro ⟨j,hj⟩
  have hm : j ∈ rootSupport t := by simp [rootSupport, hj]
  have he : rootSupport t = ∅ := Finset.card_eq_zero.mp h
  rw [he] at hm
  exact Finset.notMem_empty j hm

lemma satisfies_cast {u s t : ℕ} (h : s = t) (c : Clause u s) (b : Assignment u) :
    Satisfies (clauseCastEquiv h c) b ↔ Satisfies c b := by
  subst t
  rfl

def refreshData {u k : ℕ} (a : Assignment k) (p : RootData u k)
    (z : RefreshNoise u k) : RootData u k := ⟨p.1,refreshPart p.1 a p.2 z⟩

lemma favg_refreshData {u k : ℕ} (hku : k ≤ u) (a : Assignment k) (f : RootData u k → ℝ) :
    favg (fun p => favg (fun z : RefreshNoise u k => f (refreshData a p z))) = favg f := by
  let (t : RootType k) : Nonempty (Clause u (k-rootSize t)) := clause_nonempty _ _ (by omega)
  rw [favg_sigma, favg_sigma f]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  exact favg_refreshPart hku t a (fun p => f ⟨t,p⟩)

lemma fibre_refreshData {u k : ℕ} (a : Assignment k) (p : RootData u k)
    (z : RefreshNoise u k) (S : PairState u k) :
    fibre a (dataStep (refreshData a p z) S) =
      if rootSize p.1 = 0 then (fibre a S).filter (Satisfies z.1)
      else fibre a S ∩ dataMask p a := by
  ext b
  by_cases h : rootSize p.1 = 0
  · simp [fibre_dataStep, dataMask, DataSatisfies, refreshData, refreshPart, h,
      rootSatisfies_zero p.1 h a, satisfies_cast]
  · by_cases ht : rootSize p.1 = 1 ∧ RootSatisfies p.1 a
    · simp [fibre_dataStep, dataMask, DataSatisfies, refreshData, refreshPart, ht]
    · simp [fibre_dataStep, dataMask, DataSatisfies, refreshData, refreshPart, h, ht]

def forcedReward {u k : ℕ} (a : Assignment k) (S : PairState u k) : ℝ :=
  if S.Nonempty ∧ ∀ x ∈ S, x.1 = a then 1 else 0

lemma forcedReward_nonneg {u k : ℕ} (a : Assignment k) (S : PairState u k) :
    0 ≤ forcedReward a S := by unfold forcedReward; split <;> norm_num

lemma forcedReward_le_one {u k : ℕ} (a : Assignment k) (S : PairState u k) :
    forcedReward a S ≤ 1 := by unfold forcedReward; split <;> norm_num

lemma forcedReward_le_alive {u k : ℕ} (a : Assignment k) (S : PairState u k) :
    forcedReward a S ≤ alive u (fibre a S) := by
  unfold forcedReward
  split_ifs with h
  · obtain ⟨x,hx⟩ := h.1
    have hf : (fibre a S).Nonempty := by
      refine ⟨x.2, ?_⟩
      have he : (a,x.2) = x := by rw [← h.2 x hx]
      simp [fibre, he, hx]
    simp [alive, hf]
  · exact alive_nonneg _ _

def pairEvolution {u k : ℕ} (a : Assignment k) (env : ℕ → RootData u k)
    (i : ℕ) (z : RefreshNoise u k) (S : PairState u k) : PairState u k :=
  dataStep (refreshData a (env i) z) S

lemma pairEvolution_fibre_operator {u k : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (i : ℕ) (f : Finset (Assignment u) → ℝ) (S : PairState u k) :
    uniformStep (pairEvolution a env) i (fun T => f (fibre a T)) S =
      scheduledStep u k (fun i => rootSize (env i).1 = 0) (fun i => dataMask (env i) a) i f (fibre a S) := by
  let := clause_nonempty u k hku
  let := clause_nonempty u (k-1) (by omega)
  unfold uniformStep pairEvolution
  simp_rw [fibre_refreshData]
  by_cases h : rootSize (env i).1 = 0
  · simp only [scheduledStep, h, ite_true]
    rw [favg_prod]
    dsimp only
    have hc (c : Clause u k) :
        favg (fun _ : Fin k → Clause u (k-1) => f ((fibre a S).filter (Satisfies c))) =
        f ((fibre a S).filter (Satisfies c)) := favg_const _
    simp_rw [hc]
    rfl
  · simp only [scheduledStep, h, ite_false]
    exact favg_const _

lemma pairEvolution_drift {u k : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (i : ℕ) (S : PairState u k) :
    forcedReward a S + uniformStep (pairEvolution a env) i (fun T => lifetime u k (fibre a T)) S ≤
      lifetime u k (fibre a S) + (if rootSize (env i).1 = 0 then 0 else 1) := by
  rw [pairEvolution_fibre_operator hku]
  have hd := scheduledStep_drift hku (fun i => rootSize (env i).1 = 0)
    (fun i => dataMask (env i) a) i (fibre a S)
  linarith [forcedReward_le_alive a S]

lemma rootPath_square {u k : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (m : ℕ) {Z : ℝ}
    (hZ : (∑ i ∈ Finset.range m, if rootSize (env i).1 = 0 then (0 : ℝ) else 1) ≤ Z)
    (S : PairState u k) :
    favg (fun w : Fin m → RefreshNoise u k =>
      (pathReward (pairEvolution a env) (forcedReward a) m w S)^2) ≤
      2 * markovSum (uniformStep (pairEvolution a env))
        (fun T => forcedReward a T * (lifetime u k (fibre a T)+Z)) m S := by
  let := clause_nonempty u k hku
  let := clause_nonempty u (k-1) (by omega)
  exact pathReward_sq_potential _ _ _ (forcedReward_nonneg a)
    (fun T => lifetime_nonneg _ _ _) _ (fun _ => by split <;> norm_num)
    (pairEvolution_drift hku a env) m hZ S

def pairPrefix {u k M : ℕ} (S : PairState u k) (ps : Fin M → RootData u k)
    (m : ℕ) : PairState u k :=
  S.filter fun x => ∀ i : Fin M, i.val < m → DataSatisfies (ps i) x

lemma pairPrefix_zero {u k M : ℕ} (S : PairState u k) (ps : Fin M → RootData u k) :
    pairPrefix S ps 0 = S := by ext x; simp [pairPrefix]

lemma pairPrefix_cons {u k M : ℕ} (S : PairState u k) (p : RootData u k)
    (ps : Fin M → RootData u k) (m : ℕ) :
    pairPrefix S (Fin.cons p ps) (m+1) = pairPrefix (dataStep p S) ps m := by
  ext x
  simp only [pairPrefix, dataStep, Finset.mem_filter, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.val_zero, Nat.zero_lt_succ, true_implies,
    Fin.cons_succ, Fin.val_succ, Nat.succ_lt_succ_iff]
  tauto

def dataRewards {u k M : ℕ} (f : PairState u k → ℝ) (S : PairState u k)
    (ps : Fin M → RootData u k) : ℝ := ∑ i : Fin M, f (pairPrefix S ps i.val)

lemma dataRewards_cons {u k M : ℕ} (f : PairState u k → ℝ) (S : PairState u k)
    (p : RootData u k) (ps : Fin M → RootData u k) :
    dataRewards f S (Fin.cons p ps) = f S+dataRewards f (dataStep p S) ps := by
  rw [dataRewards, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, pairPrefix_zero, pairPrefix_cons]
  rfl

lemma rootPath_eq_rewards {u k : ℕ} (a : Assignment k) (env : ℕ → RootData u k)
    (f : PairState u k → ℝ) (M : ℕ) (z : Fin M → RefreshNoise u k) (S : PairState u k) :
    pathReward (pairEvolution a env) f M z S =
      dataRewards f S (fun i => refreshData a (env i) (z i)) := by
  induction M generalizing env S with
  | zero => simp [pathReward, dataRewards]
  | succ M ih =>
    have he : (fun i : Fin (M+1) => refreshData a (env i) (z i)) =
        Fin.cons (refreshData a (env 0) (z 0))
          (fun i : Fin M => refreshData a (env (i+1)) (Fin.tail z i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [he, dataRewards_cons, pathReward]
    change f S + pathReward (pairEvolution a (fun i => env (i+1))) f M (Fin.tail z)
      (dataStep (refreshData a (env 0) (z 0)) S) = _
    rw [ih]

lemma rootRewards_avg {u k : ℕ} (hku : k ≤ u) (a : Assignment k) (env : ℕ → RootData u k)
    (f : PairState u k → ℝ) (M : ℕ) (S : PairState u k) :
    favg (fun z : Fin M → RefreshNoise u k =>
      dataRewards f S (fun i => refreshData a (env i) (z i))) =
      markovSum (uniformStep (pairEvolution a env)) f M S := by
  let := clause_nonempty u k hku
  let := clause_nonempty u (k-1) (by omega)
  simp_rw [← rootPath_eq_rewards]
  exact pathReward_avg _ _ _ _

def noiseWordEquiv (u k M : ℕ) :
    (Fin M → RefreshNoise u k) ≃
      ((Fin M → Clause u k) × (Fin k → Fin M → Clause u (k-1))) where
  toFun w := (fun i => (w i).1, fun j i => (w i).2 j)
  invFun z := fun i => (z.1 i, fun j => z.2 j i)
  left_inv w := by funext i; rfl
  right_inv z := by rfl

lemma favg_noiseWord {u k M : ℕ} (f : (Fin M → RefreshNoise u k) → ℝ) :
    favg f = favg (fun o : Fin M → Clause u k =>
      favg (fun ys : Fin k → Fin M → Clause u (k-1) => f (fun i => (o i, fun j => ys j i)))) := by
  rw [← favg_equiv (noiseWordEquiv u k M).symm f, favg_prod]
  rfl

lemma dataSatisfies_refresh_fixed {u k : ℕ} (a : Assignment k) (p : RootData u k)
    (z : RefreshNoise u k) (b : Assignment u) :
    DataSatisfies (refreshData a p z) (a,b) ↔
      if rootSize p.1 = 0 then Satisfies z.1 b else DataSatisfies p (a,b) := by
  by_cases h : rootSize p.1 = 0
  · simp [DataSatisfies, refreshData, refreshPart, h, rootSatisfies_zero p.1 h a,
      satisfies_cast]
  · by_cases ht : rootSize p.1 = 1 ∧ RootSatisfies p.1 a
    · simp [DataSatisfies, refreshData, refreshPart, ht]
    · simp [DataSatisfies, refreshData, refreshPart, h, ht]

def fibrePrefix {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (o : Fin M → Clause u k) (m : ℕ) : Finset (Assignment u) :=
  Finset.univ.filter fun b => ∀ i : Fin M, i.val < m →
    if rootSize (env i).1 = 0 then Satisfies (o i) b else DataSatisfies (env i) (a,b)

lemma fibre_pairPrefix_refresh {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (o : Fin M → Clause u k) (ys : Fin k → Fin M → Clause u (k-1)) (m : ℕ) :
    fibre a (pairPrefix Finset.univ (fun i => refreshData a (env i) (o i, fun j => ys j i)) m) =
      fibrePrefix a env o m := by
  ext b
  simp only [fibre, pairPrefix, fibrePrefix, Finset.mem_filter, Finset.mem_univ, true_and,
    dataSatisfies_refresh_fixed]

def flipRoot {k : ℕ} (a : Assignment k) (j : Fin k) : Assignment k := Function.update a j (!(a j))

lemma flipRoot_ne {k : ℕ} (a : Assignment k) (j : Fin k) : flipRoot a j ≠ a := by
  intro h
  have hh := congrFun h j
  simp only [flipRoot, Function.update_self] at hh
  cases ha : a j <;> simp_all

def UniqueTrue {k : ℕ} (t : RootType k) (a : Assignment k) (j : Fin k) : Prop :=
  t j = some (a j) ∧ ∀ l, l ≠ j → t l ≠ some (a l)

lemma rootSatisfies_flip {k : ℕ} (t : RootType k) (a : Assignment k) (j : Fin k)
    (h : RootSatisfies t a) (hn : ¬ UniqueTrue t a j) : RootSatisfies t (flipRoot a j) := by
  obtain ⟨l,hl⟩ := h
  by_cases hlj : l = j
  · subst l
    have he : ∃ l, l ≠ j ∧ t l = some (a l) := by
      by_contra hh
      apply hn
      refine ⟨hl, ?_⟩
      intro l hlj hl
      exact hh ⟨l,hlj,hl⟩
    obtain ⟨l,hlj,hl⟩ := he
    exact ⟨l, by simpa [flipRoot, Function.update_of_ne hlj] using hl⟩
  · exact ⟨l, by simpa [flipRoot, Function.update_of_ne hlj] using hl⟩

lemma rootSize_one_unique {k : ℕ} (t : RootType k) (h : rootSize t = 1)
    {i j : Fin k} (hi : (t i).isSome) (hj : (t j).isSome) : i = j := by
  have hcard : (rootSupport t).card ≤ 1 := h.le
  exact Finset.card_le_one.mp hcard i (by simpa [rootSupport] using hi)
    j (by simpa [rootSupport] using hj)

lemma trueRoot_eq {k : ℕ} (t : RootType k) (a : Assignment k)
    (h : RootSatisfies t a) (hs : rootSize t = 1) {j : Fin k} (hj : t j = some (a j)) :
    trueRoot t a h = j := by
  apply rootSize_one_unique t hs
  · simp [trueRoot_spec t a h]
  · simp [hj]

def TestAt {u k : ℕ} (a : Assignment k) (p : RootData u k) (j : Fin k) : Prop :=
  rootSize p.1 = 1 ∧ p.1 j = some (a j)

lemma refreshPart_test {u k : ℕ} (a : Assignment k) (p : RootData u k)
    (j : Fin k) (h : TestAt a p j) (z : RefreshNoise u k) (b : Assignment u) :
    Satisfies (refreshPart p.1 a p.2 z) b ↔ Satisfies (z.2 j) b := by
  have ht : RootSatisfies p.1 a := ⟨j,h.2⟩
  have hz : rootSize p.1 ≠ 0 := by rw [h.1]; omega
  have hh : rootSize p.1 = 1 ∧ RootSatisfies p.1 a := ⟨h.1,ht⟩
  simp only [refreshPart, dite_eq_right hz, dite_eq_left hh, satisfies_cast]
  rw [trueRoot_eq _ _ _ h.1 h.2]

def Available {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k) (j : Fin k) : Prop :=
  ∀ i, 2 ≤ rootSize (env i).1 → ¬ UniqueTrue (env i).1 a j

lemma forcedPrefix_testKills {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (o : Fin M → Clause u k) (ys : Fin k → Fin M → Clause u (k-1)) (m : ℕ)
    (hforced : ∀ x ∈ pairPrefix Finset.univ
      (fun i => refreshData a (env i) (o i, fun j => ys j i)) m, x.1 = a)
    (j : Fin k) (hj : Available a env j) :
    ¬ ∃ b ∈ fibrePrefix a env o m,
      ∀ i : Fin M, i.val < m → TestAt a (env i) j → Satisfies (ys j i) b := by
  rintro ⟨b,hb,hparts⟩
  have hfb : (a,b) ∈ pairPrefix Finset.univ
      (fun i => refreshData a (env i) (o i, fun j => ys j i)) m := by
    have hh := congrArg (fun S => b ∈ S) (fibre_pairPrefix_refresh a env o ys m)
    simpa only [fibre, Finset.mem_filter, Finset.mem_univ, true_and] using hh.mpr hb
  have hflip : (flipRoot a j,b) ∈ pairPrefix Finset.univ
      (fun i => refreshData a (env i) (o i, fun j => ys j i)) m := by
    simp only [pairPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at hfb ⊢
    intro i hi
    have hh := hfb i hi
    change RootSatisfies (env i).1 a ∨ Satisfies (refreshPart (env i).1 a (env i).2
      (o i, fun j => ys j i)) b at hh
    change RootSatisfies (env i).1 (flipRoot a j) ∨ Satisfies (refreshPart (env i).1 a (env i).2
      (o i, fun j => ys j i)) b
    rcases hh with hr | hp
    · by_cases ht : UniqueTrue (env i).1 a j
      · have hs : rootSize (env i).1 = 1 := by
          have hp : 0 < rootSize (env i).1 := by
            by_contra h
            exact rootSatisfies_zero _ (by omega) a hr
          have hlt : rootSize (env i).1 < 2 := Nat.lt_of_not_ge (fun h => hj i h ht)
          omega
        exact Or.inr ((refreshPart_test a (env i) j ⟨hs,ht.1⟩ _ b).mpr
          (hparts i hi ⟨hs,ht.1⟩))
      · exact Or.inl (rootSatisfies_flip _ a j hr ht)
    · exact Or.inr hp
  exact flipRoot_ne a j (hforced _ hflip)

end RandomKSAT

end

end OAI
