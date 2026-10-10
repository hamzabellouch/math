import OAI.Probability.SATVariance.SentinelBridge

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma bystanders_perm_right {n k : ℕ} {b l r : List (Clause n k)}
    (hb : Bystanders b l) (h : l.Perm r) : Bystanders b r := by
  induction b with
  | nil => trivial
  | cons c b ih =>
    exact ⟨private_perm (h.append_left b) hb.1,ih hb.2⟩

def shuffleVar.{u_1} {α : Type u_1} (l : List α) (f : List α → ℝ) : ℝ :=
  shuffleAvg l (fun r => (f r)^2) - (shuffleAvg l f)^2

lemma shuffleVar_nonneg.{u_1} {α : Type u_1} (l : List α) (f : List α → ℝ) : 0 ≤ shuffleVar l f :=
  sub_nonneg.mpr (shuffleAvg_sq_le l f)

lemma shuffleVar_perm.{u_1} {α : Type u_1} {l r : List α} (h : l.Perm r) (f : List α → ℝ) :
    shuffleVar l f = shuffleVar r f := by
  unfold shuffleVar
  rw [shuffleAvg_perm h,shuffleAvg_perm h]

lemma shuffleVar_append_lower.{u_1} {α : Type u_1} (b l : List α) (f : List α → ℝ) :
    shuffleAvg l (fun r => insertVar b r f) ≤ shuffleVar (b++l) f := by
  simp only [shuffleVar,shuffleAvg_append,insertVar]
  rw [shuffleAvg_sub]
  have hh := shuffleAvg_sq_le l (fun r => insertAvg b r f)
  linarith

lemma favg_shuffleVar_lower.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (M : ℕ) (f : List α → ℝ) :
    favg (fun w : Fin M → α => shuffleVar (List.ofFn w) f) ≤
      fvariance (fun w : Fin M → α => f (List.ofFn w)) := by
  simp only [shuffleVar,fvariance,favg_sub,favg_shuffle]
  have hh := favg_sq_le (fun w : Fin M → α => shuffleAvg (List.ofFn w) f)
  rw [favg_shuffle] at hh
  linarith

def outsideWindow {n k : ℕ} (Q V : ℕ) (r : List (Clause n k)) : ℝ :=
  if listStop r < 2*Q ∨ V < listStop r then 1 else 0

lemma outsideWindow_nonneg {n k : ℕ} (Q V : ℕ) (r : List (Clause n k)) :
    0 ≤ outsideWindow Q V r := by unfold outsideWindow; positivity

lemma bystander_variance {n k : ℕ} {b l : List (Clause n k)} (hb : Bystanders b l)
    (Q V M : ℕ) (hlen : b.length+l.length = M) (hbQ : b.length ≤ Q)
    (hQV : Q+V ≤ M+1) :
    ((Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2)*b.length ≤
      shuffleVar (b++l) (fun r => (listStop r:ℝ)) +
      ((Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2)*b.length*
        shuffleAvg (b++l) (outsideWindow Q V) := by
  let p : ℝ := (Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2
  have hC : 0 ≤ (M:ℝ)+1-Q-V := by
    have hh : (Q:ℝ)+V ≤ M+1 := by exact_mod_cast hQV
    linarith
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hbl : (b.length:ℝ)+(l.length:ℝ) = M := by exact_mod_cast hlen
  have hq : (b.length:ℝ) ≤ Q := by exact_mod_cast hbQ
  have hlocal (r : List (Clause n k)) (hr : r.Perm l) :
      p*b.length ≤ insertVar b r (fun s => (listStop s:ℝ)) +
        p*b.length*insertAvg b r (outsideWindow Q V) := by
    have hb' : Bystanders b r := bystanders_perm_right hb hr.symm
    have hrlen : (r.length:ℝ) = l.length := by exact_mod_cast hr.length_eq
    by_cases ht : Q ≤ listStop r ∧ listStop r ≤ V
    · have hv := insertVar_stop_lower hb' hC (by positivity : (0:ℝ) < (M:ℝ)+1)
        (by exact_mod_cast ht.1 : (Q:ℝ) ≤ listStop r)
        (show (M:ℝ)+1-Q-V ≤ (r.length:ℝ)+1-listStop r by
          have htv : (listStop r:ℝ) ≤ V := by exact_mod_cast ht.2
          linarith)
        (show (b.length:ℝ)+r.length+1 ≤ (M:ℝ)+1 by linarith)
      have hn : 0 ≤ insertAvg b r (outsideWindow Q V) := by
        rw [←insertAvg_const b r 0]
        exact insertAvg_mono b r (fun s _ => outsideWindow_nonneg Q V s)
      have hh : 0 ≤ p*b.length*insertAvg b r (outsideWindow Q V) := by positivity
      dsimp [p] at hv ⊢
      nlinarith
    · have hout : insertAvg b r (outsideWindow Q V) = 1 := by
        rw [←insertAvg_const b r 1]
        apply insertAvg_congr
        intro s hs
        have hst := inserts_stop_bounds hb' hs
        have hh : listStop s < 2*Q ∨ V < listStop s := by omega
        simp [outsideWindow,hh]
      rw [hout,mul_one]
      linarith [insertVar_nonneg b r (fun s => (listStop s:ℝ))]
  have hh := shuffleAvg_mono (l := l) hlocal
  rw [shuffleAvg_const,shuffleAvg_add,shuffleAvg_mul] at hh
  have hv := shuffleVar_append_lower b l (fun r => (listStop r:ℝ))
  rw [shuffleAvg_append]
  change p*b.length ≤ _ + p*b.length*_
  linarith

lemma bystanders_map {n k M : ℕ} (hk : 1 ≤ k) (w : Fin M → Clause n k)
    {is js : List (Fin M)} (hnd : is.Nodup)
    (hi : ∀ i ∈ is, isolated w i) (hd : ∀ i ∈ is, i ∉ js) :
    Bystanders (is.map w) (js.map w) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    have hnd' := List.nodup_cons.mp hnd
    have hic := hi i (by simp)
    have hid := hd i (by simp)
    constructor
    · have hn : (w i).1.1.Nonempty := Finset.card_pos.mp (by rw [(w i).1.2]; omega)
      obtain ⟨v,hv⟩ := hn
      refine ⟨⟨v,hv⟩,?_⟩
      intro d hd'
      rcases List.mem_append.mp hd' with hd' | hd'
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd'
        have hji : j ≠ i := by intro he; subst j; exact hnd'.1 hj
        exact Finset.disjoint_left.mp (hic j hji) hv
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd'
        have hji : j ≠ i := by intro he; subst j; exact hid hj
        exact Finset.disjoint_left.mp (hic j hji) hv
    · exact ih hnd'.2 (fun j hj => hi j (by simp [hj])) (fun j hj => hd j (by simp [hj]))

def chosenIsolates {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) : Finset (Fin M) :=
  Classical.choose (Finset.exists_subset_card_eq (s := isolateSet w) (min_le_right Q (isolateSet w).card))

lemma chosenIsolates_subset {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) :
    chosenIsolates Q w ⊆ isolateSet w :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := isolateSet w) (min_le_right Q (isolateSet w).card))).1

lemma chosenIsolates_card {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) :
    (chosenIsolates Q w).card = min Q (isolateSet w).card :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := isolateSet w) (min_le_right Q (isolateSet w).card))).2

def bystanderList {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) : List (Clause n k) :=
  (chosenIsolates Q w).toList.map w

def activeList {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) : List (Clause n k) :=
  (Finset.univ \ chosenIsolates Q w).toList.map w

lemma selected_bystanders {n k M : ℕ} (hk : 1 ≤ k) (Q : ℕ) (w : Fin M → Clause n k) :
    Bystanders (bystanderList Q w) (activeList Q w) := by
  apply bystanders_map hk w (Finset.nodup_toList _)
  · intro i hi
    exact (Finset.mem_filter.mp (chosenIsolates_subset Q w (Finset.mem_toList.mp hi))).2
  · intro i hi
    simp only [Finset.mem_toList,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not]
    exact Finset.mem_toList.mp hi

lemma selected_perm {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) :
    ((bystanderList Q w)++(activeList Q w)).Perm (List.ofFn w) := by
  let I := chosenIsolates Q w
  have hnd : (I.toList++(Finset.univ\I).toList).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro i hi j hj he
    subst j
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hj)).2 (Finset.mem_toList.mp hi)
  have hid : (List.ofFn (id : Fin M → Fin M)).Nodup := List.nodup_ofFn.mpr Function.injective_id
  have hp : (I.toList++(Finset.univ\I).toList).Perm (List.ofFn (id : Fin M → Fin M)) := by
    rw [List.perm_ext_iff_of_nodup hnd hid]
    intro i
    simp only [List.mem_append,Finset.mem_toList,Finset.mem_sdiff,Finset.mem_univ,true_and,List.mem_ofFn]
    simp only [id_eq,exists_eq,iff_true]
    exact em (i ∈ I)
  have hh := hp.map w
  change ((I.toList.map w)++((Finset.univ\I).toList.map w)).Perm (List.ofFn w)
  simpa only [List.map_append,List.map_ofFn,Function.comp_id] using hh

lemma bystanderList_length {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) :
    (bystanderList Q w).length = min Q (isolateSet w).card := by
  simp only [bystanderList,List.length_map,Finset.length_toList,chosenIsolates_card]

lemma selected_lengths {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) :
    (bystanderList Q w).length+(activeList Q w).length = M := by
  have := (selected_perm Q w).length_eq
  simpa only [List.length_append,List.length_ofFn] using this

lemma selected_variance {n k M : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (Q V : ℕ) (hQV : Q+V ≤ M+1) :
    ((Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2)*
      favg (fun w : Fin M → Clause n k => (min Q (isolateSet w).card : ℝ)) ≤
    fvariance (fun w : Fin M → Clause n k => (listStop (List.ofFn w):ℝ)) +
      ((Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2)*Q*
        favg (fun w : Fin M → Clause n k => outsideWindow Q V (List.ofFn w)) := by
  let := clause_nonempty n k hkn
  let p : ℝ := (Q:ℝ)*((M:ℝ)+1-Q-V)/((M:ℝ)+1)^2
  have hC : 0 ≤ (M:ℝ)+1-Q-V := by
    have hh : (Q:ℝ)+V ≤ M+1 := by exact_mod_cast hQV
    linarith
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hh (w : Fin M → Clause n k) :
      p*(min Q (isolateSet w).card:ℝ) ≤
      shuffleVar (List.ofFn w) (fun r => (listStop r:ℝ)) + p*Q*
        shuffleAvg (List.ofFn w) (outsideWindow Q V) := by
    have ht := bystander_variance (selected_bystanders hk Q w) Q V M (selected_lengths Q w)
      (by rw [bystanderList_length]; exact min_le_left _ _) hQV
    rw [shuffleVar_perm (selected_perm Q w),shuffleAvg_perm (selected_perm Q w),bystanderList_length] at ht
    have hmin : (min Q (isolateSet w).card:ℝ) ≤ Q := by exact_mod_cast min_le_left Q (isolateSet w).card
    have hnon := shuffleAvg_nonneg (l := List.ofFn w) (fun r _ => outsideWindow_nonneg Q V r)
    have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hp) hnon
    simp only [Nat.cast_min] at ht
    apply ht.trans
    dsimp only [p] at he
    linarith
  have hh' := favg_mono hh
  simp only [favg_mul,favg_add,favg_shuffle] at hh'
  have hv := favg_shuffleVar_lower M (fun r : List (Clause n k) => (listStop r:ℝ))
  change p*_ ≤ _ + p*Q*_
  linarith

lemma min_isolate_mean_lower {n k M Q : ℕ} (hM : 0 < M) (hQ : Q ≤ M)
    {β : ℝ} (hmean : (M:ℝ)*β ≤ favg (fun w : Fin M → Clause n k => ((isolateSet w).card:ℝ))) :
    (Q:ℝ)*β ≤ favg (fun w : Fin M → Clause n k => (min Q (isolateSet w).card:ℝ)) := by
  have hh (w : Fin M → Clause n k) :
      (Q:ℝ)*(isolateSet w).card ≤ (M:ℝ)*(min Q (isolateSet w).card:ℝ) := by
    have hJ : (isolateSet w).card ≤ M := by simpa using Finset.card_le_univ (isolateSet w)
    have ht : Q*(isolateSet w).card ≤ M*min Q (isolateSet w).card := by
      by_cases h : Q ≤ (isolateSet w).card
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right (by omega)]; nlinarith
    exact_mod_cast ht
  have ht := favg_mono hh
  rw [favg_mul,favg_mul] at ht
  have hh' := mul_le_mul_of_nonneg_left hmean (show (0:ℝ) ≤ Q by positivity)
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  nlinarith

end RandomKSAT

end

end OAI
