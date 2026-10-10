import Mathlib
import OAI.Probability.ThorpRouting.Adaptive.ExposedCoins

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter
section Rotation
variable {d A : ℕ}

noncomputable def rotationMeeting (o : Card d → Option (Fin A)) (z : Terminal o)
    (u v : Card d) : ℝ :=
  match o u, o v with
  | some i, some j => if i < j then (if (z j).val = v then 1 else 0)
      else if j < i then (if (z i).val = u then 1 else 0)
      else (if (z i).val = u then 1 else 0) + (if (z i).val = v then 1 else 0)
  | _, _ => 0

lemma card_cycleFiber (o : Card d → Option (Fin A)) (i : Fin A) :
    Fintype.card {x : Card d // o x = some i} = (cycleFiber o i).card := by
  classical
  simp [cycleFiber,Fintype.card_subtype]

lemma terminal_mean {o : Card d → Option (Fin A)}
    [∀ i : Fin A, Nonempty {x : Card d // o x = some i}]
    (i : Fin A) (x : Card d) (hx : o x = some i) :
    finiteMean (fun z : Terminal o => if (z i).val = x then (1:ℝ) else 0) = slotWeight o i := by
  classical
  have hev := finiteMean_pi_eval (A := fun i : Fin A => {x : Card d // o x = some i})
    i (fun z => if z.val = x then (1:ℝ) else 0)
  rw [hev]
  have he : (fun z : {x : Card d // o x = some i} => if z.val = x then (1:ℝ) else 0) =
      (fun z => if z = ⟨x,hx⟩ then 1 else 0) := by
    funext z
    simp only [Subtype.ext_iff]
  rw [he,finiteMean_eq_indicator,card_cycleFiber,slotWeight]

lemma slotWeight_antitone (o : Card d → Option (Fin A))
    (hn : ∀ i, (cycleFiber o i).Nonempty)
    (hm : Monotone (fun i => (cycleFiber o i).card)) : Antitone (slotWeight o) := by
  intro i j hij
  unfold slotWeight
  apply one_div_le_one_div_of_le
  · exact_mod_cast Finset.card_pos.mpr (hn i)
  · exact_mod_cast hm hij

lemma rotationMeeting_mean {o : Card d → Option (Fin A)}
    [∀ i : Fin A, Nonempty {x : Card d // o x = some i}]
    (hm : Monotone (fun i => (cycleFiber o i).card)) (u v : Card d) :
    finiteMean (fun z : Terminal o => rotationMeeting o z u v) =
      min (pathWeight o u) (pathWeight o v) + withinWeight o u v := by
  classical
  have hn : ∀ i, (cycleFiber o i).Nonempty := by
    intro i
    obtain ⟨x,hx⟩ := (inferInstance : Nonempty {x : Card d // o x = some i})
    exact ⟨x,mem_cycleFiber _ _ _ |>.mpr hx⟩
  have hw := slotWeight_antitone o hn hm
  cases hu : o u with
  | none =>
    cases hv : o v with
    | none => simp [rotationMeeting,pathWeight,withinWeight,hu,hv,finiteMean]
    | some j =>
      have hj : 0 ≤ slotWeight o j := by unfold slotWeight; positivity
      simp [rotationMeeting,pathWeight,withinWeight,hu,hv,finiteMean,min_eq_left hj]
  | some i =>
    cases hv : o v with
    | none =>
      have hi : 0 ≤ slotWeight o i := by unfold slotWeight; positivity
      simp [rotationMeeting,pathWeight,withinWeight,hu,hv,finiteMean,min_eq_right hi]
    | some j =>
      simp only [rotationMeeting,pathWeight,withinWeight,hu,hv]
      rcases lt_trichotomy i j with hij | rfl | hji
      · simp only [hij,↓reduceIte,ne_of_lt hij]
        rw [terminal_mean j v hv,min_eq_right (hw (le_of_lt hij)),add_zero]
      · simp only [lt_self_iff_false,↓reduceIte,min_self]
        rw [finiteMean_add,terminal_mean i u hu,terminal_mean i v hv]
      · simp only [not_lt_of_ge (le_of_lt hji),hji,↓reduceIte,ne_of_gt hji]
        rw [terminal_mean i u hu,min_eq_left (hw (le_of_lt hji)),add_zero]

lemma pathWeight_sum (o : Card d → Option (Fin A)) (hn : ∀ i, (cycleFiber o i).Nonempty) :
    ∑ x : Card d, pathWeight o x = (A : ℝ) := by
  classical
  have he (x : Card d) : pathWeight o x =
      ∑ i : Fin A, if o x = some i then slotWeight o i else 0 := by
    cases hx : o x with
    | none => simp [pathWeight,hx]
    | some j => simp [pathWeight,hx]
  simp only [he]
  rw [Finset.sum_comm]
  have hf (i : Fin A) : (∑ x : Card d, if o x = some i then slotWeight o i else 0) = 1 := by
    rw [← Finset.sum_filter]
    change (∑ _x ∈ cycleFiber o i, slotWeight o i) = 1
    simp only [Finset.sum_const,nsmul_eq_mul,slotWeight]
    exact mul_one_div_cancel (by exact_mod_cast (Finset.card_pos.mpr (hn i)).ne')
  simp only [hf,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

lemma withinWeight_sum_bound (o : Card d → Option (Fin A))
    (hn : ∀ i, (cycleFiber o i).Nonempty) (b : Butterfly d) :
    (∑ s : SwitchIndex d, withinWeight o (switchUsers d b s).1 (switchUsers d b s).2) ≤
      ∑ i : Fin A, Real.log (cycleFiber o i).card / (2 * Real.log 2) := by
  classical
  have he (u v : Card d) : withinWeight o u v =
      ∑ i : Fin A, (if u ∈ cycleFiber o i ∧ v ∈ cycleFiber o i then (1:ℝ) else 0) * slotWeight o i := by
    simp only [mem_cycleFiber]
    cases hu : o u <;> cases hv : o v <;> simp [withinWeight,hu,hv,ite_and,eq_comm]
  simp only [he]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_mul]
  have hi := marked_switch_entropy_bound d b (cycleFiber o i)
  have hpos : (0:ℝ) < (cycleFiber o i).card := by exact_mod_cast Finset.card_pos.mpr (hn i)
  have hmul := mul_le_mul_of_nonneg_right hi (show 0 ≤ slotWeight o i by unfold slotWeight; positivity)
  calc
    _ ≤ ((cycleFiber o i).card : ℝ) * Real.log (cycleFiber o i).card /
        (2 * Real.log 2) * slotWeight o i := hmul
    _ = _ := by unfold slotWeight; field_simp

noncomputable def rotationCharge (o : Card d → Option (Fin A)) (b : Butterfly d)
    (z : Terminal o) : ℝ :=
  ∑ s : SwitchIndex d, rotationMeeting o z (switchUsers d b s).1 (switchUsers d b s).2

lemma rotationCharge_mean_bound {o : Card d → Option (Fin A)}
    [∀ i : Fin A, Nonempty {x : Card d // o x = some i}]
    (hm : Monotone (fun i => (cycleFiber o i).card)) (b : Butterfly d) :
    finiteMean (rotationCharge o b) ≤ (A:ℝ) * d / 2 +
      ∑ i : Fin A, Real.log (cycleFiber o i).card / (2 * Real.log 2) := by
  classical
  have hn : ∀ i, (cycleFiber o i).Nonempty := by
    intro i
    obtain ⟨x,hx⟩ := (inferInstance : Nonempty {x : Card d // o x = some i})
    exact ⟨x,mem_cycleFiber _ _ _ |>.mpr hx⟩
  unfold rotationCharge
  rw [finiteMean_sum]
  simp only [rotationMeeting_mean hm,Finset.sum_add_distrib]
  have h₁ := weighted_switch_min_bound d b (pathWeight o)
  rw [pathWeight_sum o hn] at h₁
  have h₂ := withinWeight_sum_bound o hn b
  linarith

lemma rotation_exp_bound {o : Card d → Option (Fin A)}
    [∀ i : Fin A, Nonempty {x : Card d // o x = some i}]
    (hm : Monotone (fun i => (cycleFiber o i).card)) (b : Butterfly d) :
    Real.exp (-Real.log 2 * ((A:ℝ)*d/2 +
      ∑ i : Fin A, Real.log (cycleFiber o i).card / (2 * Real.log 2))) ≤
      finiteMean (fun z : Terminal o => Real.exp (-Real.log 2 * rotationCharge o b z)) := by
  have hb := rotationCharge_mean_bound hm b
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hm' : -Real.log 2 * ((A:ℝ)*d/2 +
      ∑ i : Fin A, Real.log (cycleFiber o i).card / (2 * Real.log 2)) ≤
      finiteMean (fun z : Terminal o => -Real.log 2 * rotationCharge o b z) := by
    have he := finiteMean_mul_const (rotationCharge o b) (-Real.log 2)
    simp only [mul_comm] at he
    rw [he]
    exact mul_le_mul_of_nonpos_left hb (neg_nonpos.mpr hlog)
  exact (Real.exp_le_exp.mpr hm').trans (exp_finiteMean_le _)

end Rotation

section OrbitCore
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def orbitSet (p : Equiv.Perm α) (x : α) : Finset α :=
  Finset.univ.filter (p.SameCycle x)

@[simp] lemma mem_orbitSet (p : Equiv.Perm α) (x y : α) :
    y ∈ orbitSet p x ↔ p.SameCycle x y := by
  classical
  simp [orbitSet]

lemma orbitSet_nonempty (p : Equiv.Perm α) (x : α) : (orbitSet p x).Nonempty :=
  ⟨x,(mem_orbitSet _ _ _).mpr (Equiv.Perm.SameCycle.refl _ _)⟩

lemma orbitSet_eq (p : Equiv.Perm α) {x y : α} (h : p.SameCycle x y) :
    orbitSet p x = orbitSet p y := by
  ext z
  simp only [mem_orbitSet]
  exact ⟨fun hz => h.symm.trans hz,fun hz => h.trans hz⟩

@[simp] lemma orbitSet_apply (p : Equiv.Perm α) (x : α) : orbitSet p (p x) = orbitSet p x := by
  ext y
  simp only [mem_orbitSet,Equiv.Perm.sameCycle_apply_left]

lemma orbitSet_eq_or_disjoint (p : Equiv.Perm α) (x y : α) :
    orbitSet p x = orbitSet p y ∨ Disjoint (orbitSet p x) (orbitSet p y) := by
  classical
  by_cases h : p.SameCycle x y
  · exact Or.inl (orbitSet_eq p h)
  · right
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact h (((mem_orbitSet _ _ _).mp hz).trans ((mem_orbitSet _ _ _).mp hz').symm)

omit [DecidableEq α] in
lemma perm_minimalPeriod_pos (p : Equiv.Perm α) (x : α) :
    0 < Function.minimalPeriod p x :=
  Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts x)

lemma orbitSet_card (p : Equiv.Perm α) (x : α) :
    (orbitSet p x).card = Function.minimalPeriod p x := by
  classical
  let f : Fin (Function.minimalPeriod p x) → {y // p.SameCycle x y} := fun n =>
    ⟨p^[n.val] x,by rw [Equiv.Perm.iterate_eq_pow]; exact ⟨(n.val:ℤ),by simp⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Fin.ext
      exact Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt (congrArg Subtype.val hij)
    · intro y
      obtain ⟨n,hn⟩ := y.property.exists_nat_pow_eq
      refine ⟨⟨n % Function.minimalPeriod p x, Nat.mod_lt _ (perm_minimalPeriod_pos p x)⟩,?_⟩
      apply Subtype.ext
      change p^[n % Function.minimalPeriod p x] x = y.val
      rw [Function.iterate_mod_minimalPeriod_eq,Equiv.Perm.iterate_eq_pow,hn]
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa [orbitSet,Fintype.card_subtype] using hc.symm

def walkSet (p : Equiv.Perm α) (r : ℕ) (x : α) : Finset α :=
  (Finset.range r).image (fun n => p^[n] x)

omit [Fintype α] in
@[simp] lemma mem_walkSet (p : Equiv.Perm α) (r : ℕ) (x y : α) :
    y ∈ walkSet p r x ↔ ∃ n < r, p^[n] x = y := by
  simp [walkSet]

omit [Fintype α] in
@[simp] lemma walkSet_zero (p : Equiv.Perm α) (x : α) : walkSet p 0 x = ∅ := by
  simp [walkSet]

omit [Fintype α] in
lemma walkSet_succ_last (p : Equiv.Perm α) (r : ℕ) (x : α) :
    walkSet p (r+1) x = insert (p^[r] x) (walkSet p r x) := by
  simp [walkSet,Finset.range_add_one]

omit [Fintype α] in
lemma walkSet_succ_first (p : Equiv.Perm α) (r : ℕ) (x : α) :
    walkSet p (r+1) x = insert x (walkSet p r (p x)) := by
  ext y
  simp only [mem_walkSet,Finset.mem_insert]
  constructor
  · rintro ⟨n,hn,hny⟩
    cases n with
    | zero => exact Or.inl (by simpa using hny.symm)
    | succ n => exact Or.inr ⟨n,by omega,by simpa only [Function.iterate_succ_apply] using hny⟩
  · rintro (rfl | ⟨n,hn,hny⟩)
    · exact ⟨0,by omega,rfl⟩
    · exact ⟨n+1,by omega,by simpa only [Function.iterate_succ_apply] using hny⟩

omit [Fintype α] in
lemma not_mem_short_walk (p : Equiv.Perm α) (x : α) {r : ℕ}
    (hr : r < Function.minimalPeriod p x) : x ∉ walkSet p r (p x) := by
  rintro hx
  obtain ⟨n,hn,hnx⟩ := (mem_walkSet _ _ _ _).mp hx
  have hperiod : Function.IsPeriodicPt p (n+1) x := by
    simpa only [Function.IsPeriodicPt,Function.IsFixedPt,Function.iterate_succ_apply] using hnx
  have hp := hperiod.minimalPeriod_le (by omega : 0 < n+1)
  omega

lemma walkSet_period (p : Equiv.Perm α) (x : α) :
    walkSet p (Function.minimalPeriod p x) x = orbitSet p x := by
  ext y
  simp only [mem_walkSet,mem_orbitSet]
  constructor
  · rintro ⟨n,_,rfl⟩
    rw [Equiv.Perm.iterate_eq_pow]
    exact ⟨(n:ℤ),by simp⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    refine ⟨n % Function.minimalPeriod p x,Nat.mod_lt _ (perm_minimalPeriod_pos p x),?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq,Equiv.Perm.iterate_eq_pow,hn]

omit [Fintype α] in
lemma walkSet_card (p : Equiv.Perm α) (x : α) {r : ℕ}
    (hr : r ≤ Function.minimalPeriod p x) : (walkSet p r x).card = r := by
  rw [walkSet,Finset.card_image_of_injOn]
  · exact Finset.card_range _
  · intro i hi j hj hij
    exact Function.iterate_injOn_Iio_minimalPeriod
      (lt_of_lt_of_le (Finset.mem_range.mp hi) hr)
      (lt_of_lt_of_le (Finset.mem_range.mp hj) hr) hij

lemma walkSet_subset_orbit (p : Equiv.Perm α) (r : ℕ) (x : α) :
    walkSet p r x ⊆ orbitSet p x := by
  intro y hy
  obtain ⟨n,_,rfl⟩ := (mem_walkSet _ _ _ _).mp hy
  rw [mem_orbitSet,Equiv.Perm.iterate_eq_pow]
  exact ⟨(n:ℤ),by simp⟩

def cycleTrace (p : Equiv.Perm α) (S : Finset α) (a : α) :
    ℕ → α → Finset α → Option (Finset α × α)
  | 0, x, V => if x ∈ S ∧ x ∉ V ∧ p x = a then some (insert x V,x) else none
  | r+1, x, V => if x ∈ S ∧ x ∉ V then cycleTrace p S a r (p x) (insert x V) else none

lemma cycleTrace_walk (p : Equiv.Perm α) (S : Finset α) (r : ℕ) (x : α) (V : Finset α)
    (hr : r < Function.minimalPeriod p x) (hS : walkSet p (r+1) x ⊆ S)
    (hV : Disjoint V (walkSet p (r+1) x)) :
    cycleTrace p S (p^[r+1] x) r x V = some (V ∪ walkSet p (r+1) x,p^[r] x) := by
  induction r generalizing x V with
  | zero =>
    have hxS : x ∈ S := hS (by simp [walkSet_succ_first])
    have hxV : x ∉ V := fun h => Finset.disjoint_left.mp hV h (by simp [walkSet_succ_first])
    simp [cycleTrace,hxS,hxV,walkSet_succ_first]
  | succ r ih =>
    have hxS : x ∈ S := hS (by rw [walkSet_succ_first]; exact Finset.mem_insert_self _ _)
    have hxV : x ∉ V := fun h => Finset.disjoint_left.mp hV h
      (by rw [walkSet_succ_first]; exact Finset.mem_insert_self _ _)
    have hr' : r < Function.minimalPeriod p (p x) := by
      rw [Function.minimalPeriod_apply (p.injective.mem_periodicPts x)]
      omega
    have hS' : walkSet p (r+1) (p x) ⊆ S := by
      intro y hy
      apply hS
      rw [walkSet_succ_first]
      exact Finset.mem_insert_of_mem hy
    have hV' : Disjoint (insert x V) (walkSet p (r+1) (p x)) := by
      apply Finset.disjoint_left.mpr
      intro y hy hy'
      rcases Finset.mem_insert.mp hy with hy | hy
      · subst y
        exact not_mem_short_walk p x hr hy'
      · apply Finset.disjoint_left.mp hV hy
        rw [walkSet_succ_first]
        exact Finset.mem_insert_of_mem hy'
    rw [cycleTrace,ite_eq_left ⟨hxS,hxV⟩,Function.iterate_succ_apply p (r+1) x,
      ih _ _ hr' hS' hV',walkSet_succ_first p (r+1) x,Function.iterate_succ_apply]
    simp only [Finset.insert_union,Finset.union_insert]

lemma cycleTrace_orbit (p : Equiv.Perm α) (S V : Finset α) (z : α)
    (hS : orbitSet p z ⊆ S) (hV : Disjoint V (orbitSet p z)) :
    cycleTrace p S (p z) (Function.minimalPeriod p z - 1) (p z) V =
      some (V ∪ orbitSet p z,z) := by
  have hpos := perm_minimalPeriod_pos p z
  have he : Function.minimalPeriod p (p z) = Function.minimalPeriod p z :=
    Function.minimalPeriod_apply (p.injective.mem_periodicPts z)
  have hp : Function.minimalPeriod p z - 1 + 1 = Function.minimalPeriod p z := by omega
  have hw : walkSet p (Function.minimalPeriod p z - 1 + 1) (p z) = orbitSet p z := by
    rw [hp,←he,walkSet_period,orbitSet_apply]
  have hr : Function.minimalPeriod p z - 1 < Function.minimalPeriod p (p z) := by rw [he]; omega
  have h := cycleTrace_walk p S (Function.minimalPeriod p z-1) (p z) V hr
    (by simpa only [hw] using hS) (by simpa only [hw] using hV)
  have ht : p^[Function.minimalPeriod p z-1] (p z) = z := by
    rw [← Function.iterate_succ_apply,show (Function.minimalPeriod p z-1).succ =
      Function.minimalPeriod p z by omega,Function.iterate_minimalPeriod]
  have ha : p^[Function.minimalPeriod p z-1+1] (p z) = p z := by
    rw [hp,←he,Function.iterate_minimalPeriod]
  simpa only [ha,ht,hw] using h

end OrbitCore

noncomputable def exposedPaths (d : ℕ) (b : Butterfly d) (V : Finset (Card d)) :
    Finset (SwitchIndex d) :=
  V.biUnion (fun x => routeDomain d x (butterflyPerm d b x))

@[simp] lemma exposedPaths_empty (d : ℕ) (b : Butterfly d) : exposedPaths d b ∅ = ∅ := by
  classical
  simp [exposedPaths]

lemma exposedPaths_insert (d : ℕ) (b : Butterfly d) (V : Finset (Card d)) (x : Card d) :
    exposedPaths d b (insert x V) = exposedPaths d b V ∪ routeDomain d x (butterflyPerm d b x) := by
  classical
  simp [exposedPaths,Finset.union_comm]

noncomputable def terminalCharge (d : ℕ) (b : Butterfly d) (z : Card d) (V : Finset (Card d)) : ℕ :=
  (routeDomain d z (butterflyPerm d b z) ∩ exposedPaths d b V).card

namespace QueryTree

lemma followPath_stale_charge {ι : Type*} [DecidableEq ι]
    (d : ℕ) (e : SwitchIndex d → ι) (x : Card d)
    (k : Card d → QueryTree ι) (R : Finset ι) (ω : ι → Bool) :
    staleCharge (followPath d e x k) R ω =
      staleCharge (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x))
        (R ∪ (routeDomain d x (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).image e) ω := by
  have h₀ := fresh_add_stale (followPath d e x k) R ω
  have h₁ := fresh_add_stale (k (butterflyPerm d (decodeButterfly d (ω ∘ e)) x))
    (R ∪ (routeDomain d x (butterflyPerm d (decodeButterfly d (ω ∘ e)) x)).image e) ω
  rw [followPath_charge,followPath_raw_charge] at h₀
  omega

lemma seekCycle_semantics (d : ℕ) (S : Finset (Card d)) (a : Card d) (r : ℕ)
    (x : Card d) (V W : Finset (Card d)) (z : Card d)
    (k : Finset (Card d) → QueryTree (SwitchIndex d)) (ω : SwitchIndex d → Bool)
    (h : cycleTrace (butterflyPerm d (decodeButterfly d ω)) S a r x V = some (W,z)) :
    (seekCycle d S a r x V k).succeeds ω = (k W).succeeds ω ∧
      (seekCycle d S a r x V k).staleCharge (exposedPaths d (decodeButterfly d ω) V) ω =
        (k W).staleCharge (exposedPaths d (decodeButterfly d ω) W) ω +
          terminalCharge d (decodeButterfly d ω) z (W.erase z) := by
  classical
  induction r generalizing x V with
  | zero =>
    simp only [cycleTrace] at h
    split_ifs at h with hv
    obtain ⟨hxS,hxV,hxa⟩ := hv
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp only [seekCycle,ite_eq_left (show x ∈ S ∧ x ∉ V from ⟨hxS,hxV⟩),closePath_succeeds,ite_eq_left hxa]
    constructor
    · trivial
    · rw [closePath_stale_charge _ _ _ _ _ _ hxa,exposedPaths_insert,
        Finset.erase_insert hxV]
      simp only [terminalCharge,hxa]
  | succ r ih =>
    simp only [cycleTrace] at h
    split_ifs at h with hv
    obtain ⟨hxS,hxV⟩ := hv
    rw [seekCycle,ite_eq_left ⟨hxS,hxV⟩,followPath_succeeds,followPath_stale_charge]
    simp only [Function.comp_id,Finset.image_id]
    rw [← exposedPaths_insert]
    exact ih _ _ h

lemma seekCycle_orbit (d : ℕ) (S V : Finset (Card d)) (z : Card d)
    (k : Finset (Card d) → QueryTree (SwitchIndex d)) (ω : SwitchIndex d → Bool)
    (hS : orbitSet (butterflyPerm d (decodeButterfly d ω)) z ⊆ S)
    (hV : Disjoint V (orbitSet (butterflyPerm d (decodeButterfly d ω)) z)) :
    let p := butterflyPerm d (decodeButterfly d ω)
    let W := V ∪ orbitSet p z
    (seekCycle d S (p z) (Function.minimalPeriod p z-1) (p z) V k).succeeds ω = (k W).succeeds ω ∧
      (seekCycle d S (p z) (Function.minimalPeriod p z-1) (p z) V k).staleCharge
          (exposedPaths d (decodeButterfly d ω) V) ω =
        (k W).staleCharge (exposedPaths d (decodeButterfly d ω) W) ω +
          terminalCharge d (decodeButterfly d ω) z (W.erase z) := by
  exact seekCycle_semantics _ _ _ _ _ _ _ _ _ _ (cycleTrace_orbit _ _ _ _ hS hV)

end QueryTree

lemma mem_exposedPaths (d : ℕ) (b : Butterfly d) (V : Finset (Card d)) (s : SwitchIndex d) :
    s ∈ exposedPaths d b V ↔ (switchUsers d b s).1 ∈ V ∨ (switchUsers d b s).2 ∈ V := by
  classical
  simp only [exposedPaths,Finset.mem_biUnion,mem_routeDomain_iff_user]
  constructor
  · rintro ⟨x,hx,h | h⟩
    · exact Or.inl (h ▸ hx)
    · exact Or.inr (h ▸ hx)
  · rintro (h | h)
    · exact ⟨_,h,Or.inl rfl⟩
    · exact ⟨_,h,Or.inr rfl⟩

lemma terminalCharge_sum (d : ℕ) (b : Butterfly d) (z : Card d) (V : Finset (Card d))
    (hz : z ∉ V) :
    (terminalCharge d b z V : ℝ) = ∑ s : SwitchIndex d,
      ((if (switchUsers d b s).1 = z ∧ (switchUsers d b s).2 ∈ V then (1:ℝ) else 0) +
      (if (switchUsers d b s).2 = z ∧ (switchUsers d b s).1 ∈ V then (1:ℝ) else 0)) := by
  classical
  have he : routeDomain d z (butterflyPerm d b z) ∩ exposedPaths d b V =
      Finset.univ.filter (fun s =>
        ((switchUsers d b s).1 = z ∧ (switchUsers d b s).2 ∈ V) ∨
        ((switchUsers d b s).2 = z ∧ (switchUsers d b s).1 ∈ V)) := by
    ext s
    simp only [Finset.mem_inter,mem_routeDomain_iff_user,mem_exposedPaths,
      Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases h₁ : (switchUsers d b s).1 = z <;>
      by_cases h₂ : (switchUsers d b s).2 = z <;> simp [h₁,h₂,hz]
  rw [terminalCharge,he]
  simp only [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h₁ : (switchUsers d b s).1 = z <;>
    by_cases h₂ : (switchUsers d b s).2 = z <;> simp [h₁,h₂,hz]

noncomputable def priorPaths {d A : ℕ} (o : Card d → Option (Fin A)) (t : ℕ) : Finset (Card d) :=
  Finset.univ.filter (fun x => ∃ i : Fin A, o x = some i ∧ i.val < t)

@[simp] lemma mem_priorPaths {d A : ℕ} (o : Card d → Option (Fin A)) (t : ℕ) (x : Card d) :
    x ∈ priorPaths o t ↔ ∃ i : Fin A, o x = some i ∧ i.val < t := by
  classical
  simp [priorPaths]

lemma terminalCharge_prior_sum {d A : ℕ} (o : Card d → Option (Fin A))
    (b : Butterfly d) (z : Terminal o) (i : Fin A) :
    (terminalCharge d b (z i).val ((priorPaths o (i.val+1)).erase (z i).val) : ℝ) =
      ∑ s : SwitchIndex d,
        ((if (z i).val = (switchUsers d b s).1 ∧ (switchUsers d b s).2 ∈ priorPaths o (i.val+1)
          then (1:ℝ) else 0) +
        (if (z i).val = (switchUsers d b s).2 ∧ (switchUsers d b s).1 ∈ priorPaths o (i.val+1)
          then (1:ℝ) else 0)) := by
  classical
  rw [terminalCharge_sum _ _ _ _ (Finset.notMem_erase _ _)]
  apply Finset.sum_congr rfl
  intro s _
  have hn := switchUsers_ne d b s
  simp only [Finset.mem_erase]
  by_cases h₁ : (z i).val = (switchUsers d b s).1 <;>
    by_cases h₂ : (z i).val = (switchUsers d b s).2 <;> simp_all [eq_comm]

lemma rotationMeeting_eq_slot_sum {d A : ℕ} (o : Card d → Option (Fin A))
    (z : Terminal o) (u v : Card d) :
    rotationMeeting o z u v = ∑ i : Fin A,
      ((if (z i).val = u ∧ v ∈ priorPaths o (i.val+1) then (1:ℝ) else 0) +
      (if (z i).val = v ∧ u ∈ priorPaths o (i.val+1) then (1:ℝ) else 0)) := by
  classical
  have only_owner (u : Card d) (a : Fin A) (hou : o u = some a)
      (i : Fin A) (hia : i ≠ a) : (z i).val ≠ u := by
    intro h
    have hi := (z i).property
    rw [h,hou] at hi
    exact hia (Option.some.inj hi).symm
  have sum_one (u v : Card d) (a : Fin A) (hou : o u = some a) :
      (∑ i : Fin A, if (z i).val = u ∧ v ∈ priorPaths o (i.val+1) then (1:ℝ) else 0) =
      if (z a).val = u ∧ v ∈ priorPaths o (a.val+1) then 1 else 0 := by
    apply Finset.sum_eq_single a
    · intro i _ hia
      simp [only_owner u a hou i hia]
    · simp
  have sum_none (u v : Card d) (hou : o u = none) :
      (∑ i : Fin A, if (z i).val = u ∧ v ∈ priorPaths o (i.val+1) then (1:ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hn : (z i).val ≠ u := by
      intro h
      have hi := (z i).property
      rw [h,hou] at hi
      contradiction
    simp [hn]
  rw [Finset.sum_add_distrib]
  cases hou : o u with
  | none =>
    rw [sum_none u v hou]
    simp [rotationMeeting,hou,mem_priorPaths]
  | some a =>
    rw [sum_one u v a hou]
    cases hov : o v with
    | none =>
      rw [sum_none v u hov]
      simp [rotationMeeting,hou,hov,mem_priorPaths]
    | some b =>
      rw [sum_one v u b hov]
      simp only [rotationMeeting,hou,hov,mem_priorPaths,Option.some.injEq]
      rcases lt_trichotomy a b with hab | rfl | hba
      · have hn : ¬ b.val < a.val+1 := by omega
        have hy : a.val < b.val+1 := by omega
        simp [hab,hn,hy]
      · simp
      · have hn : ¬ a.val < b.val+1 := by omega
        have hy : b.val < a.val+1 := by omega
        simp [hba,not_lt_of_ge (le_of_lt hba),hn,hy]

lemma rotationCharge_eq_terminal_sum {d A : ℕ} (o : Card d → Option (Fin A))
    (b : Butterfly d) (z : Terminal o) :
    rotationCharge o b z = ∑ i : Fin A,
      (terminalCharge d b (z i).val ((priorPaths o (i.val+1)).erase (z i).val) : ℝ) := by
  simp only [rotationCharge,rotationMeeting_eq_slot_sum,terminalCharge_prior_sum]
  exact Finset.sum_comm

@[simp] lemma priorPaths_zero {d A : ℕ} (o : Card d → Option (Fin A)) : priorPaths o 0 = ∅ := by
  classical
  ext x
  simp

lemma priorPaths_succ {d A : ℕ} (o : Card d → Option (Fin A)) (t : ℕ) (ht : t < A) :
    priorPaths o (t+1) = priorPaths o t ∪ cycleFiber o ⟨t,ht⟩ := by
  classical
  ext x
  simp only [mem_priorPaths,Finset.mem_union,mem_cycleFiber]
  constructor
  · rintro ⟨i,hi,hit⟩
    by_cases h : i.val < t
    · exact Or.inl ⟨i,hi,h⟩
    · have he : i = ⟨t,ht⟩ := Fin.ext (by change i.val = t; omega)
      exact Or.inr (he ▸ hi)
  · rintro (⟨i,hi,hit⟩ | hi)
    · exact ⟨i,hi,by omega⟩
    · exact ⟨⟨t,ht⟩,hi,by change t < t+1; omega⟩

lemma priorPaths_disjoint {d A : ℕ} (o : Card d → Option (Fin A)) (i : Fin A) :
    Disjoint (priorPaths o i.val) (cycleFiber o i) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨j,hj,hji⟩ := (mem_priorPaths _ _ _).mp hx
  have he : j = i := Option.some.inj (hj.symm.trans ((mem_cycleFiber _ _ _).mp hx'))
  subst j
  exact (lt_irrefl _ hji)

namespace QueryTree

lemma seekCycles_owned {d A : ℕ} (S : Finset (Card d)) (r : Fin A → ℕ)
    (o : Card d → Option (Fin A)) (z : Terminal o) (ω : SwitchIndex d → Bool)
    (hS : ∀ i, cycleFiber o i ⊆ S)
    (hO : ∀ i, orbitSet (butterflyPerm d (decodeButterfly d ω)) (z i).val = cycleFiber o i)
    (hC : ∀ i, (cycleFiber o i).card = r i+1) :
    let p := butterflyPerm d (decodeButterfly d ω)
    let L := List.ofFn (fun i : Fin A => (p (z i).val,r i))
    (seekCycles d S L ∅).succeeds ω = true ∧
      ((seekCycles d S L ∅).staleCharge ∅ ω : ℝ) = rotationCharge o (decodeButterfly d ω) z := by
  classical
  let b := decodeButterfly d ω
  let p := butterflyPerm d b
  let f (i : Fin A) := (p (z i).val,r i)
  let c (i : Fin A) : ℝ := terminalCharge d b (z i).val ((priorPaths o (i.val+1)).erase (z i).val)
  have hc (i : Fin A) : Function.minimalPeriod p (z i).val - 1 = r i := by
    have he := orbitSet_card p (z i).val
    rw [hO,hC] at he
    omega
  have hs (t : ℕ) (ht : t ≤ A) :
      (seekCycles d S ((List.ofFn f).drop t) (priorPaths o t)).succeeds ω = true ∧
        ((seekCycles d S ((List.ofFn f).drop t) (priorPaths o t)).staleCharge (exposedPaths d b (priorPaths o t)) ω : ℝ) =
          ((List.ofFn c).drop t).sum := by
    induction ht using Nat.decreasingInduction with
    | self => simp only [List.length_ofFn,le_refl,List.drop_eq_nil_of_le,List.sum_nil,seekCycles,succeeds,staleCharge,Nat.cast_zero,and_self]
    | of_succ t ht ih =>
      have htf : t < (List.ofFn f).length := by simpa using ht
      have htc : t < (List.ofFn c).length := by simpa using ht
      rw [List.drop_eq_getElem_cons htf,List.drop_eq_getElem_cons htc]
      simp only [List.getElem_ofFn,List.sum_cons,seekCycles]
      have h := seekCycle_orbit d S (priorPaths o t) (z ⟨t,ht⟩).val
        (fun V => seekCycles d S ((List.ofFn f).drop (t+1)) V) ω
        (by rw [hO]; exact hS _) (by rw [hO]; exact priorPaths_disjoint o ⟨t,ht⟩)
      dsimp only at h
      rw [hc,hO,←priorPaths_succ o t ht] at h
      dsimp only [f]
      constructor
      · exact h.1.trans ih.1
      · rw [h.2,Nat.cast_add,ih.2]
        exact add_comm _ _
  have h := hs 0 (Nat.zero_le _)
  simp only [List.drop_zero,priorPaths_zero,exposedPaths_empty,List.sum_ofFn] at h
  dsimp only
  exact ⟨h.1,h.2.trans (rotationCharge_eq_terminal_sum o b z).symm⟩

end QueryTree

section Collections
variable {d A : ℕ}

def ValidCycleSlots (p : Equiv.Perm (Card d)) (S : Finset (Card d)) (r : Fin A → ℕ)
    (o : Card d → Option (Fin A)) : Prop :=
  (∀ i, (cycleFiber o i).card = r i + 1) ∧
  (∀ i, cycleFiber o i ⊆ S) ∧
  (∀ i x, o x = some i → orbitSet p x = cycleFiber o i)

abbrev CycleSlots (p : Equiv.Perm (Card d)) (S : Finset (Card d)) (r : Fin A → ℕ) :=
  {o : Card d → Option (Fin A) // ValidCycleSlots p S r o}

noncomputable instance (p : Equiv.Perm (Card d)) (S : Finset (Card d)) (r : Fin A → ℕ) :
    Fintype (CycleSlots p S r) := Fintype.ofFinite _

lemma CycleSlots.terminal_nonempty {p : Equiv.Perm (Card d)} {S : Finset (Card d)} {r : Fin A → ℕ}
    (c : CycleSlots p S r) (i : Fin A) : Nonempty {x : Card d // c.val x = some i} := by
  have hn : (cycleFiber c.val i).Nonempty := Finset.card_pos.mp (by rw [c.property.1]; omega)
  obtain ⟨x,hx⟩ := hn
  exact ⟨x,(mem_cycleFiber _ _ _).mp hx⟩

lemma owner_ext {o o' : Card d → Option (Fin A)}
    (h : ∀ i, cycleFiber o i = cycleFiber o' i) : o = o' := by
  funext x
  have he (i : Fin A) : o x = some i ↔ o' x = some i := by
    simpa only [mem_cycleFiber] using (Finset.ext_iff.mp (h i) x)
  cases ho : o x with
  | some i => exact ((he i).mp ho).symm
  | none =>
    cases ho' : o' x with
    | none => rfl
    | some i => have hn := (he i).mpr ho'; rw [ho] at hn; contradiction

abbrev RootedSlots (p : Equiv.Perm (Card d)) (S : Finset (Card d)) (r : Fin A → ℕ) :=
  Σ c : CycleSlots p S r, Terminal c.val

noncomputable def rootedStart {p : Equiv.Perm (Card d)} {S : Finset (Card d)} {r : Fin A → ℕ}
    (c : RootedSlots p S r) : Fin A → S := fun i =>
  ⟨p (c.2 i).val,c.1.property.2.1 i (by
    rw [←c.1.property.2.2 i (c.2 i).val (c.2 i).property]
    exact (mem_orbitSet _ _ _).mpr (Equiv.Perm.SameCycle.apply_right (Equiv.Perm.SameCycle.refl p _)))⟩

lemma rootedStart_injective {p : Equiv.Perm (Card d)} {S : Finset (Card d)} {r : Fin A → ℕ} :
    Function.Injective (rootedStart (p:=p) (S:=S) (r:=r)) := by
  rintro ⟨c,z⟩ ⟨c',z'⟩ h
  have hz (i : Fin A) : (z i).val = (z' i).val :=
    p.injective (congrArg Subtype.val (congrFun h i))
  have hc : c = c' := Subtype.ext (owner_ext (fun i => by
    rw [←c.property.2.2 i (z i).val (z i).property,
      ←c'.property.2.2 i (z' i).val (z' i).property,hz]))
  subst c'
  have hzz : z = z' := funext (fun i => Subtype.ext (hz i))
  subst z'
  rfl

lemma sum_comp_injective_le {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ a, f (e a) ≤ ∑ b, f b := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image e, f b := (Finset.sum_image (fun _ _ _ _ h => he h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hf b)

lemma rooted_weight_sum_le (S : Finset (Card d)) (r : Fin A → ℕ) (ω : SwitchIndex d → Bool) :
    (∑ c : RootedSlots (butterflyPerm d (decodeButterfly d ω)) S r,
      ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge c.1.val (decodeButterfly d ω) c.2)) ≤
    ∑ a : Fin A → S,
      if (QueryTree.seekCycles d S (List.ofFn (fun i => ((a i).val,r i))) ∅).succeeds ω then
        ((2:ℝ)^d)^A / (2:ℝ)^(QueryTree.seekCycles d S (List.ofFn (fun i => ((a i).val,r i))) ∅).staleCharge ∅ ω
      else 0 := by
  classical
  let p := butterflyPerm d (decodeButterfly d ω)
  let g (a : Fin A → S) : ℝ :=
    if (QueryTree.seekCycles d S (List.ofFn (fun i => ((a i).val,r i))) ∅).succeeds ω then
      ((2:ℝ)^d)^A / (2:ℝ)^(QueryTree.seekCycles d S (List.ofFn (fun i => ((a i).val,r i))) ∅).staleCharge ∅ ω
    else 0
  have he (c : RootedSlots p S r) :
      ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge c.1.val (decodeButterfly d ω) c.2) =
      g (rootedStart c) := by
    have hs := QueryTree.seekCycles_owned S r c.1.val c.2 ω c.1.property.2.1
      (fun i => c.1.property.2.2 i (c.2 i).val (c.2 i).property) c.1.property.1
    dsimp only at hs
    unfold g
    rw [ite_eq_left (show (QueryTree.seekCycles d S (List.ofFn (fun i => ((rootedStart c i).val,r i))) ∅).succeeds ω = true from hs.1)]
    rw [← hs.2,neg_mul,Real.exp_neg,mul_comm (Real.log 2),Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rfl
  simp_rw [he]
  exact sum_comp_injective_le rootedStart rootedStart_injective g (fun a => by dsimp [g]; split_ifs <;> positivity)

noncomputable def rotationLower (d : ℕ) {A : ℕ} (r : Fin A → ℕ) : ℝ :=
  Real.exp (-Real.log 2 * ((A:ℝ)*d/2 + ∑ i : Fin A, Real.log (r i+1) / (2 * Real.log 2)))

noncomputable def collectionWeight (d : ℕ) {A : ℕ} (r : Fin A → ℕ) : ℝ :=
  ((2:ℝ)^d)^A * (∏ i : Fin A, (r i+1 : ℝ)) * rotationLower d r

lemma collectionWeight_pos (d : ℕ) {A : ℕ} (r : Fin A → ℕ) : 0 < collectionWeight d r := by
  unfold collectionWeight rotationLower
  positivity

lemma collection_rotation_lower (S : Finset (Card d)) (r : Fin A → ℕ) (hr : Monotone r)
    (ω : SwitchIndex d → Bool) (c : CycleSlots (butterflyPerm d (decodeButterfly d ω)) S r) :
    collectionWeight d r ≤ ∑ z : Terminal c.val,
      ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge c.val (decodeButterfly d ω) z) := by
  classical
  let (i : Fin A) : Nonempty {x : Card d // c.val x = some i} := c.terminal_nonempty i
  have hm : Monotone (fun i => (cycleFiber c.val i).card) := by
    intro i j hij
    dsimp only
    rw [c.property.1,c.property.1]
    exact Nat.add_le_add_right (hr hij) 1
  have hb := rotation_exp_bound hm (decodeButterfly d ω)
  have hcard : (Fintype.card (Terminal c.val) : ℝ) = ∏ i : Fin A, (r i+1 : ℝ) := by
    rw [Fintype.card_pi,Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [card_cycleFiber,c.property.1,Nat.cast_add,Nat.cast_one]
  have hp : (0:ℝ) < Fintype.card (Terminal c.val) := Nat.cast_pos.mpr Fintype.card_pos
  have hl : rotationLower d r ≤ finiteMean (fun z : Terminal c.val => Real.exp (-Real.log 2 * rotationCharge c.val (decodeButterfly d ω) z)) := by
    simpa only [rotationLower,c.property.1,Nat.cast_add,Nat.cast_one] using hb
  have hh := (le_div_iff₀ hp).mp hl
  rw [hcard] at hh
  unfold collectionWeight
  rw [← Finset.mul_sum]
  calc
    _ = ((2:ℝ)^d)^A * (rotationLower d r * ∏ i : Fin A, (r i+1 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

lemma cycleSlots_weighted_moment (S : Finset (Card d)) (r : Fin A → ℕ) (hr : Monotone r) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      (Fintype.card (CycleSlots (butterflyPerm d (decodeButterfly d ω)) S r) : ℝ)) *
      collectionWeight d r ≤ (S.card : ℝ)^A := by
  classical
  let g (a : Fin A → S) (ω : SwitchIndex d → Bool) : ℝ :=
    if (QueryTree.seekCycles d S (List.ofFn (fun i => ((a i).val,r i))) ∅).succeeds ω then
      ((2:ℝ)^d)^A / (2:ℝ)^(QueryTree.seekCycles d S (List.ofFn (fun i => ((a i).val,r i))) ∅).staleCharge ∅ ω
    else 0
  have hω (ω : SwitchIndex d → Bool) :
      (Fintype.card (CycleSlots (butterflyPerm d (decodeButterfly d ω)) S r) : ℝ) * collectionWeight d r ≤
        ∑ a : Fin A → S, g a ω := by
    calc
      _ = ∑ _c : CycleSlots (butterflyPerm d (decodeButterfly d ω)) S r, collectionWeight d r := by simp
      _ ≤ ∑ c : CycleSlots (butterflyPerm d (decodeButterfly d ω)) S r,
          ∑ z : Terminal c.val, ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge c.val (decodeButterfly d ω) z) :=
        Finset.sum_le_sum (fun c _ => collection_rotation_lower S r hr ω c)
      _ = ∑ c : RootedSlots (butterflyPerm d (decodeButterfly d ω)) S r,
          ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge c.1.val (decodeButterfly d ω) c.2) :=
        (Fintype.sum_sigma (fun c : RootedSlots (butterflyPerm d (decodeButterfly d ω)) S r =>
          ((2:ℝ)^d)^A * Real.exp (-Real.log 2 * rotationCharge c.1.val (decodeButterfly d ω) c.2))).symm
      _ ≤ _ := rooted_weight_sum_le S r ω
  have hb := finiteMean_mono hω
  rw [finiteMean_mul_const,finiteMean_sum] at hb
  calc
    _ ≤ ∑ a : Fin A → S, finiteMean (g a) := hb
    _ ≤ ∑ _a : Fin A → S, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      have hh := QueryTree.cycles_weighted_success d S (List.ofFn (fun i : Fin A => ((a i).val,r i)))
      simpa only [List.length_ofFn] using hh
    _ = _ := by simp

lemma cycleSlots_moment (S : Finset (Card d)) (r : Fin A → ℕ) (hr : Monotone r) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      (Fintype.card (CycleSlots (butterflyPerm d (decodeButterfly d ω)) S r) : ℝ)) ≤
        (S.card : ℝ)^A / collectionWeight d r := by
  exact (le_div_iff₀ (collectionWeight_pos d r)).mpr (cycleSlots_weighted_moment S r hr)

lemma collectionWeight_eq_sqrt (d : ℕ) {A : ℕ} (r : Fin A → ℕ) :
    collectionWeight d r = (Real.sqrt ((2:ℝ)^d))^A * ∏ i : Fin A, Real.sqrt (r i+1) := by
  have hn : ((2:ℝ)^d)^A = Real.exp ((A:ℝ)*d*Real.log 2) := by
    rw [mul_assoc,Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hp : (∏ i : Fin A, (r i+1 : ℝ)) = Real.exp (∑ i : Fin A, Real.log (r i+1)) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    exact (Real.exp_log (by positivity)).symm
  have hs : Real.sqrt ((2:ℝ)^d) = Real.exp ((d:ℝ)*Real.log 2/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by positivity),Real.log_pow]
    congr 1
    ring
  have hj (i : Fin A) : Real.sqrt (r i+1) = Real.exp (Real.log (r i+1)/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  simp_rw [collectionWeight,hn,hp,rotationLower,hs,hj]
  rw [←Real.exp_add,←Real.exp_add,←Real.exp_nat_mul,←Real.exp_sum,←Real.exp_add]
  congr 1
  rw [←Finset.sum_div,←Finset.sum_div]
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

lemma butterfly_cycleSlots_moment (S : Finset (Card d)) (r : Fin A → ℕ) (hr : Monotone r) :
    finiteMean (fun ω : SwitchIndex d → Bool =>
      (Fintype.card (CycleSlots (butterflyPerm d (decodeButterfly d ω)) S r) : ℝ)) ≤
        ((S.card : ℝ) / Real.sqrt ((2:ℝ)^d))^A *
          ∏ i : Fin A, (1 / Real.sqrt (r i+1)) := by
  have h := cycleSlots_moment S r hr
  rw [collectionWeight_eq_sqrt,div_mul_eq_div_mul_one_div] at h
  rw [div_pow]
  simpa only [one_div,Finset.prod_inv_distrib] using h

end Collections

variable {d A : ℕ}

abbrev SelectedCycle (p : Equiv.Perm (Card d)) (S : Finset (Card d)) :=
  {C : Finset (Card d) // (∃ x, C = orbitSet p x) ∧ C ⊆ S}

noncomputable instance (p : Equiv.Perm (Card d)) (S : Finset (Card d)) :
    Fintype (SelectedCycle p S) := Fintype.ofFinite _

lemma SelectedCycle.nonempty {p : Equiv.Perm (Card d)} {S : Finset (Card d)}
    (C : SelectedCycle p S) : C.val.Nonempty := by
  obtain ⟨x,hx⟩ := C.property.1
  rw [hx]
  exact orbitSet_nonempty p x

lemma SelectedCycle.orbit_eq {p : Equiv.Perm (Card d)} {S : Finset (Card d)}
    (C : SelectedCycle p S) {x : Card d} (hx : x ∈ C.val) : orbitSet p x = C.val := by
  obtain ⟨y,hy⟩ := C.property.1
  rw [hy] at hx ⊢
  exact (orbitSet_eq p ((mem_orbitSet _ _ _).mp hx)).symm

lemma SelectedCycle.eq_of_mem {p : Equiv.Perm (Card d)} {S : Finset (Card d)}
    (C D : SelectedCycle p S) {x : Card d} (hC : x ∈ C.val) (hD : x ∈ D.val) : C = D := by
  apply Subtype.ext
  exact (C.orbit_eq hC).symm.trans (D.orbit_eq hD)

abbrev SlotAssignment (p : Equiv.Perm (Card d)) (S : Finset (Card d)) (r : Fin A → ℕ) :=
  {f : Fin A → SelectedCycle p S // Function.Injective f ∧ ∀ i, (f i).val.card = r i+1}

noncomputable instance (p : Equiv.Perm (Card d)) (S : Finset (Card d)) (r : Fin A → ℕ) :
    Fintype (SlotAssignment p S r) := Fintype.ofFinite _

noncomputable def slotsToAssignment {p : Equiv.Perm (Card d)} {S : Finset (Card d)} {r : Fin A → ℕ}
    (c : CycleSlots p S r) : SlotAssignment p S r := by
  classical
  let f (i : Fin A) : SelectedCycle p S := ⟨cycleFiber c.val i,by
    obtain ⟨x,hx⟩ := c.terminal_nonempty i
    exact ⟨⟨x,(c.property.2.2 i x hx).symm⟩,c.property.2.1 i⟩⟩
  refine ⟨f,?_,fun i => c.property.1 i⟩
  intro i j hij
  have he : cycleFiber c.val i = cycleFiber c.val j := congrArg Subtype.val hij
  obtain ⟨x,hx⟩ := c.terminal_nonempty i
  have hxi : x ∈ cycleFiber c.val i := (mem_cycleFiber _ _ _).mpr hx
  rw [he] at hxi
  exact Option.some.inj (hx.symm.trans ((mem_cycleFiber _ _ _).mp hxi))

noncomputable def assignmentOwner {p : Equiv.Perm (Card d)} {S : Finset (Card d)} {r : Fin A → ℕ}
    (f : SlotAssignment p S r) (x : Card d) : Option (Fin A) := by
  classical
  exact if h : ∃ i, x ∈ (f.val i).val then some (Classical.choose h) else none

end Thorp

end ThorpNine.Adaptive

end OAI
