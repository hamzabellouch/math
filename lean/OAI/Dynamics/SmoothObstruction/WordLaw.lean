import OAI.Dynamics.SmoothObstruction.Sampling
import OAI.Dynamics.SmoothObstruction.FiniteLaw

namespace OAI

section

open Finset

namespace SmoothObstruction.WordLaw
open Finset FiniteLaw GroupSampler SequentialLaw SymplecticSampling

/-- The literal dyadic predecessor schedule of W1, padded by absent equations
up to K slots. Groups restart this schedule at zero. -/
def lagBack (K t : ℕ) (j : Fin K) : Option (Fin t) :=
  if h : j.val ≤ K / 8 ∧ 2 ^ j.val ≤ t then
    some ⟨t - 2 ^ j.val, Nat.sub_lt (lt_of_lt_of_le (by positivity) h.2) (by positivity)⟩
  else none

lemma lagBack_eq {K t k : ℕ} (hk : k < K) (hk8 : k ≤ K / 8) (hkt : 2 ^ k ≤ t) :
    lagBack K t ⟨k, hk⟩ = some ⟨t - 2 ^ k,
      Nat.sub_lt (lt_of_lt_of_le (by positivity) hkt) (by positivity)⟩ := by
  simp [lagBack, hk8, hkt]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Fintype V] [DecidableEq V]
variable (B : LinearMap.BilinForm (ZMod 2) V) {K H q : ℕ}

noncomputable def groupLaw (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (H : ℕ) :
    Law (Fin H → {v : V // v ≠ 0}) where
  mass := weight (step B (lagBack K)) H
  nonneg := weight_nonneg (fun _ _ _ => kernel_nonneg B _ _) H
  total := sum_weight (step_sum B (lagBack K) hd) H

noncomputable def rawLaw (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (H q : ℕ) :
    Law (Fin q → Fin H → {v : V // v ≠ 0}) :=
  product (fun _ : Fin q => groupLaw B hd H)

lemma group_relations (hd : K + 1 ≤ Module.finrank (ZMod 2) V)
    {w : Fin H → {v : V // v ≠ 0}} (hw : 0 < (groupLaw B hd H).mass w)
    {r k : ℕ} (hk : k < K) (hk8 : k ≤ K / 8) (hrt : r + 2 ^ k < H) :
    B (w ⟨r, lt_trans (Nat.lt_add_of_pos_right (by positivity)) hrt⟩).val
      (w ⟨r + 2 ^ k, hrt⟩).val = 0 := by
  have hlag : 2 ^ k ≤ r + 2 ^ k := Nat.le_add_left _ _
  have hre : lagBack K (r + 2 ^ k) ⟨k, hk⟩ =
      some ⟨r, Nat.lt_add_of_pos_right (by positivity)⟩ := by
    simp [lagBack, hk8, hlag]
  exact supported_constraints B (lagBack K) H w hw ⟨r + 2 ^ k, hrt⟩ ⟨k, hk⟩ _ hre

lemma raw_relations (hd : K + 1 ≤ Module.finrank (ZMod 2) V)
    {w : Fin q → Fin H → {v : V // v ≠ 0}} (hw : 0 < (rawLaw B hd H q).mass w)
    (b : Fin q) {r k : ℕ} (hk : k < K) (hk8 : k ≤ K / 8) (hrt : r + 2 ^ k < H) :
    B (w b ⟨r, lt_trans (Nat.lt_add_of_pos_right (by positivity)) hrt⟩).val
      (w b ⟨r + 2 ^ k, hrt⟩).val = 0 := by
  apply group_relations B hd (k := k) (r := r) _ hk hk8 hrt
  have hz : (groupLaw B hd H).mass (w b) ≠ 0 := by
    intro hz
    have hp : (∏ i, (groupLaw B hd H).mass (w i)) = 0 :=
      prod_eq_zero (mem_univ b) hz
    exact (ne_of_gt hw) hp
  exact lt_of_le_of_ne ((groupLaw B hd H).nonneg (w b)) hz.symm

lemma group_label (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (r : Fin H) (a : {v : V // v ≠ 0}) :
    expect (groupLaw B hd H) (fun w => if w r = a then 1 else 0) =
      1 / Fintype.card {v : V // v ≠ 0} := by
  simpa only [FiniteLaw.expect, groupLaw, mul_ite, mul_one, mul_zero, marginal]
    using uniform_position B hB hnd (lagBack K) hd r a

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Empirical probability vector formed from a single group. -/
noncomputable def empirical (f : {v : V // v ≠ 0} → C)
    (w : Fin H → {v : V // v ≠ 0}) (c : C) : ℝ :=
  (∑ r, if f (w r) = c then (1 : ℝ) else 0) / H

omit [Module (ZMod 2) V] [Fintype V] [DecidableEq V] [Fintype C] in
lemma empirical_nonneg (f : {v : V // v ≠ 0} → C)
    (w : Fin H → {v : V // v ≠ 0}) (c : C) : 0 ≤ empirical f w c := by
  unfold empirical
  positivity

omit [Module (ZMod 2) V] [Fintype V] [DecidableEq V] in
lemma empirical_total (hH : 0 < H) (f : {v : V // v ≠ 0} → C)
    (w : Fin H → {v : V // v ≠ 0}) : ∑ c, empirical f w c = 1 := by
  unfold empirical
  rw [← sum_div, sum_comm]
  simp [hH.ne']

omit [Fintype C] in
lemma group_observable (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (f : {v : V // v ≠ 0} → C)
    (r : Fin H) (c : C) :
    expect (groupLaw B hd H) (fun w => if f (w r) = c then 1 else 0) =
      (∑ a : {v : V // v ≠ 0}, if f a = c then (1 : ℝ) else 0) /
        Fintype.card {v : V // v ≠ 0} := by
  have he (w : Fin H → {v : V // v ≠ 0}) :
      (if f (w r) = c then (1 : ℝ) else 0) =
        ∑ a, (if w r = a then (1 : ℝ) else 0) * (if f a = c then 1 else 0) := by
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  simp_rw [he]
  rw [expect_sum]
  simp_rw [expect_mul_const, group_label B hB hnd hd]
  rw [← mul_sum]
  ring

omit [Fintype C] in
lemma group_mean (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (hH : 0 < H)
    (f : {v : V // v ≠ 0} → C) (c : C) :
    expect (groupLaw B hd H) (fun w => empirical f w c) =
      (∑ a : {v : V // v ≠ 0}, if f a = c then (1 : ℝ) else 0) /
        Fintype.card {v : V // v ≠ 0} := by
  simp only [empirical, div_eq_mul_inv]
  rw [expect_mul_const, expect_sum]
  simp_rw [← div_eq_mul_inv, group_observable B hB hnd hd]
  simp [hH.ne']

/-- The first source use of the probability-vector estimate: it averages
groups, not falsely independent positions within a group. -/
theorem raw_empirical_tv (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (hH : 0 < H) (hq : 0 < q)
    (f : {v : V // v ≠ 0} → C) :
    expect (rawLaw B hd H q) (fun w => (1 / 2 : ℝ) * ∑ c,
      |(∑ b, empirical f (w b) c) / q -
        (∑ a : {v : V // v ≠ 0}, if f a = c then (1 : ℝ) else 0) /
          Fintype.card {v : V // v ≠ 0}|) ≤
      (1 / 2 : ℝ) * Real.sqrt (Fintype.card C / q) := by
  have : NeZero q := ⟨hq.ne'⟩
  simpa only [Fintype.card_fin, rawLaw] using independent_vectors_tv
    (fun _ : Fin q => groupLaw B hd H) (fun _ => empirical f) _
    (fun _ => empirical_nonneg f) (fun _ => empirical_total hH f)
    (fun _ => group_mean B hB hnd hd hH f)


/-- A specified arbitrary sublist, across any number of groups. The exponent
is the exact number of specified coordinates, not the size of its span. -/
theorem raw_sublist_groups (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (m : Fin q → Fin H → Option {v : V // v ≠ 0}) :
    FiniteLaw.expect (rawLaw B hd H q) (fun w => ∏ b, test (m b) (w b)) ≤
      ((2 : ℝ) ^ (2 * K) / Fintype.card {v : V // v ≠ 0}) ^
        (∑ b, (univ.filter (fun r => (m b r).isSome)).card) := by
  change FiniteLaw.expect (product (fun _ : Fin q => groupLaw B hd H)) _ ≤ _
  rw [product_moment]
  calc
    _ ≤ ∏ b, ((2 : ℝ) ^ (2 * K) / Fintype.card {v : V // v ≠ 0}) ^
        (univ.filter (fun r => (m b r).isSome)).card := by
      apply prod_le_prod₀
      · intro b _; exact expect_nonneg _ (test_nonneg _)
      · intro b _; exact raw_sublist B (lagBack K) hK hd H (m b)
    _ = _ := prod_pow_eq_pow_sum _ _ _

/-- All actual conditioned laws pay the factor two once for the whole word. -/
theorem conditioned_sublist (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1 / 2 ≤ prob (rawLaw B hd H q) E)
    (m : Fin q → Fin H → Option {v : V // v ≠ 0}) :
    FiniteLaw.expect (condition (rawLaw B hd H q) E (by change 0 < prob _ E; linarith))
      (fun w => ∏ b, test (m b) (w b)) ≤
      2 * ((2 : ℝ) ^ (2 * K) / Fintype.card {v : V // v ≠ 0}) ^
        (∑ b, (univ.filter (fun r => (m b r).isSome)).card) := by
  exact (condition_bound (rawLaw B hd H q) E hE _
    (fun w => prod_nonneg (fun b _ => test_nonneg _ _))).trans
      (mul_le_mul_of_nonneg_left (raw_sublist_groups B hd hK m) (by norm_num))

noncomputable def tvFromUniformObservable (f : {v : V // v ≠ 0} → C)
    (w : Fin q → Fin H → {v : V // v ≠ 0}) : ℝ :=
  (1 / 2 : ℝ) * ∑ c, |(∑ b, empirical f (w b) c) / q -
    (∑ a : {v : V // v ≠ 0}, if f a = c then (1 : ℝ) else 0) /
      Fintype.card {v : V // v ≠ 0}|

/-- A concrete, nonempty conditioning event enforcing the per-word condition
simultaneously for all the earlier-level windows. -/
theorem approximation_event {I : Type*} [Fintype I]
    (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (hH : 0 < H) (hq : 0 < q)
    (f : I → {v : V // v ≠ 0} → C) {θ : ℝ} (hθ : 0 < θ)
    (hbudget : (Fintype.card I : ℝ) *
      ((1 / 2 : ℝ) * Real.sqrt (Fintype.card C / q)) / θ ≤ 1 / 2) :
    1 / 2 ≤ prob (rawLaw B hd H q)
      (univ.filter (fun w => ∀ i, tvFromUniformObservable (f i) w ≤ θ)) := by
  apply good_event_mass _ _ _ hθ _ hbudget
  · intro i w
    unfold tvFromUniformObservable
    positivity
  · intro i
    exact raw_empirical_tv B hB hnd hd hH hq (f i)

end SmoothObstruction.WordLaw

namespace SmoothObstruction.FiniteLaw
open Finset
variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]
  [DecidableEq A] [DecidableEq I] [DecidableEq J]

omit [DecidableEq A] [DecidableEq J] in
lemma product_injective_moment (P : I → Law A) (e : J → I) (he : Function.Injective e)
    (f : J → A → ℝ) :
    expect (product P) (fun x => ∏ j, f j (x (e j))) =
      ∏ j, expect (P (e j)) (f j) := by
  classical
  let F : I → A → ℝ := fun i a => if h : i ∈ Set.range e then f (Classical.choose h) a else 1
  have hF (j : J) (a : A) : F (e j) a = f j a := by
    have h : e j ∈ Set.range e := ⟨j, rfl⟩
    have hj : Classical.choose h = j := he (Classical.choose_spec h)
    dsimp only [F]
    rw [dite_eq_left h, hj]
  have hnot (i : I) (hi : i ∉ Set.range e) : F i = fun _ => 1 := by
    funext a
    dsimp only [F]
    rw [dite_eq_right hi]
  have hprod (x : I → A) : (∏ j, f j (x (e j))) = ∏ i, F i (x i) := by
    exact Fintype.prod_of_injective e he _ _ (fun i hi => congrFun (hnot i hi) (x i))
      (fun j => (hF j (x (e j))).symm)
  simp_rw [hprod]
  rw [product_moment]
  symm
  exact Fintype.prod_of_injective e he _ _
    (fun i hi => by rw [hnot i hi]; exact expect_const _ 1)
    (fun j => by congr 1; funext a; exact (hF j a).symm)

lemma product_restriction (P : I → Law A) (e : J → I) (he : Function.Injective e)
    (y : J → A) :
    expect (product P) (fun x => if (fun j => x (e j)) = y then 1 else 0) =
      (product (fun j => P (e j))).mass y := by
  classical
  have hprod (x : I → A) :
      (if (fun j => x (e j)) = y then (1 : ℝ) else 0) =
        ∏ j, if x (e j) = y j then (1 : ℝ) else 0 := by
    simp only [prod_boole, mem_univ, forall_const, funext_iff]
  simp_rw [hprod]
  rw [product_injective_moment P e he (fun j a => if a = y j then 1 else 0)]
  apply prod_congr rfl
  intro j _
  simp [expect, mul_ite]

lemma product_restriction_expect (P : I → Law A) (e : J → I) (he : Function.Injective e)
    (f : (J → A) → ℝ) :
    expect (product P) (fun x => f (fun j => x (e j))) =
      expect (product (fun j => P (e j))) f := by
  classical
  have hsum (x : I → A) : f (fun j => x (e j)) =
      ∑ y : J → A, (if (fun j => x (e j)) = y then (1 : ℝ) else 0) * f y := by
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  simp_rw [hsum]
  rw [expect_sum]
  simp_rw [expect_mul_const, product_restriction P e he]
  rfl

omit [DecidableEq A] [DecidableEq I] in
lemma prob_card_bound (P : Law A) (E : Finset A) {c : ℝ} (hc : ∀ a ∈ E, P.mass a ≤ c) :
    prob P E ≤ E.card * c := by
  calc
    _ ≤ ∑ _a ∈ E, c := sum_le_sum hc
    _ = _ := by simp

omit [DecidableEq A] in
lemma product_mass_upper (P : I → Law A) {c : ℝ} (hc : ∀ i a, (P i).mass a ≤ c)
    (x : I → A) : (product P).mass x ≤ c ^ Fintype.card I := by
  calc
    _ ≤ ∏ _i : I, c := prod_le_prod₀ (fun i _ => (P i).nonneg (x i)) (fun i _ => hc i (x i))
    _ = _ := by simp

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.MatchingCount

variable {A I : Type*} [Fintype A] [Fintype I]

/-- Equalities oriented to a distinct later variable determine the removed
coordinates uniquely from those left free. This is the acyclic comparison
count, without an assumption of independence between equality events. -/
lemma increasing_count {n : ℕ} (f g : I → Fin n)
    (hfg : ∀ i, f i < g i) (hg : Function.Injective g) :
    Nat.card {w : Fin n → A // ∀ i, w (f i) = w (g i)} ≤
      Fintype.card A ^ (n - Fintype.card I) := by
  classical
  let F := {j : Fin n // j ∉ Set.range g}
  let restrict : {w : Fin n → A // ∀ i, w (f i) = w (g i)} → (F → A) :=
    fun w j => w.val j.val
  have hinj : Function.Injective restrict := by
    intro u v huv
    apply Subtype.ext
    funext j
    have heq : ∀ m, ∀ k : Fin n, k.val = m → u.val k = v.val k := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro k hk
        by_cases hmem : k ∈ Set.range g
        · obtain ⟨i, rfl⟩ := hmem
          rw [← u.property i, ← v.property i]
          exact ih (f i).val (by simpa [← hk] using hfg i) (f i) rfl
        · exact congrFun huv (⟨k, hmem⟩ : F)
    exact heq j.val j rfl
  have hcardF : Fintype.card F = n - Fintype.card I := by
    have hsum := Fintype.card_subtype_compl (fun j : Fin n => j ∈ Set.range g)
    have hrange : Fintype.card {j : Fin n // j ∈ Set.range g} = Fintype.card I :=
      (Fintype.card_congr (Equiv.ofInjective g hg)).symm
    simp only [Fintype.card_fin] at hsum
    dsimp [F]
    omega
  have hbound := Nat.card_le_card_of_injective restrict hinj
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun, hcardF] using hbound


/-- For a comparison with two injective endpoint lists and no tautological
loops, at least half the equality constraints can be oriented to distinct
later variables. This includes parallel edges and all repeated-word cases. -/
theorem matching_count {n : ℕ} (f g : I → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g) (hne : ∀ i, f i ≠ g i) :
    Nat.card {w : Fin n → A // ∀ i, w (f i) = w (g i)} ≤
      Fintype.card A ^ (n - (Fintype.card I + 1) / 2) := by
  classical
  let J := {i : I // f i < g i}
  let J' := {i : I // ¬ f i < g i}
  have hj : Fintype.card J + Fintype.card J' = Fintype.card I := by
    have h := Fintype.card_subtype_compl (fun i : I => f i < g i)
    have hle := Fintype.card_subtype_le (fun i : I => f i < g i)
    change Fintype.card J' = Fintype.card I - Fintype.card J at h
    change Fintype.card J ≤ Fintype.card I at hle
    omega
  by_cases ha : IsEmpty A
  · let := ha
    by_cases hn : n = 0
    · subst n
      have : IsEmpty I := ⟨fun i => Fin.elim0 (f i)⟩
      simp [Fintype.card_eq_zero]
    · have : IsEmpty (Fin n → A) := ⟨fun w => isEmptyElim (w ⟨0, Nat.pos_of_ne_zero hn⟩)⟩
      simp
  have : Nonempty A := not_isEmpty_iff.mp ha
  have mono {c : ℕ} (h : (Fintype.card I + 1) / 2 ≤ c) :
      Fintype.card A ^ (n - c) ≤ Fintype.card A ^ (n - (Fintype.card I + 1) / 2) :=
    Nat.pow_le_pow_right Fintype.card_pos (Nat.sub_le_sub_left h _)
  by_cases hJ : (Fintype.card I + 1) / 2 ≤ Fintype.card J
  · let R : {w : Fin n → A // ∀ i, w (f i) = w (g i)} →
        {w : Fin n → A // ∀ i : J, w (f i.val) = w (g i.val)} :=
      fun w => ⟨w.val, fun i => w.property i.val⟩
    have hinj : Function.Injective R := fun u v h => Subtype.ext (show u.val = v.val from congrArg (fun w => w.val) h)
    exact (Nat.card_le_card_of_injective R hinj).trans
      ((increasing_count (fun i : J => f i.val) (fun i : J => g i.val)
        (fun i => i.property) (hg.comp Subtype.val_injective)).trans (mono hJ))
  · have hJ' : (Fintype.card I + 1) / 2 ≤ Fintype.card J' := by omega
    let R : {w : Fin n → A // ∀ i, w (f i) = w (g i)} →
        {w : Fin n → A // ∀ i : J', w (g i.val) = w (f i.val)} :=
      fun w => ⟨w.val, fun i => (w.property i.val).symm⟩
    have hinj : Function.Injective R := fun u v h => Subtype.ext (show u.val = v.val from congrArg (fun w => w.val) h)
    have hgf (i : J') : g i.val < f i.val :=
      lt_of_le_of_ne (le_of_not_gt i.property) (hne i.val).symm
    exact (Nat.card_le_card_of_injective R hinj).trans
      ((increasing_count (fun i : J' => g i.val) (fun i : J' => f i.val) hgf
        (hf.comp Subtype.val_injective)).trans (mono hJ'))

end SmoothObstruction.MatchingCount

namespace SmoothObstruction.MatchingCount
open Finset
variable {A I W : Type*} [Fintype A] [Fintype I] [Fintype W]

/-- The comparison count in an arbitrary finite ambient coordinate set,
including several complete sampled words and repeated sample-list indices. -/
theorem matching_count_finite (f g : I → W)
    (hf : Function.Injective f) (hg : Function.Injective g) (hne : ∀ i, f i ≠ g i) :
    Nat.card {w : W → A // ∀ i, w (f i) = w (g i)} ≤
      Fintype.card A ^ (Fintype.card W - (Fintype.card I + 1) / 2) := by
  classical
  let E := Fintype.equivFin W
  let e : {w : W → A // ∀ i, w (f i) = w (g i)} ≃
      {w : Fin (Fintype.card W) → A // ∀ i, w (E (f i)) = w (E (g i))} :=
    { toFun := fun w => ⟨w.val ∘ E.symm, by simpa using w.property⟩
      invFun := fun w => ⟨w.val ∘ E, w.property⟩
      left_inv := fun w => Subtype.ext (by funext i; simp)
      right_inv := fun w => Subtype.ext (by funext i; simp) }
  rw [Nat.card_congr e]
  exact matching_count _ _ (E.injective.comp hf) (E.injective.comp hg)
    (fun i he => hne i (E.injective he))

/-- Cardinality to probability: the reference comparison estimate, valid for
any nonnegative finite law with a pointwise full-list bound. -/
theorem comparison_probability [DecidableEq W] [DecidableEq A]
    (P : FiniteLaw.Law (W → A)) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ w, P.mass w ≤ c)
    (f g : I → W) (hf : Function.Injective f) (hg : Function.Injective g)
    (hne : ∀ i, f i ≠ g i) :
    FiniteLaw.prob P (univ.filter (fun w => ∀ i, w (f i) = w (g i))) ≤
      (Fintype.card A : ℝ) ^ (Fintype.card W - (Fintype.card I + 1) / 2) * c := by
  have hcount : (univ.filter (fun w : W → A => ∀ i, w (f i) = w (g i))).card ≤
      Fintype.card A ^ (Fintype.card W - (Fintype.card I + 1) / 2) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using matching_count_finite (A := A) f g hf hg hne
  exact (FiniteLaw.prob_card_bound P _ (fun w _ => hc w)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hc0)

end SmoothObstruction.MatchingCount

namespace SmoothObstruction.FiniteLaw
open Finset
variable {A I J R : Type*} [Fintype A] [Fintype I] [Fintype J] [Fintype R]
  [DecidableEq A] [DecidableEq I] [DecidableEq J] [DecidableEq R]

omit [DecidableEq A] in
lemma prob_mono (P : Law A) {E F : Finset A} (h : E ⊆ F) : prob P E ≤ prob P F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro a _ _
  exact P.nonneg a

/-- Actual independent complete-list sampling, with arbitrary repeated uses of
list indices in the comparison endpoints. The index injection counts each
independently sampled word once and all unused sampled words are integrated. -/
lemma sampled_matching_probability (P : I → Law (R → A)) (e : J → I)
    (he : Function.Injective e) (f g : R → J × R)
    (hf : Function.Injective f) (hg : Function.Injective g) (hne : ∀ r, f r ≠ g r)
    (s : Finset R) {c : ℝ} (hc : 0 ≤ c) (hP : ∀ j w, (P (e j)).mass w ≤ c) :
    prob (product P) (univ.filter (fun x => ∀ r ∈ s,
      x (e (f r).1) (f r).2 = x (e (g r).1) (g r).2)) ≤
      (Fintype.card A : ℝ) ^ (Fintype.card J * Fintype.card R - (s.card + 1) / 2) *
        c ^ Fintype.card J := by
  classical
  rw [prob_eq_expect]
  simp only [mem_filter, mem_univ, true_and]
  rw [product_restriction_expect P e he
    (fun x => if ∀ r ∈ s, x (f r).1 (f r).2 = x (g r).1 (g r).2 then 1 else 0)]
  have hprob : expect (product (fun j => P (e j)))
      (fun x => if ∀ r ∈ s, x (f r).1 (f r).2 = x (g r).1 (g r).2 then 1 else 0) =
      prob (product (fun j => P (e j)))
      (univ.filter (fun x => ∀ r ∈ s, x (f r).1 (f r).2 = x (g r).1 (g r).2)) := by
    rw [prob_eq_expect]
    simp only [mem_filter, mem_univ, true_and]
  rw [hprob]
  let Q := product (fun j => P (e j))
  let E : Finset (J → R → A) := univ.filter
    (fun x => ∀ r ∈ s, x (f r).1 (f r).2 = x (g r).1 (g r).2)
  have hcount : E.card ≤ Fintype.card A ^
      (Fintype.card J * Fintype.card R - (s.card + 1) / 2) := by
    let se : {x : J → R → A // ∀ r ∈ s, x (f r).1 (f r).2 = x (g r).1 (g r).2} ≃
        {x : J × R → A // ∀ r : s, x (f r) = x (g r)} :=
      { toFun := fun x => ⟨Function.uncurry x.val, fun r => x.property r r.property⟩
        invFun := fun x => ⟨Function.curry x.val, fun r hr => x.property ⟨r, hr⟩⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    have h := MatchingCount.matching_count_finite (A := A)
      (fun r : s => f r) (fun r : s => g r)
      (hf.comp Subtype.val_injective) (hg.comp Subtype.val_injective) (fun r => hne r)
    rw [← Nat.card_congr se] at h
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, E] using h
  exact (prob_card_bound Q E (fun x _ => product_mass_upper _ hP x)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (pow_nonneg hc _))

/-- Union over specified matching-position sets. No label independence inside
a sampled word is assumed. -/
lemma sampled_bad_comparison (P : I → Law (R → A)) (e : J → I)
    (he : Function.Injective e) (f g : R → J × R)
    (hf : Function.Injective f) (hg : Function.Injective g) (hne : ∀ r, f r ≠ g r)
    (a : ℕ) {c : ℝ} (hc : 0 ≤ c) (hP : ∀ j w, (P (e j)).mass w ≤ c) :
    prob (product P) (univ.filter (fun x => a ≤ (univ.filter (fun r =>
      x (e (f r).1) (f r).2 = x (e (g r).1) (g r).2)).card)) ≤
      (2 : ℝ) ^ Fintype.card R *
        (Fintype.card A : ℝ) ^ (Fintype.card J * Fintype.card R - (a + 1) / 2) *
        c ^ Fintype.card J := by
  classical
  let S := powersetCard a (univ : Finset R)
  let E : S → Finset (I → R → A) := fun s => univ.filter (fun x => ∀ r ∈ s.val,
    x (e (f r).1) (f r).2 = x (e (g r).1) (g r).2)
  have hsub : (univ.filter (fun x => a ≤ (univ.filter (fun r : R =>
      x (e (f r).1) (f r).2 = x (e (g r).1) (g r).2)).card)) ⊆ univ.biUnion E := by
    intro x hx
    obtain ⟨s, hs, hsa⟩ := Finset.exists_subset_card_eq (mem_filter.mp hx).2
    have hsS : s ∈ S := mem_powersetCard.mpr ⟨subset_univ _, hsa⟩
    apply mem_biUnion.mpr
    refine ⟨⟨s, hsS⟩, mem_univ _, ?_⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro r hr
    exact (mem_filter.mp (hs hr)).2
  have hbound (s : S) : prob (product P) (E s) ≤
      (Fintype.card A : ℝ) ^ (Fintype.card J * Fintype.card R - (a + 1) / 2) *
        c ^ Fintype.card J := by
    have h := sampled_matching_probability P e he f g hf hg hne s.val hc hP
    have hs := (mem_powersetCard.mp s.property).2
    simpa only [hs] using h
  have hcard : Fintype.card S ≤ 2 ^ Fintype.card R := by
    rw [Fintype.card_coe, card_powersetCard, card_univ]
    exact Nat.choose_le_two_pow _ _
  calc
    _ ≤ prob (product P) (univ.biUnion E) := prob_mono _ hsub
    _ ≤ ∑ s : S, prob (product P) (E s) := union_bound _ E
    _ ≤ ∑ _s : S, (Fintype.card A : ℝ) ^
        (Fintype.card J * Fintype.card R - (a + 1) / 2) * c ^ Fintype.card J :=
      sum_le_sum (fun s _ => hbound s)
    _ = (Fintype.card S : ℝ) * ((Fintype.card A : ℝ) ^
        (Fintype.card J * Fintype.card R - (a + 1) / 2) * c ^ Fintype.card J) := by simp
    _ ≤ (2 : ℝ) ^ Fintype.card R * ((Fintype.card A : ℝ) ^
        (Fintype.card J * Fintype.card R - (a + 1) / 2) * c ^ Fintype.card J) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg (by positivity) (pow_nonneg hc _))
    _ = _ := by ring

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.FiniteLaw

/-- Exact simplification of the sampled comparison cost. The one-time
conditioning doubles each of at most three word laws, costing eight, not a
factor per selected label. -/
lemma comparison_cost {L U : ℝ} (hL : 1 ≤ L) (hU : 1 ≤ U)
    {N j a : ℕ} (hj : 1 ≤ j) (hj' : j ≤ 3) (ha : a ≤ N) :
    (2 : ℝ) ^ N * L ^ (j * N - (a + 1) / 2) *
      (2 * (U / L) ^ N) ^ j ≤
      8 * 2 ^ N * U ^ (3 * N) * L ^ (-(a : ℝ) / 2) := by
  have hLp : 0 < L := by linarith
  have hUp : 0 < U := by linarith
  have hd : (a + 1) / 2 ≤ j * N := by
    have h1 : (a + 1) / 2 ≤ a := by omega
    have h2 : N ≤ j * N := by nlinarith
    omega
  have heq : L ^ (j * N - (a + 1) / 2) * (2 * (U / L) ^ N) ^ j =
      (2 : ℝ) ^ j * U ^ (j * N) / L ^ ((a + 1) / 2) := by
    simp only [mul_pow, div_pow, ← pow_mul]
    rw [Nat.mul_comm N j]
    apply (eq_div_iff (pow_ne_zero _ hLp.ne')).mpr
    have hp : L ^ (j * N - (a + 1) / 2) * L ^ ((a + 1) / 2) = L ^ (j * N) := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    field_simp
    nlinarith [congrArg (fun z => (2 : ℝ) ^ j * U ^ (j * N) * z) hp]
  have ht : (2 : ℝ) ^ j ≤ 8 := by
    calc
      _ ≤ (2 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hj'
      _ = _ := by norm_num
  have hu : U ^ (j * N) ≤ U ^ (3 * N) := pow_le_pow_right₀ hU (Nat.mul_le_mul_right _ hj')
  have hhalf : (a : ℝ) / 2 ≤ ((a + 1) / 2 : ℕ) := by
    have h : a ≤ 2 * ((a + 1) / 2) := by omega
    have hr : (a : ℝ) ≤ 2 * (((a + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hp : L ^ ((a : ℝ) / 2) ≤ L ^ ((a + 1) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL hhalf
  have hinv : 1 / L ^ ((a + 1) / 2) ≤ L ^ (-(a : ℝ) / 2) := by
    rw [show -(a : ℝ) / 2 = -((a : ℝ) / 2) by ring,
      Real.rpow_neg hLp.le, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLp _) hp
  calc
    _ = 2 ^ N * ((2 : ℝ) ^ j * U ^ (j * N) / L ^ ((a + 1) / 2)) := by
      rw [mul_assoc, heq]
    _ ≤ 2 ^ N * (8 * U ^ (3 * N) / L ^ ((a + 1) / 2)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (mul_le_mul ht hu (by positivity) (by norm_num)) (by positivity))
        (by positivity)
    _ ≤ 2 ^ N * (8 * U ^ (3 * N) * L ^ (-(a : ℝ) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [div_eq_mul_inv, one_div, one_mul] using
        mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 8 * U ^ (3 * N))
    _ = _ := by ring

end SmoothObstruction.FiniteLaw

end

end OAI
