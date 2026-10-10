import OAI.Dynamics.SmoothObstruction.WordParameters
import OAI.Dynamics.SmoothObstruction.WordLaw

namespace OAI

section

open Finset

namespace SmoothObstruction.ShiftComparisons
open Finset

/-- The exact first endpoint of a comparison against a length-N window in
uv. It also includes aligned different-word comparisons when t=0. -/
def first {M N : ℕ} (a b : Fin M) (t r : Fin N) : Fin M × Fin N :=
  (if r.val + t.val < N then a else b, r + t)
def second {M N : ℕ} (c : Fin M) (r : Fin N) : Fin M × Fin N := (c,r)

lemma first_injective {M N : ℕ} (a b : Fin M) (t : Fin N) :
    Function.Injective (first a b t) := by
  intro r s h
  have hh := congrArg Prod.snd h
  have hm : r.val + t.val ≡ s.val + t.val [MOD N] := congrArg Fin.val hh
  exact Fin.ext ((Nat.ModEq.add_right_cancel' t.val hm).eq_of_lt_of_lt r.isLt s.isLt)
lemma second_injective {M N : ℕ} (c : Fin M) : Function.Injective (second (N := N) c) := by
  intro r s h
  exact congrArg Prod.snd h
lemma no_loops {M N : ℕ} [NeZero N] (a b c : Fin M) (t : Fin N)
    (h : t ≠ 0 ∨ a ≠ c) (r : Fin N) : first a b t r ≠ second c r := by
  intro he
  have hs : r + t = r := congrArg Prod.snd he
  have hm : r.val + t.val ≡ r.val + (0 : Fin N).val [MOD N] :=
    congrArg Fin.val (hs.trans (Fin.add_zero r).symm)
  have ht : t = 0 := Fin.ext ((Nat.ModEq.add_left_cancel' r.val hm).eq_of_lt_of_lt t.isLt (0 : Fin N).isLt)
  rcases h with h | h
  · exact h ht
  · subst t
    have ha := congrArg Prod.fst he
    have hr : r.val < N := r.isLt
    simp only [first, second, Fin.val_zero, add_zero, ite_eq_left hr] at ha
    exact h ha

/-- Only the at-most-three sampled words actually present are charged by the
probability bound, even when some input indices coincide. -/
def used {M : ℕ} (a b c : Fin M) : Finset (Fin M) := {a,b,c}

lemma used_nonempty {M : ℕ} (a b c : Fin M) : (used a b c).Nonempty := by
  exact ⟨a, by simp [used]⟩
lemma used_card {M : ℕ} (a b c : Fin M) : (used a b c).card ≤ 3 := by
  calc
    _ ≤ ({b,c} : Finset (Fin M)).card + 1 := card_insert_le _ _
    _ ≤ ({c} : Finset (Fin M)).card + 1 + 1 := Nat.add_le_add_right (card_insert_le _ _) 1
    _ = _ := by simp

noncomputable def firstUsed {M N : ℕ} (a b c : Fin M) (t r : Fin N) :
    {j : Fin M // j ∈ used a b c} × Fin N :=
  (⟨(first a b t r).1, by
    unfold first used
    split_ifs <;> simp⟩, (first a b t r).2)
def secondUsed {M N : ℕ} (a b c : Fin M) (r : Fin N) :
    {j : Fin M // j ∈ used a b c} × Fin N :=
  (⟨c, by simp [used]⟩,r)

lemma firstUsed_injective {M N : ℕ} (a b c : Fin M) (t : Fin N) :
    Function.Injective (firstUsed a b c t) := by
  intro r s h
  exact first_injective a b t (congrArg (fun z => (z.1.val,z.2)) h)
lemma secondUsed_injective {M N : ℕ} (a b c : Fin M) :
    Function.Injective (secondUsed (N := N) a b c) := by
  intro r s h
  exact congrArg Prod.snd h
lemma no_loops_used {M N : ℕ} [NeZero N] (a b c : Fin M) (t : Fin N)
    (h : t ≠ 0 ∨ a ≠ c) (r : Fin N) : firstUsed a b c t r ≠ secondUsed a b c r := by
  intro he
  exact no_loops a b c t h r (congrArg (fun z => (z.1.val,z.2)) he)

end SmoothObstruction.ShiftComparisons

namespace SmoothObstruction.ShiftComparisons
open Finset FiniteLaw
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def matchCount {M N : ℕ} (w : Fin M → Fin N → A) (a b c : Fin M) (t : Fin N) : ℕ :=
  (univ.filter (fun r => w (first a b t r).1 (first a b t r).2 = w c r)).card

/-- Source shifted-comparison probability, including coincidences among all
three selected sample-list indices. -/
theorem bad_probability {M N : ℕ} [NeZero N] (P : Law (Fin N → A))
    (a b c : Fin M) (t : Fin N) (h : t ≠ 0 ∨ a ≠ c) (d : ℕ) (hd : d ≤ N)
    {U : ℝ} (hU : 1 ≤ U) (hA : 1 ≤ (Fintype.card A : ℝ))
    (hP : ∀ w, P.mass w ≤ 2 * (U / Fintype.card A) ^ N) :
    prob (product (fun _ : Fin M => P)) (univ.filter (fun w => d ≤ matchCount w a b c t)) ≤
      8 * 2 ^ N * U ^ (3 * N) * (Fintype.card A : ℝ) ^ (-(d : ℝ) / 2) := by
  let J := {j : Fin M // j ∈ used a b c}
  have hc : 0 ≤ 2 * (U / Fintype.card A) ^ N := by positivity
  have hp := sampled_bad_comparison (fun _ : Fin M => P) (Subtype.val : J → Fin M)
    Subtype.val_injective (firstUsed a b c t) (secondUsed a b c)
    (firstUsed_injective a b c t) (secondUsed_injective a b c)
    (no_loops_used a b c t h) d hc (fun _ => hP)
  change prob _ (univ.filter (fun w => d ≤ matchCount w a b c t)) ≤ _ at hp
  have hj : 1 ≤ Fintype.card J := by
    simpa only [J, Fintype.card_coe] using Nat.succ_le_iff.mpr (used_nonempty a b c).card_pos
  have hj' : Fintype.card J ≤ 3 := by simpa only [J, Fintype.card_coe] using used_card a b c
  simp only [Fintype.card_fin] at hp
  exact hp.trans (comparison_cost hA hU hj hj' hd)

abbrev Config (M N : ℕ) [NeZero N] :=
  {z : Fin M × Fin M × Fin M × Fin N // z.2.2.2 ≠ 0 ∨ z.1 ≠ z.2.2.1}

lemma card_config (M N : ℕ) [NeZero N] : Fintype.card (Config M N) ≤ N * M ^ 3 := by
  have h := Fintype.card_subtype_le (fun z : Fin M × Fin M × Fin M × Fin N =>
    z.2.2.2 ≠ 0 ∨ z.1 ≠ z.2.2.1)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  convert h using 1
  ring

/-- Simultaneous bound for every aligned or shifted comparison in the actual
M-word sample. The finite index set has at most N M³ members. -/
theorem all_bad_probability {M N : ℕ} [NeZero N] (P : Law (Fin N → A))
    (d : ℕ) (hd : d ≤ N) {U : ℝ} (hU : 1 ≤ U) (hA : 1 ≤ (Fintype.card A : ℝ))
    (hP : ∀ w, P.mass w ≤ 2 * (U / Fintype.card A) ^ N) :
    prob (product (fun _ : Fin M => P))
      (univ.biUnion (fun z : Config M N => univ.filter (fun w =>
        d ≤ matchCount w z.val.1 z.val.2.1 z.val.2.2.1 z.val.2.2.2))) ≤
      (N * M ^ 3 : ℝ) * (8 * 2 ^ N * U ^ (3 * N) *
        (Fintype.card A : ℝ) ^ (-(d : ℝ) / 2)) := by
  let C := 8 * (2 : ℝ) ^ N * U ^ (3 * N) * (Fintype.card A : ℝ) ^ (-(d : ℝ) / 2)
  calc
    _ ≤ ∑ z : Config M N, prob (product (fun _ : Fin M => P))
      (univ.filter (fun w => d ≤ matchCount w z.val.1 z.val.2.1 z.val.2.2.1 z.val.2.2.2)) :=
        union_bound _ _
    _ ≤ ∑ _ : Config M N, C := sum_le_sum (fun z _ =>
      bad_probability P _ _ _ _ z.property d hd hU hA hP)
    _ = Fintype.card (Config M N) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_config M N) (by dsimp [C]; positivity)

end SmoothObstruction.ShiftComparisons

namespace SmoothObstruction.WordFamily
open Finset FiniteLaw ShiftComparisons
variable {A C I : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  [Fintype I]

noncomputable def observableLaw {N : ℕ} (P : Law (Fin N → A)) (f : (Fin N → A) → C) (c : C) : ℝ :=
  expect P (fun w => if f w = c then 1 else 0)

noncomputable def empiricalTV {M N : ℕ} (P : Law (Fin N → A)) (f : (Fin N → A) → C)
    (w : Fin M → Fin N → A) : ℝ :=
  (1/2 : ℝ) * ∑ c, |(∑ i, if f (w i) = c then (1 : ℝ) else 0) / M - observableLaw P f c|

omit [DecidableEq A] in
lemma empiricalTV_nonneg {M N : ℕ} (P : Law (Fin N → A)) (f : (Fin N → A) → C)
    (w : Fin M → Fin N → A) : 0 ≤ empiricalTV P f w := by
  unfold empiricalTV; positivity

omit [DecidableEq A] in
lemma expectedTV {M N : ℕ} [NeZero M] (P : Law (Fin N → A)) (f : (Fin N → A) → C) :
    expect (product (fun _ : Fin M => P)) (empiricalTV P f) ≤
      (1/2 : ℝ) * Real.sqrt (Fintype.card C / M) := by
  unfold empiricalTV
  simpa only [Fintype.card_fin] using independent_vectors_tv
    (fun _ : Fin M => P) (fun _ w c => if f w = c then (1 : ℝ) else 0)
    (observableLaw P f) (by intros; positivity) (by intros; simp) (by intros; rfl)

lemma window_bad_probability {M N : ℕ} [NeZero M] (P : Law (Fin N → A))
    (f : I → (Fin N → A) → C) {θ : ℝ} (hθ : 0 < θ) :
    prob (product (fun _ : Fin M => P))
      (univ.biUnion (fun i => univ.filter (fun w => θ < empiricalTV P (f i) w))) ≤
        Fintype.card I * ((1/2 : ℝ) * Real.sqrt (Fintype.card C / M)) / θ := by
  classical
  calc
    _ ≤ ∑ i, prob (product (fun _ : Fin M => P))
      (univ.filter (fun w => θ < empiricalTV P (f i) w)) := union_bound _ _
    _ ≤ ∑ _ : I, ((1/2 : ℝ) * Real.sqrt (Fintype.card C / M)) / θ :=
      sum_le_sum (fun i _ => (markov _ _ (empiricalTV_nonneg P (f i)) hθ).trans
        (div_le_div_of_nonneg_right (expectedTV P (f i)) hθ.le))
    _ = _ := by simp [mul_div_assoc]

omit [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq A] in
lemma product_support {M N : ℕ} (P : Law (Fin N → A))
    {w : Fin M → Fin N → A} (hw : 0 < (product (fun _ : Fin M => P)).mass w) (i : Fin M) :
    0 < P.mass (w i) := by
  have hn : P.mass (w i) ≠ 0 := by
    intro hz
    have hp : (∏ j, P.mass (w j)) = 0 := prod_eq_zero (mem_univ i) hz
    exact (ne_of_gt hw) hp
  exact lt_of_le_of_ne (P.nonneg (w i)) hn.symm

omit [Fintype C] [DecidableEq C] [Fintype I] [Fintype A] in
lemma injective_of_separation {M N d : ℕ} [NeZero N] {w : Fin M → Fin N → A} (hd : d ≤ N)
    (hsep : ∀ a b c : Fin M, ∀ t : Fin N, t ≠ 0 ∨ a ≠ c → matchCount w a b c t < d) :
    Function.Injective w := by
  intro a c he
  by_contra hac
  have hb := hsep a a c 0 (Or.inr hac)
  have hmc : matchCount w a a c 0 = N := by
    unfold matchCount
    have hall (r : Fin N) : w (first a a 0 r).1 (first a a 0 r).2 = w c r := by
      simp [first, he]
    simp [hall]
  omega

/-- Actual simultaneous family selection. The two bad events are evaluated
in one product law and support is preserved for each complete list. -/
theorem exists_family {M N d : ℕ} [NeZero M] [NeZero N]
    (P : Law (Fin N → A)) (f : I → (Fin N → A) → C)
    {U θ : ℝ} (hU : 1 ≤ U) (hA : 1 ≤ (Fintype.card A : ℝ)) (hθ : 0 < θ)
    (hd : d ≤ N) (hP : ∀ w, P.mass w ≤ 2 * (U / Fintype.card A) ^ N)
    (hwindow : Fintype.card I * ((1/2 : ℝ) * Real.sqrt (Fintype.card C / M)) / θ < 1/4)
    (hdistance : (N * M ^ 3 : ℝ) * (8 * 2 ^ N * U ^ (3 * N) *
      (Fintype.card A : ℝ) ^ (-(d : ℝ) / 2)) < 1/4) :
    ∃ w : Fin M → Fin N → A, Function.Injective w ∧
      (∀ i, 0 < P.mass (w i)) ∧
      (∀ i, empiricalTV P (f i) w ≤ θ) ∧
      ∀ a b c : Fin M, ∀ t : Fin N, t ≠ 0 ∨ a ≠ c → matchCount w a b c t < d := by
  classical
  let E₀ := univ.biUnion (fun i => univ.filter (fun w : Fin M → Fin N → A => θ < empiricalTV P (f i) w))
  let E₁ := univ.biUnion (fun z : Config M N => univ.filter (fun w : Fin M → Fin N → A =>
    d ≤ matchCount w z.val.1 z.val.2.1 z.val.2.2.1 z.val.2.2.2))
  let E : Bool → Finset (Fin M → Fin N → A) := fun b => if b then E₁ else E₀
  have he₀ : prob (product (fun _ : Fin M => P)) E₀ < 1/4 :=
    (window_bad_probability P f hθ).trans_lt hwindow
  have he₁ : prob (product (fun _ : Fin M => P)) E₁ < 1/4 :=
    (all_bad_probability P d hd hU hA hP).trans_lt hdistance
  have hsum : (∑ b, prob (product (fun _ : Fin M => P)) (E b)) < 1 := by
    simp only [E, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    linarith
  obtain ⟨w,hw,havoid⟩ := exists_good (product (fun _ : Fin M => P)) E hsum
  have hw₀ : w ∉ E₀ := havoid false
  have hw₁ : w ∉ E₁ := havoid true
  have hsep : ∀ a b c : Fin M, ∀ t : Fin N, t ≠ 0 ∨ a ≠ c → matchCount w a b c t < d := by
    intro a b c t h
    by_contra hn
    exact hw₁ (mem_biUnion.mpr ⟨⟨(a,b,c,t),h⟩,mem_univ _,mem_filter.mpr ⟨mem_univ _,show d ≤ matchCount w a b c t from by omega⟩⟩)
  refine ⟨w,injective_of_separation hd hsep,product_support P hw,?_,hsep⟩
  intro i
  by_contra hn
  exact hw₀ (mem_biUnion.mpr ⟨i,mem_univ i,mem_filter.mpr ⟨mem_univ _,by linarith⟩⟩)

end SmoothObstruction.WordFamily

namespace SmoothObstruction.FiniteLaw
open Finset
variable {A B : Type*} [Fintype A] [Fintype B]
noncomputable def transport (e : A ≃ B) (P : Law A) : Law B where
  mass b := P.mass (e.symm b)
  nonneg b := P.nonneg (e.symm b)
  total := (e.symm.sum_comp P.mass).trans P.total

lemma expect_transport (e : A ≃ B) (P : Law A) (f : B → ℝ) :
    expect (transport e P) f = expect P (f ∘ e) := by
  unfold expect transport
  exact Fintype.sum_equiv e.symm _ _ (fun b => by simp)
end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.WordFlatten
open Finset FiniteLaw WordLaw SequentialLaw
variable {A : Type*} {q H : ℕ}

def flattenEquiv : (Fin q → Fin H → A) ≃ (Fin (q*H) → A) where
  toFun w i := w (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  invFun w b r := w (finProdFinEquiv (b,r))
  left_inv w := by funext b r; simp
  right_inv w := by
    funext i
    change w (finProdFinEquiv (finProdFinEquiv.symm i)) = w i
    rw [Equiv.apply_symm_apply]

lemma full_test [Fintype A] [DecidableEq A] (v w : Fin q → Fin H → A) :
    (∏ b, test (fun r => some (v b r)) (w b)) = if w = v then 1 else 0 := by
  classical
  have ht (b : Fin q) : test (fun r => some (v b r)) (w b) =
      if w b = v b then 1 else 0 := by
    rw [test_eq_indicator]
    congr 1
    simp only [Option.some.injEq, funext_iff]
    apply propext
    constructor
    · intro h i
      exact h i _ rfl
    · intro h i a ha
      exact (h i).trans ha
  simp only [ht, Finset.prod_boole, mem_univ, forall_const, ← funext_iff]

lemma expect_full_test [Fintype A] [DecidableEq A] (P : Law (Fin q → Fin H → A))
    (v : Fin q → Fin H → A) :
    expect P (fun w => ∏ b, test (fun r => some (v b r)) (w b)) = P.mass v := by
  classical
  simp [full_test, FiniteLaw.expect, mul_ite]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Fintype V] [DecidableEq V] (B : LinearMap.BilinForm (ZMod 2) V) {K : ℕ}

/-- Pointwise mass of the true constrained and once-conditioned complete
list. This is derived from the arbitrary sublist estimate, not independence
of constituent positions. -/
lemma conditioned_mass (hd : K+1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E) (v : Fin q → Fin H → {v : V // v ≠ 0}) :
    (condition (rawLaw B hd H q) E (by change 0 < prob _ E; linarith)).mass v ≤
      2 * ((2 : ℝ) ^ (2*K) / Fintype.card {v : V // v ≠ 0}) ^ (q*H) := by
  have h := conditioned_sublist B hd hK E hE (fun b r => some (v b r))
  rw [expect_full_test] at h
  simpa using h

noncomputable def flatLaw (hd : K+1 ≤ Module.finrank (ZMod 2) V)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E) : Law (Fin (q*H) → {v : V // v ≠ 0}) :=
  transport flattenEquiv (condition (rawLaw B hd H q) E (by change 0 < prob _ E; linarith))

lemma flat_mass (hd : K+1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E) (v : Fin (q*H) → {v : V // v ≠ 0}) :
    (flatLaw B hd E hE).mass v ≤
      2 * ((2 : ℝ) ^ (2*K) / Fintype.card {v : V // v ≠ 0}) ^ (q*H) :=
  conditioned_mass B hd hK E hE _

lemma flat_support (hd : K+1 ≤ Module.finrank (ZMod 2) V)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E) {v : Fin (q*H) → {v : V // v ≠ 0}}
    (hv : 0 < (flatLaw B hd E hE).mass v) :
    flattenEquiv.symm v ∈ E ∧ 0 < (rawLaw B hd H q).mass (flattenEquiv.symm v) := by
  exact condition_supported (rawLaw B hd H q) E (by linarith) hv

lemma flat_relations (hd : K+1 ≤ Module.finrank (ZMod 2) V)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E) {v : Fin (q*H) → {v : V // v ≠ 0}}
    (hv : 0 < (flatLaw B hd E hE).mass v) (b : Fin q)
    {r k : ℕ} (hk : k < K) (hk8 : k ≤ K/8) (hrt : r+2^k < H) :
    B (v (finProdFinEquiv (b,⟨r,lt_trans (Nat.lt_add_of_pos_right (by positivity)) hrt⟩))).val
      (v (finProdFinEquiv (b,⟨r+2^k,hrt⟩))).val = 0 :=
  raw_relations B hd (flat_support B hd E hE hv).2 b hk hk8 hrt

/-- Complete supported family selection for the actual grouped symplectic
sampler. Caller-specified observables encode the short windows, while E is
the proved per-word approximation event. -/
theorem exists_family {M d : ℕ} [NeZero M] [NeZero (q*H)]
    {C I : Type*} [Fintype C] [DecidableEq C] [Fintype I]
    (hd : K+1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (hA : 1 ≤ (Fintype.card {v : V // v ≠ 0} : ℝ))
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E)
    (f : I → (Fin (q*H) → {v : V // v ≠ 0}) → C)
    {θ : ℝ} (hθ : 0 < θ) (hmatch : d ≤ q*H)
    (hwindow : Fintype.card I * ((1/2 : ℝ) * Real.sqrt (Fintype.card C / M)) / θ < 1/4)
    (hdistance : ((q*H) * M^3 : ℝ) * (8 * 2^(q*H) * ((2 : ℝ)^(2*K))^(3*(q*H)) *
      (Fintype.card {v : V // v ≠ 0} : ℝ)^(-(d : ℝ)/2)) < 1/4) :
    ∃ w : Fin M → Fin (q*H) → {v : V // v ≠ 0}, Function.Injective w ∧
      (∀ i, flattenEquiv.symm (w i) ∈ E) ∧
      (∀ i b (r k : ℕ) (_hk : k<K) (_hk8 : k ≤ K/8) (hr : r+2^k<H),
        B (w i (finProdFinEquiv (b,⟨r,lt_trans (Nat.lt_add_of_pos_right (by positivity)) hr⟩))).val
          (w i (finProdFinEquiv (b,⟨r+2^k,hr⟩))).val = 0) ∧
      (∀ i, WordFamily.empiricalTV (flatLaw B hd E hE) (f i) w ≤ θ) ∧
      ∀ a b c : Fin M, ∀ t : Fin (q*H), t≠0 ∨ a≠c → ShiftComparisons.matchCount w a b c t < d := by
  obtain ⟨w,hinj,hsupp,htv,hsep⟩ := WordFamily.exists_family
    (flatLaw B hd E hE) f (by exact one_le_pow₀ (by norm_num)) hA hθ hmatch
    (flat_mass B hd hK E hE) hwindow (by simpa only [Nat.cast_mul] using hdistance)
  exact ⟨w,hinj,fun i => (flat_support B hd E hE (hsupp i)).1,
    fun i b _ _ hk hk8 hr => flat_relations B hd E hE (hsupp i) b hk hk8 hr,htv,hsep⟩
end SmoothObstruction.WordFlatten

end

section

namespace SmoothObstruction.WordStep
open WordParameters WordAlphabet FiniteLaw WordLaw
open scoped BigOperators

instance alphabetFintype (s : ℕ) : Fintype (Alphabet s) := inferInstance
instance alphabetDecidableEq (s : ℕ) : DecidableEq (Alphabet s) := inferInstance

noncomputable def N (s : ℕ) := 2 ^ K s
noncomputable def H (s : ℕ) := 2 ^ (K s / 2)
noncomputable def q (s : ℕ) := 2 ^ (K s - K s / 2)
noncomputable def D (s : ℕ) := 2 ^ (K s / 8)
lemma q_mul_H (s : ℕ) : q s * H s = N s := by
  simp only [q,H,N,←pow_add,Nat.sub_add_cancel (Nat.div_le_self (K s) 2)]
lemma N_pos (s : ℕ) : 0 < N s := by unfold N; positivity
lemma H_pos (s : ℕ) : 0 < H s := by unfold H; positivity
lemma q_pos (s : ℕ) : 0 < q s := by unfold q; positivity
instance qH_neZero (s : ℕ) : NeZero (q s*H s) := ⟨(mul_pos (q_pos s) (H_pos s)).ne'⟩
lemma D_le_N (s : ℕ) : D s ≤ N s :=
  Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
lemma cardAlphabetReal (s : ℕ) : (Fintype.card (Alphabet s) : ℝ) = alphabetSize s := by
  rw [card_alphabet,Nat.cast_sub (Nat.one_le_two_pow),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  rfl
lemma epsilon_le_one (i : ℕ) : epsilon i ≤ 1 := by
  unfold epsilon
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

noncomputable def matchThreshold (i s : ℕ) := ⌈epsilon i * N s⌉₊
lemma matchThreshold_le (i s : ℕ) : matchThreshold i s ≤ N s := by
  apply Nat.ceil_le.mpr
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (epsilon_le_one i) (Nat.cast_nonneg (N s))
lemma le_matchThreshold (i s : ℕ) : epsilon i * N s ≤ matchThreshold i s := Nat.le_ceil _

/-- Actual offset set for nonwrapping source D-windows. -/
abbrev Offsets (s : ℕ) := {t : Fin (q s * H s) // t.val+D s ≤ q s*H s}
def window (s : ℕ) (t : Offsets s) (w : Fin (q s*H s) → Alphabet s) : Fin (D s) → Alphabet s :=
  fun r => w ⟨t.val.val + r.val,lt_of_lt_of_le (Nat.add_lt_add_left r.isLt _) t.property⟩
lemma card_offsets (s : ℕ) : Fintype.card (Offsets s) ≤ N s := by
  exact (Fintype.card_subtype_le _).trans_eq (by simp [q_mul_H])

lemma window_budget {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    (Fintype.card (Offsets s) : ℝ) * ((1/2:ℝ) * Real.sqrt
      (Fintype.card (Fin (D s) → Alphabet s) / Fintype.card (Alphabet (nextS i s)))) / (1/10000) < 1/4 := by
  have hc : (Fintype.card (Offsets s) : ℝ) ≤ (N s : ℝ) := by exact_mod_cast card_offsets s
  have hcard : (Fintype.card (Fin (D s) → Alphabet s) : ℝ) = alphabetSize s ^ D s := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,cardAlphabetReal]
  rw [hcard,cardAlphabetReal]
  have hsqrt : 0 ≤ Real.sqrt (alphabetSize s ^ D s / alphabetSize (nextS i s)) := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hc hsqrt
  have hn : (N s : ℝ) = (2 : ℝ)^K s := by simp only [N,Nat.cast_pow,Nat.cast_ofNat]
  have hbound := (actual_budgets hk hε).2.1
  unfold windowBudget at hbound
  rw [←hn] at hbound
  change _ < (1/4:ℝ)
  dsimp [D] at *
  nlinarith

lemma distance_budget {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    ((q s*H s) * (Fintype.card (Alphabet (nextS i s)))^3 : ℝ) *
      (8 * 2^(q s*H s) * ((2:ℝ)^(2*K s))^(3*(q s*H s)) *
        (Fintype.card (Alphabet s) : ℝ)^(-(matchThreshold i s : ℝ)/2)) < 1/4 := by
  have hs : 1 ≤ s := s_pos_of_Kpos (by omega)
  have ht : 1 ≤ nextS i s := s_pos_of_Kpos (by have := one_step_growth hk hε; omega)
  have hA : 1 ≤ alphabetSize s := by
    have hp : (2 : ℝ)^(2:ℕ) ≤ (2:ℝ)^(2*s) := pow_le_pow_right₀ (by norm_num) (by omega)
    unfold alphabetSize
    norm_num at hp
    linarith
  have hexp : -(matchThreshold i s : ℝ)/2 ≤ -epsilon i * N s/2 := by
    have := le_matchThreshold i s
    linarith
  have hr := Real.rpow_le_rpow_of_exponent_le hA hexp
  have hpow : (2 : ℝ)^(N s) * ((2:ℝ)^(2*K s))^(3*N s) =
      (2:ℝ)^((6*K s+1)*N s) := by
    rw [←pow_mul,←pow_add]
    congr 1
    ring
  rw [q_mul_H,cardAlphabetReal,cardAlphabetReal,←Nat.cast_mul,q_mul_H]
  have hm : 0 ≤ (N s : ℝ) * alphabetSize (nextS i s)^3 :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (alphabetSize_pos ht).le _)
  have hm' : 0 ≤ 8*(2:ℝ)^((6*K s+1)*N s) := by positivity
  have hle := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hm') hm
  have hn : (N s : ℝ) = (2:ℝ)^K s := by simp only [N,Nat.cast_pow,Nat.cast_ofNat]
  have hbound := (actual_budgets hk hε).2.2
  unfold distanceBudget at hbound
  rw [←hn] at hbound
  have heq : 8*(2:ℝ)^N s*((2:ℝ)^(2*K s))^(3*N s) = 8*(2:ℝ)^((6*K s+1)*N s) := by
    rw [mul_assoc,hpow]
  rw [heq]
  change _ < (1/4:ℝ)
  dsimp only [N] at *
  have hnn := mul_nonneg hm (mul_nonneg hm'
    (Real.rpow_nonneg (by positivity : 0 ≤ alphabetSize s) (-epsilon i * (N s : ℝ)/2)))
  nlinarith

lemma alphabetSize_ge_one {s : ℕ} (hs : 1 ≤ s) : 1 ≤ alphabetSize s := by
  have hp : (2:ℝ)^(2:ℕ) ≤ (2:ℝ)^(2*s) := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold alphabetSize
  norm_num at hp
  linarith

/-- One actual finite-family selection at the exact source parameters.
No distance, injectivity, window law or symplectic relation is an assumption;
they are all supplied by the independent sample argument and checked budgets.
The single per-word conditioning event is passed with its proved mass bound. -/
theorem exists_step {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s)
    (E : Finset (Fin (q s) → Fin (H s) → Alphabet s))
    (hE : 1/2 ≤ prob (rawLaw (form s) (by rw [finrank]; exact dimension_budget hk) (H s) (q s)) E) :
    ∃ w : Fin (Fintype.card (Alphabet (nextS i s))) → Fin (q s*H s) → Alphabet s,
      Function.Injective w ∧
      (∀ a, WordFlatten.flattenEquiv.symm (w a) ∈ E) ∧
      (∀ a b (r k : ℕ) (_hk : k<K s) (_hk8 : k ≤ K s/8) (hr : r+2^k<H s),
        form s (w a (finProdFinEquiv (b,⟨r,lt_trans (Nat.lt_add_of_pos_right (by positivity)) hr⟩))).val
          (w a (finProdFinEquiv (b,⟨r+2^k,hr⟩))).val = 0) ∧
      (∀ t, WordFamily.empiricalTV
        (WordFlatten.flatLaw (form s) (by rw [finrank]; exact dimension_budget hk) E hE)
        (window s t) w ≤ 1/10000) ∧
      ∀ a b c, ∀ t : Fin (q s*H s), t≠0 ∨ a≠c →
        ShiftComparisons.matchCount w a b c t < matchThreshold i s := by
  have hnext : 1 ≤ nextS i s := s_pos_of_Kpos (by have := one_step_growth hk hε; omega)
  have hcard : 0 < Fintype.card (Alphabet (nextS i s)) := by
    have hh : (0:ℝ) < Fintype.card (Alphabet (nextS i s)) := by
      rw [cardAlphabetReal]; exact alphabetSize_pos hnext
    exact_mod_cast hh
  let : NeZero (Fintype.card (Alphabet (nextS i s))) := ⟨hcard.ne'⟩
  let : NeZero (q s*H s) := ⟨(mul_pos (q_pos s) (H_pos s)).ne'⟩
  apply WordFlatten.exists_family (form s)
    (by rw [finrank]; exact dimension_budget hk) (by omega)
    (by rw [cardAlphabetReal]; exact alphabetSize_ge_one (s_pos_of_Kpos (by omega)))
    E hE (window s) (by norm_num)
    (by rw [q_mul_H]; exact matchThreshold_le i s)
    (window_budget hk hε) (distance_budget hk hε)

/-- At successive exact source levels the per-word approximation event
has probability at least a half, for every actual previous-window map. -/
theorem approximation_mass {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s)
    (f : Offsets s → Alphabet (nextS i s) → (Fin (D s) → Alphabet s)) :
    1/2 ≤ prob (rawLaw (form (nextS i s))
      (by rw [finrank]; exact dimension_budget (by have := one_step_growth hk hε; omega))
      (H (nextS i s)) (q (nextS i s)))
      (Finset.univ.filter (fun w => ∀ t, tvFromUniformObservable (f t) w ≤ 1/10000)) := by
  apply approximation_event _ (form_alt _) (form_nondegenerate _) _
    (H_pos _) (q_pos _) f (by norm_num)
  have hc : (Fintype.card (Offsets s) : ℝ) ≤ (N s : ℝ) := by exact_mod_cast card_offsets s
  have hcard : (Fintype.card (Fin (D s) → Alphabet s) : ℝ) = alphabetSize s ^ D s := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,cardAlphabetReal]
  rw [hcard]
  have hmul := mul_le_mul_of_nonneg_right hc
    (Real.sqrt_nonneg (alphabetSize s ^ D s / q (nextS i s)))
  have hbound := (actual_budgets hk hε).1
  unfold filterBudget at hbound
  simp only [N,q,D,Nat.cast_pow,Nat.cast_ofNat] at *
  nlinarith
end SmoothObstruction.WordStep

end

end OAI
