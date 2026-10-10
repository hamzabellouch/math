import OAI.Dynamics.SmoothObstruction.WordHierarchy

namespace OAI

section

namespace SmoothObstruction.WordFlatten
open Finset FiniteLaw WordLaw SequentialLaw
variable {A : Type*} [Fintype A] [DecidableEq A] {q H : ℕ}

omit [Fintype A] in
lemma test_flatten (m : Fin (q*H) → Option A) (w : Fin q → Fin H → A) :
    test m (flattenEquiv w) = ∏ b, test (fun r => m (finProdFinEquiv (b,r))) (w b) := by
  unfold test
  calc
    _ = ∏ br : Fin q × Fin H, mark (m (finProdFinEquiv br)) (w br.1 br.2) := by
      simpa only [flattenEquiv, Equiv.coe_fn_mk,Equiv.symm_apply_apply] using
        (finProdFinEquiv.prod_comp (fun j => mark (m j) (flattenEquiv w j))).symm
    _ = _ := Fintype.prod_prod_type _

omit [Fintype A] [DecidableEq A] in
lemma count_grouped (m : Fin (q*H) → Option A) :
    (∑ b : Fin q, (univ.filter (fun r : Fin H => (m (finProdFinEquiv (b,r))).isSome)).card) =
      (univ.filter (fun r => (m r).isSome)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  calc
    _ = ∑ br : Fin q × Fin H, if (m (finProdFinEquiv br)).isSome then 1 else 0 :=
      (Fintype.sum_prod_type (fun br : Fin q × Fin H =>
        if (m (finProdFinEquiv br)).isSome then (1:ℕ) else 0)).symm
    _ = _ := finProdFinEquiv.sum_comp (fun r => if (m r).isSome then 1 else 0)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Fintype V] [DecidableEq V] (B : LinearMap.BilinForm (ZMod 2) V) {K : ℕ}

omit [FiniteDimensional (ZMod 2) V] in
/-- W3 itself: the actual single conditioned law controls every arbitrary
partial list, with a single factor two, including lists crossing groups. -/
theorem flat_sublist (hd : K+1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E)
    (m : Fin (q*H) → Option {v : V // v ≠ 0}) :
    expect (flatLaw B hd E hE) (test m) ≤
      2 * ((2 : ℝ)^(2*K) / Fintype.card {v : V // v ≠ 0}) ^
        (univ.filter (fun r => (m r).isSome)).card := by
  unfold flatLaw
  rw [expect_transport]
  have ht : ((test m) ∘ flattenEquiv) =
      (fun w => ∏ b, test (fun r => m (finProdFinEquiv (b,r))) (w b)) := by
    funext w
    exact test_flatten m w
  rw [ht]
  have hh := conditioned_sublist B hd hK E hE (fun b r => m (finProdFinEquiv (b,r)))
  simpa only [count_grouped] using hh
end SmoothObstruction.WordFlatten

namespace SmoothObstruction.FiniteLaw
open Finset FiniteEntropy
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def uniform [Nonempty α] : Law α where
  mass := fun _ => (Fintype.card α : ℝ)⁻¹
  nonneg := fun _ => by positivity
  total := by simp [Fintype.card_ne_zero]

noncomputable def mixture (P : Law α) (Q : α → Law β) : Law β where
  mass b := ∑ a,P.mass a*(Q a).mass b
  nonneg b := sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) ((Q a).nonneg b))
  total := by
    rw [sum_comm]
    simp only [←mul_sum,(Q _).total,mul_one,P.total]

noncomputable def TV (P Q : Law α) : ℝ := (1/2:ℝ)*∑ a,|P.mass a-Q.mass a|
noncomputable def entropy (P : Law α) : ℝ := natEntropy P.mass

lemma TV_nonneg (P Q : Law α) : 0 ≤ TV P Q := by unfold TV; positivity
lemma TV_symm (P Q : Law α) : TV P Q=TV Q P := by simp only [TV,abs_sub_comm]
lemma TV_triangle (P Q R : Law α) : TV P R ≤ TV P Q+TV Q R := by
  unfold TV
  rw [←mul_add,←sum_add_distrib]
  exact mul_le_mul_of_nonneg_left (sum_le_sum (fun a _ => abs_sub_le (P.mass a) (Q.mass a) (R.mass a))) (by norm_num)

lemma push_sub [DecidableEq β] (P Q : Law α) (f : α → β) (b : β) :
    (push P f).mass b-(push Q f).mass b = ∑ a,if f a=b then P.mass a-Q.mass a else 0 := by
  classical
  simp only [push,←sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  split_ifs <;> ring

lemma TV_push [DecidableEq β] (P Q : Law α) (f : α → β) : TV (push P f) (push Q f) ≤ TV P Q := by
  classical
  unfold TV
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simp_rw [push_sub]
  calc
    _ ≤ ∑ b,∑ a,|if f a=b then P.mass a-Q.mass a else 0| := sum_le_sum (fun b _ => abs_sum_le_sum_abs _ _)
    _ = ∑ a,|P.mass a-Q.mass a| := by
      rw [sum_comm]
      simp only [apply_ite abs,abs_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma entropy_nonneg (P : Law α) : 0 ≤ entropy P := FiniteEntropy.entropy_nonneg P.nonneg P.total
lemma entropy_mixture (P : Law α) (Q : α → Law β) :
    ∑ a,P.mass a*entropy (Q a) ≤ entropy (mixture P Q) :=
  FiniteEntropy.entropy_mixture P.mass (fun a => (Q a).mass) P.nonneg P.total (fun a => (Q a).nonneg)

lemma entropy_atom_lower (P : Law α) {M : ℝ} (_hM : 0 < M) (h : ∀ a,P.mass a ≤ M) :
    -Real.log M ≤ entropy P := by
  have hb (a : α) : P.mass a*(-Real.log M) ≤ Real.negMulLog (P.mass a) := by
    rcases (P.nonneg a).eq_or_lt with hz|hp
    · rw [←hz,zero_mul,Real.negMulLog_zero]
    · have hh := Real.log_le_log hp (h a)
      rw [Real.negMulLog_def]
      nlinarith [mul_le_mul_of_nonneg_left hh hp.le]
  have hs := sum_le_sum (fun a (_ha : a ∈ (univ : Finset α)) => hb a)
  simpa only [←sum_mul,P.total,one_mul,entropy,natEntropy] using hs

/-- Exactly the one-bit TV cost used in source equation (tv-entropy),
expressed first in natural units. -/
lemma entropy_tv_lower (P Q : Law α) {s : ℝ} (hs : TV P Q ≤ s) :
    entropy P-Real.log 2-s*Real.log (Fintype.card α) ≤ entropy Q := by
  have hcard : 1 ≤ Fintype.card α := by
    by_contra h
    have he : IsEmpty α := Fintype.card_eq_zero_iff.mp (by omega)
    have hh := P.total
    simp only [univ_eq_empty,sum_empty] at hh
    norm_num at hh
  have hc : 0 ≤ Real.log (Fintype.card α) := Real.log_nonneg (by exact_mod_cast hcard)
  have hh := FiniteEntropy.entropy_tv Q.nonneg P.nonneg Q.total P.total
  rw [←TV,TV_symm] at hh
  change entropy P ≤ entropy Q+Real.log 2+TV P Q*Real.log (Fintype.card α) at hh
  nlinarith [mul_le_mul_of_nonneg_right hs hc]

lemma entropy_close_atom_lower (P Q : Law α) {M s : ℝ} (hM : 0 < M)
    (hP : ∀ a,P.mass a ≤ M) (hs : TV P Q ≤ s) :
    -Real.log M-Real.log 2-s*Real.log (Fintype.card α) ≤ entropy Q := by
  have ha := entropy_atom_lower P hM hP
  have hb := entropy_tv_lower P Q hs
  linarith

/-- Mixtures over arbitrary parent laws retain each admissible-slot bound;
only the total exceptional-slot mass is lost. -/
theorem entropy_good_mixture (P : Law α) (Q : α → Law β) (E : Finset α)
    {L : ℝ} (h : ∀ a ∈ E,L ≤ entropy (Q a)) :
    (∑ a ∈ E,P.mass a)*L ≤ entropy (mixture P Q) := by
  classical
  calc
    _ = ∑ a ∈ E,P.mass a*L := sum_mul _ _ _
    _ ≤ ∑ a ∈ E,P.mass a*entropy (Q a) := sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (h a ha) (P.nonneg a))
    _ ≤ ∑ a,P.mass a*entropy (Q a) := sum_le_sum_of_subset_of_nonneg (subset_univ E)
      (fun a _ _ => mul_nonneg (P.nonneg a) (entropy_nonneg (Q a)))
    _ ≤ _ := entropy_mixture P Q
end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.SequentialLaw
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A] {q N : ℕ}

noncomputable def embeddedMarks (e : Fin q ↪ Fin N) (v : Fin q → A) : Fin N → Option A :=
  fun i => if h : ∃ j, e j=i then some (v h.choose) else none

omit [Fintype A] [DecidableEq A] in
lemma embeddedMarks_at (e : Fin q ↪ Fin N) (v : Fin q → A) (j : Fin q) :
    embeddedMarks e v (e j)=some (v j) := by
  classical
  have h : ∃ k, e k=e j := ⟨j,rfl⟩
  have hc := e.injective h.choose_spec
  simp only [embeddedMarks,dite_eq_left h,hc]

omit [Fintype A] [DecidableEq A] in
lemma embeddedMarks_some (e : Fin q ↪ Fin N) (v : Fin q → A) (i : Fin N) (a : A) :
    embeddedMarks e v i=some a ↔ ∃ j,e j=i ∧ v j=a := by
  classical
  constructor
  · intro h
    unfold embeddedMarks at h
    split_ifs at h with hi
    · exact ⟨hi.choose,hi.choose_spec,Option.some.inj h⟩
  · rintro ⟨j,rfl,rfl⟩
    exact embeddedMarks_at e v j

omit [Fintype A] [DecidableEq A] in
lemma embeddedMarks_count (e : Fin q ↪ Fin N) (v : Fin q → A) :
    (univ.filter (fun i => (embeddedMarks e v i).isSome)).card=q := by
  classical
  have he : univ.filter (fun i => (embeddedMarks e v i).isSome)=univ.map e := by
    ext i
    simp only [mem_filter,mem_univ,true_and,mem_map]
    constructor
    · intro hi
      cases hm : embeddedMarks e v i with
      | none => simp [hm] at hi
      | some a =>
        obtain ⟨j,hj,_⟩ := (embeddedMarks_some e v i a).mp hm
        exact ⟨j,hj⟩
    · rintro ⟨j,rfl⟩
      simp only [embeddedMarks_at,Option.isSome_some]
  rw [he,card_map,card_univ,Fintype.card_fin]

lemma embeddedMarks_test (e : Fin q ↪ Fin N) (v : Fin q → A) (w : Fin N → A) :
    test (embeddedMarks e v) w=if w ∘ e=v then 1 else 0 := by
  classical
  rw [test_eq_indicator]
  congr 1
  apply propext
  constructor
  · intro h
    funext j
    exact h (e j) (v j) (embeddedMarks_at e v j)
  · intro h i a hm
    obtain ⟨j,rfl,hj⟩ := (embeddedMarks_some e v i a).mp hm
    exact (congrFun h j).trans hj
end SmoothObstruction.SequentialLaw

namespace SmoothObstruction.WordFlatten
open Finset FiniteLaw WordLaw SequentialLaw
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Fintype V] [DecidableEq V] (B : LinearMap.BilinForm (ZMod 2) V) {K b H q : ℕ}

omit [FiniteDimensional (ZMod 2) V] in
/-- The pushed law of any distinct coordinate list has the exact W3 atom
bound; the law is the recursively used single conditioned sampler. -/
theorem flat_window_atom (hd : K+1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (E : Finset (Fin b → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H b) E)
    (e : Fin q ↪ Fin (b*H)) (v : Fin q → {v : V // v ≠ 0}) :
    (push (flatLaw B hd E hE) (fun w => w ∘ e)).mass v ≤
      2*((2:ℝ)^(2*K)/Fintype.card {v : V // v ≠ 0})^q := by
  have hh := flat_sublist B hd hK E hE (embeddedMarks e v)
  rw [embeddedMarks_count] at hh
  simp only [FiniteLaw.expect,embeddedMarks_test] at hh
  simpa only [push,FiniteLaw.expect,mul_ite,mul_one,mul_zero] using hh
end SmoothObstruction.WordFlatten

namespace SmoothObstruction.FiniteLaw
open Finset
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

lemma mass_ext (P Q : Law A) (h : P.mass=Q.mass) : P=Q := by
  cases P; cases Q; cases h; rfl

lemma push_comp [DecidableEq B] [DecidableEq C] (P : Law A) (f : A → B) (g : B → C) :
    push (push P f) g=push P (g ∘ f) := by
  apply mass_ext
  funext c
  simp only [push]
  calc
    _ = ∑ b,∑ a,if g b=c then (if f a=b then P.mass a else 0) else 0 := by
      apply sum_congr rfl
      intro b _
      split_ifs <;> simp
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      have he (b : B) : (if g b=c then (if f a=b then P.mass a else 0) else 0) =
          if f a=b then (if g b=c then P.mass a else 0) else 0 := by split_ifs <;> rfl
      simp only [he,Finset.sum_ite_eq,mem_univ,ite_true,Function.comp_apply]

lemma push_uniform_mass [Nonempty A] [DecidableEq B] (f : A → B) (b : B) :
    (push uniform f).mass b=(∑ a,if f a=b then (1:ℝ) else 0)/Fintype.card A := by
  simp only [push,uniform,div_eq_mul_inv,sum_mul,ite_mul,one_mul,zero_mul]

lemma uniform_reindex [Nonempty A] [Nonempty B] [DecidableEq C] (e : A ≃ B) (f : B → C) :
    push (uniform (α:=A)) (f ∘ e)=push (uniform (α:=B)) f := by
  apply mass_ext
  funext c
  rw [push_uniform_mass,push_uniform_mass,Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun b => if f b=c then (1:ℝ) else 0)

lemma push_observable {N : ℕ} [DecidableEq C] (P : Law (Fin N → A))
    (f : (Fin N → A) → C) (c : C) :
    (push P f).mass c=WordFamily.observableLaw P f c := by
  simp only [push,WordFamily.observableLaw,expect,mul_ite,mul_one,mul_zero]

lemma TV_empirical {M N : ℕ} [NeZero M] [DecidableEq C]
    (P : Law (Fin N → A)) (f : (Fin N → A) → C) (w : Fin M → Fin N → A) :
    TV (push uniform (f ∘ w)) (push P f)=WordFamily.empiricalTV P f w := by
  simp only [TV,push_uniform_mass,Fintype.card_fin,push_observable,
    WordFamily.empiricalTV,Function.comp_apply]

lemma TV_grouped {q H : ℕ} [NeZero q] [NeZero H] [Nonempty A] [DecidableEq C]
    (f : A → C) (w : Fin q → Fin H → A) :
    TV (push uniform (f ∘ WordFlatten.flattenEquiv w)) (push uniform f) =
      (1/2:ℝ)*∑ c, |(∑ b,(∑ r,if f (w b r)=c then (1:ℝ) else 0)/(H:ℝ))/(q:ℝ)-
        (∑ a,if f a=c then (1:ℝ) else 0)/Fintype.card A| := by
  unfold TV
  congr 1
  apply sum_congr rfl
  intro c _
  rw [push_uniform_mass,push_uniform_mass,Fintype.card_fin]
  congr 2
  have he : (∑ j : Fin (q*H),if (f ∘ WordFlatten.flattenEquiv w) j=c then (1:ℝ) else 0) =
      ∑ b,∑ r,if f (w b r)=c then (1:ℝ) else 0 := by
    rw [← finProdFinEquiv.sum_comp]
    simpa only [Function.comp_apply,WordFlatten.flattenEquiv,Equiv.coe_fn_mk,
      Equiv.symm_apply_apply] using Fintype.sum_prod_type (fun br : Fin q × Fin H =>
      if f (w br.1 br.2)=c then (1:ℝ) else 0)
  rw [he,←sum_div,Nat.cast_mul]
  simp only [div_div]
  rw [mul_comm]

lemma atom_entropy_formula {q K : ℕ} [Nonempty A] (P : Law (Fin q → A))
    (hP : ∀ v,P.mass v ≤ 2*((2:ℝ)^(2*K)/Fintype.card A)^q) :
    (q:ℝ)*(Real.log (Fintype.card A)-(2*K:ℕ)*Real.log 2)-Real.log 2 ≤ entropy P := by
  have hc : (0:ℝ)<Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hM : 0<2*((2:ℝ)^(2*K)/Fintype.card A)^q := by positivity
  have hh := entropy_atom_lower P hM hP
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,
    Real.log_div (by positivity) hc.ne',Real.log_pow] at hh
  convert hh using 1; ring

lemma window_entropy_close {q K : ℕ} [Nonempty A] (P Q : Law (Fin q → A))
    (hP : ∀ v,P.mass v ≤ 2*((2:ℝ)^(2*K)/Fintype.card A)^q)
    {s : ℝ} (hPQ : TV P Q ≤ s) :
    (q:ℝ)*((1-s)*Real.log (Fintype.card A)-(2*K:ℕ)*Real.log 2)-2*Real.log 2 ≤ entropy Q := by
  have ha := atom_entropy_formula P hP
  have ht := entropy_tv_lower P Q hPQ
  rw [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow] at ht
  nlinarith
end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.WordHierarchy
open Finset WordParameters WordStep WordAlphabet FiniteLaw

noncomputable instance levelNonempty (i : ℕ) : Nonempty (A i) := alphabet_nonempty i
noncomputable instance groupNeZero (i : ℕ) : NeZero (groupLength i) :=
  ⟨by rw [groupLength,q_mul_H]; exact (N_pos _).ne'⟩
noncomputable instance familyNeZero (i : ℕ) : NeZero (size i) := ⟨Fintype.card_ne_zero⟩

noncomputable def conditionedLabels (i : ℕ) : Law (Labels i) :=
  WordFlatten.flatLaw (form (S i)) (goodDim i) (stage i).E (stage i).massE
noncomputable def conditionedWindow (i : ℕ) (t : Offsets (S i)) : Law (Fin (D (S i)) → A i) :=
  push (conditionedLabels i) (window (S i) t)
noncomputable def uniformWindow (i : ℕ) (t : Offsets (S i)) : Law (Fin (D (S i)) → A i) :=
  push uniform (fun a : A (i+1) => window (S i) t ((stage i).word a))
noncomputable def parentWindow (i : ℕ) (a : A (i+2)) (t : Offsets (S i)) : Law (Fin (D (S i)) → A i) :=
  push uniform (fun j : Fin (groupLength (i+1)) =>
    window (S i) t ((stage i).word ((stage (i+1)).word a j)))

/-- W3 for the actual uniform selected family, in the finite-law API. -/
lemma uniformWindow_close (i : ℕ) (t : Offsets (S i)) :
    TV (uniformWindow i t) (conditionedWindow i t) ≤ 1/10000 := by
  have h := (stage i).windowTV t
  rw [←TV_empirical] at h
  change TV (push uniform ((window (S i) t) ∘ (stage i).w)) (conditionedWindow i t) ≤ _ at h
  have he : uniformWindow i t=push uniform ((window (S i) t) ∘ (stage i).w) := by
    exact uniform_reindex (Fintype.equivFin (A (i+1))) ((window (S i) t) ∘ (stage i).w)
  rwa [he]

/-- W4 for each actual parent: uniformity is only over its slots, never
an assumption on the parent-word distribution. -/
lemma parentWindow_close (i : ℕ) (a : A (i+2)) (t : Offsets (S i)) :
    TV (parentWindow i a t) (uniformWindow i t) ≤ 1/10000 := by
  let : NeZero (q (S (i+1))) := ⟨(q_pos _).ne'⟩
  let : NeZero (H (S (i+1))) := ⟨(H_pos _).ne'⟩
  have hh := TV_grouped (fun b => window (S i) t ((stage i).word b))
    (WordFlatten.flattenEquiv.symm ((stage (i+1)).word a))
  simp only [Equiv.apply_symm_apply] at hh
  change TV (parentWindow i a t) (uniformWindow i t)=
    WordLaw.tvFromUniformObservable (fun b => window (S i) t ((stage i).word b))
      (WordFlatten.flattenEquiv.symm ((stage (i+1)).word a)) at hh
  rw [hh]
  exact stage_approximates i a t

/-- The two and only two approximation costs used in the manuscript. -/
lemma parent_conditioned_close (i : ℕ) (a : A (i+2)) (t : Offsets (S i)) :
    TV (conditionedWindow i t) (parentWindow i a t) ≤ 2/10000 := by
  rw [TV_symm]
  have ht := TV_triangle (parentWindow i a t) (uniformWindow i t) (conditionedWindow i t)
  have h1 := parentWindow_close i a t
  have h2 := uniformWindow_close i t
  linarith

def windowEmbedding (i : ℕ) (t : Offsets (S i)) {r : ℕ} (hr : r ≤ D (S i)) : Fin r ↪ Fin (groupLength i) where
  toFun k := ⟨t.val.val+k.val,by change t.val.val+k.val < q (S i)*H (S i); have h := t.property; have hk := k.isLt; omega⟩
  inj' := by intro j k h; apply Fin.ext; have he := congrArg Fin.val h; dsimp at he; omega

def takePrefix {level r d : ℕ} (hr : r ≤ d) (w : Fin d → A level) : Fin r → A level :=
  fun k => w ⟨k.val,lt_of_lt_of_le k.isLt hr⟩

lemma conditioned_prefix_atom (i : ℕ) (t : Offsets (S i)) {r : ℕ} (hr : r ≤ D (S i))
    (v : Fin r → A i) :
    (push (conditionedWindow i t) (takePrefix hr)).mass v ≤
      2*((2:ℝ)^(2*K (S i))/Fintype.card (A i))^r := by
  rw [conditionedWindow,push_comp]
  exact WordFlatten.flat_window_atom (form (S i)) (goodDim i)
    (by change 1 ≤ K (sequence 40000 i); have := (step_conditions initial_threshold i).1; omega)
    (stage i).E (stage i).massE (windowEmbedding i t hr) v

/-- A real entropy lower bound for EVERY selected parent and admissible
internal offset, with fully constructed comparison law and all atom bounds. -/
theorem parent_prefix_entropy (i : ℕ) (a : A (i+2)) (t : Offsets (S i))
    {r : ℕ} (hr : r ≤ D (S i)) :
    (r:ℝ)*((1-2/10000)*Real.log (Fintype.card (A i))-(2*K (S i):ℕ)*Real.log 2)-2*Real.log 2 ≤
      entropy (push (parentWindow i a t) (takePrefix hr)) := by
  exact window_entropy_close (push (conditionedWindow i t) (takePrefix hr)) _
    (conditioned_prefix_atom i t hr)
    ((TV_push _ _ (takePrefix hr)).trans (parent_conditioned_close i a t))
end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.FiniteLaw
open MeasureTheory Set Finset
variable {X α β : Type*} [MeasurableSpace X] [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma observed_ext {P Q : Law α} (h : P.mass=Q.mass) : P=Q := by
  cases P; cases Q; cases h; rfl

noncomputable def observed (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → α) (hf : Measurable f) : Law α where
  mass a := μ.real {x | f x=a}
  nonneg _ := measureReal_nonneg
  total := by
    have h := Alignment.sum_fibers μ univ hf
    simpa only [Set.mem_univ,true_and,probReal_univ] using h

lemma observed_push [DecidableEq β]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → α) (hf : Measurable f)
    (g : α → β) : push (observed μ f hf) g = observed μ (g ∘ f) ((measurable_of_countable g).comp hf) := by
  classical
  apply observed_ext
  funext b
  dsimp only [push,FiniteEntropy.pushMass,observed,Function.comp_apply]
  rw [←Alignment.sum_fibers μ {x | g (f x)=b} hf]
  apply sum_congr rfl
  intro a _
  by_cases ha : g a=b
  · rw [ite_eq_left ha]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun hx => ⟨by rw [hx,ha],hx⟩,And.right⟩
  · rw [ite_eq_right ha]
    have he : {x | x∈{x | g (f x)=b} ∧ f x=a}=∅ := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      rintro ⟨hb,hf⟩
      exact ha (hf ▸ hb)
    rw [he,measureReal_empty]

noncomputable def conditionalObserved (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → α) (hf : Measurable f) (k : X → β) (_hk : Measurable k)
    [Nonempty α] (b : β) : Law α := by
  let p := μ.real {x | k x=b}
  by_cases hp : p=0
  · exact uniform
  · refine ⟨(fun a => μ.real {x | k x=b ∧ f x=a}/p),fun _ => div_nonneg measureReal_nonneg measureReal_nonneg,?_⟩
    rw [←sum_div]
    have hs := Alignment.sum_fibers μ {x | k x=b} hf
    simp only [Set.mem_ofPred_eq] at hs
    rw [hs]
    exact div_self hp

lemma conditionalObserved_mass (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → α) (hf : Measurable f) (k : X → β) (hk : Measurable k)
    [Nonempty α] (b : β) (a : α) :
    (observed μ k hk).mass b*(conditionalObserved μ f hf k hk b).mass a =
      μ.real {x | k x=b ∧ f x=a} := by
  change μ.real {x | k x=b}*_= _
  unfold conditionalObserved
  dsimp only
  split_ifs with hp
  · rw [hp,zero_mul]
    apply (le_antisymm ?_ measureReal_nonneg).symm
    calc
      _ ≤ μ.real {x | k x=b} := measureReal_mono (by intro x hx; exact hx.1)
      _ = 0 := hp
  · exact mul_div_cancel₀ _ hp

/-- Disintegration over a finite actual observation. Zero conditional masses
are represented by a harmless uniform law and contribute exactly zero. -/
theorem observed_mixture (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → α) (hf : Measurable f) (k : X → β) (hk : Measurable k)
    [Nonempty α] :
    observed μ f hf=mixture (observed μ k hk) (conditionalObserved μ f hf k hk) := by
  apply observed_ext
  funext a
  change μ.real {x | f x=a}=∑ b,_
  simp only [conditionalObserved_mass]
  have h := Alignment.sum_fibers μ {x | f x=a} hk
  simpa only [Set.mem_ofPred_eq,and_comm] using h.symm
end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set Finset FiniteLaw
open scoped ENNReal

noncomputable instance stageLengthNeZero (i : ℕ) : NeZero (N (S i)) := ⟨(N_pos _).ne'⟩

lemma measurable_slot (i : ℕ) : Measurable (slot i) := by
  have hh : slot i = (fun a : ZMod (length 40000 (i+1)) =>
      (⟨a.val / length 40000 i,by
        apply (Nat.div_lt_iff_lt_mul (length_pos 40000 i)).mpr
        simpa only [length_step,Nat.mul_comm] using ZMod.val_lt a⟩ : Fin (N (S i)))) ∘ phase (i+1) := rfl
  rw [hh]
  exact (measurable_of_countable _).comp (measurable_phase (i+1))

lemma pack_slots (i : ℕ) (x : Extension) :
    pack (slot (i+1) x,slot i x)=parentSlot i x := by
  apply Fin.ext
  rw [pack_val,slot_pair]

lemma slots_iff (i : ℕ) (x : Extension) (u : Fin (N (S i))) (h : Fin (N (S (i+1)))) :
    slot i x=u ∧ slot (i+1) x=h ↔ parentSlot i x=pack (h,u) := by
  rw [←pack_slots,(Equiv.injective pack).eq_iff,Prod.mk.injEq,and_comm]

lemma boundary_phase_zero (μ : Measure Extension) (i : ℕ) :
    ∀ᵐ x ∂boundary μ i,phase i x=0 := by
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_eq_fun (measurable_phase i) measurable_const)) _

lemma boundary_slots_mass (μ : Measure Extension) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) (v : A (i+2))
    (u : Fin (N (S i))) (h : Fin (N (S (i+1)))) :
    (boundary μ i).real {x | label (i+2) x=v ∧ slot i x=u ∧ slot (i+1) x=h} =
      μ.real {x | label (i+2) x=v}/((N (S i):ℝ)*N (S (i+1))) := by
  have he : {x | label (i+2) x=v ∧ slot i x=u ∧ slot (i+1) x=h} =
      {x | parentSlot i x=pack (h,u) ∧ label (i+2) x=v} := by
    ext x
    simp only [Set.mem_ofPred_eq,←slots_iff,and_comm]
  rw [he]
  apply (eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (N_pos _).ne') (Nat.cast_ne_zero.mpr (N_pos _).ne') : (N (S i):ℝ)*N (S (i+1))≠0)).mpr
  have hh := boundary_parentSlot_mass μ hT i v (pack (h,u))
  simpa only [Nat.cast_mul,mul_comm] using hh

noncomputable def windowKey (i : ℕ) (x : Extension) : A (i+2) × Fin (N (S i)) :=
  (label (i+2) x,slot i x)

lemma measurable_windowKey (i : ℕ) : Measurable (windowKey i) :=
  (measurable_label _).prodMk (measurable_slot _)

lemma boundary_key_mass (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) (v : A (i+2)) (u : Fin (N (S i))) :
    (boundary μ i).real {x | windowKey i x=(v,u)} =
      μ.real {x | label (i+2) x=v}/N (S i) := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  rw [←Alignment.sum_fibers (boundary μ i) {x | windowKey i x=(v,u)} (measurable_slot (i+1))]
  have hs (h : Fin (N (S (i+1)))) :
      (boundary μ i).real {x | x∈{x | windowKey i x=(v,u)} ∧ slot (i+1) x=h} =
        μ.real {x | label (i+2) x=v}/((N (S i):ℝ)*N (S (i+1))) := by
    convert boundary_slots_mass μ hT i v u h using 2
    ext x
    simp only [Set.mem_ofPred_eq,windowKey,Prod.mk.injEq,and_assoc]
  simp only [hs,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr (N_pos (S (i+1))).ne']

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set Finset FiniteLaw

/-- The actual r-child window at an internal offset of a specified parent. -/
noncomputable def sampledWindow (i r : ℕ) (u : Fin (N (S i)))
    (hr : u.val+r ≤ N (S i)) (v : A (i+2)) (h : Fin (N (S (i+1)))) : Fin r → A i :=
  fun j => children i (children (i+1) v h) ⟨u.val+j.val,by have := j.isLt; omega⟩

noncomputable def sampledLaw (i r : ℕ) (u : Fin (N (S i)))
    (hr : u.val+r ≤ N (S i)) (v : A (i+2)) : Law (Fin r → A i) :=
  push uniform (sampledWindow i r u hr v)

lemma labelList_key (i r : ℕ) (u : Fin (N (S i))) (hr : u.val+r ≤ N (S i))
    (v : A (i+2)) (h : Fin (N (S (i+1)))) (x : Extension) (hx : phase i x=0)
    (hk : windowKey i x=(v,u)) (hh : slot (i+1) x=h) :
    labelList i r x=sampledWindow i r u hr v h := by
  have hv : label (i+2) x=v := congrArg Prod.fst hk
  have hu : slot i x=u := congrArg Prod.snd hk
  rw [labelList_inside i r x hx (by simpa only [hu] using hr)]
  simp only [hv,hu,hh]
  rfl

/-- Exact disintegration at an admissible offset. Stationarity gives slot
uniformity even when the parent marginal has zero or varying masses. -/
theorem boundary_window_joint (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i r : ℕ) (u : Fin (N (S i)))
    (hr : u.val+r ≤ N (S i)) (v : A (i+2)) (w : Fin r → A i) :
    (boundary μ i).real {x | windowKey i x=(v,u) ∧ labelList i r x=w} =
      (boundary μ i).real {x | windowKey i x=(v,u)}*(sampledLaw i r u hr v).mass w := by
  classical
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  rw [←Alignment.sum_fibers (boundary μ i)
    {x | windowKey i x=(v,u) ∧ labelList i r x=w} (measurable_slot (i+1))]
  have hs (h : Fin (N (S (i+1)))) :
      (boundary μ i).real {x | x∈{x | windowKey i x=(v,u) ∧ labelList i r x=w} ∧ slot (i+1) x=h} =
        if sampledWindow i r u hr v h=w then μ.real {x | label (i+2) x=v}/((N (S i):ℝ)*N (S (i+1))) else 0 := by
    by_cases hw : sampledWindow i r u hr v h=w
    · rw [ite_eq_left hw]
      apply (measureReal_congr ?_).trans (boundary_slots_mass μ hT i v u h)
      filter_upwards [boundary_phase_zero μ i] with x hx
      apply propext
      constructor
      · rintro ⟨⟨hk,_⟩,hh⟩
        exact ⟨congrArg Prod.fst hk,congrArg Prod.snd hk,hh⟩
      · rintro ⟨hv,hu,hh⟩
        have hk : windowKey i x=(v,u) := Prod.ext hv hu
        exact ⟨⟨hk,(labelList_key i r u hr v h x hx hk hh).trans hw⟩,hh⟩
    · rw [ite_eq_right hw]
      apply (measureReal_congr (t := (∅ : Set Extension)) ?_).trans measureReal_empty
      filter_upwards [boundary_phase_zero μ i] with x hx
      apply propext
      change ((windowKey i x=(v,u) ∧ labelList i r x=w) ∧ slot (i+1) x=h) ↔ False
      constructor
      · rintro ⟨⟨hk,hlist⟩,hh⟩
        exact hw ((labelList_key i r u hr v h x hx hk hh).symm.trans hlist)
      · exact False.elim
  simp only [hs,boundary_key_mass μ hT i v u]
  simp only [sampledLaw,push,uniform,Fintype.card_fin]
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  split_ifs <;> simp [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]

/-- The conditional law is the actual finite-parent sampled window law on
all positive-probability fibres. No hypothesis about parent frequencies. -/
lemma conditional_window_eq (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i r : ℕ) (u : Fin (N (S i)))
    (hr : u.val+r ≤ N (S i)) (v : A (i+2))
    (hp : (boundary μ i).real {x | windowKey i x=(v,u)}≠0) :
    let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
    conditionalObserved (boundary μ i) (labelList i r) (measurable_labelList i r)
      (windowKey i) (measurable_windowKey i) (v,u)=sampledLaw i r u hr v := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  apply mass_ext
  funext w
  have hh := conditionalObserved_mass (boundary μ i) (labelList i r)
    (measurable_labelList i r) (windowKey i) (measurable_windowKey i) (v,u) w
  rw [boundary_window_joint μ hT i r u hr v w] at hh
  exact (mul_left_cancel₀ hp) hh

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Finset WordParameters WordStep FiniteLaw

lemma sampledLaw_prefix (i : ℕ) (a : A (i+2)) (t : Offsets (S i))
    {r : ℕ} (hr : r ≤ D (S i)) :
    sampledLaw i r ((finCongr (q_mul_H (S i))) t.val)
      (by have _ht := t.property; change t.val.val+r ≤ N (S i); rw [←q_mul_H]; omega) a =
      push (parentWindow i a t) (takePrefix hr) := by
  classical
  rw [parentWindow,push_comp]
  have he : (fun j : Fin (groupLength (i+1)) =>
      takePrefix hr (window (S i) t ((stage i).word ((stage (i+1)).word a j)))) =
      sampledWindow i r ((finCongr (q_mul_H (S i))) t.val)
      (by have _ht := t.property; change t.val.val+r ≤ N (S i); rw [←q_mul_H]; omega) a ∘
        (finCongr (q_mul_H (S (i+1)))) := by
    funext j k
    simp only [Function.comp_apply,sampledWindow,children,Equiv.symm_apply_apply,takePrefix,window]
    congr 2
  change push uniform _ = push uniform _
  dsimp only [Function.comp_def]
  rw [he]
  exact (uniform_reindex (finCongr (q_mul_H (S (i+1)))) _).symm

noncomputable def windowLower (i r : ℕ) : ℝ :=
  (r:ℝ)*((1-2/10000)*Real.log (Fintype.card (A i))-(2*K (S i):ℕ)*Real.log 2)-2*Real.log 2

lemma sampled_entropy (i : ℕ) (a : A (i+2)) (u : Fin (N (S i)))
    (hu : u.val+D (S i) ≤ N (S i)) {r : ℕ} (hr : r ≤ D (S i)) :
    windowLower i r ≤ entropy (sampledLaw i r u (by omega) a) := by
  let t : Offsets (S i) := ⟨(finCongr (q_mul_H (S i))).symm u,by
    change u.val+D (S i) ≤ q (S i)*H (S i)
    rwa [q_mul_H]⟩
  have hh := parent_prefix_entropy i a t hr
  rw [←sampledLaw_prefix] at hh
  simpa only [t,windowLower,Equiv.apply_symm_apply] using hh

/-- The entropy of the genuine stationary aligned orbit window is bounded
using the exactly uniform internal-slot law, not a selected parent law. -/
theorem boundary_window_entropy (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i r : ℕ) (hr : r ≤ D (S i)) :
    let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
    (∑ b : A (i+2) × Fin (N (S i)),
      if b.2.val+D (S i) ≤ N (S i) then
        (observed (boundary μ i) (windowKey i) (measurable_windowKey i)).mass b else 0)*windowLower i r ≤
      entropy (observed (boundary μ i) (labelList i r) (measurable_labelList i r)) := by
  classical
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  dsimp only
  rw [observed_mixture (boundary μ i) (labelList i r) (measurable_labelList i r)
    (windowKey i) (measurable_windowKey i)]
  apply le_trans _ (entropy_mixture _ _)
  rw [sum_mul]
  apply sum_le_sum
  rintro ⟨v,u⟩ _
  by_cases hu : u.val+D (S i) ≤ N (S i)
  · rw [ite_eq_left hu]
    by_cases hp : (boundary μ i).real {x | windowKey i x=(v,u)}=0
    · change (boundary μ i).real {x | windowKey i x=(v,u)}*_ ≤ _
      simp only [hp,zero_mul,observed,le_refl]
    · rw [conditional_window_eq μ hT i r u (by omega) v hp]
      exact mul_le_mul_of_nonneg_left (sampled_entropy i v u hu hr) measureReal_nonneg
  · rw [ite_eq_right hu,zero_mul]
    exact mul_nonneg measureReal_nonneg (entropy_nonneg _)

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Finset WordParameters WordStep FiniteLaw

lemma D_pos (s : ℕ) : 0<D s := by unfold D; positivity

lemma good_offset_count (s : ℕ) :
    #{u : Fin (N s) | u.val+D s ≤ N s}=N s-D s+1 := by
  have hD := D_le_N s
  have hp := D_pos s
  have he : (univ.filter (fun u : Fin (N s) => u.val+D s ≤ N s))=
      (univ.filter (fun u : Fin (N s) => u.val < N s-D s+1)) := by
    apply Finset.filter_congr
    intro u hu
    omega
  rw [he,Fin.card_filter_val_lt,min_eq_right (by omega)]

lemma good_key_mass (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) :
    let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
    (∑ b : A (i+2) × Fin (N (S i)),
      if b.2.val+D (S i) ≤ N (S i) then
        (observed (boundary μ i) (windowKey i) (measurable_windowKey i)).mass b else 0)=
      (N (S i)-D (S i)+1:ℕ)/(N (S i):ℝ) := by
  classical
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  dsimp only
  rw [Fintype.sum_prod_type]
  simp only [observed,boundary_key_mass μ hT]
  have hs (v : A (i+2)) :
      (∑ u : Fin (N (S i)),if u.val+D (S i) ≤ N (S i) then
        μ.real {x | label (i+2) x=v}/N (S i) else 0)=
      (N (S i)-D (S i)+1:ℕ)*(μ.real {x | label (i+2) x=v}/N (S i)) := by
    rw [←sum_filter]
    simp only [sum_const,nsmul_eq_mul,good_offset_count]
  simp only [hs]
  rw [←mul_sum,←sum_div]
  have hm := (observed μ (label (i+2)) (measurable_label (i+2))).total
  change (∑ v,μ.real {x | label (i+2) x=v})=1 at hm
  rw [hm,mul_one_div]

/-- The manuscript's explicit stationary entropy lower bound, with the
exact loss from inadmissible offsets and an arbitrary invariant probability. -/
theorem stationary_window_entropy (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i r : ℕ) (hr : r ≤ D (S i)) :
    let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
    ((N (S i)-D (S i)+1:ℕ)/(N (S i):ℝ))*windowLower i r ≤
      entropy (observed (boundary μ i) (labelList i r) (measurable_labelList i r)) := by
  have hh := boundary_window_entropy μ hT i r hr
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  dsimp only at hh ⊢
  rw [good_key_mass μ hT i] at hh
  exact hh

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Finset WordParameters WordAlphabet WordStep FiniteLaw

lemma log_card (i : ℕ) : Real.log (Fintype.card (A i))=ell (S i)*Real.log 2 := by
  change Real.log (Fintype.card (Alphabet (S i)))=_
  rw [cardAlphabetReal]
  dsimp only [ell,alphabetSize,Real.logb]
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2)))]

lemma K_large {i : ℕ} (hi : 1 ≤ i) : 4000 ≤ K (S i) := by
  have h := K_double_exponential initial_threshold i
  have hpow : 2 ≤ (2:ℕ)^i := by
    calc
      _ = (2:ℕ)^1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hi
  have hh : (2:ℕ)^16 ≤ 2^(8*2^i) := Nat.pow_le_pow_right (by decide) (by omega)
  exact (by norm_num : 4000 ≤ (2:ℕ)^16).trans (hh.trans h)

lemma bad_offset_small (i : ℕ) : (D (S i):ℝ)/(N (S i):ℝ) ≤ 1/2000 := by
  have hk := (step_conditions initial_threshold i).1
  change 256 ≤ K (S i) at hk
  have he : K (S i)/8+11 ≤ K (S i) := by omega
  have hp : 2048*D (S i) ≤ N (S i) := by
    calc
      _ = 2^(K (S i)/8+11) := by rw [pow_add]; norm_num [D]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) he
  have hr : (2000:ℝ)*(D (S i):ℝ) ≤ N (S i) := by
    exact_mod_cast (show 2000*D (S i) ≤ N (S i) by omega)
  have hN : (0:ℝ)<N (S i) := by exact_mod_cast N_pos (S i)
  apply (div_le_iff₀ hN).mpr
  linarith

lemma good_offset_large (i : ℕ) : (1999/2000:ℝ) ≤
    (N (S i)-D (S i)+1:ℕ)/(N (S i):ℝ) := by
  have hD := D_le_N (S i)
  have hN : (0:ℝ)<N (S i) := by exact_mod_cast N_pos (S i)
  have hb := bad_offset_small i
  rw [Nat.cast_add,Nat.cast_sub hD,Nat.cast_one]
  apply (le_div_iff₀ hN).mpr
  have hb' := (div_le_iff₀ hN).mp hb
  nlinarith

lemma windowLower_large {i r : ℕ} (hi : 1 ≤ i) (hr : 1 ≤ r) :
    (2497/2500:ℝ)*r*Real.log (Fintype.card (A i)) ≤ windowLower i r := by
  have hk : (4000:ℝ)≤K (S i) := by exact_mod_cast K_large hi
  have he := (K_bounds (S i)).1
  have hK : 2*(K (S i):ℝ) ≤ ell (S i)/2000 := by nlinarith
  have h1 : (2:ℝ) ≤ ell (S i)/2000 := by nlinarith
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hr' : (1:ℝ)≤r := by exact_mod_cast hr
  have hepos : 0 ≤ ell (S i) := ell_nonneg _
  have hklog := mul_le_mul_of_nonneg_right hK hlog.le
  have h1log := mul_le_mul_of_nonneg_right h1 hlog.le
  have hklogr := mul_le_mul_of_nonneg_left hklog (show (0:ℝ)≤r by positivity)
  have hcost : 2*Real.log 2 ≤ (r:ℝ)*(ell (S i)/2000*Real.log 2) := by
    exact h1log.trans (le_mul_of_one_le_left (by positivity) hr')
  rw [windowLower,log_card]
  push_cast
  nlinarith

/-- Uniform stationary window entropy, with the manuscript's decimal constant.
It is valid already at level one beyond the fixed initial level, independently
of the stationary probability and independently of the window length. Entropy
here uses natural logarithms, so both sides have the same conversion factor. -/
theorem stationary_window_entropy_996 (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) {i r : ℕ} (hi : 1 ≤ i)
    (hr : 1 ≤ r) (hrD : r ≤ D (S i)) :
    let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
    (996/1000:ℝ)*r*Real.log (Fintype.card (A i)) ≤
      entropy (observed (boundary μ i) (labelList i r) (measurable_labelList i r)) := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  dsimp only
  have hh := stationary_window_entropy μ hT i r hrD
  dsimp only at hh
  have hl := windowLower_large hi hr
  have hg := good_offset_large i
  have hlog : 0 ≤ Real.log (Fintype.card (A i)) := by
    rw [log_card]
    exact mul_nonneg (ell_nonneg _) (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hpos : 0 ≤ (2497/2500:ℝ)*r*Real.log (Fintype.card (A i)) := by positivity
  calc
    _ ≤ (1999/2000:ℝ)*((2497/2500:ℝ)*r*Real.log (Fintype.card (A i))) := by nlinarith
    _ ≤ ((N (S i)-D (S i)+1:ℕ)/(N (S i):ℝ))*windowLower i r :=
      mul_le_mul hg hl hpos (by positivity)
    _ ≤ _ := hh

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open WordParameters WordAlphabet WordStep WordConcatenation MeasureTheory Set Finset

lemma graph_block_room (i k : ℕ) (hk : k ≤ K (S i)/8) : 2*2^k ≤ H (S i) := by
  have hK := (step_conditions initial_threshold i).1
  change 256 ≤ K (S i) at hK
  have he : k+1 ≤ K (S i)/2 := by omega
  calc
    _ = 2^(k+1) := by rw [pow_succ]; omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

lemma group_site_lt (i : ℕ) (u : Fin (N (S i))) {r : ℕ} (hr : r<H (S i)) :
    H (S i)*(u.val/H (S i))+r < N (S i) := by
  have hd : u.val/H (S i)<q (S i) := by
    apply (Nat.div_lt_iff_lt_mul (H_pos (S i))).mpr
    rw [q_mul_H]
    exact u.isLt
  have hh : (u.val/H (S i)+1)*H (S i) ≤ q (S i)*H (S i) :=
    Nat.mul_le_mul_right _ hd
  rw [q_mul_H] at hh
  nlinarith

lemma children_graph (i k : ℕ) (hk : k ≤ K (S i)/8)
    (a : A (i+1)) (u : Fin (N (S i))) (j : ℕ)
    (hr : u.val%H (S i)+j+2^k < H (S i)) :
    let h₁ : u.val+j < N (S i) := by
      have hh := group_site_lt i u (show u.val%H (S i)+j<H (S i) from lt_of_le_of_lt (Nat.le_add_right _ _) hr)
      have he := Nat.div_add_mod u.val (H (S i))
      omega
    let h₂ : u.val+j+2^k < N (S i) := by
      have hh := group_site_lt i u hr
      have he := Nat.div_add_mod u.val (H (S i))
      omega
    form (S i) (children i a ⟨u.val+j,h₁⟩).val
      (children i a ⟨u.val+j+2^k,h₂⟩).val=0 := by
  dsimp only
  have hK := (step_conditions initial_threshold i).1
  change 256 ≤ K (S i) at hK
  have hkk : k<K (S i) := by omega
  let b : Fin (q (S i)) := ⟨u.val/H (S i),by
    apply (Nat.div_lt_iff_lt_mul (H_pos (S i))).mpr
    rw [q_mul_H]
    exact u.isLt⟩
  have hh := (stage i).relations ((Fintype.equivFin (A (i+1))) a) b
    (u.val%H (S i)+j) k hkk hk hr
  have he₁ : (finCongr (q_mul_H (S i))).symm
      (⟨u.val+j,by
        have hh := group_site_lt i u (show u.val%H (S i)+j<H (S i) from lt_of_le_of_lt (Nat.le_add_right _ _) hr)
        have he := Nat.div_add_mod u.val (H (S i)); omega⟩ : Fin (N (S i))) =
      finProdFinEquiv (b,⟨u.val%H (S i)+j,lt_of_le_of_lt (Nat.le_add_right _ _) hr⟩) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    change u.val+j = u.val%H (S i)+j+H (S i)*(u.val/H (S i))
    have he := Nat.mod_add_div u.val (H (S i))
    omega
  have he₂ : (finCongr (q_mul_H (S i))).symm
      (⟨u.val+j+2^k,by
        have hh := group_site_lt i u hr
        have he := Nat.div_add_mod u.val (H (S i)); omega⟩ : Fin (N (S i))) =
      finProdFinEquiv (b,⟨u.val%H (S i)+j+2^k,hr⟩) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    change u.val+j+2^k = u.val%H (S i)+j+2^k+H (S i)*(u.val/H (S i))
    have he := Nat.mod_add_div u.val (H (S i))
    omega
  simpa only [children,Family.word,he₁,he₂] using hh

/-- The genuine two-window graph event on a boundary-started orbit. -/
def graphWindows (i k : ℕ) (x : Extension) : Prop :=
  ∀ j : Fin (2^k-1), form (S i)
    (label i ((T^[j.val*length 40000 i]) x)).val
    (label i ((T^[(j.val+2^k)*length 40000 i]) x)).val=0

lemma graphWindows_of_good (i k : ℕ) (hk : k ≤ K (S i)/8) (x : Extension)
    (hx : phase i x=0)
    (hgood : (slot i x).val%H (S i)+(2*2^k-1) ≤ H (S i)) :
    graphWindows i k x := by
  intro j
  have hD : 0<(2:ℕ)^k := by positivity
  have hj := j.isLt
  have hr : (slot i x).val%H (S i)+j.val+2^k < H (S i) := by omega
  have hh := children_graph i k hk (label (i+1) x) (slot i x) j.val hr
  dsimp only at hh
  have he := Nat.div_add_mod (slot i x).val (H (S i))
  have h₁ : (slot i x).val+j.val<N (S i) := by
    have hh := group_site_lt i (slot i x) (show (slot i x).val%H (S i)+j.val<H (S i) by omega)
    omega
  have h₂ : (slot i x).val+(j.val+2^k)<N (S i) := by
    have hh := group_site_lt i (slot i x) hr
    omega
  rw [label_advance_child i j.val x hx h₁,label_advance_child i (j.val+2^k) x hx h₂]
  simpa only [Nat.add_assoc] using hh

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open WordParameters WordAlphabet WordStep WordConcatenation MeasureTheory Set Finset FiniteLaw

lemma boundary_slot_mass (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) (u : Fin (N (S i))) :
    (boundary μ i).real {x | slot i x=u}=1/(N (S i):ℝ) := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  rw [←Alignment.sum_fibers (boundary μ i) {x | slot i x=u} (measurable_label (i+2))]
  have he (v : A (i+2)) : {x | x∈{x | slot i x=u} ∧ label (i+2) x=v}=
      {x | windowKey i x=(v,u)} := by
    ext x
    simp only [Set.mem_ofPred_eq,windowKey,Prod.mk.injEq,and_comm]
  simp only [he,boundary_key_mass μ hT]
  rw [←sum_div]
  have hm := (observed μ (label (i+2)) (measurable_label (i+2))).total
  change (∑ v,μ.real {x | label (i+2) x=v})=1 at hm
  rw [hm]

lemma residue_sum (i c : ℕ) (hc : c ≤ H (S i)) :
    (∑ u : Fin (N (S i)), if u.val%H (S i)<c then (1:ℝ)/N (S i) else 0)=
      (c:ℝ)/H (S i) := by
  classical
  let e : Fin (q (S i)) × Fin (H (S i)) ≃ Fin (N (S i)) :=
    finProdFinEquiv.trans (finCongr (q_mul_H (S i)))
  have he (v : Fin (q (S i)) × Fin (H (S i))) : (e v).val%H (S i)=v.2.val := by
    change (v.2.val+H (S i)*v.1.val)%H (S i)=v.2.val
    simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,zero_mul,Nat.zero_mod,Nat.add_zero,
      Nat.mod_eq_of_lt v.2.isLt]
  rw [←e.sum_comp]
  simp only [he,Fintype.sum_prod_type]
  have hs : (∑ r : Fin (H (S i)),if r.val<c then (1:ℝ)/N (S i) else 0)=
      (c:ℝ)/N (S i) := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,Fin.card_filter_val_lt,min_eq_right hc,mul_one_div]
  simp only [hs,sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [←q_mul_H (S i),Nat.cast_mul]
  have hq : (q (S i):ℝ)≠0 := by exact_mod_cast (q_pos (S i)).ne'
  field_simp

lemma boundary_residue_mass (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i c : ℕ) (hc : c ≤ H (S i)) :
    (boundary μ i).real {x | (slot i x).val%H (S i)<c}=(c:ℝ)/H (S i) := by
  classical
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  rw [←Alignment.sum_fibers (boundary μ i)
    {x | (slot i x).val%H (S i)<c} (measurable_slot i)]
  have hs (u : Fin (N (S i))) :
      (boundary μ i).real {x | x∈{x | (slot i x).val%H (S i)<c} ∧ slot i x=u}=
      if u.val%H (S i)<c then (1:ℝ)/N (S i) else 0 := by
    split_ifs with hu
    · have he : {x | x∈{x | (slot i x).val%H (S i)<c} ∧ slot i x=u}={x | slot i x=u} := by
        ext x
        simp only [Set.mem_ofPred_eq]
        constructor
        · exact And.right
        · intro hx; exact ⟨by simpa only [hx] using hu,hx⟩
      rw [he,boundary_slot_mass μ hT]
    · have he : {x | x∈{x | (slot i x).val%H (S i)<c} ∧ slot i x=u}=∅ := by
        ext x
        simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
        rintro ⟨hr,hx⟩
        exact hu (by simpa only [hx] using hr)
      rw [he,measureReal_empty]
  simp only [hs]
  exact residue_sum i c hc

/-- The two lists of the actual system pass all graph tests simultaneously
except for the precise group-boundary fraction (2D-2)/H. -/
theorem boundary_graph_probability (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i k : ℕ) (hk : k ≤ K (S i)/8) :
    1-((2*2^k-2:ℕ):ℝ)/H (S i) ≤
      (boundary μ i).real {x | graphWindows i k x} := by
  let : IsProbabilityMeasure (boundary μ i) := boundary_isProbability μ hT i
  have hD : 0<(2:ℕ)^k := by positivity
  have hH := graph_block_room i k hk
  let c := H (S i)-(2*2^k-1)+1
  have hc : c ≤ H (S i) := by dsimp only [c]; omega
  have he : {x : Extension | (slot i x).val%H (S i)<c}=
      {x | (slot i x).val%H (S i)+(2*2^k-1)≤H (S i)} := by
    ext x
    change (slot i x).val%H (S i)<c ↔
      (slot i x).val%H (S i)+(2*2^k-1)≤H (S i)
    dsimp only [c]
    omega
  have hm := boundary_residue_mass μ hT i c hc
  rw [he] at hm
  have hle : (boundary μ i).real {x | (slot i x).val%H (S i)+(2*2^k-1)≤H (S i)} ≤
      (boundary μ i).real {x | graphWindows i k x} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [boundary_phase_zero μ i] with x hx
    exact fun hg => graphWindows_of_good i k hk x hx hg
  rw [hm] at hle
  have hc' : c=H (S i)-(2*2^k-2) := by dsimp only [c]; omega
  have hsub : 2*2^k-2 ≤ H (S i) := by omega
  rw [hc',Nat.cast_sub hsub] at hle
  have hHp : (H (S i):ℝ)≠0 := by exact_mod_cast (H_pos (S i)).ne'
  convert hle using 1
  field_simp

end SmoothObstruction.WordHierarchy

end

section

open Finset

namespace SmoothObstruction.FiniteLaw
open MeasureTheory Set Finset
variable {X α : Type*} [MeasurableSpace X] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Every finite observable's real expectation agrees with integration in
its original probability space. No conditional normalization occurs. -/
theorem observed_integral (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → α) (hf : Measurable f) (g : α → ℝ) :
    (∑ a,(observed μ f hf).mass a*g a)=∫ x,g (f x) ∂μ := by
  calc
    _ = ∫ a,g a ∂(μ.map f) := by
      rw [integral_fintype (Integrable.of_finite (μ:=μ.map f))]
      apply sum_congr rfl
      intro a _
      simp only [observed,Measure.real,Measure.map_apply hf (measurableSet_singleton a),
        smul_eq_mul]
      rfl
    _ = _ := integral_map hf.aemeasurable (measurable_of_countable g).aestronglyMeasurable

/-- A lower bound on a success event is a lower bound in the UNCONDITIONED
law. In particular .95 mass at statistic .96 gives expectation .912. -/
theorem integral_lower_of_event (μ : Measure X) [IsProbabilityMeasure μ]
    (Z : X → ℝ) (hZi : Integrable Z μ) (hZn : ∀ x,0≤Z x)
    (G : Set X) (hG : MeasurableSet G) (a b : ℝ) (ha : 0≤a)
    (hGm : b≤μ.real G) (hZG : ∀ x∈G,a≤Z x) :
    a*b≤∫ x,Z x ∂μ := by
  calc
    a*b ≤ μ.real G*a := by nlinarith
    _ = ∫ x,G.indicator (fun _ => a) x ∂μ := by
      rw [integral_indicator_const a hG,smul_eq_mul]
    _ ≤ _ := integral_mono_ae ((integrable_const a).indicator hG) hZi
      (Filter.Eventually.of_forall (fun x => by
        by_cases hx : x∈G
        · simpa only [indicator_of_mem hx] using hZG x hx
        · simpa only [indicator_of_notMem hx] using hZn x))

end SmoothObstruction.FiniteLaw

end

end OAI
