import OAI.Combinatorics.Coboundary.LinkSpectrum

namespace OAI

/-!
Finite F2 averaging and bounded-cone estimates for weighted local cochains.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Averaging

section
open scoped BigOperators
variable {A B G : Type} [Fintype A] [Fintype B] [Fintype G]
  [DecidableEq A] [DecidableEq B] [DecidableEq G]

def supportNorm (w : A → ℝ) (f : A → ZMod 2) : ℝ :=
  ∑ a, if f a = 0 then 0 else w a

omit [DecidableEq A] in
lemma supportNorm_nonneg (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (f : A → ZMod 2) :
    0 ≤ supportNorm w f := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact le_rfl
  · exact hw a

omit [Fintype B] [DecidableEq B] in
lemma support_indicator_sum_le (s : Finset B) (f : B → ZMod 2) :
    (if ∑ b ∈ s, f b = 0 then (0 : ℝ) else 1) ≤
      ∑ b ∈ s, if f b = 0 then (0 : ℝ) else 1 := by
  split_ifs with h
  · exact Finset.sum_nonneg (fun b _ => by split_ifs <;> norm_num)
  · obtain ⟨b, hb, hfb⟩ : ∃ b ∈ s, f b ≠ 0 := by
      by_contra hh
      push Not at hh
      exact h (Finset.sum_eq_zero hh)
    calc
      (1 : ℝ) = (if f b = 0 then 0 else 1) := by simp [hfb]
      _ ≤ ∑ b ∈ s, if f b = 0 then (0 : ℝ) else 1 :=
        Finset.single_le_sum (f := fun b => if f b = 0 then (0 : ℝ) else 1)
          (fun b _ => by split_ifs <;> norm_num) hb

omit [DecidableEq G] in
lemma exists_le_of_sum_le [Nonempty G] (v : G → ℝ) (c : ℝ)
    (h : ∑ g, v g ≤ Fintype.card G * c) : ∃ g, v g ≤ c := by
  by_contra hn
  push Not at hn
  have hh : Fintype.card G * c < ∑ g, v g := by
    simpa using Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun g _ => hn g)
  linarith

omit [DecidableEq A] [DecidableEq G] in
theorem exists_small_dual [Nonempty G]
    (wA : A → ℝ) (hwA : ∀ a, 0 ≤ wA a) (hwSum : ∑ a, wA a = 1)
    (wB : B → ℝ) (hwB : ∀ b, 0 ≤ wB b)
    (act : G → B → B) (C : ℝ) (hC : 0 ≤ C)
    (H : A → Finset B) (R : ℕ) (hH : ∀ a, (H a).card ≤ R)
    (hOcc : ∀ a b, b ∈ H a → ∀ t, ((Finset.univ.filter (fun g => act g b = t)).card : ℝ) ≤
      Fintype.card G * C * wB t)
    (f : B → ZMod 2) :
    ∃ g, supportNorm wA (fun a => ∑ b ∈ H a, f (act g b)) ≤
      (R : ℝ) * C * supportNorm wB f := by
  apply exists_le_of_sum_le
  have hnon : 0 ≤ supportNorm wB f := supportNorm_nonneg wB hwB f
  have hp (a : A) (b : B) (hb : b ∈ H a) :
      ∑ g, (if f (act g b) = 0 then (0 : ℝ) else 1) ≤
        Fintype.card G * C * supportNorm wB f := by
    have he : (∑ g, if f (act g b) = 0 then (0 : ℝ) else 1) =
        ∑ t, ((Finset.univ.filter (fun g => act g b = t)).card : ℝ) *
          (if f t = 0 then (0 : ℝ) else 1) := by
      simp only [← Finset.sum_boole, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_eq_single (act g b)]
      · simp
      · intro t _ ht
        simp [ht.symm]
      · simp
    rw [he, supportNorm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    split_ifs with ht
    · simp
    · simpa using hOcc a b hb t
  calc
    (∑ g, supportNorm wA (fun a => ∑ b ∈ H a, f (act g b))) ≤
        ∑ g, ∑ a, wA a * ∑ b ∈ H a, if f (act g b) = 0 then (0 : ℝ) else 1 := by
      apply Finset.sum_le_sum
      intro g _
      apply Finset.sum_le_sum
      intro a _
      have hh := mul_le_mul_of_nonneg_left (support_indicator_sum_le (H a) (fun b => f (act g b))) (hwA a)
      simpa only [mul_ite, mul_zero, mul_one] using hh
    _ = ∑ a, wA a * ∑ b ∈ H a, ∑ g, if f (act g b) = 0 then (0 : ℝ) else 1 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ∑ a, wA a * ((H a).card * (Fintype.card G * C * supportNorm wB f)) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (hwA a)
      simpa using Finset.sum_le_sum (fun b (hb : b ∈ H a) => hp a b hb)
    _ ≤ ∑ a, wA a * ((R : ℝ) * (Fintype.card G * C * supportNorm wB f)) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (hwA a)
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hH a)
      positivity
    _ = Fintype.card G * ((R : ℝ) * C * supportNorm wB f) := by
      rw [← Finset.sum_mul, hwSum]
      ring

end

open scoped BigOperators
variable {G A B : Type} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [DecidableEq G] [DecidableEq A] [DecidableEq B]
  [MulAction G A] [MulAction G B]

omit [Fintype G] [DecidableEq G] [DecidableEq A] in
lemma sum_smul (g : G) (f : A → ℝ) : (∑ a, f (g • a)) = ∑ a, f a := by
  exact (Equiv.sum_comp (MulAction.toPerm g) f)

omit [Fintype A] [DecidableEq G] [DecidableEq A] in
lemma action_average_eq (a b : A) (h : ∃ g : G, g • a = b) (f : A → ℝ) :
    (∑ g : G, f (g • a)) = ∑ g : G, f (g • b) := by
  obtain ⟨h, rfl⟩ := h
  simpa [mul_smul] using (Equiv.sum_comp (Equiv.mulRight h) (fun g : G => f (g • a))).symm

omit [DecidableEq G] [DecidableEq A] in
lemma transitive_average (a : A) (hTrans : ∀ b, ∃ g : G, g • a = b) (f : A → ℝ) :
    (Fintype.card A : ℝ) * (∑ g : G, f (g • a)) =
      Fintype.card G * ∑ b : A, f b := by
  calc
    (Fintype.card A : ℝ) * (∑ g : G, f (g • a)) = ∑ b : A, ∑ g : G, f (g • b) := by
      symm
      have h (b : A) := (action_average_eq a b (hTrans b) f).symm
      simp_rw [h]
      simp
    _ = ∑ g : G, ∑ b : A, f (g • b) := Finset.sum_comm
    _ = Fintype.card G * ∑ b : A, f b := by simp [sum_smul]

omit [Fintype B] [DecidableEq G] [DecidableEq A] in
theorem occupation_le_incidence (I : A → B → Prop) [DecidableRel I]
    (hI : ∀ (g : G) a b, I a b → I (g • a) (g • b))
    (hTrans : ∀ a a' : A, ∃ g : G, g • a = a')
    (b : B) (a : A) (hab : I a b) (t : B) :
    (Fintype.card A : ℝ) * ((Finset.univ.filter (fun g : G => g • b = t)).card : ℝ) ≤
      Fintype.card G * ((Finset.univ.filter (fun a : A => I a t)).card : ℝ) := by
  have hh : (∑ g : G, if g • b = t then (1 : ℝ) else 0) ≤
      ∑ g : G, if I (g • a) t then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro g _
    by_cases ht : g • b = t
    · have hi := hI g a b hab
      simp only [ht] at hi
      simp [ht, hi]
    · simp only [ht, ↓reduceIte]
      split_ifs <;> norm_num
  have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (Fintype.card A) : (0 : ℝ) ≤ _)
  rw [transitive_average a (hTrans a) (fun a => if I a t then (1 : ℝ) else 0)] at hh'
  simpa only [Finset.sum_boole] using hh'

end CoboundaryExpanders.Averaging

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V : Type} [DecidableEq V]

def eval (f : Finset V → k) : Raw V →ₗ[k] k := Finsupp.linearCombination k f

omit [DecidableEq V] in
@[simp] lemma eval_single (f : Finset V → k) (s : Finset V) (a : k) :
    eval f (Finsupp.single s a) = a * f s := by simp [eval, smul_eq_mul]

omit [DecidableEq V] in
lemma eval_support (f : Finset V → k) (c : Raw V) :
    eval f c = ∑ s ∈ c.support, f s := by
  rw [eval, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hn : c s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have ho : c s = 1 := by
    have he : ∀ a : k, a = 0 ∨ a = 1 := by decide
    exact (he (c s)).resolve_left hn
  simp [ho]

def delta (f : Finset V → k) (s : Finset V) : k :=
  eval f (rawBoundary (Finsupp.single s 1))

lemma eval_delta (f : Finset V → k) (c : Raw V) :
    eval (delta f) c = eval f (rawBoundary c) := by
  have hh : eval (delta f) = (eval f).comp rawBoundary := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, eval_single]
    have hsingle : Finsupp.single s a = a • Finsupp.single s (1 : k) := by simp
    rw [hsingle, map_smul, map_smul]
    rfl
  exact LinearMap.congr_fun hh c

@[simp] lemma delta_eq_sum (f : Finset V → k) (s : Finset V) :
    delta f s = ∑ v ∈ s, f (s.erase v) := by simp [delta]

@[simp] lemma delta_delta (f : Finset V → k) (s : Finset V) : delta (delta f) s = 0 := by
  rw [delta, eval_delta]
  change eval f ((rawBoundary.comp rawBoundary) (Finsupp.single s 1)) = 0
  rw [rawBoundary_squared]
  simp

def correction (T : Raw V →ₗ[k] Raw V) (f : Finset V → k) (s : Finset V) : k :=
  eval f (T (Finsupp.single s 1))

omit [DecidableEq V] in
lemma eval_correction (T : Raw V →ₗ[k] Raw V) (f : Finset V → k) (c : Raw V) :
    eval (correction T f) c = eval f (T c) := by
  have hh : eval (correction T f) = (eval f).comp T := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, eval_single]
    have hsingle : Finsupp.single s a = a • Finsupp.single s (1 : k) := by simp
    rw [hsingle, map_smul, map_smul]
    rfl
  exact LinearMap.congr_fun hh c

lemma correction_identity {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (f : Finset V → k) (s : Finset V) (hs : s ∈ X.faces) (hn : s.card ≤ n) :
    f s + delta (correction H.hom f) s = eval (delta f) (H.hom (Finsupp.single s 1)) := by
  have hh := congrArg (eval f) (H.contraction s hs hn)
  rw [map_add, eval_single, one_mul, ← eval_delta f (H.hom (Finsupp.single s 1)),
    ← eval_correction H.hom f (rawBoundary (Finsupp.single s 1))] at hh
  change _ + delta (correction H.hom f) s = f s at hh
  rw [← hh]
  simp [add_assoc, CharTwo.add_self_eq_zero]

variable {G : Type} [Group G] [MulAction G V]
open scoped Pointwise

def pull (g : G) (f : Finset V → k) (s : Finset V) : k := f (g • s)

lemma eval_pull (g : G) (f : Finset V → k) (c : Raw V) :
    eval (pull g f) c = eval f (relabel (fun v => g • v) c) := by
  have hh : eval (pull g f) = (eval f).comp (relabel (fun v => g • v)) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp [pull, Finset.image_smul]
  exact LinearMap.congr_fun hh c

lemma delta_pull (g : G) (f : Finset V → k) (s : Finset V) :
    delta (pull g f) s = pull g (delta f) s := by
  rw [delta, eval_pull]
  have hh := LinearMap.congr_fun (relabel_boundary (fun v : V => g • v)
    (MulAction.injective g)) (Finsupp.single s 1)
  simp only [LinearMap.comp_apply, relabel_single, Finset.image_smul] at hh
  rw [← hh]
  rfl

@[simp] lemma pull_inv (g : G) (f : Finset V → k) : pull g (pull g⁻¹ f) = f := by
  funext s
  simp [pull]

def movedCorrection (g : G) (T : Raw V →ₗ[k] Raw V) (f : Finset V → k) : Finset V → k :=
  pull g⁻¹ (correction T (pull g f))

lemma movedCorrection_identity {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (g : G) (f : Finset V → k) (s : Finset V) (hs : s ∈ X.faces) (hn : s.card ≤ n) :
    f (g • s) + delta (movedCorrection g H.hom f) (g • s) =
      ∑ t ∈ (H.hom (Finsupp.single s 1)).support, delta f (g • t) := by
  have hh := correction_identity H (pull g f) s hs hn
  have he : delta (movedCorrection g H.hom f) (g • s) =
      delta (correction H.hom (pull g f)) s := by
    rw [movedCorrection, delta_pull]
    simp [pull]
  rw [he]
  simpa only [pull, funext (delta_pull g f), eval_support] using hh

end CoboundaryExpanders.InfiniteChains.Cone

namespace CoboundaryExpanders.InfiniteChains.FiniteWeights

section
open Attachment Cone Averaging
open scoped BigOperators Pointwise
variable {V : Type} [Fintype V] [DecidableEq V]

def weight (X : CoboundaryExpanders.InfiniteChains.Complex V) (N r : ℕ) (s : Finset V) : ℝ :=
  if s ∈ level X r then cofaces X N s / ((N.choose r : ℝ) * (level X N).card) else 0

lemma weight_nonneg (X : CoboundaryExpanders.InfiniteChains.Complex V) (N r : ℕ) (s : Finset V) : 0 ≤ weight X N r s := by
  unfold weight
  split_ifs <;> positivity

lemma cofaces_eq_sum (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (s : Finset V) :
    (cofaces X N s : ℝ) = ∑ t ∈ level X N, if s ⊆ t then (1 : ℝ) else 0 := by
  simp [cofaces]

lemma subsets_level (X : CoboundaryExpanders.InfiniteChains.Complex V) {N r : ℕ} (t : Finset V) (ht : t ∈ level X N) :
    (level X r).filter (fun s => s ⊆ t) = t.powersetCard r := by
  ext s
  simp only [Finset.mem_filter, mem_level, Finset.mem_powersetCard]
  constructor
  · intro h; exact ⟨h.2,h.1.2⟩
  · intro h; exact ⟨⟨X.downward (mem_level X N t |>.mp ht).1 h.1,h.2⟩,h.1⟩

lemma sum_cofaces (X : CoboundaryExpanders.InfiniteChains.Complex V) (N r : ℕ) :
    (∑ s ∈ level X r, (cofaces X N s : ℝ)) =
      (N.choose r : ℝ) * (level X N).card := by
  simp_rw [cofaces_eq_sum]
  rw [Finset.sum_comm]
  have h (t : Finset V) (ht : t ∈ level X N) :
      (∑ s ∈ level X r, if s ⊆ t then (1 : ℝ) else 0) = N.choose r := by
    rw [Finset.sum_boole, subsets_level X t ht, Finset.card_powersetCard,
      (mem_level X N t).mp ht |>.2]
  rw [Finset.sum_congr rfl h]
  simp [mul_comm]

lemma weight_sum (X : CoboundaryExpanders.InfiniteChains.Complex V) {N r : ℕ} (hr : r ≤ N) (hN : (level X N).Nonempty) :
    ∑ s : Finset V, weight X N r s = 1 := by
  have hc : (N.choose r : ℝ) * (level X N).card ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne')
      (Nat.cast_ne_zero.mpr hN.card_pos.ne')
  simp only [weight, ← Finset.sum_filter]
  have he : Finset.univ.filter (fun s : Finset V => s ∈ level X r) = level X r := by ext; simp
  rw [he, ← Finset.sum_div, sum_cofaces, div_self hc]

variable {G : Type} [Group G] [Fintype G] [MulAction G V]

def Invariant (G : Type) [Group G] [MulAction G V] (X : CoboundaryExpanders.InfiniteChains.Complex V) : Prop :=
  ∀ (g : G) s, s ∈ X.faces → g • s ∈ X.faces

omit [Fintype V] [Fintype G] in
lemma invariant_iff {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (g : G) (s : Finset V) :
    g • s ∈ X.faces ↔ s ∈ X.faces := by
  constructor
  · intro h
    simpa using hX g⁻¹ (g • s) h
  · exact hX g s

omit [Fintype G] in
lemma level_smul_iff {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (g : G) (r : ℕ) (s : Finset V) :
    g • s ∈ level X r ↔ s ∈ level X r := by
  simp only [mem_level, invariant_iff hX, Finset.card_smul_finset]

omit [Fintype G] in
lemma cofaces_smul {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (g : G) (N : ℕ) (s : Finset V) :
    cofaces X N (g • s) = cofaces X N s := by
  unfold cofaces
  symm
  apply Finset.card_bij (fun t _ => g • t)
  · intro t ht
    exact Finset.mem_filter.mpr ⟨(level_smul_iff hX g N t).mpr (Finset.mem_filter.mp ht).1,
      Finset.smul_finset_subset_smul_finset (Finset.mem_filter.mp ht).2⟩
  · intro t ht u hu he
    exact MulAction.injective g he
  · intro t ht
    refine ⟨g⁻¹ • t, ?_, by simp⟩
    refine Finset.mem_filter.mpr ⟨(level_smul_iff hX g⁻¹ N t).mpr (Finset.mem_filter.mp ht).1, ?_⟩
    have hh := Finset.smul_finset_subset_smul_finset (a := g⁻¹) (Finset.mem_filter.mp ht).2
    simpa using hh

omit [Fintype G] in
lemma weight_smul {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (g : G) (N r : ℕ) (s : Finset V) :
    weight X N r (g • s) = weight X N r s := by
  simp only [weight, level_smul_iff hX, cofaces_smul hX]

omit [Fintype G] in
lemma norm_pull {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (g : G) (N r : ℕ) (f : Finset V → k) :
    supportNorm (weight X N r) (pull g f) = supportNorm (weight X N r) f := by
  classical
  unfold supportNorm
  apply Finset.sum_bij (fun s _ => g • s)
  · intro s hs; exact Finset.mem_univ _
  · intro s hs t ht he; exact MulAction.injective g he
  · intro s hs; exact ⟨g⁻¹ • s, Finset.mem_univ _, by simp⟩
  · intro s hs; simp only [pull, weight_smul hX]; rfl

@[instance_reducible]
def faceAction {X : CoboundaryExpanders.InfiniteChains.Complex V} (hX : Invariant G X) (r : ℕ) : MulAction G (X.Face r) where
  smul g s := ⟨g • s.val, hX g s.val s.property.1, by simp [s.property.2]⟩
  one_smul s := Subtype.ext (one_smul _ _)
  mul_smul g h s := Subtype.ext (mul_smul g h s.val)

end

open Attachment Cone Averaging
open scoped BigOperators Pointwise
variable {V : Type} [Fintype V] [DecidableEq V]

instance faceFintype (X : CoboundaryExpanders.InfiniteChains.Complex V) (r : ℕ) : Fintype (X.Face r) := Fintype.ofFinite _

omit [DecidableEq V] in
lemma card_faces (X : CoboundaryExpanders.InfiniteChains.Complex V) (r : ℕ) : Fintype.card (X.Face r) = (level X r).card := by
  let e : X.Face r ≃ ↥(level X r) :=
    { toFun := fun s => ⟨s.val, (mem_level X r s.val).mpr s.property⟩
      invFun := fun s => ⟨s.val,(mem_level X r s.val).mp s.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

lemma count_incident (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (s : Finset V) :
    (Finset.univ.filter (fun t : X.Face N => s ⊆ t.val)).card = cofaces X N s := by
  unfold cofaces
  apply Finset.card_bij (fun t _ => t.val)
  · intro t ht
    exact Finset.mem_filter.mpr ⟨(mem_level X N t.val).mpr t.property,(Finset.mem_filter.mp ht).2⟩
  · intro t ht u hu he; exact Subtype.ext he
  · intro t ht
    refine ⟨⟨t,(mem_level X N t).mp (Finset.mem_filter.mp ht).1⟩,?_,rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp ht).2

variable {G : Type} [Group G] [Fintype G] [DecidableEq G] [MulAction G V]

omit [DecidableEq G] in
lemma occupancy {X : CoboundaryExpanders.InfiniteChains.Complex V} {N r : ℕ} (hX : Invariant G X) (hP : Pure X N)
    (hTrans : ∀ a b : X.Face N, ∃ g : G, g • a.val = b.val)
    (hr : r ≤ N) (s : Finset V) (hs : s ∈ level X r) (t : Finset V) :
    ((Finset.univ.filter (fun g : G => g • s = t)).card : ℝ) ≤
      Fintype.card G * (N.choose r : ℝ) * weight X N r t := by
  classical
  by_cases ht : t ∈ level X r
  · obtain ⟨a,ha,hsa⟩ := hP.2 s ((mem_level X r s).mp hs).1
    let aa : X.Face N := ⟨a, (mem_level X N a).mp ha⟩
    let : MulAction G (X.Face N) := faceAction hX N
    have htrans : ∀ a b : X.Face N, ∃ g : G, g • a = b := by
      intro a b
      obtain ⟨g,hg⟩ := hTrans a b
      exact ⟨g, Subtype.ext hg⟩
    have hi : ∀ (g : G) (a : X.Face N) (b : Finset V), b ⊆ a.val →
        g • b ⊆ (g • a).val := by
      intro g a b hb
      exact Finset.smul_finset_subset_smul_finset hb
    have hh := occupation_le_incidence (fun a : X.Face N => fun b : Finset V => b ⊆ a.val)
      hi htrans s aa hsa t
    rw [card_faces, count_incident] at hh
    have hc : 0 < ((level X N).card : ℝ) := Nat.cast_pos.mpr hP.1.card_pos
    have hb : (N.choose r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne'
    rw [weight, ite_eq_left ht]
    apply le_of_mul_le_mul_left _ hc
    calc
      ((level X N).card : ℝ) * ((Finset.univ.filter (fun g : G => g • s = t)).card : ℝ) ≤
          Fintype.card G * (cofaces X N t : ℝ) := hh
      _ = (level X N).card * (Fintype.card G * (N.choose r : ℝ) *
          (cofaces X N t / ((N.choose r : ℝ) * (level X N).card))) := by
        field_simp
  · have hempty : Finset.univ.filter (fun g : G => g • s = t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have he := (Finset.mem_filter.mp hg).2
      have hmem := (level_smul_iff hX g r s).mpr hs
      exact ht (he ▸ hmem)
    simp [hempty, weight, ht]

omit [DecidableEq G] in
theorem weighted_correction {X : CoboundaryExpanders.InfiniteChains.Complex V} {N n r R : ℕ}
    (hX : Invariant G X) (hP : Pure X N)
    (hTrans : ∀ a b : X.Face N, ∃ g : G, g • a.val = b.val)
    (H : BoundedCone X n R) (hr : r ≤ n) (hrN : r+1 ≤ N)
    (f : Finset V → k) :
    ∃ b : Finset V → k,
      supportNorm (weight X N r) (fun s => f s + delta b s) ≤
        (R : ℝ) * (N.choose (r+1) : ℝ) * supportNorm (weight X N (r+1)) (delta f) := by
  classical
  let L : Finset V → Finset (Finset V) := fun s =>
    if s ∈ level X r then (H.hom (Finsupp.single s 1)).support else ∅
  have hL (s : Finset V) : (L s).card ≤ R := by
    dsimp only [L]
    split_ifs with hs
    · obtain ⟨hs',he⟩ := (mem_level X r s).mp hs
      exact H.bound s hs' (by omega)
    · simp
  have hLS (s t : Finset V) (ht : t ∈ L s) : t ∈ level X (r+1) := by
    dsimp only [L] at ht
    split_ifs at ht with hs
    · obtain ⟨hs',he⟩ := (mem_level X r s).mp hs
      have hh := ((mem_supported _ _).mp (H.support s hs' (by omega))) t (Finsupp.mem_support_iff.mp ht)
      exact (mem_level X (r+1) t).mpr ⟨hh.1, by simpa [he] using hh.2⟩
    · simp at ht
  obtain ⟨g,hg⟩ := exists_small_dual (G := G)
    (weight X N r) (weight_nonneg X N r) (weight_sum X (by omega) hP.1)
    (weight X N (r+1)) (weight_nonneg X N (r+1))
    (fun g t => g • t) (N.choose (r+1) : ℝ) (Nat.cast_nonneg _)
    L R hL (fun s t ht u => occupancy hX hP hTrans hrN t (hLS s t ht) u)
    (delta f)
  refine ⟨movedCorrection g H.hom f, ?_⟩
  rw [← norm_pull hX g]
  have he : supportNorm (weight X N r)
      (pull g (fun s => f s + delta (movedCorrection g H.hom f) s)) =
      supportNorm (weight X N r) (fun s => ∑ t ∈ L s, delta f (g • t)) := by
    unfold supportNorm
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s ∈ level X r
    · obtain ⟨hs',hsr⟩ := (mem_level X r s).mp hs
      have hh := movedCorrection_identity H g f s hs' (by omega)
      simp only [pull, L, ite_eq_left hs, hh]
    · simp [weight, hs]
  exact he ▸ hg

end CoboundaryExpanders.InfiniteChains.FiniteWeights

end

end OAI
