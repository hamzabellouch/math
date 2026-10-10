import OAI.Combinatorics.PlanarL1.Clipping
import OAI.Combinatorics.PlanarL1.Gluing

namespace OAI

section

namespace PlanarL1.Increment
open Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

noncomputable def clamp (a b t : ℝ) : ℝ := min b (max a t)

lemma clamp_bounds {a b t : ℝ} (hab : a ≤ b) : a ≤ clamp a b t ∧ clamp a b t ≤ b :=
  ⟨le_min hab (le_max_left _ _),min_le_left _ _⟩

lemma clamp_lipschitz (a b : ℝ) : LipschitzWith 1 (clamp a b) :=
  (LipschitzWith.id.const_max a).const_min b

lemma clamp_eq {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b) : clamp a b t = t := by
  rw [clamp,max_eq_right hat,min_eq_right htb]

lemma clamp_left {a b t : ℝ} (hab : a ≤ b) (ht : t ≤ a) : clamp a b t = a := by
  rw [clamp,max_eq_left ht,min_eq_right hab]

lemma clamp_right {a b t : ℝ} (ht : b ≤ t) : clamp a b t = b := by
  exact min_eq_left (ht.trans (le_max_right _ _))

noncomputable def quadratic (a b c d t : ℝ) : ℝ :=
  clamp a b t * (c-clamp a b t)/d

lemma quadratic_lipschitz {a b c d : ℝ} {K : ℝ≥0} (hab : a ≤ b) (hd : 0 < d)
    (hlo : -(K:ℝ)*d ≤ c-2*b) (hhi : c-2*a ≤ (K:ℝ)*d) :
    LipschitzWith K (quadratic a b c d) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨hxa,hxb⟩ := clamp_bounds (t := x) hab
  obtain ⟨hya,hyb⟩ := clamp_bounds (t := y) hab
  have hf : |c-clamp a b x-clamp a b y| ≤ (K:ℝ)*d := by
    rw [abs_le]
    constructor <;> linarith
  have hc := (clamp_lipschitz a b).dist_le_mul x y
  rw [Real.dist_eq,NNReal.coe_one,one_mul] at hc
  rw [Real.dist_eq]
  have he : quadratic a b c d x-quadratic a b c d y =
      (clamp a b x-clamp a b y)*(c-clamp a b x-clamp a b y)/d := by
    unfold quadratic
    ring
  rw [he,abs_div,abs_mul,abs_of_pos hd]
  calc
    _ ≤ (|clamp a b x-clamp a b y| *((K:ℝ)*d))/d :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf (abs_nonneg _)) hd.le
    _ = (K:ℝ)*|clamp a b x-clamp a b y| := by field_simp
    _ ≤ (K:ℝ)*dist x y := mul_le_mul_of_nonneg_left hc K.coe_nonneg

noncomputable def splice (c : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ := if t ≤ c then f t else g t

lemma splice_lipschitz {K : ℝ≥0} {c : ℝ} {f g : ℝ → ℝ}
    (hf : LipschitzWith K f) (hg : LipschitzWith K g) (he : f c = g c) :
    LipschitzWith K (splice c f g) := by
  have h : LipschitzWith K ((Iic c).piecewise f g) := Gluing.lipschitz_piecewise isClosed_Iic
    hg hf.lipschitzOnWith (by simpa only [frontier_Iic,eqOn_singleton] using he)
  exact h

noncomputable def low (a t : ℝ) : ℝ := -quadratic a (2*a) a a t
noncomputable def high (r t : ℝ) : ℝ := splice (8*r) id (quadratic (8*r) (10*r) (10*r) (2*r)) t
noncomputable def positivePart (a r t : ℝ) : ℝ := splice (2*a) (low a) (high r) t
noncomputable def scalar (a r t : ℝ) : ℝ := splice 0 (fun t => -positivePart a r (-t)) (positivePart a r) t

lemma low_lipschitz {a : ℝ} (ha : 0 < a) : LipschitzWith 6 (low a) := by
  have h : LipschitzWith 6 (quadratic a (2*a) a a) :=
    quadratic_lipschitz (by linarith) ha (by norm_num; linarith) (by norm_num; linarith)
  exact h.neg

lemma high_lipschitz {r : ℝ} (hr : 0 < r) : LipschitzWith 6 (high r) := by
  apply splice_lipschitz (LipschitzWith.id.weaken (by norm_num))
  · exact quadratic_lipschitz (by linarith) (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  · dsimp only [id,quadratic]
    rw [clamp_eq (by rfl) (by linarith)]
    field_simp
    ring

lemma positive_zero {a r t : ℝ} (ha : 0 < a) (ht : t ≤ a) : positivePart a r t = 0 := by
  rw [positivePart,splice,ite_eq_left (by linarith),low,quadratic,clamp_left (by linarith) ht]
  ring

lemma positive_plateau {a r t : ℝ} (ha : 0 < a) (hl : 2*a ≤ t) (hu : t ≤ 8*r) :
    positivePart a r t = t := by
  by_cases he : t = 2*a
  · rw [positivePart,splice,ite_eq_left (by linarith),low,quadratic,clamp_right hl,he]
    field_simp
    ring
  · rw [positivePart,splice,ite_eq_right (by intro h; exact he (le_antisymm h hl)),high,splice,ite_eq_left hu]
    rfl

lemma positive_lipschitz {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) :
    LipschitzWith 6 (positivePart a r) := by
  apply splice_lipschitz (low_lipschitz ha) (high_lipschitz hr)
  rw [low,quadratic,clamp_right (le_refl _),high,splice,ite_eq_left har]
  dsimp only [id]
  field_simp
  ring

lemma scalar_lipschitz {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) :
    LipschitzWith 6 (scalar a r) := by
  have hp := positive_lipschitz ha hr har
  have hn : LipschitzWith 6 (fun t => -positivePart a r (-t)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_neg_neg] using hp.dist_le_mul (-x) (-y)
  apply splice_lipschitz hn hp
  simp only [neg_zero,positive_zero ha (by linarith : (0:ℝ) ≤ a)]

lemma positive_far_zero {a r t : ℝ} (hr : 0 < r) (har : 2*a ≤ 8*r)
    (ht : 10*r ≤ t) : positivePart a r t = 0 := by
  rw [positivePart,splice,ite_eq_right (by linarith),high,splice,ite_eq_right (by linarith),
    quadratic,clamp_right ht]
  ring

lemma positive_nonneg {a r t : ℝ} (ha : 0 < a) (hr : 0 < r)
    (ht : 0 ≤ t) : 0 ≤ positivePart a r t := by
  unfold positivePart splice
  split_ifs with h
  · obtain ⟨hl,hu⟩ := clamp_bounds (t := t) (show a ≤ 2*a by linarith)
    unfold low quadratic
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) ha.le)
  · unfold high splice
    split_ifs with h'
    · exact ht
    · obtain ⟨hl,hu⟩ := clamp_bounds (t := t) (show 8*r ≤ 10*r by linarith)
      unfold quadratic
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

lemma positive_le {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) :
    positivePart a r t ≤ 10*r := by
  unfold positivePart splice
  split_ifs with h
  · obtain ⟨hl,hu⟩ := clamp_bounds (t := t) (show a ≤ 2*a by linarith)
    have hc : clamp a (2*a) t * (clamp a (2*a) t-a) ≤ 2*a*a := by
      nlinarith [sq_nonneg (clamp a (2*a) t-2*a)]
    unfold low quadratic
    calc
      _ = (clamp a (2*a) t * (clamp a (2*a) t-a))/a := by ring
      _ ≤ (2*a*a)/a := div_le_div_of_nonneg_right hc ha.le
      _ = 2*a := by field_simp
      _ ≤ 10*r := by linarith
  · unfold high splice
    split_ifs with h'
    · dsimp
      linarith
    · obtain ⟨hl,hu⟩ := clamp_bounds (t := t) (show 8*r ≤ 10*r by linarith)
      unfold quadratic
      rw [div_le_iff₀ (by linarith : 0 < 2*r)]
      nlinarith [sq_nonneg (clamp (8*r) (10*r) t-8*r)]

lemma scalar_support {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r)
    (hne : scalar a r t ≠ 0) : a < |t| ∧ |t| < 10*r := by
  by_cases ht : t ≤ 0
  · have he : |t| = -t := abs_of_nonpos ht
    rw [scalar,splice,ite_eq_left ht,neg_ne_zero] at hne
    rw [he]
    constructor
    · exact lt_of_not_ge (fun h => hne (positive_zero ha h))
    · exact lt_of_not_ge (fun h => hne (positive_far_zero hr har h))
  · have he : |t| = t := abs_of_pos (lt_of_not_ge ht)
    rw [scalar,splice,ite_eq_right ht] at hne
    rw [he]
    constructor
    · exact lt_of_not_ge (fun h => hne (positive_zero ha h))
    · exact lt_of_not_ge (fun h => hne (positive_far_zero hr har h))

lemma scalar_magnitude {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) :
    |scalar a r t| ≤ 10*r := by
  unfold scalar splice
  split_ifs with ht
  · rw [abs_neg,abs_of_nonneg (positive_nonneg ha hr (by linarith))]
    exact positive_le ha hr har
  · rw [abs_of_nonneg (positive_nonneg ha hr (by linarith))]
    exact positive_le ha hr har

lemma scalar_plateau {a r t : ℝ} (ha : 0 < a) (hl : 2*a ≤ |t|) (hu : |t| ≤ 8*r) :
    scalar a r t = t := by
  unfold scalar splice
  split_ifs with ht
  · dsimp only
    rw [abs_of_nonpos ht] at hl hu
    rw [positive_plateau ha hl hu,neg_neg]
  · rw [abs_of_pos (by linarith)] at hl hu
    exact positive_plateau ha hl hu

section Taper
variable {X : Type*} [PseudoMetricSpace X]
open Metric

noncomputable def taper (S : Set X) (r : ℝ) (x : X) : ℝ :=
  if S.Nonempty then min 1 (infDist x S/r) else 1

lemma taper_bounds {S : Set X} {r : ℝ} (hr : 0 < r) (x : X) :
    0 ≤ taper S r x ∧ taper S r x ≤ 1 := by
  unfold taper
  split_ifs
  · exact ⟨le_min (by norm_num) (div_nonneg infDist_nonneg hr.le),min_le_left _ _⟩
  · norm_num

lemma taper_difference {S : Set X} {r : ℝ} (hr : 0 < r) (x y : X) :
    |taper S r x-taper S r y| ≤ dist x y/r := by
  by_cases hS : S.Nonempty
  · simp only [taper,hS,ite_true]
    have h := (LipschitzWith.id.const_min (1:ℝ)).dist_le_mul (infDist x S/r) (infDist y S/r)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,id_eq] at h
    have hd := (lipschitz_infDist_pt S).dist_le_mul x y
    rw [Real.dist_eq,NNReal.coe_one,one_mul] at hd
    calc
      _ ≤ |infDist x S/r-infDist y S/r| := h
      _ = |infDist x S-infDist y S|/r := by rw [← sub_div,abs_div,abs_of_pos hr]
      _ ≤ dist x y/r := div_le_div_of_nonneg_right hd hr.le
  · simp only [taper,hS,ite_false,sub_self,abs_zero]
    exact div_nonneg dist_nonneg hr.le

lemma taper_zero {S : Set X} {r : ℝ} {x : X} (hx : x ∈ S) : taper S r x = 0 := by
  simp only [taper,show S.Nonempty from ⟨x,hx⟩,ite_true,infDist_zero_of_mem hx,
    zero_div,min_eq_right (by norm_num : (0:ℝ) ≤ 1)]

noncomputable def update (S : Set X) (a r : ℝ) (t : X → ℝ) (x : X) : ℝ :=
  scalar a r (t x)*taper S r x

lemma update_lipschitz {S : Set X} {a r : ℝ} {t : X → ℝ}
    (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) (ht : LipschitzWith 4 t) :
    LipschitzWith 34 (update S a r t) := by
  have hs : LipschitzWith 24 (fun x => scalar a r (t x)) := by
    simpa only [Function.comp_def,show (6:ℝ≥0)*4=24 by norm_num] using
      (scalar_lipschitz ha hr har).comp ht
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy := hs.dist_le_mul x y
  rw [Real.dist_eq] at hxy
  norm_num at hxy ⊢
  obtain ⟨hfx,hfx'⟩ := taper_bounds (S := S) hr x
  have he : update S a r t x-update S a r t y =
      (scalar a r (t x)-scalar a r (t y))*taper S r x+
      scalar a r (t y)*(taper S r x-taper S r y) := by unfold update; ring
  rw [Real.dist_eq,he]
  calc
    _ ≤ |(scalar a r (t x)-scalar a r (t y))*taper S r x|+
        |scalar a r (t y)*(taper S r x-taper S r y)| := abs_add_le _ _
    _ = |scalar a r (t x)-scalar a r (t y)| *taper S r x+
        |scalar a r (t y)| *|taper S r x-taper S r y| := by rw [abs_mul,abs_mul,abs_of_nonneg hfx]
    _ ≤ (24*dist x y)*1+(10*r)*(dist x y/r) := by
      exact add_le_add (mul_le_mul hxy hfx' hfx (by positivity))
        (mul_le_mul (scalar_magnitude ha hr har) (taper_difference hr x y)
          (abs_nonneg _) (by positivity))
    _ = 34*dist x y := by field_simp; ring

lemma update_magnitude {S : Set X} {a r : ℝ} {t : X → ℝ}
    (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) (x : X) :
    |update S a r t x| ≤ 10*r := by
  obtain ⟨h,h'⟩ := taper_bounds (S := S) hr x
  rw [update,abs_mul,abs_of_nonneg h]
  calc
    _ ≤ (10*r)*1 := mul_le_mul (scalar_magnitude ha hr har) h' h (by positivity)
    _ = 10*r := mul_one _

lemma update_zero {S : Set X} {a r : ℝ} {t : X → ℝ} {x : X} (hx : x ∈ S) :
    update S a r t x = 0 := by rw [update,taper_zero hx,mul_zero]

lemma update_support {S : Set X} {a r : ℝ} {t : X → ℝ}
    (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) {x : X}
    (hx : update S a r t x ≠ 0) : a < |t x| ∧ |t x| < 10*r :=
  scalar_support ha hr har (left_ne_zero_of_mul hx)

lemma sum_lipschitz_sparse {I : Type*} (A : Finset I) {f : I → X → ℝ} {K : ℝ≥0}
    (hf : ∀ i ∈ A, LipschitzWith K (f i))
    (hs : ∀ x, (A.filter (fun i => f i x ≠ 0)).card ≤ 1) :
    LipschitzWith (2*K) (fun x => ∑ i ∈ A, f i x) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let T := (A.filter (fun i => f i x ≠ 0)) ∪ (A.filter (fun i => f i y ≠ 0))
  have hTA : T ⊆ A := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hc : T.card ≤ 2 := (Finset.card_union_le _ _).trans (by linarith [hs x,hs y])
  have he : ∑ i ∈ A, (f i x-f i y) = ∑ i ∈ T, (f i x-f i y) := by
    symm
    apply Finset.sum_subset hTA
    intro i hi hnot
    have hix : f i x = 0 := by
      by_contra h
      exact hnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi,h⟩))
    have hiy : f i y = 0 := by
      by_contra h
      exact hnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,h⟩))
    rw [hix,hiy,sub_self]
  rw [Real.dist_eq,← Finset.sum_sub_distrib,he]
  calc
    _ ≤ ∑ i ∈ T, |f i x-f i y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ T, (K:ℝ)*dist x y := Finset.sum_le_sum (fun i hi =>
      by simpa only [Real.dist_eq] using (hf i (hTA hi)).dist_le_mul x y)
    _ = (T.card:ℝ)*((K:ℝ)*dist x y) := by simp
    _ ≤ 2*((K:ℝ)*dist x y) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = ((2*K:ℝ≥0):ℝ)*dist x y := by simp; ring

lemma update_sparse {I : Type*} (A : Finset I) {c : ℝ} {r : I → ℝ} {t : X → ℝ}
    {S : I → Set X} (hc : 0 < c) (hcr : c ≤ 4)
    (hr : ∀ i ∈ A, 0 < r i)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → 10*r i ≤ c*r j ∨ 10*r j ≤ c*r i)
    (x : X) : (A.filter (fun i => update (S i) (c*r i) (r i) t x ≠ 0)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiA,hi⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjA,hj⟩ := Finset.mem_filter.mp hj
  by_contra hij
  obtain ⟨hil,hiu⟩ := update_support (mul_pos hc (hr i hiA)) (hr i hiA)
    (by nlinarith [hr i hiA]) hi
  obtain ⟨hjl,hju⟩ := update_support (mul_pos hc (hr j hjA)) (hr j hjA)
    (by nlinarith [hr j hjA]) hj
  rcases hsep i hiA j hjA hij with h | h <;> linarith

lemma lifetime_lipschitz {I : Type*} (A : Finset I) {c : ℝ} {r : I → ℝ} {t : X → ℝ}
    {S : I → Set X} (hc : 0 < c) (hcr : c ≤ 4)
    (hr : ∀ i ∈ A, 0 < r i) (ht : LipschitzWith 4 t)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → 10*r i ≤ c*r j ∨ 10*r j ≤ c*r i) :
    LipschitzWith 68 (fun x => ∑ i ∈ A, update (S i) (c*r i) (r i) t x) := by
  have h := sum_lipschitz_sparse A (K := 34)
    (f := fun i => update (S i) (c*r i) (r i) t)
    (fun i hi => update_lipschitz (mul_pos hc (hr i hi)) (hr i hi)
      (by nlinarith [hr i hi]) ht) (update_sparse A hc hcr hr hsep)
  norm_num only at h
  exact h

noncomputable def signedUpdate (e : Bool) (S : Set X) (a r : ℝ) (t : X → ℝ) (x : X) : ℝ :=
  if e then update S a r t x else -update S a r t x

lemma signed_lifetime_lipschitz {I : Type*} (A : Finset I) {c : ℝ} {r : I → ℝ} {t : X → ℝ}
    {S : I → Set X} (e : I → Bool) (hc : 0 < c) (hcr : c ≤ 4)
    (hr : ∀ i ∈ A, 0 < r i) (ht : LipschitzWith 4 t)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → 10*r i ≤ c*r j ∨ 10*r j ≤ c*r i) :
    LipschitzWith 68 (fun x => ∑ i ∈ A, signedUpdate (e i) (S i) (c*r i) (r i) t x) := by
  have hf (i) (hi : i ∈ A) : LipschitzWith 34 (signedUpdate (e i) (S i) (c*r i) (r i) t) := by
    have h := update_lipschitz (S := S i) (mul_pos hc (hr i hi)) (hr i hi)
      (by nlinarith [hr i hi]) ht
    cases e i
    · exact h.neg
    · exact h
  have he (x) : A.filter (fun i => signedUpdate (e i) (S i) (c*r i) (r i) t x ≠ 0) =
      A.filter (fun i => update (S i) (c*r i) (r i) t x ≠ 0) := by
    apply Finset.filter_congr
    intro i _
    cases e i <;> simp [signedUpdate]
  have h := sum_lipschitz_sparse A hf (fun x => by rw [he]; exact update_sparse A hc hcr hr hsep x)
  norm_num only at h
  exact h

lemma taper_one {S : Set X} {r : ℝ} {x : X} (hr : 0 < r)
    (hx : S.Nonempty → r ≤ infDist x S) : taper S r x = 1 := by
  unfold taper
  split_ifs with h
  · apply min_eq_left
    exact (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hx h)
  · rfl

lemma update_plateau {S : Set X} {a r : ℝ} {t : X → ℝ} {x : X}
    (ha : 0 < a) (hr : 0 < r) (hl : 2*a ≤ |t x|) (hu : |t x| ≤ 8*r)
    (hx : S.Nonempty → r ≤ infDist x S) : update S a r t x = t x := by
  rw [update,scalar_plateau ha hl hu,taper_one hr hx,mul_one]

end Taper

lemma opposite_sign_gain (p q : ℝ) : |q| ≤ |p+q| ∨ |q| ≤ |p-q| := by
  by_contra h
  push Not at h
  have ht := abs_sub_le (p+q) 0 (p-q)
  have he : |(p+q)-(p-q)| = 2*|q| := by
    rw [show (p+q)-(p-q) = 2*q by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [he,sub_zero,zero_sub,abs_neg] at ht
  linarith

lemma geometric_separation {r c Q : ℝ} (hr : 0 < r)
    (hQ : 1 < Q) (hsep : 10 ≤ c*Q) {i j : ℕ} (hij : i < j) :
    10*(r/Q^j) ≤ c*(r/Q^i) := by
  have hpow : Q^(i+1) ≤ Q^j := (pow_le_pow_right₀ hQ.le (Nat.succ_le_of_lt hij))
  have hpos : 0 < Q^i := pow_pos (by linarith) _
  calc
    _ ≤ 10*(r/Q^(i+1)) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hr.le (pow_pos (by linarith) _) hpow) (by norm_num)
    _ ≤ c*(r/Q^i) := by
      rw [pow_succ]
      calc
        _ ≤ (c*Q)*(r/(Q^i*Q)) := mul_le_mul_of_nonneg_right hsep
          (div_nonneg hr.le (mul_pos hpos (by linarith)).le)
        _ = c*(r/Q^i) := by field_simp


end PlanarL1.Increment



end

section

namespace PlanarL1.Increment
open scoped NNReal
variable {X : Type*} [PseudoMetricSpace X]

/-- The actual increment with an ambient-metric taper. The scalar transverse
field is measured intrinsically, while this weight may use the unrestricted
metric. -/
noncomputable def damped (a r : ℝ) (t w : X → ℝ) (x : X) : ℝ :=
  scalar a r (t x)*w x

lemma damped_lipschitz {a r : ℝ} {t w : X → ℝ}
    (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) (ht : LipschitzWith 4 t)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (hd : ∀ x y, |w x-w y| ≤ dist x y/r) :
    LipschitzWith 34 (damped a r t w) := by
  have hs : LipschitzWith 24 (fun x => scalar a r (t x)) := by
    simpa only [Function.comp_def,show (6:ℝ≥0)*4=24 by norm_num] using
      (scalar_lipschitz ha hr har).comp ht
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy := hs.dist_le_mul x y
  rw [Real.dist_eq] at hxy
  norm_num at hxy ⊢
  have he : damped a r t w x-damped a r t w y =
      (scalar a r (t x)-scalar a r (t y))*w x+
      scalar a r (t y)*(w x-w y) := by unfold damped; ring
  rw [Real.dist_eq,he]
  calc
    _ ≤ |(scalar a r (t x)-scalar a r (t y))*w x|+
        |scalar a r (t y)*(w x-w y)| := abs_add_le _ _
    _ = |scalar a r (t x)-scalar a r (t y)| *w x+
        |scalar a r (t y)| *|w x-w y| := by rw [abs_mul,abs_mul,abs_of_nonneg (hw x).1]
    _ ≤ (24*dist x y)*1+(10*r)*(dist x y/r) := by
      exact add_le_add (mul_le_mul hxy (hw x).2 (hw x).1 (by positivity))
        (mul_le_mul (scalar_magnitude ha hr har) (hd x y)
          (abs_nonneg _) (by positivity))
    _ = 34*dist x y := by field_simp; ring

noncomputable def signedDamped (e : Bool) (a r : ℝ) (t w : X → ℝ) (x : X) : ℝ :=
  if e then damped a r t w x else -damped a r t w x

omit [PseudoMetricSpace X] in
lemma signedDamped_support {e : Bool} {a r : ℝ} {t w : X → ℝ}
    (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) {x : X}
    (hx : signedDamped e a r t w x ≠ 0) : a < |t x| ∧ |t x| < 10*r := by
  have hn : damped a r t w x ≠ 0 := by
    cases e <;> simpa only [signedDamped,Bool.false_eq_true,ite_false,ite_true,neg_ne_zero] using hx
  exact scalar_support ha hr har (left_ne_zero_of_mul hn)

lemma damped_lifetime {I : Type*} (A : Finset I) {c : ℝ} {r : I → ℝ} {t : X → ℝ}
    {w : I → X → ℝ} (e : I → Bool) (hc : 0 < c) (hcr : c ≤ 4)
    (hr : ∀ i ∈ A, 0 < r i) (ht : LipschitzWith 4 t)
    (hw : ∀ i ∈ A, ∀ x, 0 ≤ w i x ∧ w i x ≤ 1)
    (hd : ∀ i ∈ A, ∀ x y, |w i x-w i y| ≤ dist x y/r i)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → 10*r i ≤ c*r j ∨ 10*r j ≤ c*r i) :
    LipschitzWith 68 (fun x => ∑ i ∈ A, signedDamped (e i) (c*r i) (r i) t (w i) x) := by
  have hf (i) (hi : i ∈ A) :
      LipschitzWith 34 (signedDamped (e i) (c*r i) (r i) t (w i)) := by
    have h := damped_lipschitz (mul_pos hc (hr i hi)) (hr i hi)
      (by nlinarith [hr i hi]) ht (hw i hi) (hd i hi)
    cases e i
    · exact h.neg
    · exact h
  have hs (x : X) : (A.filter (fun i => signedDamped (e i) (c*r i) (r i) t (w i) x ≠ 0)).card ≤ 1 := by
    classical
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨hiA,hi⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjA,hj⟩ := Finset.mem_filter.mp hj
    by_contra hij
    obtain ⟨hil,hiu⟩ := signedDamped_support (mul_pos hc (hr i hiA)) (hr i hiA)
      (by nlinarith [hr i hiA]) hi
    obtain ⟨hjl,hju⟩ := signedDamped_support (mul_pos hc (hr j hjA)) (hr j hjA)
      (by nlinarith [hr j hjA]) hj
    rcases hsep i hiA j hjA hij with h | h <;> linarith
  simpa only [show (2:ℝ≥0)*34=68 by norm_num] using sum_lipschitz_sparse A hf hs
end PlanarL1.Increment


end

section

namespace PlanarL1.Increment
open scoped NNReal
variable {X : Type*} [PseudoMetricSpace X]

lemma tapered_magnitude {a r q : ℝ} {S : Set X} {x y : X}
    (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) (hy : y ∈ S) :
    |scalar a r q*taper S r x| ≤ 10*dist x y := by
  have hb : taper S r x ≤ dist x y/r := by
    unfold taper
    rw [ite_eq_left (show S.Nonempty from ⟨y,hy⟩)]
    exact (min_le_right _ _).trans
      (div_le_div_of_nonneg_right (Metric.infDist_le_dist_of_mem hy) hr.le)
  rw [abs_mul,abs_of_nonneg (taper_bounds hr x).1]
  calc
    _ ≤ (10*r)*(dist x y/r) := mul_le_mul (scalar_magnitude ha hr har) hb
      (taper_bounds hr x).1 (by positivity)
    _ = 10*dist x y := by field_simp

lemma signed_tapered_magnitude (e : Bool) {a r q : ℝ} {S : Set X} {x y : X}
    (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) (hy : y ∈ S) :
    |if e then scalar a r q*taper S r x else -(scalar a r q*taper S r x)| ≤
      10*dist x y := by
  cases e <;> simpa only [Bool.false_eq_true,ite_false,ite_true,abs_neg] using
    tapered_magnitude ha hr har hy

end PlanarL1.Increment


end

end OAI
