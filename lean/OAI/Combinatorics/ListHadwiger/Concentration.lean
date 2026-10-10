import OAI.Combinatorics.ListHadwiger.Exchanges

namespace OAI

namespace LinearListHadwiger.FiniteConcentration
open scoped BigOperators

noncomputable def mean {α : Type} [Fintype α] (w f : α → ℝ) : ℝ := ∑ a, w a * f a

lemma mean_const {α : Type} [Fintype α] {w : α → ℝ} (hw : ∑ a, w a = 1) (c : ℝ) :
    mean w (fun _ => c) = c := by simp [mean, ← Finset.sum_mul, hw]

lemma mean_sub {α : Type} [Fintype α] (w f g : α → ℝ) :
    mean w (fun a => f a - g a) = mean w f - mean w g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_mono {α : Type} [Fintype α] {w f g : α → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hfg : ∀ a, f a ≤ g a) : mean w f ≤ mean w g := by
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hfg a) (hw a)

lemma mean_sub_const {α : Type} [Fintype α] {w : α → ℝ}
    (hw : ∑ a, w a = 1) (f : α → ℝ) (c : ℝ) :
    mean w (fun a => f a - c) = mean w f - c := by
  rw [mean_sub, mean_const hw]

lemma mean_const_sub {α : Type} [Fintype α] {w : α → ℝ}
    (hw : ∑ a, w a = 1) (f : α → ℝ) (c : ℝ) :
    mean w (fun a => c - f a) = c - mean w f := by
  rw [mean_sub, mean_const hw]

lemma centered_bound {α : Type} [Fintype α] {w g : α → ℝ} {b : ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (hg : ∀ a a', |g a - g a'| ≤ b) (a : α) : |g a - mean w g| ≤ b := by
  rw [abs_le]
  have hl := mean_mono hw (fun a' => (abs_le.mp (hg a a')).1)
  have hu := mean_mono hw (fun a' => (abs_le.mp (hg a a')).2)
  rw [mean_const hs, mean_const_sub hs] at hl
  rw [mean_const hs, mean_const_sub hs] at hu
  exact ⟨hl, hu⟩

lemma centered_mgf {α : Type} [Fintype α] {w X : α → ℝ} {b : ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (hX : mean w X = 0)
    (hb : 0 < b) (hbound : ∀ a, |X a| ≤ b) (l : ℝ) :
    mean w (fun a => Real.exp (l * X a)) ≤ Real.exp (l ^ 2 * b ^ 2 / 2) := by
  let u : α → ℝ := fun a => (b + X a) / (2 * b)
  let v : α → ℝ := fun a => (b - X a) / (2 * b)
  have hu : ∀ a, 0 ≤ u a := by
    intro a; dsimp [u]; apply div_nonneg _ (by positivity)
    linarith [(abs_le.mp (hbound a)).1]
  have hv : ∀ a, 0 ≤ v a := by
    intro a; dsimp [v]; apply div_nonneg _ (by positivity)
    linarith [(abs_le.mp (hbound a)).2]
  have huv : ∀ a, u a + v a = 1 := by
    intro a; dsimp [u, v]; field_simp; ring
  have he : ∀ a, Real.exp (l * X a) ≤
      u a * Real.exp (l * b) + v a * Real.exp (-(l * b)) := by
    intro a
    have h := convexOn_exp.2 (Set.mem_univ (l * b)) (Set.mem_univ (-(l * b)))
      (hu a) (hv a) (huv a)
    simp only [smul_eq_mul] at h
    convert h using 1
    congr 1
    dsimp [u, v]
    field_simp
    ring
  have hmu : mean w u = 1 / 2 := by
    dsimp [mean, u]
    simp_rw [← mul_div_assoc, mul_add]
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, hs]
    change (1 * b + mean w X) / (2 * b) = 1 / 2
    rw [hX]
    field_simp
    ring
  have hmv : mean w v = 1 / 2 := by
    dsimp [mean, v]
    simp_rw [← mul_div_assoc, mul_sub]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
    change (1 * b - mean w X) / (2 * b) = 1 / 2
    rw [hX]
    field_simp
    ring
  calc
    mean w (fun a => Real.exp (l * X a))
        ≤ mean w (fun a => u a * Real.exp (l * b) + v a * Real.exp (-(l * b))) :=
      mean_mono hw he
    _ = Real.cosh (l * b) := by
      simp only [mean, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
      change mean w u * Real.exp (l * b) + mean w v * Real.exp (-(l * b)) = _
      rw [hmu, hmv, Real.cosh_eq]
      ring
    _ ≤ Real.exp ((l * b) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
    _ = _ := by congr 1; ring

noncomputable def mass {α : Type} [Fintype α] {n : ℕ}
    (w : Fin n → α → ℝ) (x : Fin n → α) : ℝ := ∏ i, w i (x i)

lemma mass_nonneg {α : Type} [Fintype α] {n : ℕ} {w : Fin n → α → ℝ}
    (hw : ∀ i a, 0 ≤ w i a) (x : Fin n → α) : 0 ≤ mass w x :=
  Finset.prod_nonneg fun i _ => hw i (x i)

lemma mass_sum {α : Type} [Fintype α] {n : ℕ} {w : Fin n → α → ℝ}
    (hw : ∀ i, ∑ a, w i a = 1) : ∑ x, mass w x = 1 := by
  simp only [mass]
  rw [← Fintype.prod_sum]
  simp [hw]

lemma sum_cons {α : Type} [Fintype α] {n : ℕ} (f : (Fin (n + 1) → α) → ℝ) :
    ∑ x, f x = ∑ a, ∑ y, f (Fin.cons a y) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => α)) f]
  rw [Fintype.sum_prod_type]
  rfl

lemma mass_cons {α : Type} [Fintype α] {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (a : α) (x : Fin n → α) :
    mass w (Fin.cons a x) = w 0 a * mass (fun i => w i.succ) x := by
  simp [mass, Fin.prod_univ_succ]

lemma mean_cons {α : Type} [Fintype α] {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (f : (Fin (n + 1) → α) → ℝ) :
    mean (mass w) f = mean (w 0) (fun a => mean (mass (fun i => w i.succ))
      (fun x => f (Fin.cons a x))) := by
  simp only [mean, sum_cons, mass_cons, mul_assoc, Finset.mul_sum]

def BoundedChanges {α : Type} {n : ℕ} (f : (Fin n → α) → ℝ) (b : ℝ) : Prop :=
  ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b

lemma BoundedChanges.tail {α : Type} {n : ℕ} {f : (Fin (n + 1) → α) → ℝ} {b : ℝ}
    (h : BoundedChanges f b) (a : α) : BoundedChanges (fun x => f (Fin.cons a x)) b := by
  intro i x y hxy
  apply h i.succ
  intro j hj
  induction j using Fin.cases with
  | zero => simp
  | succ j =>
    simp only [Fin.cons_succ]
    apply hxy j
    intro he
    exact hj (congrArg Fin.succ he)

lemma BoundedChanges.head_mean {α : Type} [Fintype α] {n : ℕ}
    {f : (Fin (n + 1) → α) → ℝ} {b : ℝ} {w : Fin n → α → ℝ}
    (h : BoundedChanges f b) (hw : ∀ i a, 0 ≤ w i a) (hs : ∀ i, ∑ a, w i a = 1)
    (a a' : α) :
    |mean (mass w) (fun x => f (Fin.cons a x)) -
      mean (mass w) (fun x => f (Fin.cons a' x))| ≤ b := by
  have hd : ∀ x : Fin n → α, |f (Fin.cons a x) - f (Fin.cons a' x)| ≤ b := by
    intro x
    apply h 0
    intro j hj
    induction j using Fin.cases with
    | zero => exact (hj rfl).elim
    | succ j => simp
  rw [← mean_sub, abs_le]
  constructor
  · have hh := mean_mono (mass_nonneg hw) (fun x => (abs_le.mp (hd x)).1)
    simpa only [mean_const (mass_sum hs)] using hh
  · have hh := mean_mono (mass_nonneg hw) (fun x => (abs_le.mp (hd x)).2)
    simpa only [mean_const (mass_sum hs)] using hh

theorem bounded_changes_mgf {α : Type} [Fintype α] {n : ℕ}
    (w : Fin n → α → ℝ) (hw : ∀ i a, 0 ≤ w i a) (hs : ∀ i, ∑ a, w i a = 1)
    (f : (Fin n → α) → ℝ) {b : ℝ} (hb : 0 < b) (hf : BoundedChanges f b) (l : ℝ) :
    mean (mass w) (fun x => Real.exp (l * (f x - mean (mass w) f))) ≤
      Real.exp (n * l ^ 2 * b ^ 2 / 2) := by
  induction n with
  | zero => simp [mean, mass]
  | succ n ih =>
    let w' : Fin n → α → ℝ := fun i => w i.succ
    let g : α → ℝ := fun a => mean (mass w') (fun x => f (Fin.cons a x))
    have hmean : mean (mass w) f = mean (w 0) g := mean_cons w f
    have hg : ∀ a a', |g a - g a'| ≤ b :=
      hf.head_mean (fun i => hw i.succ) (fun i => hs i.succ)
    have hcenter : mean (w 0) (fun a => g a - mean (w 0) g) = 0 := by
      rw [mean_sub_const (hs 0), sub_self]
    have hhead := centered_mgf (hw 0) (hs 0) hcenter hb
      (centered_bound (hw 0) (hs 0) hg) l
    have htail : ∀ a, mean (mass w') (fun x =>
        Real.exp (l * (f (Fin.cons a x) - g a))) ≤
        Real.exp (n * l ^ 2 * b ^ 2 / 2) := by
      intro a
      exact ih w' (fun i => hw i.succ) (fun i => hs i.succ)
        (fun x => f (Fin.cons a x)) (hf.tail a)
    rw [mean_cons]
    let c := Real.exp (n * l ^ 2 * b ^ 2 / 2)
    calc
      mean (w 0) (fun a => mean (mass w')
          (fun x => Real.exp (l * (f (Fin.cons a x) - mean (mass w) f))))
          = mean (w 0) (fun a => Real.exp (l * (g a - mean (w 0) g)) *
            mean (mass w') (fun x => Real.exp (l * (f (Fin.cons a x) - g a)))) := by
        apply congrArg (mean (w 0))
        funext a
        rw [hmean]
        change (∑ x, mass w' x * Real.exp (l * (f (Fin.cons a x) - mean (w 0) g))) =
          Real.exp (l * (g a - mean (w 0) g)) *
            ∑ x, mass w' x * Real.exp (l * (f (Fin.cons a x) - g a))
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        have he : l * (f (Fin.cons a x) - mean (w 0) g) =
            l * (g a - mean (w 0) g) + l * (f (Fin.cons a x) - g a) := by ring
        rw [he, Real.exp_add]
        ring
      _ ≤ mean (w 0) (fun a => Real.exp (l * (g a - mean (w 0) g)) * c) :=
        mean_mono (hw 0) (fun a => mul_le_mul_of_nonneg_left (htail a) (by positivity))
      _ = mean (w 0) (fun a => Real.exp (l * (g a - mean (w 0) g))) * c := by
        simp only [mean, ← mul_assoc, Finset.sum_mul]
      _ ≤ Real.exp (l ^ 2 * b ^ 2 / 2) * c :=
        mul_le_mul_of_nonneg_right hhead (by dsimp [c]; positivity)
      _ = Real.exp ((n + 1 : ℕ) * l ^ 2 * b ^ 2 / 2) := by
        dsimp [c]
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

noncomputable def probability {α : Type} [Fintype α] (w : α → ℝ) (p : α → Prop) : ℝ := by
  classical
  exact ∑ a, if p a then w a else 0

lemma exponential_markov {α : Type} [Fintype α] (w X : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) {l u : ℝ} (hl : 0 ≤ l) :
    probability w (fun a => u ≤ X a) ≤
      mean w (fun a => Real.exp (l * X a)) / Real.exp (l * u) := by
  classical
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  simp only [probability, mean, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  split_ifs with ha
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha hl)) (hw a)
  · simp only [zero_mul]
    exact mul_nonneg (hw a) (Real.exp_pos _).le

lemma probability_abs_le {α : Type} [Fintype α] (w X : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (u : ℝ) :
    probability w (fun a => u ≤ |X a|) ≤
      probability w (fun a => u ≤ X a) + probability w (fun a => u ≤ -X a) := by
  classical
  simp only [probability, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : u ≤ X a
  · simp only [h, ite_true]
    split_ifs <;> linarith [hw a]
  · by_cases h' : u ≤ -X a
    · simp only [h, h', ite_false, ite_true, zero_add]
      split_ifs <;> linarith [hw a]
    · have ha : ¬u ≤ |X a| := by
        have : |X a| < u := abs_lt.mpr ⟨by linarith, by linarith⟩
        exact not_le_of_gt this
      simp [h, h', ha]

theorem bounded_changes_upper {α : Type} [Fintype α] {n : ℕ} (hn : 1 ≤ n)
    (w : Fin n → α → ℝ) (hw : ∀ i a, 0 ≤ w i a) (hs : ∀ i, ∑ a, w i a = 1)
    (f : (Fin n → α) → ℝ) {b u : ℝ} (hb : 0 < b) (hu : 0 < u)
    (hf : BoundedChanges f b) :
    probability (mass w) (fun x => u ≤ f x - mean (mass w) f) ≤
      Real.exp (-u ^ 2 / (2 * n * b ^ 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let l : ℝ := u / (n * b ^ 2)
  have hl : 0 < l := by dsimp [l]; positivity
  calc
    probability (mass w) (fun x => u ≤ f x - mean (mass w) f)
        ≤ mean (mass w) (fun x => Real.exp (l * (f x - mean (mass w) f))) /
          Real.exp (l * u) :=
      exponential_markov _ _ (mass_nonneg hw) hl.le
    _ ≤ Real.exp (n * l ^ 2 * b ^ 2 / 2) / Real.exp (l * u) :=
      div_le_div_of_nonneg_right (bounded_changes_mgf w hw hs f hb hf l) (by positivity)
    _ = _ := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [l]
      field_simp
      ring

lemma BoundedChanges.neg {α : Type} {n : ℕ} {f : (Fin n → α) → ℝ} {b : ℝ}
    (h : BoundedChanges f b) : BoundedChanges (fun x => -f x) b := by
  intro i x y hxy
  simpa only [neg_sub_neg, abs_sub_comm] using h i x y hxy

theorem bounded_differences {α : Type} [Fintype α] {n : ℕ} (hn : 1 ≤ n)
    (w : Fin n → α → ℝ) (hw : ∀ i a, 0 ≤ w i a) (hs : ∀ i, ∑ a, w i a = 1)
    (f : (Fin n → α) → ℝ) {b u : ℝ} (hb : 0 < b) (hu : 0 < u)
    (hf : BoundedChanges f b) :
    probability (mass w) (fun x => u ≤ |f x - mean (mass w) f|) ≤
      2 * Real.exp (-u ^ 2 / (2 * n * b ^ 2)) := by
  have hupp := bounded_changes_upper hn w hw hs f hb hu hf
  have hlow := bounded_changes_upper hn w hw hs (fun x => -f x) hb hu hf.neg
  have he : mean (mass w) (fun x => -f x) = -mean (mass w) f := by
    simp [mean, Finset.sum_neg_distrib]
  rw [he] at hlow
  have hevent : (fun x => u ≤ -f x - -mean (mass w) f) =
      (fun x => u ≤ -(f x - mean (mass w) f)) := by
    funext x; congr 1; ring
  rw [hevent] at hlow
  have h := probability_abs_le (mass w) (fun x => f x - mean (mass w) f) (mass_nonneg hw) u
  linarith

end LinearListHadwiger.FiniteConcentration

end OAI
