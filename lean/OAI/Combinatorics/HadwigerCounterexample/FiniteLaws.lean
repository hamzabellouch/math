import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace OAI

/-! # Finite Laws -/

noncomputable section
open scoped BigOperators

namespace HadwigerCounterexample

abbrev Wgt (α : Type*) := α → ℝ

variable {α β : Type*}

/-- Real indicator. -/
def ind (p : Prop) : ℝ := @ite ℝ p (Classical.propDecidable _) 1 0

theorem ind_eq (p : Prop) [Decidable p] : ind p = if p then 1 else 0 := by
  unfold ind
  congr

theorem ind_one {p : Prop} (h : p) : ind p = 1 := by classical simp [ind, h]
theorem ind_zero {p : Prop} (h : ¬p) : ind p = 0 := by classical simp [ind, h]
@[simp] theorem ind_true : ind True = 1 := ind_one trivial
@[simp] theorem ind_false : ind False = 0 := ind_zero (not_false)

theorem ind_nonneg (p : Prop) : 0 ≤ ind p := by
  by_cases h : p
  · exact le_of_lt (by rw [ind_one h]; norm_num)
  · rw [ind_zero h]

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  by_cases h : p
  · rw [ind_one h]
  · rw [ind_zero h]
    norm_num

theorem ind_mono {p q : Prop} (hp : p → q) : ind p ≤ ind q := by
  by_cases h : p
  · rw [ind_one h, ind_one (hp h)]
  · rw [ind_zero h]
    exact ind_nonneg _

theorem ind_not (p : Prop) : ind (¬p) = 1 - ind p := by
  by_cases h : p <;> simp [ind, h]

theorem ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by
  by_cases h : p <;> by_cases h2 : q <;> simp [ind, h, h2]

theorem ind_or_le (p q : Prop) : ind (p ∨ q) ≤ ind p + ind q := by
  by_cases h : p
  · simp only [h, true_or, ind_true]
    have := ind_nonneg q
    linarith
  · simp [h]

/-- Total weight. -/
def tot [Fintype α] (w : Wgt α) : ℝ := ∑ x, w x
/-- Weighted average (not normalized if the weights are not a probability law). -/
def avg [Fintype α] (w f : Wgt α) : ℝ := ∑ x, w x * f x
/-- Weight of an event. -/
def pr [Fintype α] (w : Wgt α) (p : α → Prop) := avg w (fun x => ind (p x))

structure SubLaw [Fintype α] (w : Wgt α) : Prop where
  nz (x : α) : 0 ≤ w x
  total : tot w ≤ 1
structure IsLaw [Fintype α] (w : Wgt α) : Prop where
  nz (x : α) : 0 ≤ w x
  total : tot w = 1

theorem IsLaw.sub [Fintype α] {w : Wgt α} (hw : IsLaw w) : SubLaw w where
  nz := hw.nz
  total := hw.total.le

/-- All positive mass is supported on `p`. We use the equivalent contrapositive with
zero mass (and supply nonnegativity wherever we speak of a law). -/
def carried (w : Wgt α) (p : α → Prop) := ∀ x : α, ¬ p x → w x = 0

section Basic
variable [Fintype α] {w v f g : Wgt α} {p q : α → Prop}

theorem tot_nonneg (hw : ∀ x, 0 ≤ w x) : 0 ≤ tot w := Finset.sum_nonneg fun x _ => hw x

theorem tot_mono (h : ∀ x, w x ≤ v x) : tot w ≤ tot v :=
  Finset.sum_le_sum fun x _ => h x

theorem weight_le_tot (hw : ∀ x, 0 ≤ w x) (x) : w x ≤ tot w :=
  Finset.single_le_sum (fun y _ => hw y) (Finset.mem_univ x)

theorem SubLaw.weight_le_one (hw : SubLaw w) (x) : w x ≤ 1 :=
  (weight_le_tot hw.nz x).trans hw.total

theorem IsLaw.weight_le_one (hw : IsLaw w) (x) : w x ≤ 1 := hw.sub.weight_le_one x

theorem avg_comm (w f : Wgt α) : avg w f = avg f w := by simp only [avg, mul_comm]

theorem avg_mono (hw : ∀ x, 0 ≤ w x) (h : ∀ x, f x ≤ g x) : avg w f ≤ avg w g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hw x)

theorem avg_mono_left (hf : ∀ x, 0 ≤ f x) (h : ∀ x, w x ≤ v x) : avg w f ≤ avg v f := by
  rw [avg_comm w, avg_comm v]
  exact avg_mono hf h

theorem avg_nonneg (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg w f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)

@[simp] theorem avg_zero (w : Wgt α) : avg w (fun _ => 0) = 0 := by simp [avg]

theorem avg_const (w : Wgt α) (a : ℝ) : avg w (fun _ => a) = tot w * a := by
  rw [avg, tot, Finset.sum_mul]

theorem IsLaw.avg_const (hw : IsLaw w) (a : ℝ) : avg w (fun _ => a) = a := by
  rw [HadwigerCounterexample.avg_const, hw.total, one_mul]

theorem SubLaw.avg_le (hw : SubLaw w) {b : ℝ} (hb : 0 ≤ b) (h : ∀ x, f x ≤ b) :
    avg w f ≤ b := by
  refine (avg_mono hw.nz h).trans ?_
  rw [avg_const]
  exact (mul_le_mul_of_nonneg_right hw.total hb).trans_eq (one_mul b)

theorem IsLaw.avg_le (hw : IsLaw w) {b : ℝ} (h : ∀ x, f x ≤ b) : avg w f ≤ b :=
  (avg_mono hw.nz h).trans (hw.avg_const _).le

theorem IsLaw.le_avg (hw : IsLaw w) {b : ℝ} (h : ∀ x, b ≤ f x) : b ≤ avg w f :=
  (hw.avg_const _).ge.trans (avg_mono hw.nz h)

theorem abs_avg_le (hw : ∀ x, 0 ≤ w x) : |avg w f| ≤ avg w (fun x => |f x|) := by
  rw [avg, avg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  simp_rw [abs_mul, abs_of_nonneg (hw _)]

theorem avg_add (w f g : Wgt α) : avg w (fun x => f x + g x) = avg w f + avg w g := by
  simp only [avg, mul_add, Finset.sum_add_distrib]

theorem avg_sub (w f g : Wgt α) : avg w (fun x => f x - g x) = avg w f - avg w g := by
  simp only [avg, mul_sub, Finset.sum_sub_distrib]

theorem avg_mul (w f : Wgt α) (b : ℝ) : avg w (fun x => f x * b) = avg w f * b := by
  simp only [avg, Finset.sum_mul, mul_assoc]

theorem avg_mul' (w f : Wgt α) (b : ℝ) : avg w (fun x => b * f x) = b * avg w f := by
  simpa only [mul_comm b] using avg_mul w f b

theorem avg_div (w f : Wgt α) (b : ℝ) : avg w (fun x => f x / b) = avg w f / b := by
  simp_rw [div_eq_mul_inv]
  exact avg_mul _ _ _

theorem avg_congr (h : ∀ x, w x ≠ 0 → f x = g x) : avg w f = avg w g := by
  unfold avg
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : w x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx]

theorem avg_sum {ι : Type*} (w : Wgt α) (s : Finset ι) (f : ι → Wgt α) :
    avg w (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, avg w (f i) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem avg_avg [Fintype β] (w : Wgt α) (v : Wgt β) (f : α → β → ℝ) :
    avg w (fun x => avg v (f x)) = avg v (fun y => avg w (fun x => f x y)) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

theorem pr_nonneg (hw : ∀ x, 0 ≤ w x) : 0 ≤ pr w p :=
  avg_nonneg hw fun _ => ind_nonneg _

theorem pr_le_tot (hw : ∀ x, 0 ≤ w x) : pr w p ≤ tot w := by
  unfold pr
  refine (avg_mono hw fun x => ind_le_one (p x)).trans_eq ?_
  rw [avg_const, mul_one]

theorem pr_mono (hw : ∀ x, 0 ≤ w x) (h : ∀ x, p x → q x) : pr w p ≤ pr w q :=
  avg_mono hw fun x => ind_mono (h x)

theorem pr_mono_left (h : ∀ x, w x ≤ v x) (p : α → Prop) : pr w p ≤ pr v p :=
  avg_mono_left (fun x => ind_nonneg (p x)) h

theorem pr_not (w : Wgt α) (p : α → Prop) : pr w (fun x => ¬p x) = tot w - pr w p := by
  simp_rw [pr, ind_not, avg_sub, avg_const, mul_one]

@[simp] theorem pr_point (w : Wgt α) (x : α) : pr w (fun y => x = y) = w x := by
  classical simp [pr, avg, ind]

@[simp] theorem pr_point' (w : Wgt α) (x : α) : pr w (fun y => y = x) = w x := by
  classical simp [pr, avg, ind]

@[simp] theorem pr_true (w : Wgt α) : pr w (fun _ => True) = tot w := by simp [pr, avg, tot]
@[simp] theorem pr_false (w : Wgt α) : pr w (fun _ => False) = 0 := by simp [pr]

theorem pr_or_le (hw : ∀ x, 0 ≤ w x) :
    pr w (fun x => p x ∨ q x) ≤ pr w p + pr w q :=
  (avg_mono hw fun x => ind_or_le (p x) (q x)).trans_eq (avg_add _ _ _)

theorem pr_union_le (hw : ∀ x, 0 ≤ w x) {ι : Type*} (s : Finset ι) (p : ι → α → Prop) :
    pr w (fun x => ∃ i ∈ s, p i x) ≤ ∑ i ∈ s, pr w (p i) := by
  let F : ι → Wgt α := fun i x => ind (p i x)
  change _ ≤ ∑ i ∈ s, avg w (F i)
  rw [← avg_sum]
  refine avg_mono hw fun x => ?_
  change ind (∃ i ∈ s, p i x) ≤ _
  by_cases h : ∃ i ∈ s, p i x
  · rw [ind_one h]
    obtain ⟨i, hi, hp⟩ := h
    have : F i x ≤ ∑ i ∈ s, F i x :=
      Finset.single_le_sum (fun (j : ι) _ => ind_nonneg (p j x)) hi
    simpa only [F, ind_one hp] using this
  · rw [ind_zero h]
    exact Finset.sum_nonneg fun i _ => ind_nonneg (p i x)

theorem pr_exists_le (hw : ∀ x, 0 ≤ w x) {ι : Type*} [Fintype ι] (p : ι → α → Prop) :
    pr w (fun x => ∃ i, p i x) ≤ ∑ i, pr w (p i) := by
  simpa using pr_union_le hw Finset.univ p

theorem weight_le_pr (hw : ∀ x, 0 ≤ w x) {x} (hx : p x) : w x ≤ pr w p := by
  have h := pr_mono (p:=fun y => x = y) (q:=p) hw (fun y e => e ▸ hx)
  simpa only [pr_point] using h

theorem exists_of_pr_pos (hw : ∀ x, 0 ≤ w x) (hp : 0 < pr w p) :
    ∃ x, p x ∧ 0 < w x := by
  by_contra! hn
  have h : pr w p = 0 := by
    unfold pr avg
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : p x
    · rw [le_antisymm (hn x hx) (hw x), zero_mul]
    · simp only [ind_zero hx, mul_zero]
  exact hp.ne' h

theorem carried_iff_pr (hw : ∀ x, 0 ≤ w x) : carried w p ↔ pr w p = tot w := by
  constructor
  · intro h
    unfold pr
    have e : avg w (fun x => ind (p x)) = avg w (fun _ => 1) := by
      refine avg_congr fun x hx => ind_one (Classical.byContradiction fun hn => hx (h x hn))
    rw [e, avg_const, mul_one]
  · intro he x hx
    have h := weight_le_pr (p:=fun x => ¬p x) hw hx
    rw [pr_not, he, sub_self] at h
    exact le_antisymm h (hw x)

theorem le_avg_markov (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) (b : ℝ) :
    b * pr w (fun x => b ≤ f x) ≤ avg w f := by
  unfold pr
  rw [← avg_mul']
  refine avg_mono hw fun x => ?_
  by_cases h : b ≤ f x
  · simpa [ind_one h] using h
  · simpa [ind_zero h] using hf x

end Basic

/-- Restrict weights; *not* renormalized. -/
def subW (w : Wgt α) (p : α → Prop) := fun x => w x * ind (p x)

/-- Divide a finite weight function by its total, giving zero if total is zero. -/
def normW [Fintype α] (w : Wgt α) := fun x => w x / tot w

def unif [Fintype α] : Wgt α := normW fun _ => 1
def unifOn [Fintype α] (p : α → Prop) : Wgt α := normW (fun x => ind (p x))

section Restrict
variable [Fintype α] {w : Wgt α} {p : α → Prop}

omit [Fintype α] in
theorem subW_nonneg (hw : ∀ x, 0 ≤ w x) (p : α → Prop) : ∀ x, 0 ≤ subW w p x :=
  fun x => mul_nonneg (hw x) (ind_nonneg _)

@[simp] theorem subW_tot (w : Wgt α) (p : α → Prop) : tot (subW w p) = pr w p := rfl

omit [Fintype α] in
theorem subW_le (hw : ∀ x, 0 ≤ w x) (p : α → Prop) (x : α) : subW w p x ≤ w x :=
  (mul_le_mul_of_nonneg_left (ind_le_one _) (hw x)).trans_eq (mul_one _)

omit [Fintype α] in
theorem subW_carried (w : Wgt α) (p : α → Prop) : carried (subW w p) p :=
  fun x h => by rw [subW, ind_zero h, mul_zero]

theorem subLaw_sub (hw : SubLaw w) (p : α → Prop) : SubLaw (subW w p) :=
  ⟨subW_nonneg hw.nz p, (pr_le_tot hw.nz).trans hw.total⟩

theorem pr_sub (w : Wgt α) (p q : α → Prop) :
    pr (subW w p) q = pr w (fun x => p x ∧ q x) := by
  simp only [pr, avg, ind_and, subW, mul_assoc]

theorem normW_nonneg (hw : ∀ x, 0 ≤ w x) : ∀ x, 0 ≤ normW w x :=
  fun x => div_nonneg (hw x) (tot_nonneg hw)

theorem avg_norm (w f : Wgt α) : avg (normW w) f = avg w f / tot w := by
  rw [avg_comm, avg_comm w f]
  exact avg_div _ _ _

theorem tot_norm (w : Wgt α) : tot (normW w) = tot w / tot w := by
  simp only [tot, normW, div_eq_mul_inv, Finset.sum_mul]

theorem normW_law (hw : ∀ x, 0 ≤ w x) (hpos : 0 < tot w) : IsLaw (normW w) :=
  ⟨normW_nonneg hw, by rw [tot_norm, div_self hpos.ne']⟩

theorem normW_subLaw (hw : ∀ x, 0 ≤ w x) : SubLaw (normW w) := by
  refine ⟨normW_nonneg hw, ?_⟩
  rw [tot_norm]
  by_cases h : tot w = 0 <;> simp [h]

theorem normW_carried (hp : carried w p) : carried (normW w) p :=
  fun x h => by rw [normW, hp x h, zero_div]

theorem unif_apply (x : α) : unif x = (Fintype.card α : ℝ)⁻¹ := by
  simp [unif, normW, tot]

theorem unif_subLaw : SubLaw (unif : Wgt α) :=
  normW_subLaw (fun _ => zero_le_one)

theorem unif_law [Nonempty α] : IsLaw (unif : Wgt α) := by
  refine normW_law (fun _ => zero_le_one) ?_
  simp [tot, Fintype.card_pos]

theorem unifOn_law (h : ∃ x, p x) : IsLaw (unifOn p) := by
  refine normW_law (fun _ => ind_nonneg _) ?_
  obtain ⟨x, hx⟩ := h
  have := weight_le_tot (fun x => ind_nonneg (p x)) x
  change 0 < tot _
  rw [ind_one hx] at this
  exact lt_of_lt_of_le zero_lt_one this

end Restrict

def pairW (w : Wgt α) (v : Wgt β) : Wgt (α × β) := fun p => w p.1 * v p.2
def mixW [Fintype α] (w : Wgt α) (F : α → Wgt β) : Wgt β := fun y => avg w (fun x => F x y)
def mapW [Fintype α] (w : Wgt α) (f : α → β) : Wgt β := fun y => pr w (fun x => f x = y)

section Prod
variable [Fintype α] [Fintype β] {w : Wgt α} {v : Wgt β}

theorem pairW_avg (w : Wgt α) (v : Wgt β) (f : α × β → ℝ) :
    avg (pairW w v) f = avg w (fun x => avg v (fun y => f (x,y))) := by
  simp only [avg, Finset.mul_sum, Fintype.sum_prod_type, pairW, mul_assoc]

theorem pairW_separate (w f : Wgt α) (v g : Wgt β) :
    avg (pairW w v) (fun p => f p.1 * g p.2) = avg w f * avg v g := by
  simp only [pairW_avg, avg_mul', avg_mul]

theorem pairW_pr (w : Wgt α) (v : Wgt β) (p : α → Prop) (q : β → Prop) :
    pr (pairW w v) (fun x => p x.1 ∧ q x.2) = pr w p * pr v q := by
  simp_rw [pr, ind_and]
  exact pairW_separate w (fun x => ind (p x)) v (fun y => ind (q y))

theorem pairW_tot (w : Wgt α) (v : Wgt β) : tot (pairW w v) = tot w * tot v := by
  simpa using pairW_pr w v (fun _ => True) (fun _ => True)

theorem pairW_law (hw : IsLaw w) (hv : IsLaw v) : IsLaw (pairW w v) :=
  ⟨fun x => mul_nonneg (hw.nz _) (hv.nz _), by rw [pairW_tot, hw.total, hv.total, mul_one]⟩

theorem mixW_avg (w : Wgt α) (F : α → Wgt β) (g : Wgt β) :
    avg (mixW w F) g = avg w (fun x => avg (F x) g) := by
  simp only [avg, mixW, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem mixW_tot (w : Wgt α) (F : α → Wgt β) :
    tot (mixW w F) = avg w (fun x => tot (F x)) := by
  simpa only [avg_const, mul_one] using mixW_avg w F (fun _ => 1)

theorem mixW_law (hw : IsLaw w) {F : α → Wgt β} (hF : ∀ x, IsLaw (F x)) :
    IsLaw (mixW w F) := by
  refine ⟨fun x => avg_nonneg hw.nz (fun y => (hF y).nz _), ?_⟩
  rw [mixW_tot]
  simp_rw [(hF _).total]
  exact hw.avg_const _

theorem mapW_avg (w : Wgt α) (f : α → β) (g : Wgt β) :
    avg (mapW w f) g = avg w (fun x => g (f x)) := by
  classical
  change avg (mixW w (fun x y => ind (f x = y))) g = _
  rw [mixW_avg]
  simp [avg, ind]

theorem mapW_law (hw : IsLaw w) (f : α → β) : IsLaw (mapW w f) := by
  refine ⟨fun _ => pr_nonneg hw.nz, ?_⟩
  simpa only [avg_const, mul_one, hw.total] using mapW_avg w f (fun _ => 1)

theorem mapW_pr (w : Wgt α) (f : α → β) (q : β → Prop) :
    pr (mapW w f) q = pr w (fun x => q (f x)) := mapW_avg _ _ _

end Prod

end HadwigerCounterexample

end

end OAI
