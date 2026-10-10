import OAI.Combinatorics.HadwigerCounterexample.ProductLaws
import Mathlib.Tactic.FieldSimp

namespace OAI


/-! # Finite Conditioning -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

variable {A B : Type*} [Fintype A]

/-- Number of solutions as a real. -/
def nbr (p : A → Prop) := tot (fun x => ind (p x))

def onW (w : Wgt A) (p : A → Prop) := normW (subW w p)

theorem nbr_eq_card (p : A → Prop) [Fintype {x // p x}] :
    nbr p = (Fintype.card {x // p x}:ℝ) := by
  classical
  rw [Fintype.card_subtype]
  simp [nbr,tot,ind]

theorem pr_unif (p : A → Prop) :
    pr unif p = nbr p / Fintype.card A := by
  simp only [pr, avg, nbr, tot, unif_apply, div_eq_mul_inv]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem unifOn_val (p : A → Prop) (x) :
    unifOn p x = ind (p x) / nbr p := rfl

theorem unifOn_sub (p : A → Prop) : SubLaw (unifOn p) :=
  normW_subLaw fun x => ind_nonneg (p x)

theorem unifOn_carried (p : A → Prop) : carried (unifOn p) p :=
  fun x h => by rw [unifOn_val,ind_zero h,zero_div]

theorem on_unif [Nonempty A] (p : A → Prop) : onW unif p = unifOn p := by
  have h : (0:ℝ)<Fintype.card A := by exact_mod_cast Fintype.card_pos
  funext x
  simp only [onW, normW, subW_tot,subW,pr_unif,unifOn_val,unif_apply]
  by_cases hx : nbr p = 0
  · simp [hx]
  · field_simp

theorem unifOn_true : unifOn (fun _ : A => True) = unif := by
  simp [unifOn, unif]

theorem pr_on (w : Wgt A) (p q : A → Prop) :
    pr (onW w p) q = pr w (fun x => p x ∧ q x) / pr w p := by
  unfold onW
  change avg _ _ = _
  rw [avg_norm,subW_tot]
  exact congrArg (fun b => b / pr w p) (pr_sub w p q)

theorem pr_of_on {w : Wgt A} (hw : ∀ x, 0 ≤ w x) (p q : A → Prop) :
    pr w (fun x => p x ∧ q x) = pr w p * pr (onW w p) q := by
  rw [pr_on]
  by_cases h : pr w p = 0
  · rw [h,zero_mul]
    apply le_antisymm _ (pr_nonneg hw)
    rw [← h]
    exact pr_mono hw fun _ => And.left
  · field_simp

theorem onW_val (w : Wgt A) (p : A → Prop) (x) :
    onW w p x = w x * ind (p x) / pr w p := rfl

theorem on_mon {w : Wgt A} (hw : ∀ x, 0 ≤ w x) {p : A → Prop} {a : ℝ}
    (ha : 0 < a) (h : a ≤ pr w p) (x) : onW w p x ≤ a⁻¹ * w x :=
  calc onW w p x = (subW w p x) / pr w p := rfl
       _ ≤ w x / a := div_le_div₀ (hw x) (subW_le hw p x) ha h
       _ = _ := by rw [div_eq_mul_inv,mul_comm]

/-- Being a probability with support p and all point masses there equal
uniquely characterizes unifOn. -/
theorem uniform_support {w : Wgt A} {p : A → Prop} (hw : IsLaw w)
    (hp : carried w p) (he : ∀ x y, p x → p y → w x = w y) :
    w = unifOn p := by
  have h := (carried_iff_pr hw.nz).mp hp
  rw [hw.total] at h
  obtain ⟨x,hx,_⟩ := exists_of_pr_pos hw.nz (h.trans_gt zero_lt_one)
  have e : ∀ y, w y = w x * ind (p y) := by
    intro y; by_cases h : p y
    · rw [ind_one h, mul_one, he _ _ h hx]
    · rw [hp y h,ind_zero h,mul_zero]
  have hsum : w x * nbr p = 1 := by
    calc w x * nbr p = tot w := by
           unfold nbr tot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => (e y).symm
         _ = 1 := hw.total
  have hn : nbr p ≠ 0 := right_ne_zero_of_mul (hsum.trans_ne one_ne_zero)
  funext y; rw [e,unifOn_val,eq_div_iff hn,mul_right_comm,hsum,one_mul]

theorem avg_bij (e : A ≃ A) (w f : Wgt A) :
    avg (fun x => w (e x)) (fun x => f (e x)) = avg w f := by
  unfold avg
  exact Equiv.sum_comp e (fun x => w x * f x)

variable [Fintype B]

omit [Fintype B] in
theorem mapW_carried {w : Wgt A} {p : A → Prop} {q : B → Prop} {f : A → B}
    (hw : carried w p) (h : ∀ x, p x → q (f x)) : carried (mapW w f) q := by
  intro y hy
  change ∑ x, w x * ind (f x=y) = 0
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases e : f x=y
  · rw [hw x (fun hp => hy (e ▸ h x hp)),zero_mul]
  · rw [ind_zero e,mul_zero]

/-- Pointwise transitivity transfer of a uniform law under observation. -/
theorem uniform_orbit {p : A → Prop} {q : B → Prop} (f : A → B) (hp : ∃ x, p x)
    (hq : ∀ x, p x → q (f x))
    (h : ∀ y z, q y → q z → ∃ e : A ≃ A, (∀ x, p x ↔ p (e x))
      ∧ ∀ x, f x = y ↔ f (e x)=z) :
    mapW (unifOn p) f = unifOn q := by
  refine uniform_support (mapW_law (unifOn_law hp) _) (mapW_carried (unifOn_carried p) hq)
    (fun y z hy hz => ?_)
  obtain ⟨e,he,hE⟩ := h y z hy hz
  unfold mapW pr
  rw [← avg_bij e (unifOn p) (fun x => ind (f x = z))]
  simp_rw [unifOn_val,← he,← hE]
  rfl

/-- A pointwise fiber disintegration. -/
theorem disintegrate {w : Wgt A} (hw : ∀ x, 0 ≤ w x) (f : A → B) :
    w = mixW (mapW w f) (fun y => onW w (fun x => f x = y)) := by
  funext x
  unfold mixW avg
  rw [Finset.sum_eq_single (f x)]
  · simp only [mapW,onW_val,ind_true,mul_one]
    by_cases h : pr w (fun z => f z = f x) = 0
    · rw [h,zero_mul]
      apply le_antisymm _ (hw x)
      rw [← h]; exact weight_le_pr hw rfl
    · field_simp
  · intro i _ hi; simp [onW_val, ind, Ne.symm hi]
  · simp

omit [Fintype B] in
/-- Mapping changes a density bound functorially. -/
theorem mapW_cap {w v : Wgt A} {c : ℝ} (h : ∀ x, w x ≤ c * v x) (f : A → B) (y) :
    mapW w f y ≤ c * mapW v f y := by
  unfold mapW
  refine (pr_mono_left (v:=fun x => c * v x) h _).trans_eq ?_
  simp only [pr,avg,Finset.mul_sum,mul_assoc]

end HadwigerCounterexample

end

end OAI
