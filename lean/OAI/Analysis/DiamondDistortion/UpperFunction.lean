import OAI.Analysis.DiamondDistortion.EquivalentNorm

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace RecursiveModel
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]
abbrev Full (h : ℕ) := lp (fun _ : Coord h => ℝ) p
lemma p_ne_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞)<1) (Fact.out : 1 ≤ p))
variable (hp : 0 < p.toReal)

def child (h : ℕ) (v : Full p (h+1)) (i : ℕ) : Full p h :=
  ⟨fun s => v (.inr (i,s)),(memℓp_gen_iff hp).mpr ((v.property.summable hp).comp_injective (by
    intro a b hh
    exact (Prod.mk.inj (Sum.inr.inj hh)).2))⟩
lemma child_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (v : Full p (h+1)) (i : ℕ) (s : Coord h) :
    child p hp h v i s=v (.inr (i,s)) := rfl
lemma child_sum (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (v : Full p (h+1)) (i : ℕ) :
    ‖child p hp h v i‖^p.toReal=∑' s : Coord h,‖v (.inr (i,s))‖^p.toReal :=
  lp.norm_rpow_eq_tsum hp _
lemma child_summable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (v : Full p (h+1)) :
    Summable (fun q : ℕ × Coord h => ‖v (.inr q)‖^p.toReal) :=
  (v.property.summable hp).comp_injective Sum.inr_injective

def children (h : ℕ) (v : Full p (h+1)) : lp (fun _ : ℕ => Full p h) p :=
  ⟨fun i => child p hp h v i,(memℓp_gen_iff hp).mpr (by
    have hh := (child_summable p hp h v).prod
    simpa only [← child_sum p hp h v] using hh)⟩
lemma children_apply (h : ℕ) (v : Full p (h+1)) (i : ℕ) : children p hp h v i=child p hp h v i := rfl
lemma children_norm (h : ℕ) (v : Full p (h+1)) : ‖children p hp h v‖ ≤ ‖v‖ := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp).mp
  rw [lp.norm_rpow_eq_tsum hp,lp.norm_rpow_eq_tsum hp]
  simp_rw [children_apply,child_sum]
  rw [← (child_summable p hp h v).tsum_prod]
  exact Summable.tsum_le_tsum_of_inj (fun q : ℕ × Coord h => (Sum.inr q : Coord (h+1)))
    Sum.inr_injective (fun _ _ => by positivity) (fun _ => le_rfl)
    (child_summable p hp h v) (v.property.summable hp)

@[simp] lemma child_add (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (u v : Full p (h+1)) (i : ℕ) :
    child p hp h (u+v) i=child p hp h u i+child p hp h v i := by ext s; rfl
@[simp] lemma child_neg (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (v : Full p (h+1)) (i : ℕ) :
    child p hp h (-v) i=-child p hp h v i := by ext s; rfl
@[simp] lemma child_smul (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (a : ℝ) (v : Full p (h+1)) (i : ℕ) :
    child p hp h (a • v) i=a • child p hp h v i := by ext s; rfl
@[simp] lemma child_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (i : ℕ) : child p hp h 0 i=0 := by ext s; rfl
end RecursiveModel

namespace UpperFunction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
structure Data (E : Type*) [NormedAddCommGroup E] (C : ℝ) where
  value : E → ℝ × ℝ
  nonneg : ∀ v,0 ≤ (value v).1 ∧ 0 ≤ (value v).2
  bound : ∀ v,(value v).1 ≤ C*‖v‖ ∧ (value v).2 ≤ C*‖v‖
namespace Data
variable {C : ℝ} (U : Data E C) (hC : 0 ≤ C) {p : ℝ≥0∞} [Fact (1 ≤ p)]
def positiveArray (v : lp (fun _ : ℕ => E) p) : lp (fun _ : ℕ => ℝ) p :=
  LpBoundedMap.map (fun x => (U.value x).1) C hC (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (U.nonneg x).1] using (U.bound x).1) v
def negativeArray (v : lp (fun _ : ℕ => E) p) : lp (fun _ : ℕ => ℝ) p :=
  LpBoundedMap.map (fun x => (U.value x).2) C hC (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (U.nonneg x).2] using (U.bound x).2) v
lemma positiveArray_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : ℝ} (U : Data E C) (hC : 0 ≤ C) {p : ℝ≥0∞} [Fact (1 ≤ p)] (v : lp (fun _ : ℕ => E) p) (i : ℕ) :
    positiveArray U hC v i=(U.value (v i)).1 := rfl
lemma negativeArray_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : ℝ} (U : Data E C) (hC : 0 ≤ C) {p : ℝ≥0∞} [Fact (1 ≤ p)] (v : lp (fun _ : ℕ => E) p) (i : ℕ) :
    negativeArray U hC v i=(U.value (v i)).2 := rfl
lemma positiveArray_norm (hp : p ≠ 0) (v : lp (fun _ : ℕ => E) p) :
    ‖positiveArray U hC v‖ ≤ C*‖v‖ := LpBoundedMap.map_norm hp _ _ _ _ v
lemma negativeArray_norm (hp : p ≠ 0) (v : lp (fun _ : ℕ => E) p) :
    ‖negativeArray U hC v‖ ≤ C*‖v‖ := LpBoundedMap.map_norm hp _ _ _ _ v
end Data
end UpperFunction

namespace RecursiveModel
lemma join_upper_bound {r a b C M : ℝ} (hC : 1 ≤ C) (hM : 0 ≤ M)
    (hr : |r| ≤ M) (ha : a ≤ C*M) (hb : b ≤ C*M) :
    (join r a b).1 ≤ (3*C)*M ∧ (join r a b).2 ≤ (3*C)*M := by
  have hCM : M ≤ C*M := by nlinarith
  have hrp := (abs_le.mp hr).2
  have hrn := (abs_le.mp hr).1
  constructor <;> apply max_le <;> nlinarith

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal)
/-- Least upper values on the original full ℓp component, not on a finite-support
    substitute. All child sequences are genuine countable ℓp vectors. -/
def fullUpperData : (h : ℕ) → UpperFunction.Data (Full p h) (3^h)
  | 0 => {
      value v := (max (v ()) 0,max (-v ()) 0)
      nonneg v := ⟨le_max_right _ _,le_max_right _ _⟩
      bound v := by
        simp only [pow_zero,one_mul]
        have hb := lp.norm_apply_le_norm (p_ne_zero p) v ()
        rw [Real.norm_eq_abs] at hb
        exact ⟨max_le ((le_abs_self _).trans hb) (norm_nonneg _),
          max_le ((neg_le_abs _).trans hb) (norm_nonneg _)⟩ }
  | h+1 =>
    let U := fullUpperData h
    let a (v : Full p (h+1)) := ‖U.positiveArray (by positivity) (children p hp h v)‖
    let b (v : Full p (h+1)) := ‖U.negativeArray (by positivity) (children p hp h v)‖
    { value v := join (v (.inl ())) (a v) (b v)
      nonneg v := ⟨(norm_nonneg _).trans (le_max_left _ _),(norm_nonneg _).trans (le_max_right _ _)⟩
      bound v := by
        have ha := (U.positiveArray_norm (by positivity) (p_ne_zero p) (children p hp h v)).trans
          (mul_le_mul_of_nonneg_left (children_norm p hp h v) (by positivity : (0:ℝ) ≤ 3^h))
        have hb := (U.negativeArray_norm (by positivity) (p_ne_zero p) (children p hp h v)).trans
          (mul_le_mul_of_nonneg_left (children_norm p hp h v) (by positivity : (0:ℝ) ≤ 3^h))
        have hr : |v (.inl ())| ≤ ‖v‖ := by
          simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm (p_ne_zero p) v (.inl ())
        have hh := join_upper_bound (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3)) (norm_nonneg v) hr ha hb
        simpa only [pow_succ,show (3:ℝ)*3^h=3^h*3 by ring] using hh }

def fullUpper (h : ℕ) (v : Full p h) : ℝ × ℝ := (fullUpperData p hp h).value v
def fullPChildren (h : ℕ) (v : Full p (h+1)) : lp (fun _ : ℕ => ℝ) p :=
  (fullUpperData p hp h).positiveArray (by positivity) (children p hp h v)
def fullQChildren (h : ℕ) (v : Full p (h+1)) : lp (fun _ : ℕ => ℝ) p :=
  (fullUpperData p hp h).negativeArray (by positivity) (children p hp h v)
lemma fullUpper_zero_height (v : Full p 0) : fullUpper p hp 0 v=(max (v ()) 0,max (-v ()) 0) := rfl
lemma fullUpper_succ (h : ℕ) (v : Full p (h+1)) :
    fullUpper p hp (h+1) v=join (v (.inl ())) ‖fullPChildren p hp h v‖ ‖fullQChildren p hp h v‖ := rfl
lemma fullPChildren_apply (h : ℕ) (v : Full p (h+1)) (i : ℕ) :
    fullPChildren p hp h v i=(fullUpper p hp h (child p hp h v i)).1 := rfl
lemma fullQChildren_apply (h : ℕ) (v : Full p (h+1)) (i : ℕ) :
    fullQChildren p hp h v i=(fullUpper p hp h (child p hp h v i)).2 := rfl
lemma fullUpper_nonneg (h : ℕ) (v : Full p h) :
    0 ≤ (fullUpper p hp h v).1 ∧ 0 ≤ (fullUpper p hp h v).2 := (fullUpperData p hp h).nonneg v
lemma fullUpper_bound (h : ℕ) (v : Full p h) :
    (fullUpper p hp h v).1 ≤ 3^h*‖v‖ ∧ (fullUpper p hp h v).2 ≤ 3^h*‖v‖ :=
  (fullUpperData p hp h).bound v

@[simp] lemma fullUpper_zero (h : ℕ) : fullUpper p hp h 0=0 := by
  have hn := fullUpper_nonneg p hp h 0
  have hb := fullUpper_bound p hp h 0
  simp only [norm_zero,mul_zero] at hb
  exact Prod.ext (le_antisymm hb.1 hn.1) (le_antisymm hb.2 hn.2)

lemma child_finiteLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (h : ℕ) (v : Vec (h+1)) (i : ℕ) :
    child p hp h (finiteLp p v) i=finiteLp p ((rootChildren h v).2 i) := by ext s; rfl

lemma fullUpper_finiteLp (h : ℕ) (v : Vec h) : fullUpper p hp h (finiteLp p v)=upper p h v := by
  induction h with
  | zero => rfl
  | succ h ih =>
    let w := rootChildren h v
    let P := w.2.mapRange (fun z => (upper p h z).1) (by simp)
    let Q := w.2.mapRange (fun z => (upper p h z).2) (by simp)
    have hP : fullPChildren p hp h (finiteLp p v)=finiteLp p P := by
      ext i
      rw [fullPChildren_apply,child_finiteLp,ih]
      rfl
    have hQ : fullQChildren p hp h (finiteLp p v)=finiteLp p Q := by
      ext i
      rw [fullQChildren_apply,child_finiteLp,ih]
      rfl
    rw [fullUpper_succ,hP,hQ]
    rfl
end RecursiveModel

end DiamondDistortion

end

end OAI
