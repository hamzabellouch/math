import OAI.Analysis.DiskMaximal.MaximalEstimates

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace ScalarCancellation

/-- A nonnegative scalar residual retaining exactly the net mass. Its removal
has the exact cancellation defect as L1 cost. -/
theorem positive_residual {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} (hh : Integrable h μ) (hc : 0 ≤ ∫ x, h x ∂μ) :
    ∃ ρ : α → ℝ, Integrable ρ μ ∧ (∀ x, 0 ≤ ρ x) ∧
      (∀ x, ρ x ≤ max (h x) 0) ∧ (∫ x, ρ x ∂μ) = ∫ x, h x ∂μ ∧
      (∫ x, |h x-ρ x| ∂μ) = (∫ x, |h x| ∂μ) - ∫ x, h x ∂μ ∧
      (∀ x, h x = 0 → ρ x = 0) := by
  let p : α → ℝ := fun x => max (h x) 0
  have hp : Integrable p μ := by
    convert (hh.add hh.abs).div_const 2 using 1
    funext x
    by_cases hx : 0 ≤ h x
    · simp only [p,max_eq_left hx,abs_of_nonneg hx,Pi.add_apply]
      ring
    · simp only [p,max_eq_right (le_of_not_ge hx),abs_of_nonpos (le_of_not_ge hx),Pi.add_apply]
      ring
  have hp0 : 0 ≤ ∫ x, p x ∂μ := integral_nonneg (fun x => le_max_right _ _)
  have hcp : (∫ x, h x ∂μ) ≤ ∫ x, p x ∂μ := integral_mono hh hp (fun x => le_max_left _ _)
  by_cases hP : (∫ x, p x ∂μ) = 0
  · have hc0 : (∫ x, h x ∂μ) = 0 := le_antisymm (hP ▸ hcp) hc
    refine ⟨0,integrable_zero _ _ _,fun _ => le_rfl,fun x => le_max_right _ _,?_,?_,fun _ _ => rfl⟩
    · simp [hc0]
    · simp [hc0]
  · have hPpos : 0 < ∫ x, p x ∂μ := lt_of_le_of_ne hp0 (Ne.symm hP)
    let q := (∫ x, h x ∂μ)/(∫ x, p x ∂μ)
    have hq0 : 0 ≤ q := div_nonneg hc hp0
    have hq1 : q ≤ 1 := (div_le_one hPpos).mpr hcp
    let ρ : α → ℝ := fun x => q*p x
    have hρ : Integrable ρ μ := hp.const_mul q
    have hρ0 : ∀ x, 0 ≤ ρ x := fun x => mul_nonneg hq0 (le_max_right _ _)
    have hρp : ∀ x, ρ x ≤ p x := fun x => mul_le_of_le_one_left (le_max_right _ _) hq1
    have hi : (∫ x, ρ x ∂μ) = ∫ x, h x ∂μ := by
      rw [show ρ = fun x => q*p x from rfl,integral_const_mul]
      exact div_mul_cancel₀ _ hP
    have habs : ∀ x, |h x-ρ x| = |h x|-ρ x := by
      intro x
      by_cases hhx : 0 ≤ h x
      · rw [abs_of_nonneg hhx,abs_of_nonneg]
        simpa only [p,max_eq_left hhx] using sub_nonneg.mpr (hρp x)
      · have hx0 : h x ≤ 0 := (lt_of_not_ge hhx).le
        have : ρ x = 0 := by simp [ρ,p,max_eq_right hx0]
        simp [this]
    refine ⟨ρ,hρ,hρ0,hρp,hi,?_,?_⟩
    · simp_rw [habs]
      rw [integral_sub hh.abs hρ,hi]
    · intro x hx
      simp [ρ,p,hx]

/-- Every integrable scalar density splits into a constant-sign root and a
zero-mass error, without replacing the actual terminal density by its mass. -/
theorem residual_split {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} (hh : Integrable h μ) :
    ∃ ρ β : α → ℝ, Integrable ρ μ ∧ Integrable β μ ∧
      (∀ x, h x = ρ x+β x) ∧ (∫ x, ρ x ∂μ) = ∫ x, h x ∂μ ∧
      (∫ x, β x ∂μ) = 0 ∧ (∫ x, |ρ x| ∂μ) = |∫ x, h x ∂μ| ∧
      (∫ x, |β x| ∂μ) = (∫ x, |h x| ∂μ)-|∫ x, h x ∂μ| ∧
      ((0 ≤ ∫ x, h x ∂μ) → ∀ x, 0 ≤ ρ x) ∧
      ((∫ x, h x ∂μ) < 0 → ∀ x, ρ x ≤ 0) ∧
      (∀ x, h x = 0 → ρ x = 0 ∧ β x = 0) := by
  by_cases hc : 0 ≤ ∫ x, h x ∂μ
  · obtain ⟨ρ,hρ,hρ0,_,hi,hcost,hzero⟩ := positive_residual hh hc
    refine ⟨ρ,fun x => h x-ρ x,hρ,hh.sub hρ,fun x => by ring,hi,?_,?_,?_,
      fun _ => hρ0,fun hn => (not_lt_of_ge hc hn).elim,?_⟩
    · rw [integral_sub hh hρ,hi,sub_self]
    · simp_rw [abs_of_nonneg (hρ0 _)]
      rw [hi,abs_of_nonneg hc]
    · rwa [abs_of_nonneg hc]
    · intro x hx
      simp [hx,hzero x hx]
  · have hc' : (∫ x, h x ∂μ) < 0 := lt_of_not_ge hc
    have hn : 0 ≤ ∫ x, -h x ∂μ := by rw [integral_neg]; linarith
    obtain ⟨ρ,hρ,hρ0,_,hi,hcost,hzero⟩ := positive_residual hh.neg hn
    have hi' : (∫ x, ρ x ∂μ) = -(∫ x, h x ∂μ) := by simpa only [Pi.neg_apply,integral_neg] using hi
    refine ⟨fun x => -ρ x,fun x => h x+ρ x,hρ.neg,hh.add hρ,fun x => by ring,?_,?_,?_,?_,
      fun hn => (not_le_of_gt hc' hn).elim,fun _ x => neg_nonpos.mpr (hρ0 x),?_⟩
    · rw [integral_neg,hi',neg_neg]
    · rw [integral_add hh hρ,hi',add_neg_cancel]
    · simp_rw [abs_neg,abs_of_nonneg (hρ0 _)]
      rw [hi',abs_of_neg hc']
    · have heq : (fun x => |-h x-ρ x|) = fun x => |h x+ρ x| := by
        funext x
        rw [show -h x-ρ x = -(h x+ρ x) by ring,abs_neg]
      simp only [Pi.neg_apply] at hcost
      rw [heq] at hcost
      simpa only [abs_neg,integral_neg,abs_of_neg hc',sub_neg_eq_add] using hcost
    · intro x hx
      have hz := hzero x (by simp [hx])
      simp [hx,hz]

/-- One backward refinement step. The new cancelling piece has cost no larger
than the scalar norm defect of the children; overlap can only lower this cost. -/
theorem refinement_residual {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ρ : ι → α → ℝ)
    (hρ : ∀ i, Integrable (ρ i) μ) :
    ∃ R β : α → ℝ, Integrable R μ ∧ Integrable β μ ∧
      (∀ x, (∑ i, w i*ρ i x) = R x+β x) ∧
      (∫ x, R x ∂μ) = ∑ i, w i*(∫ x, ρ i x ∂μ) ∧
      (∫ x, β x ∂μ) = 0 ∧
      (∫ x, |R x| ∂μ) = |∑ i, w i*(∫ x, ρ i x ∂μ)| ∧
      (∫ x, |β x| ∂μ) ≤
        (∑ i, w i*(∫ x, |ρ i x| ∂μ))-|∑ i, w i*(∫ x, ρ i x ∂μ)| ∧
      ((0 ≤ ∑ i, w i*(∫ x, ρ i x ∂μ)) → ∀ x, 0 ≤ R x) ∧
      (∀ x, (∀ i, w i*ρ i x = 0) → R x = 0 ∧ β x = 0) := by
  classical
  let f : α → ℝ := fun x => ∑ i, w i*ρ i x
  have hf : Integrable f μ := integrable_finsetSum _ (fun i _ => (hρ i).const_mul _)
  have hfi : (∫ x, f x ∂μ) = ∑ i, w i*(∫ x, ρ i x ∂μ) := by
    rw [show f = fun x => ∑ i, w i*ρ i x from rfl,integral_finsetSum]
    · simp only [integral_const_mul]
    · exact fun i _ => (hρ i).const_mul _
  have hcost : (∫ x, |f x| ∂μ) ≤ ∑ i, w i*(∫ x, |ρ i x| ∂μ) := by
    calc
      _ ≤ ∫ x, ∑ i, w i*|ρ i x| ∂μ := by
        apply integral_mono hf.abs (integrable_finsetSum _ (fun i _ => (hρ i).abs.const_mul _))
        intro x
        calc
          _ ≤ ∑ i, |w i*ρ i x| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by simp_rw [abs_mul,abs_of_nonneg (hw _)]
      _ = _ := by
        rw [integral_finsetSum _ (fun i _ => (hρ i).abs.const_mul _)]
        simp only [integral_const_mul]
  obtain ⟨R,β,hR,hβ,hdec,hi,hzero,habs,hβcost,hpos,_,hsupp⟩ := residual_split hf
  refine ⟨R,β,hR,hβ,hdec,hi.trans hfi,hzero,?_,?_,?_,?_⟩
  · rwa [hfi] at habs
  · rw [hβcost,hfi]
    exact sub_le_sub_right hcost _
  · intro hp
    apply hpos
    rwa [hfi]
  · intro x hx
    apply hsupp
    exact Finset.sum_eq_zero (fun i _ => hx i)

end ScalarCancellation

namespace ScalarCancellation
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Canonical positive/negative root selected from the proved scalar splitting,
not an assumed decomposition. -/
def root (μ : Measure α) (f : α → ℝ) : α → ℝ := by
  classical
  exact if h : Integrable f μ then (residual_split h).choose else 0

lemma root_spec {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (root μ f) μ ∧
      (∫ x, root μ f x ∂μ) = ∫ x, f x ∂μ ∧
      (∫ x, |root μ f x| ∂μ) = |∫ x, f x ∂μ| ∧
      (∫ x, |f x-root μ f x| ∂μ) = (∫ x, |f x| ∂μ)-|∫ x, f x ∂μ| ∧
      ((0 ≤ ∫ x, f x ∂μ) → ∀ x, 0 ≤ root μ f x) ∧
      ((∫ x, f x ∂μ) < 0 → ∀ x, root μ f x ≤ 0) ∧
      (∀ x, f x = 0 → root μ f x = 0) := by
  rw [root,dite_eq_left hf]
  obtain ⟨β,hR,_,hdec,hi,_,habs,hcost,hpos,hneg,hsupp⟩ := (residual_split hf).choose_spec
  refine ⟨hR,hi,habs,?_,hpos,hneg,fun x hx => (hsupp x hx).1⟩
  convert hcost using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp only; rw [hdec x]; congr 1; ring)

variable {ι : Type*} [Fintype ι]

def refined (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ) : ℕ → ι → α → ℝ
  | 0,q => f q
  | k+1,q => fun x => ∑ s, w k q s*refined w f k s x

def roots (μ : Measure α) (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ) : ℕ → ι → α → ℝ
  | 0,q => root μ (f q)
  | k+1,q => root μ (fun x => ∑ s, w k q s*roots μ w f k s x)

def errors (μ : Measure α) (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ) : ℕ → ι → α → ℝ
  | 0,q => fun x => f q x-roots μ w f 0 q x
  | k+1,q => fun x => (∑ s, w k q s*roots μ w f k s x)-roots μ w f (k+1) q x

lemma refined_integrable (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    Integrable (refined w f k q) μ := by
  induction k generalizing q with
  | zero => exact hf q
  | succ k ih => exact integrable_finsetSum _ (fun s _ => (ih s).const_mul _)

lemma roots_integrable (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    Integrable (roots μ w f k q) μ := by
  induction k generalizing q with
  | zero => exact (root_spec (hf q)).1
  | succ k ih => exact (root_spec (integrable_finsetSum _ (fun s _ => (ih s).const_mul _))).1

lemma roots_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, roots μ w f k q x ∂μ) = ∫ x, refined w f k q x ∂μ := by
  induction k generalizing q with
  | zero => exact (root_spec (hf q)).2.1
  | succ k ih =>
    rw [roots,(root_spec (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _))).2.1,
      refined,integral_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _),
      integral_finsetSum _ (fun s _ => (refined_integrable w hf k s).const_mul _)]
    simp_rw [integral_const_mul,ih]

lemma roots_abs_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, |roots μ w f k q x| ∂μ) = |∫ x, refined w f k q x ∂μ| := by
  cases k with
  | zero => exact (root_spec (hf q)).2.2.1
  | succ k =>
    have hs := root_spec (integrable_finsetSum Finset.univ
      (fun s _ => (roots_integrable w hf k s).const_mul (w k q s)))
    change (∫ x, |root μ _ x| ∂μ) = _
    rw [hs.2.2.1,← hs.2.1]
    exact congrArg abs (roots_mass w hf (k+1) q)

lemma errors_integrable (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    Integrable (errors μ w f k q) μ := by
  cases k with
  | zero => exact (hf q).sub (roots_integrable w hf 0 q)
  | succ k =>
    exact (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _)).sub
      (roots_integrable w hf (k+1) q)

lemma errors_zero_mass (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, errors μ w f k q x ∂μ) = 0 := by
  cases k with
  | zero =>
    rw [errors,integral_sub (hf q) (roots_integrable w hf 0 q),roots_mass]
    exact sub_self _
    exact hf
  | succ k =>
    rw [errors,integral_sub
      (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _))
      (roots_integrable w hf (k+1) q),roots,
      (root_spec (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _))).2.1,
      sub_self]

/-- The whole scalar cancellation tree is built by backward splitting. Each
nonterminal zero-mass piece costs at most its positive refinement norm defect. -/
theorem errors_cost (w : ℕ → ι → ι → ℝ) (hw : ∀ k q s, 0 ≤ w k q s)
    {f : ι → α → ℝ} (hf : ∀ q, Integrable (f q) μ) (k : ℕ) (q : ι) :
    (∫ x, |errors μ w f (k+1) q x| ∂μ) ≤
      (∑ s, w k q s*|∫ x, refined w f k s x ∂μ|)-|∫ x, refined w f (k+1) q x ∂μ| := by
  have hi : Integrable (fun x => ∑ s, w k q s*roots μ w f k s x) μ :=
    integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).const_mul _)
  have hs := root_spec hi
  change (∫ x, |(∑ s, w k q s*roots μ w f k s x)-root μ _ x| ∂μ) ≤ _
  rw [hs.2.2.2.1]
  have hm : (∫ x, ∑ s, w k q s*roots μ w f k s x ∂μ) = ∫ x, refined w f (k+1) q x ∂μ := by
    rw [← hs.2.1]
    exact roots_mass w hf (k+1) q
  rw [hm]
  apply sub_le_sub_right
  calc
    _ ≤ ∫ x, ∑ s, w k q s*|roots μ w f k s x| ∂μ := by
      apply integral_mono hi.abs (integrable_finsetSum _ (fun s _ => (roots_integrable w hf k s).abs.const_mul _))
      intro x
      calc
        _ ≤ ∑ s, |w k q s*roots μ w f k s x| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp_rw [abs_mul,abs_of_nonneg (hw k q _)]
    _ = _ := by
      rw [integral_finsetSum _ (fun s _ => (roots_integrable w hf k s).abs.const_mul _)]
      simp_rw [integral_const_mul,roots_abs_mass w hf]

lemma errors_terminal_cost (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (q : ι) :
    (∫ x, |errors μ w f 0 q x| ∂μ) = (∫ x, |f q x| ∂μ)-|∫ x, f q x ∂μ| :=
  (root_spec (hf q)).2.2.2.1

lemma error_recurrence (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ) (k : ℕ) (q : ι) (x : α) :
    refined w f (k+1) q x-roots μ w f (k+1) q x = errors μ w f (k+1) q x+
      ∑ s, w k q s*(refined w f k s x-roots μ w f k s x) := by
  simp only [refined,errors,mul_sub,Finset.sum_sub_distrib]
  ring

/-- Support nesting is preserved by the new construction, even when child
scalar masses vanish or overlapping densities cancel each other. -/
theorem roots_errors_support (w : ℕ → ι → ι → ℝ) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (S : ℕ → ι → Set α)
    (hfS : ∀ q x, x ∉ S 0 q → f q x = 0)
    (hS : ∀ k q s, w k q s ≠ 0 → S k s ⊆ S (k+1) q) :
    ∀ k q x, x ∉ S k q → roots μ w f k q x = 0 ∧ errors μ w f k q x = 0 := by
  intro k
  induction k with
  | zero =>
    intro q x hx
    have hf0 := hfS q x hx
    have hR0 := (root_spec (hf q)).2.2.2.2.2.2 x hf0
    exact ⟨hR0,by simp only [errors,roots,hf0,hR0,sub_self]⟩
  | succ k ih =>
    intro q x hx
    have hz : (∑ s, w k q s*roots μ w f k s x) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      by_cases hw : w k q s = 0
      · simp [hw]
      · have hs : x ∉ S k s := fun h => hx (hS k q s hw h)
        rw [(ih s x hs).1,mul_zero]
    have hR0 := (root_spec (integrable_finsetSum Finset.univ
      (fun s _ => (roots_integrable w hf k s).const_mul (w k q s)))).2.2.2.2.2.2 x hz
    exact ⟨hR0,by simp only [errors,roots,hz,hR0,sub_self]⟩

end ScalarCancellation

namespace ScalarCancellation
open Finset
variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]

lemma scalar_defect_sum (w : ℕ → ι → ι → ℝ) (hw : ∀ k q s, 0 ≤ w k q s)
    (hcol : ∀ k s, ∑ q, w k q s = 1) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) :
    (∑ q, ∫ x, |errors μ w f (k+1) q x| ∂μ) ≤
      (∑ q, |∫ x, refined w f k q x ∂μ|)-(∑ q, |∫ x, refined w f (k+1) q x ∂μ|) := by
  calc
    _ ≤ ∑ q, ((∑ s, w k q s*|∫ x, refined w f k s x ∂μ|)-|∫ x, refined w f (k+1) q x ∂μ|) :=
      sum_le_sum (fun q _ => errors_cost w hw hf k q)
    _ = _ := by
      rw [sum_sub_distrib,sum_comm]
      congr 1
      apply sum_congr rfl
      intro s _
      rw [← sum_mul,hcol,one_mul]

/-- The total cancellation cost of all levels is bounded by the actual scalar
input mass, independently of the number of refinement levels. -/
theorem errors_total_cost (w : ℕ → ι → ι → ℝ) (hw : ∀ k q s, 0 ≤ w k q s)
    (hcol : ∀ k s, ∑ q, w k q s = 1) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q, ∫ x, |errors μ w f k q x| ∂μ) +
      (∑ q, |∫ x, refined w f n q x ∂μ|) ≤ ∑ q, ∫ x, |f q x| ∂μ := by
  induction n with
  | zero =>
    simp only [Nat.zero_add,range_one,sum_singleton,errors_terminal_cost w hf,refined,sum_sub_distrib]
    exact (sub_add_cancel _ _).le
  | succ n ih =>
    rw [sum_range_succ]
    have hstep := scalar_defect_sum w hw hcol hf n
    linarith

lemma errors_total_cost_le (w : ℕ → ι → ι → ℝ) (hw : ∀ k q s, 0 ≤ w k q s)
    (hcol : ∀ k s, ∑ q, w k q s = 1) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q, ∫ x, |errors μ w f k q x| ∂μ) ≤ ∑ q, ∫ x, |f q x| ∂μ := by
  have h := errors_total_cost w hw hcol hf n
  have hx : 0 ≤ ∑ q, |∫ x, refined w f n q x ∂μ| := sum_nonneg (fun _ _ => abs_nonneg _)
  linarith

/-- Exact expansion in a coherent family of refinement coefficients. The
finite zero-mass pieces are the explicitly constructed `errors`, not merely
scalar mass certificates. -/
theorem telescoped_decomposition [DecidableEq ι] (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ)
    (Λ : ℕ → ℕ → ι → ι → ℝ)
    (hdiag : ∀ k q s, Λ k k q s = if q = s then 1 else 0)
    (hstep : ∀ k j q s, j ≤ k → Λ (k+1) j q s = ∑ a, w k q a*Λ k j a s)
    (k : ℕ) (q : ι) (x : α) :
    refined w f k q x = roots μ w f k q x +
      ∑ j ∈ range (k+1), ∑ s, Λ k j q s*errors μ w f j s x := by
  classical
  induction k generalizing q with
  | zero =>
    simp only [Nat.zero_add,Finset.range_one,sum_singleton,hdiag,ite_mul,one_mul,zero_mul]
    rw [sum_ite_eq univ q]
    simp only [Finset.mem_univ,ite_true,errors,refined]
    ring
  | succ k ih =>
    rw [sum_range_succ]
    have hlast : (∑ s, Λ (k+1) (k+1) q s*errors μ w f (k+1) s x) = errors μ w f (k+1) q x := by
      simp only [hdiag,ite_mul,one_mul,zero_mul]
      simp
    rw [hlast,errors,refined]
    simp_rw [ih]
    simp only [mul_add,sum_add_distrib]
    have hsum : (∑ a, w k q a*(∑ j ∈ range (k+1), ∑ s, Λ k j a s*errors μ w f j s x)) =
        ∑ j ∈ range (k+1), ∑ s, Λ (k+1) j q s*errors μ w f j s x := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      rw [hstep k j q s (Nat.le_of_lt_succ (mem_range.mp hj)),sum_mul]
      apply sum_congr rfl
      intro a _
      ring
    rw [hsum]
    ring

end ScalarCancellation

open MeasureTheory Set
open scoped ENNReal NNReal Topology
noncomputable section

end
end

end OAI
