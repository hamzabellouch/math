import OAI.Analysis.TreePotential.TailEstimates

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

/- Finite fair histories. Each new sign is consed to its past; the order is
chronological from the right. This is the uniform space {±1}^k in bit notation. -/
namespace Dyadic

def histories : ℕ → List (List Bool)
  | 0 => [[]]
  | k+1 => (histories k).flatMap (fun w => [false::w,true::w])

def average (k : ℕ) (f : List Bool → ℝ) : ℝ :=
  ((2:ℝ)^k)⁻¹ * ((histories k).map f).sum

lemma mem_histories {k : ℕ} {w : List Bool} : w ∈ histories k ↔ w.length = k := by
  induction k generalizing w with
  | zero => simp [histories]
  | succ k ih =>
    cases w with
    | nil => simp [histories]
    | cons b w => cases b <;> simp [histories, List.mem_flatMap, ih]

lemma average_zero (f : List Bool → ℝ) : average 0 f = f [] := by simp [average, histories]

lemma average_succ (k : ℕ) (f : List Bool → ℝ) :
    average (k+1) f = average k (fun w => (f (false::w)+f (true::w))/2) := by
  have he (l : List (List Bool)) :
      ((l.flatMap (fun w => [false::w,true::w])).map f).sum =
      2*((l.map (fun w => (f (false::w)+f (true::w))/2)).sum) := by
    induction l with
    | nil => simp
    | cons w l ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, ih]
      ring
  simp only [average, histories, he, pow_succ, mul_inv_rev]
  ring

lemma average_const (k : ℕ) (c : ℝ) : average k (fun _ => c) = c := by
  induction k with
  | zero => exact average_zero _
  | succ k ih => rw [average_succ]; simpa using ih

lemma average_mono {k : ℕ} {f g : List Bool → ℝ} (h : ∀ w, w.length = k → f w ≤ g w) :
    average k f ≤ average k g := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact List.sum_le_sum (fun w hw => h w (mem_histories.mp hw))

lemma average_congr {k : ℕ} {f g : List Bool → ℝ} (h : ∀ w, w.length = k → f w = g w) :
    average k f = average k g := le_antisymm (average_mono (fun w hw => (h w hw).le))
      (average_mono (fun w hw => (h w hw).ge))

lemma average_add (k : ℕ) (f g : List Bool → ℝ) :
    average k (fun w => f w+g w) = average k f+average k g := by
  unfold average
  rw [List.sum_map_add]
  ring

lemma average_mul (k : ℕ) (c : ℝ) (f : List Bool → ℝ) :
    average k (fun w => c*f w) = c*average k f := by
  unfold average
  rw [List.sum_map_mul_left]
  ring

lemma average_sub (k : ℕ) (f g : List Bool → ℝ) :
    average k (fun w => f w-g w) = average k f-average k g := by
  have he : (fun w => f w-g w) = (fun w => f w+(-1)*g w) := by funext w; ring
  rw [he, average_add, average_mul]
  ring

lemma average_nonneg {k : ℕ} {f : List Bool → ℝ} (h : ∀ w, w.length = k → 0 ≤ f w) :
    0 ≤ average k f := by
  simpa only [average_const] using average_mono h

/-- The one-step arithmetic martingale identity on fair dyadic histories. -/
def IsMartingale {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (W : List Bool → E) : Prop :=
  ∀ w, w.length < m → W w = (1/2 : ℝ) • (W (false::w)+W (true::w))

lemma endpoints {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℕ} {W : List Bool → E} (hW : IsMartingale m W) (w : List Bool) (hw : w.length < m) :
    W w+(1/2 : ℝ) • (W (false::w)-W (true::w)) = W (false::w) ∧
    W w-(1/2 : ℝ) • (W (false::w)-W (true::w)) = W (true::w) := by
  rw [hW w hw]
  constructor <;> module

/-- Telescoping a predictable fair-child estimate, with the exact uniform
averages and finite horizon, rather than an assumed energy conclusion. -/
lemma telescope {m : ℕ} {v e : List Bool → ℝ} (hv : ∀ w, 0 ≤ v w)
    (he : ∀ w, w.length < m → (e (false::w)+e (true::w))/2 ≤
      16*((v (false::w)+v (true::w))/2-v w)) :
    (∑ i ∈ Finset.range m, average (i+1) e) ≤ 16*average m v := by
  have hstep : ∀ i < m, average (i+1) e ≤ 16*(average (i+1) v-average i v) := by
    intro i hi
    rw [average_succ, average_succ]
    have hh := average_mono (k := i) (fun w hw => he w (by omega))
    rw [average_mul, average_sub] at hh
    exact hh
  have hh : ∀ k ≤ m, (∑ i ∈ Finset.range k, average (i+1) e) ≤
      16*(average k v-average 0 v) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 := hstep k (by omega)
      linarith
  have h0 : 0 ≤ average 0 v := by rw [average_zero]; exact hv []
  linarith [hh m le_rfl]

end Dyadic

namespace CostHeads
open TreeCalculus BlockCalculus _root_.OAI.BoundedTreePotentials.Dyadic

/-- Exact predictable timing: P_i has the same value for the two children
of a history of length i-1. The support and nesting clauses are retained. -/
structure PredictableLinearHeads (m : ℕ) (W : List Bool → LinearOuter)
    (P : List Bool → FiniteOuterHead) : Prop where
  predictable : ∀ w, w.length < m → P (false::w) = P (true::w)
  nested : ∀ w b, w.length < m → ∀ n, (P w).nodes n ⊆ (P (b::w)).nodes n
  supported : ∀ w, w.length ≤ m → linearOuterHead (P w).nodes (P w).initial (W w) = W w

/-- Measurable-window restriction to P_i \ P_{i-1}. -/
def linearLayer (P : List Bool → FiniteOuterHead) (W : List Bool → LinearOuter)
    (w : List Bool) : LinearOuter :=
  linearOuterHead (P w).nodes (P w).initial (W w) -
    linearOuterHead (P w.tail).nodes (P w.tail).initial (W w)

lemma linear_predictable_step {m : ℕ} {W : List Bool → LinearOuter}
    {P : List Bool → FiniteOuterHead} (hW : IsMartingale m W)
    (hP : PredictableLinearHeads m W P) (w : List Bool) (hw : w.length < m) :
    (‖linearLayer P W (false::w)‖^2+‖linearLayer P W (true::w)‖^2)/2 ≤
      16*((‖W (false::w)‖^2+‖W (true::w)‖^2)/2-‖W w‖^2) := by
  let z := (1/2 : ℝ) • (W (false::w)-W (true::w))
  obtain ⟨hp, hm⟩ := endpoints hW w hw
  have hx := hP.supported w hw.le
  have he := linear_fresh_energy_sixteen (P w) (W w) z hx
  change W w+z = W (false::w) at hp
  change W w-z = W (true::w) at hm
  rw [hp, hm] at he
  have hplus : linearLayer P W (false::w) = z-linearOuterHead (P w).nodes (P w).initial z := by
    unfold linearLayer
    rw [hP.supported _ (by simp only [List.length_cons]; omega)]
    simp only [List.tail_cons]
    rw [← hp, map_add, hx]
    abel
  have hminus : linearLayer P W (true::w) = -(z-linearOuterHead (P w).nodes (P w).initial z) := by
    unfold linearLayer
    rw [hP.supported _ (by simp only [List.length_cons]; omega)]
    simp only [List.tail_cons]
    rw [← hm, map_sub, hx]
    abel
  rw [hplus, hminus, norm_neg]
  linarith

/-- A stronger constant is proved first. No predictability or support premise
is moved to the wrong side of the newly revealed sign. -/
theorem linear_predictable_energy_sixteen {m : ℕ} {W : List Bool → LinearOuter}
    {P : List Bool → FiniteOuterHead} (hW : IsMartingale m W)
    (hP : PredictableLinearHeads m W P) :
    (∑ i ∈ Finset.range m, average (i+1) (fun w => ‖linearLayer P W w‖^2)) ≤
      16*average m (fun w => ‖W w‖^2) :=
  telescope (fun _ => sq_nonneg _) (linear_predictable_step hW hP)

theorem linear_predictable_energy_495 {m : ℕ} {W : List Bool → LinearOuter}
    {P : List Bool → FiniteOuterHead} (hW : IsMartingale m W)
    (hP : PredictableLinearHeads m W P) {C : ℝ}
    (hC : ∀ w, w.length = m → ‖W w‖ ≤ C) :
    (∑ i ∈ Finset.range m, average (i+1) (fun w => ‖linearLayer P W w‖^2)) ≤ 495*C^2 := by
  have he := linear_predictable_energy_sixteen hW hP
  have hb : average m (fun w => ‖W w‖^2) ≤ C^2 := by
    rw [← average_const m (C^2)]
    apply average_mono
    intro w hw
    have hc := hC w hw
    nlinarith [norm_nonneg (W w)]
  nlinarith [sq_nonneg C]

theorem linear_variation_energy_252 {m : ℕ} {W : List Bool → LinearOuter}
    {P : List Bool → FiniteOuterHead} (hW : IsMartingale m W)
    (hP : PredictableLinearHeads m W P) {C : ℝ}
    (hC : ∀ w, w.length = m → ‖W w‖ ≤ C) :
    (∑ i ∈ Finset.range m, average (i+1) (fun w => ‖linearLayer P W w‖^2)) ≤ 252*C^2 := by
  have he := linear_predictable_energy_sixteen hW hP
  have hb : average m (fun w => ‖W w‖^2) ≤ C^2 := by
    rw [← average_const m (C^2)]
    apply average_mono
    intro w hw
    have hc := hC w hw
    nlinarith [norm_nonneg (W w)]
  nlinarith [sq_nonneg C]

end CostHeads


end BoundedTreePotentials

end

end OAI
