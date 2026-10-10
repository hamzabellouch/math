import OAI.Analysis.TreePotential.CostCompletion

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

/- A leakage refinement of inward clipping. The error multiplies the tail
parameter, rather than the head parameter. This allows square-summable leakage
without any support hypothesis on the martingale. -/
namespace BlockCalculus
open TreeCalculus
open scoped Classical

lemma inward_pair_identity_leak {n : ℕ} {D : Set Node} (hD : Initial D)
    (h g x y : TreeHilbert n) (hh : head D h = h) (a b : ℝ) :
    inner ℝ (a • h+b • inwardOne hD h g hh) (x+y) +
      inner ℝ (a • h+b • inwardTwo hD h g hh) (x-y) =
    2*a*inner ℝ h (head D x) + b*inner ℝ g (y-head D y) +
      b*inner ℝ (inwardOne hD h g hh+inwardTwo hD h g hh) (x-head D x) := by
  have hhead : inner ℝ h (head D x) = inner ℝ h x := by rw [← head_inner, hh]
  have hr1 : inner ℝ (inwardOne hD h g hh) (head D x) = 0 := by
    rw [← head_inner, inwardOne_head, inner_zero_left]
  have hr2 : inner ℝ (inwardTwo hD h g hh) (head D x) = 0 := by
    rw [← head_inner, inwardTwo_head, inner_zero_left]
  have hd : inner ℝ (inwardOne hD h g hh) y-inner ℝ (inwardTwo hD h g hh) y =
      inner ℝ g (y-head D y) := by
    rw [← inner_sub_left, inward_difference, inner_sub_left, head_inner, inner_sub_right]
  rw [hhead, ← hd]
  simp only [inner_add_left, inner_add_right, inner_sub_right, real_inner_smul_left, hr1, hr2]
  ring

lemma InwardPiece.linear_le_two {n : ℕ} {D : Set Node} {h g r : TreeHilbert n}
    (hr : InwardPiece D h g r) (hh : head D h = h) (hg : linearPolar n g ≤ 1) :
    linearPolar n r ≤ 2 := by
  have he := hr.linear_sq hh (a := 0) (b := 1) (by norm_num) (by norm_num)
  simp only [zero_smul, one_smul, zero_add, zero_pow (by decide : 2 ≠ 0),
    one_pow, zero_mul, mul_one] at he
  have hn := linearPolar_nonneg g
  nlinarith [linearPolar_nonneg r]

lemma InwardPiece.error_bound {n : ℕ} {D : Set Node} {h g r : TreeHilbert n}
    (hr : InwardPiece D h g r) (hh : head D h = h) (hg : linearPolar n g ≤ 1)
    (z : TreeHilbert n) : -2*linearBlockCost n z ≤ inner ℝ r z := by
  have he := linearBlockCost_abs_eval_scaled r z
  have hp := hr.linear_le_two hh hg
  have hz : 0 ≤ linearBlockCost n z := linearCost_nonneg _ _
  have hi := neg_abs_le (inner ℝ r z)
  have hm := mul_le_mul_of_nonneg_right hp hz
  linarith

theorem linear_paired_leak {n : ℕ} {D : Set Node} (hD : Initial D)
    (x y : TreeHilbert n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2+4*b^2 ≤ 1) :
    a*linearBlockCost n (head D x)+(b/2)*linearBlockCost n (y-head D y) ≤
      (linearBlockCost n (x+y)+linearBlockCost n (x-y))/2 +
        2*b*linearBlockCost n (x-head D x) := by
  obtain ⟨f, hf, hfx⟩ := linearBlockCost_norming n (head D x)
  obtain ⟨g, hg, hgy⟩ := linearBlockCost_norming n (y-head D y)
  let h := head D f
  have hh : head D h = h := head_idem D f
  have hh1 : linearPolar n h ≤ 1 := (head_linearPolar_le hD f).trans hf
  have hhx : inner ℝ h (head D x) = linearBlockCost n (head D x) := by
    dsimp [h]
    rw [head_inner, head_idem, hfx]
  have hp := linearBlockCost_eval_le ((inwardOne_piece hD h g hh).linear_budget hh hh1 hg ha hb hab) (x+y)
  have hm := linearBlockCost_eval_le ((inwardTwo_piece hD h g hh).linear_budget hh hh1 hg ha hb hab) (x-y)
  have he := inward_pair_identity_leak hD h g x y hh a b
  rw [hhx, hgy] at he
  simp only [inner_add_left] at he hp hm
  have hr1 := (inwardOne_piece hD h g hh).error_bound hh hg (x-head D x)
  have hr2 := (inwardTwo_piece hD h g hh).error_bound hh hg (x-head D x)
  have herr := mul_le_mul_of_nonneg_left (add_le_add hr1 hr2) hb
  nlinarith

end BlockCalculus

lemma leakage_energy_scalar {r l q c d u v : ℝ}
    (hr : 0 ≤ r) (hl : 0 ≤ l) (hq : 0 ≤ q) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hup : u ≤ l+q) (hvp : v ≤ l+q)
    (h : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a^2+4*b^2 ≤ 1 →
      a*r+(b/2)*q ≤ (c+d)/2+2*b*l) :
    (u^2+v^2)/2 ≤ 50*l^2+32*((c^2+d^2)/2-r^2) := by
  have hbase := h 1 0 (by norm_num) (by norm_num) (by norm_num)
  have hgap : r^2 ≤ (c^2+d^2)/2 := by nlinarith [sq_nonneg (c-d)]
  have hup2 : u^2 ≤ (l+q)^2 := by nlinarith
  have hvp2 : v^2 ≤ (l+q)^2 := by nlinarith
  by_cases hq4 : 4*l ≤ q
  · have hroot := BlockCalculus.ellipse_sup_bound hr (show 0 ≤ q-4*l by linarith)
      (show 0 ≤ (c+d)/2 by positivity) (by
        intro a b ha hb hab
        have he := h a b ha hb hab
        nlinarith)
    have hs := Real.sq_sqrt (show 0 ≤ r^2+(q-4*l)^2/16 by positivity)
    have hn := Real.sqrt_nonneg (r^2+(q-4*l)^2/16)
    have he : r^2+(q-4*l)^2/16 ≤ (c^2+d^2)/2 := by
      nlinarith [sq_nonneg (c-d)]
    nlinarith [sq_nonneg (q-9*l)]
  · have hq5 : (l+q)^2 ≤ 25*l^2 := by nlinarith
    nlinarith [sq_nonneg l]

namespace BlockCalculus
open TreeCalculus
open scoped Classical

/-- One-step energy with actual leakage, valid with no head support assumption. -/
theorem linear_leakage_step {n : ℕ} {D : Set Node} (hD : Initial D)
    (x y : TreeHilbert n) :
    ((linearBlockCost n ((x+y)-head D (x+y)))^2+
      (linearBlockCost n ((x-y)-head D (x-y)))^2)/2 ≤
      50*(linearBlockCost n (x-head D x))^2+
      32*(((linearBlockCost n (x+y))^2+(linearBlockCost n (x-y))^2)/2-
        (linearBlockCost n (head D x))^2) := by
  have hp : linearBlockCost n ((x+y)-head D (x+y)) ≤
      linearBlockCost n (x-head D x)+linearBlockCost n (y-head D y) := by
    have he : (x+y)-head D (x+y) = (x-head D x)+(y-head D y) := by
      rw [show head D (x+y) = head D x+head D y from (headLM D).map_add x y]
      abel
    rw [he]
    exact linearCost_add_le _ _ _
  have hm : linearBlockCost n ((x-y)-head D (x-y)) ≤
      linearBlockCost n (x-head D x)+linearBlockCost n (y-head D y) := by
    have he : (x-y)-head D (x-y) = (x-head D x)-(y-head D y) := by
      rw [show head D (x-y) = head D x-head D y from (headLM D).map_sub x y]
      abel
    rw [he]
    change ‖(linearBlockEquiv n).symm ((x-head D x)-(y-head D y))‖ ≤
      ‖(linearBlockEquiv n).symm (x-head D x)‖+‖(linearBlockEquiv n).symm (y-head D y)‖
    rw [map_sub]
    exact norm_sub_le _ _
  apply leakage_energy_scalar (linearCost_nonneg _ _) (linearCost_nonneg _ _)
    (linearCost_nonneg _ _) (linearCost_nonneg _ _) (linearCost_nonneg _ _)
    (linearCost_nonneg _ _) (linearCost_nonneg _ _) hp hm
  intro a b ha hb hab
  exact linear_paired_leak hD x y ha hb hab

lemma head_nested {n : ℕ} {A D : Set Node} (hAD : A ⊆ D) (x : TreeHilbert n) :
    head A (head D x) = head A x := by
  ext s
  by_cases hs : s.val ∈ A
  · simp only [head_apply, ite_eq_left hs, ite_eq_left (hAD hs)]
  · simp only [head_apply, ite_eq_right hs]

end BlockCalculus

namespace CostHeads
open TreeCalculus BlockCalculus _root_.OAI.BoundedTreePotentials.Dyadic
open scoped Classical

lemma linearOuterHead_nested {A D : ℕ → Set Node} (hA : ∀ n, Initial (A n))
    (hD : ∀ n, Initial (D n)) (hAD : ∀ n, A n ⊆ D n) (x : LinearOuter) :
    linearOuterHead A hA (linearOuterHead D hD x) = linearOuterHead A hA x := by
  apply Subtype.ext
  funext n
  apply (linearBlockEquiv (n+1)).injective
  simp only [linearOuterHead_apply, linearHead_equiv, head_nested (hAD n)]

lemma linearOuterHead_norm_mono {A D : ℕ → Set Node} (hA : ∀ n, Initial (A n))
    (hD : ∀ n, Initial (D n)) (hAD : ∀ n, A n ⊆ D n) (x : LinearOuter) :
    ‖linearOuterHead A hA x‖ ≤ ‖linearOuterHead D hD x‖ := by
  rw [← linearOuterHead_nested hA hD hAD x]
  exact linearOuterHead_contract A hA _

theorem linearOuter_leakage_step (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x y : LinearOuter) :
    (‖(x+y)-linearOuterHead D hD (x+y)‖^2+
      ‖(x-y)-linearOuterHead D hD (x-y)‖^2)/2 ≤
      50*‖x-linearOuterHead D hD x‖^2+
      32*((‖x+y‖^2+‖x-y‖^2)/2-‖linearOuterHead D hD x‖^2) := by
  have hL := ((lp_hasSum_sq ((x+y)-linearOuterHead D hD (x+y))).add
    (lp_hasSum_sq ((x-y)-linearOuterHead D hD (x-y)))).div_const 2
  have hR := ((lp_hasSum_sq (x-linearOuterHead D hD x)).mul_left 50).add
    (((((lp_hasSum_sq (x+y)).add (lp_hasSum_sq (x-y))).div_const 2).sub
      (lp_hasSum_sq (linearOuterHead D hD x))).mul_left 32)
  have hh := hL.summable.tsum_le_tsum (fun n => ?_) hR.summable
  · simpa only [hL.tsum_eq, hR.tsum_eq] using hh
  · exact linear_leakage_step (hD n) (linearBlockEquiv (n+1) (x n))
      (linearBlockEquiv (n+1) (y n))

/-- Both window endpoints are chosen from the past history. Within a history
A_t is contained in D_t, and D_t is contained in either next A_{t+1}.
There is deliberately no support assertion. -/
structure AdaptiveLinearWindows (m : ℕ) (A D : List Bool → FiniteOuterHead) : Prop where
  included : ∀ w, w.length < m → ∀ n, (A w).nodes n ⊆ (D w).nodes n
  nested : ∀ w b, w.length+1 < m → ∀ n, (D w).nodes n ⊆ (A (b::w)).nodes n

def adaptiveLinearLayer (A D : List Bool → FiniteOuterHead)
    (W : List Bool → LinearOuter) (w : List Bool) : LinearOuter :=
  linearOuterHead (D w.tail).nodes (D w.tail).initial (W w)-
    linearOuterHead (A w.tail).nodes (A w.tail).initial (W w)

def adaptiveLinearLeak (A D : List Bool → FiniteOuterHead)
    (W : List Bool → LinearOuter) (w : List Bool) : LinearOuter :=
  linearOuterHead (D w).nodes (D w).initial (W w)-
    linearOuterHead (A w).nodes (A w).initial (W w)

def adaptiveLinearState (D : List Bool → FiniteOuterHead)
    (W : List Bool → LinearOuter) : List Bool → LinearOuter
  | [] => 0
  | b::w => linearOuterHead (D w).nodes (D w).initial (W (b::w))

lemma adaptiveLinearState_contract (D : List Bool → FiniteOuterHead)
    (W : List Bool → LinearOuter) (w : List Bool) : ‖adaptiveLinearState D W w‖ ≤ ‖W w‖ := by
  cases w with
  | nil => simpa only [adaptiveLinearState, norm_zero] using norm_nonneg (W [])
  | cons b w => exact linearOuterHead_contract _ _ _

lemma adaptiveLinearState_le_head {m : ℕ} {A D : List Bool → FiniteOuterHead}
    (hAD : AdaptiveLinearWindows m A D) (W : List Bool → LinearOuter)
    (w : List Bool) (hw : w.length < m) :
    ‖adaptiveLinearState D W w‖ ≤ ‖linearOuterHead (A w).nodes (A w).initial (W w)‖ := by
  cases w with
  | nil => simpa only [adaptiveLinearState, norm_zero] using norm_nonneg _
  | cons b w =>
    exact linearOuterHead_norm_mono (D w).initial (A (b::w)).initial
      (hAD.nested w b (by simpa only [List.length_cons] using hw)) _

lemma linear_adaptive_step {m : ℕ} {W : List Bool → LinearOuter}
    {A D : List Bool → FiniteOuterHead} (hW : IsMartingale m W)
    (hAD : AdaptiveLinearWindows m A D) (w : List Bool) (hw : w.length < m) :
    (‖adaptiveLinearLayer A D W (false::w)‖^2+‖adaptiveLinearLayer A D W (true::w)‖^2)/2 ≤
      50*‖adaptiveLinearLeak A D W w‖^2+
      32*((‖adaptiveLinearState D W (false::w)‖^2+‖adaptiveLinearState D W (true::w)‖^2)/2-
        ‖adaptiveLinearState D W w‖^2) := by
  let P := linearOuterHead (D w).nodes (D w).initial
  let Q := linearOuterHead (A w).nodes (A w).initial
  let z := (1/2 : ℝ) • (W (false::w)-W (true::w))
  obtain ⟨hp,hm⟩ := endpoints hW w hw
  change W w+z = W (false::w) at hp
  change W w-z = W (true::w) at hm
  have hQP (v : LinearOuter) : Q (P v) = Q v :=
    linearOuterHead_nested (A w).initial (D w).initial (hAD.included w hw) v
  have he := linearOuter_leakage_step (A w).nodes (A w).initial (P (W w)) (P z)
  change (‖P (W w)+P z-Q (P (W w)+P z)‖^2+
    ‖P (W w)-P z-Q (P (W w)-P z)‖^2)/2 ≤
    50*‖P (W w)-Q (P (W w))‖^2+
    32*((‖P (W w)+P z‖^2+‖P (W w)-P z‖^2)/2-‖Q (P (W w))‖^2) at he
  rw [← map_add P, ← map_sub P, hp, hm, hQP, hQP, hQP] at he
  have hcomp := adaptiveLinearState_le_head hAD W w hw
  change ‖adaptiveLinearState D W w‖ ≤ ‖Q (W w)‖ at hcomp
  change (‖P (W (false::w))-Q (W (false::w))‖^2+
    ‖P (W (true::w))-Q (W (true::w))‖^2)/2 ≤
    50*‖P (W w)-Q (W w)‖^2+
    32*((‖P (W (false::w))‖^2+‖P (W (true::w))‖^2)/2-
      ‖adaptiveLinearState D W w‖^2)
  nlinarith [norm_nonneg (adaptiveLinearState D W w), norm_nonneg (Q (W w))]

end CostHeads

namespace Dyadic

lemma telescope_leak {m : ℕ} {v e l : List Bool → ℝ} (hv : ∀ w, 0 ≤ v w)
    (he : ∀ w, w.length < m → (e (false::w)+e (true::w))/2 ≤
      50*l w+32*((v (false::w)+v (true::w))/2-v w)) :
    (∑ i ∈ Finset.range m, average (i+1) e) ≤
      50*(∑ i ∈ Finset.range m, average i l)+32*average m v := by
  have hstep : ∀ i < m, average (i+1) e ≤
      50*average i l+32*(average (i+1) v-average i v) := by
    intro i hi
    rw [average_succ, average_succ]
    have hh := average_mono (k := i) (fun w hw => he w (by omega))
    rw [average_add, average_mul, average_mul, average_sub] at hh
    exact hh
  have hh : ∀ k ≤ m, (∑ i ∈ Finset.range k, average (i+1) e) ≤
      50*(∑ i ∈ Finset.range k, average i l)+32*(average k v-average 0 v) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 := hstep k (by omega)
      linarith
  have h0 : 0 ≤ average 0 v := by rw [average_zero]; exact hv []
  linarith [hh m le_rfl]

end Dyadic

namespace CostHeads
open TreeCalculus BlockCalculus _root_.OAI.BoundedTreePotentials.Dyadic

/-- Adaptive-window energy with an explicit absolute constant. The leakage is
the actual parent window contribution. No parent support condition is present. -/
theorem linear_adaptive_energy_fifty {m : ℕ} {W : List Bool → LinearOuter}
    {A D : List Bool → FiniteOuterHead} (hW : IsMartingale m W)
    (hAD : AdaptiveLinearWindows m A D) :
    (∑ i ∈ Finset.range m, average (i+1) (fun w => ‖adaptiveLinearLayer A D W w‖^2)) ≤
      50*(average m (fun w => ‖W w‖^2)+
        ∑ i ∈ Finset.range m, average i (fun w => ‖adaptiveLinearLeak A D W w‖^2)) := by
  have he := telescope_leak (m := m)
    (e := fun w => ‖adaptiveLinearLayer A D W w‖^2)
    (l := fun w => ‖adaptiveLinearLeak A D W w‖^2)
    (fun w => sq_nonneg ‖adaptiveLinearState D W w‖) (linear_adaptive_step hW hAD)
  have hcomp : average m (fun w => ‖adaptiveLinearState D W w‖^2) ≤
      average m (fun w => ‖W w‖^2) := by
    apply average_mono
    intro w hw
    have hh := adaptiveLinearState_contract D W w
    nlinarith [norm_nonneg (adaptiveLinearState D W w), norm_nonneg (W w)]
  have hn : 0 ≤ average m (fun w => ‖W w‖^2) := average_nonneg (fun _ _ => sq_nonneg _)
  linarith

/-- The adaptive estimate is uniform in the horizon, martingale, and measurable nested windows. -/

theorem linear_adaptive_energy : ∃ K : ℝ, 0 < K ∧
    ∀ (m : ℕ) (W : List Bool → LinearOuter) (A D : List Bool → FiniteOuterHead),
      IsMartingale m W → AdaptiveLinearWindows m A D →
      (∑ i ∈ Finset.range m, average (i+1) (fun w => ‖adaptiveLinearLayer A D W w‖^2)) ≤
      K*(average m (fun w => ‖W w‖^2)+
        ∑ i ∈ Finset.range m, average i (fun w => ‖adaptiveLinearLeak A D W w‖^2)) := by
  exact ⟨50, by norm_num, fun _ _ _ _ hW hAD => linear_adaptive_energy_fifty hW hAD⟩

/-- Fixed finite heads without support assumptions: the stronger adaptive estimate implies the leakage constant 1024. -/

theorem linear_fixed_leakage_1024 {m : ℕ} {W : List Bool → LinearOuter}
    (P : ℕ → FiniteOuterHead) (hW : IsMartingale m W)
    (hP : ∀ i < m, ∀ n, (P i).nodes n ⊆ (P (i+1)).nodes n) :
    (∑ i ∈ Finset.range m, average (i+1) (fun w =>
      ‖linearOuterHead (P (i+1)).nodes (P (i+1)).initial (W w)-
        linearOuterHead (P i).nodes (P i).initial (W w)‖^2)) ≤
    1024*(average m (fun w => ‖W w‖^2)+
      ∑ i ∈ Finset.range m, average i (fun w =>
        ‖linearOuterHead (P (i+1)).nodes (P (i+1)).initial (W w)-
          linearOuterHead (P i).nodes (P i).initial (W w)‖^2)) := by
  let A : List Bool → FiniteOuterHead := fun w => P w.length
  let D : List Bool → FiniteOuterHead := fun w => P (w.length+1)
  have hAD : AdaptiveLinearWindows m A D := by
    constructor
    · intro w hw; exact hP w.length hw
    · intro w b hw n
      change (P (w.length+1)).nodes n ⊆ (P (List.length (b::w))).nodes n
      simp only [List.length_cons]
      exact Set.Subset.rfl
  have he := linear_adaptive_energy_fifty hW hAD
  have h1 (i : ℕ) : average (i+1) (fun w => ‖adaptiveLinearLayer A D W w‖^2) =
      average (i+1) (fun w => ‖linearOuterHead (P (i+1)).nodes (P (i+1)).initial (W w)-
        linearOuterHead (P i).nodes (P i).initial (W w)‖^2) := by
    apply average_congr
    intro w hw
    have ht : w.tail.length = i := by rw [List.length_tail, hw]; omega
    simp only [adaptiveLinearLayer, A, D, ht]
  have h2 (i : ℕ) : average i (fun w => ‖adaptiveLinearLeak A D W w‖^2) =
      average i (fun w => ‖linearOuterHead (P (i+1)).nodes (P (i+1)).initial (W w)-
        linearOuterHead (P i).nodes (P i).initial (W w)‖^2) := by
    apply average_congr
    intro w hw
    simp only [adaptiveLinearLeak, A, D, hw]
  simp_rw [h1, h2] at he
  have hn : 0 ≤ average m (fun w => ‖W w‖^2)+
      ∑ i ∈ Finset.range m, average i (fun w =>
        ‖linearOuterHead (P (i+1)).nodes (P (i+1)).initial (W w)-
          linearOuterHead (P i).nodes (P i).initial (W w)‖^2) := by
    apply add_nonneg (average_nonneg (fun _ _ => sq_nonneg _))
    exact Finset.sum_nonneg (fun i hi => average_nonneg (fun _ _ => sq_nonneg _))
  linarith

end CostHeads

end BoundedTreePotentials

end

end OAI
