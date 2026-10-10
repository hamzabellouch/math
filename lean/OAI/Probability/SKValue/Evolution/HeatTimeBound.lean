import Mathlib
import OAI.Probability.SKValue.Equations.ShortStripClose

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmooth.heat_time_bound {f : ℝ → ℝ} (hf : BoundedSmooth f) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, |_root_.deriv (_root_.deriv f) x| ≤ C) {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    |heat h f x-f x| ≤ (C/2)*h := by
  have hd (r : ℝ) (hr : r∈Ioi (0 : ℝ)) :
      HasDerivAt (fun r ↦ heat r f x) ((1/2 : ℝ)*heat r (_root_.deriv (_root_.deriv f)) x) r :=
    heat_time_hasDerivAt
      (fun y ↦ (hf.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne' y).hasDerivAt)
      (fun y ↦ (hf.deriv.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne' y).hasDerivAt)
      hf.deriv.deriv.smooth.continuous hf.expGrowth hf.deriv.expGrowth hf.deriv.deriv.expGrowth x hr
  have hl : LipschitzOnWith ⟨C/2,by positivity⟩ (fun r ↦ heat r f x) (Ioi (0 : ℝ)) := by
    apply (convex_Ioi (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun r hr ↦ (hd r hr).hasDerivWithinAt)
    intro r hr
    have hh := heat_bound hC hb r x
    have habs : |(1/2 : ℝ)*heat r (_root_.deriv (_root_.deriv f)) x| ≤ C/2 := by
      rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
      linarith
    exact_mod_cast habs
  have hc : Continuous (fun r ↦ heat r f x) :=
    (heat_continuous hf.smooth.continuous hf.expGrowth).comp (continuous_id.prodMk continuous_const)
  have hl' := LipschitzOnWith.closure hc.continuousOn hl
  rw [closure_Ioi] at hl'
  have hb' := hl'.dist_le_mul h (show h∈Ici (0 : ℝ) from hh) 0 (show (0 : ℝ)∈Ici 0 from (by simp))
  change dist (heat h f x) (heat 0 f x) ≤ (C/2)*dist h 0 at hb'
  simpa only [Real.dist_eq,heat_zero,sub_zero,abs_of_nonneg hh] using hb'

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.burgers_all_jets {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (deriv (V a)) x=heat (b-a) (iteratedDeriv n (deriv (V b))) x+
      ∫ s in a..b, γ s*heat (s-a) (iteratedDeriv n
        (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y)) x := by
  cases n with
  | zero => simpa only [iteratedDeriv_zero] using h.burgers_mild hm hγ hi ha hab hb x
  | succ m =>
    rw [congrFun (h.burgers_jet_mild hm hγ hi ha hab hb m) x]
    have hbT : b∈Icc (0 : ℝ) T := ⟨ha.trans hab,hb⟩
    rw [((h.slices b hbT).jets.iteratedDeriv m).heat_deriv,iteratedDeriv_succ]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hsT : s∈Icc (0 : ℝ) T := ⟨ha.trans hs.1,hs.2.trans hb⟩
    have hg := ((h.slices s hsT).jets.mul (h.slices s hsT).jets.deriv).iteratedDeriv m
    dsimp only
    rw [hg.heat_deriv,iteratedDeriv_succ]

lemma SmoothEvolution.temporal_jet_bound {T S Γ A : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (hST : S ≤ T) (n : ℕ) (hΓ : 0 ≤ Γ) (hA : 0 ≤ A)
    (hγbd : ∀ t∈Icc (0 : ℝ) S, |γ t| ≤ Γ)
    (hjets : ∀ t∈Icc (0 : ℝ) S, ∀ k ≤ n+2, ∀ x, |iteratedDeriv k (deriv (V t)) x| ≤ A)
    {a b : ℝ} (ha : a∈Icc (0 : ℝ) S) (hb : b∈Icc (0 : ℝ) S) (hab : a ≤ b) (x : ℝ) :
    |iteratedDeriv n (deriv (V a)) x-iteratedDeriv n (deriv (V b)) x| ≤
      (A/2+Γ*(A+lowerJetConstant n A))*(b-a) := by
  let G := fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y
  let K := A+lowerJetConstant n A
  have hK : 0 ≤ K := add_nonneg hA (lowerJetConstant_nonneg n hA)
  have hG (s : ℝ) (hs : s∈Icc a b) (y : ℝ) : |iteratedDeriv n (G s) y| ≤ K := by
    have hsS : s∈Icc (0 : ℝ) S := ⟨ha.1.trans hs.1,hs.2.trans hb.2⟩
    apply ((h.slices s ⟨hsS.1,hsS.2.trans hST⟩).product_jet_bound n hA
      (fun k hk z ↦ hjets s hsS k (by omega) z) y).trans
    exact add_le_add (hjets s hsS (n+1) (by omega) y) le_rfl
  have hint : |∫ s in a..b, γ s*heat (s-a) (iteratedDeriv n (G s)) x| ≤ Γ*K*(b-a) := by
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := Γ*K) (f := fun s ↦ γ s*heat (s-a) (iteratedDeriv n (G s)) x) (by
        intro s hs
        rw [uIoc_of_le hab] at hs
        have hsS : s∈Icc (0 : ℝ) S := ⟨ha.1.trans hs.1.le,hs.2.trans hb.2⟩
        rw [Real.norm_eq_abs,abs_mul]
        exact mul_le_mul (hγbd s hsS) (heat_bound hK (hG s ⟨hs.1.le,hs.2⟩) (s-a) x)
          (abs_nonneg _) hΓ)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),Real.dist_eq] using hbnd
  have hterm := ((h.slices b ⟨hb.1,hb.2.trans hST⟩).jets.iteratedDeriv n).heat_time_bound hA
    (fun y ↦ by simpa only [iteratedDeriv_succ,iteratedDeriv_succ'] using hjets b hb (n+2) le_rfl y)
    (sub_nonneg.mpr hab) x
  have hid := h.burgers_all_jets hm hγ hi ha.1 hab (hb.2.trans hST) n x
  rw [hid]
  rw [add_sub_right_comm]
  exact (abs_add_le _ _).trans ((add_le_add hterm hint).trans_eq (by ring))

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.restrict {T S : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hST : S ≤ T) : SmoothEvolution S γ V := by
  have hs : Icc (0 : ℝ) S⊆Icc (0 : ℝ) T := Icc_subset_Icc le_rfl hST
  refine ⟨fun t ht ↦ h.slices t (hs ht),fun x ↦ (h.continuous_value x).mono hs,
    fun n x ↦ (h.continuous_jet n x).mono hs,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := h.bound n
    exact ⟨C,hC,fun t ht ↦ hb t (hs ht)⟩
  · intro n
    obtain ⟨L,hL,hb⟩ := h.temporal n
    exact ⟨L,hL,fun s hs' t ht ↦ hb s (hs hs') t (hs ht)⟩
  · exact fun t ht s hs' ↦ h.value_pde t (hs ht) s (hs hs')
  · exact fun t ht s hs' ↦ h.gradient_pde t (hs ht) s (hs hs')

lemma SmoothEvolution.uniform_temporal_jet {T S Γ A : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (hST : S ≤ T) (n : ℕ) (hΓ : 0 ≤ Γ) (hA : 0 ≤ A)
    (hγbd : ∀ t∈Icc (0 : ℝ) S, |γ t| ≤ Γ)
    (hjets : ∀ t∈Icc (0 : ℝ) S, ∀ k ≤ n+2, ∀ x, |iteratedDeriv k (deriv (V t)) x| ≤ A)
    {a b : ℝ} (ha : a∈Icc (0 : ℝ) S) (hb : b∈Icc (0 : ℝ) S) (x : ℝ) :
    |iteratedDeriv n (deriv (V a)) x-iteratedDeriv n (deriv (V b)) x| ≤
      (A/2+Γ*(A+lowerJetConstant n A))*|a-b| := by
  rcases le_total a b with hab | hba
  · rw [abs_sub_comm a b,abs_of_nonneg (sub_nonneg.mpr hab)]
    exact h.temporal_jet_bound hm hγ hi hST n hΓ hA hγbd hjets ha hb hab x
  · rw [abs_sub_comm (iteratedDeriv n _ x),abs_of_nonneg (sub_nonneg.mpr hba)]
    exact h.temporal_jet_bound hm hγ hi hST n hΓ hA hγbd hjets hb ha hba x

lemma uniform_bulk_temporal (Γ : ℝ) (hΓ : 0 ≤ Γ) (T : ℝ) (m : ℕ)
    {S : ℝ} (hS : 0 ≤ S) (hST : S<T) : ∃ L : ℝ, 0 ≤ L ∧
      ∀ (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ), SmoothEvolution T γ V → Measurable γ →
        MonotoneOn γ (Icc (0 : ℝ) T) → (∀ t∈Icc (0 : ℝ) T, |γ t| ≤ Γ) →
        ∀ s∈Icc (0 : ℝ) S, ∀ t∈Icc (0 : ℝ) S, ∀ x,
          |iteratedDeriv m (deriv (V s)) x-iteratedDeriv m (deriv (V t)) x| ≤ L*|s-t| := by
  obtain ⟨A,hA,ha⟩ := uniform_bulk_jets Γ hΓ T (m+2) S hS hST
  refine ⟨A/2+Γ*(A+lowerJetConstant m A),by positivity [lowerJetConstant_nonneg m hA],?_⟩
  intro γ V h hm hmono hbd s hs t ht x
  have hi : IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le (hS.trans hST.le)] using hmono
  apply h.uniform_temporal_jet hm hmono hi hST.le m hΓ hA (fun r hr ↦ hbd r ⟨hr.1,hr.2.trans hST.le⟩)
    (ha γ V h hm hmono hbd) hs ht x

end SKValue

end

end OAI
