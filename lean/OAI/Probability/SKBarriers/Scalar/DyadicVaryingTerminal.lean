import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFTerminalStability

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem dyadicScalarAverage_varying_terminal (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {F A : ℕ → ℝ → ℝ} {f a da : ℝ → ℝ}
    (hF : ∀ n, BoundedDerivs (F n)) (hf : BoundedDerivs f)
    (hA : ∀ n, Continuous (A n))
    (ha : ∀ z, HasDerivAt a (da z) z) (hda : Continuous da)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f)
    (hAB : ∀ n z, |A n z| ≤ B) (haB : ∀ z, |a z| ≤ B)
    (hdaC : ∀ z, |da z| ≤ C)
    (hFf : TendstoUniformly F f atTop) (hAa : TendstoUniformly A a atTop)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t (F n) (A n) x)
      atTop (𝓝 (scalarCDFAverage β α s t f a x)) := by
  have hfixed := dyadicScalarAverage_tendsto_C1 β hα hmono hf ha hda hfK haB hdaC s t ht x
  have hac : Continuous a := continuous_iff_continuousAt.mpr (fun z => (ha z).continuousAt)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let φ : ℝ → ℝ := fun e => 2*e+2*(B:ℝ)*(Real.exp (2*e)-1)
  have hφ : ContinuousAt φ 0 := by dsimp [φ]; fun_prop
  obtain ⟨δ,hδ,hbound⟩ := Metric.continuousAt_iff.mp hφ ε hε
  let e := δ/2
  have he : 0<e := half_pos hδ
  have hsmall : φ e<ε := by
    have H := hbound (show dist e 0<δ by rw [Real.dist_eq,sub_zero,abs_of_pos he]; dsimp [e]; linarith)
    have hzero : φ 0=0 := by simp [φ]
    rw [hzero,Real.dist_eq,sub_zero] at H
    exact (le_abs_self _).trans_lt H
  have E : ∀ᶠ n in atTop, dist (dyadicScalarAverage β α n s t (F n) (A n) x)
      (scalarCDFAverage β α s t f a x)<ε := by
    filter_upwards [Metric.tendstoUniformly_iff.mp hFf e he,
      Metric.tendstoUniformly_iff.mp hAa e he,Metric.tendsto_nhds.mp hfixed e he] with n hfn han hfix
    have H := scalarHierarchyAverage_terminal_stability _ _
      (fun i => β*Real.sqrt (((dyadicIntervals α n s t).get i).2:ℝ))
      (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _))
      (show Monotone (fun i : Fin (dyadicIntervals α n s t).length =>
        ((dyadicIntervals α n s t).get i).1) from by
        intro i j hij
        rcases lt_or_eq_of_le hij with hij|rfl
        · exact (List.pairwise_iff_get.mp (dyadicIntervals_pairwise hmono n s t)) i j hij
        · exact le_rfl)
      (hF n) hf he.le (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (hfn z).le)
      (hA n) hac B.coe_nonneg (hAB n) haB
      (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (han z).le) x
    change |dyadicScalarAverage β α n s t (F n) (A n) x-
      dyadicScalarAverage β α n s t f a x| ≤ _ at H
    rw [Real.dist_eq] at hfix ⊢
    calc
      _ ≤ |dyadicScalarAverage β α n s t (F n) (A n) x-
            dyadicScalarAverage β α n s t f a x|+
          |dyadicScalarAverage β α n s t f a x-scalarCDFAverage β α s t f a x| := abs_sub_le _ _ _
      _ < e+2*(B:ℝ)*(Real.exp (2*e)-1)+e := add_lt_add_of_le_of_lt H hfix
      _ = φ e := by dsimp [φ]; ring
      _ < ε := hsmall
  exact eventually_atTop.mp E

end SK.Analytic

end
end

end OAI
