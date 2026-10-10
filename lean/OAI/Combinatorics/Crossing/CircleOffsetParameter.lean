import OAI.Combinatorics.Crossing.CircleOffset
import OAI.Combinatorics.Crossing.CircleDeterminantOrder
import Mathlib.Tactic.FunProp

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

def offsetParameter (a δ : ℝ) : ℝ :=
  (circleOffset (circlePoint a) δ).2/(1+(circleOffset (circlePoint a) δ).1)

theorem continuous_circleOffset (u : Plane) : Continuous (circleOffset u) := by
  change Continuous (fun δ : ℝ => Real.sqrt (1-δ^2) • u+δ • rotateQuarter u)
  fun_prop

@[simp] theorem offsetParameter_zero (a : ℝ) : offsetParameter a 0=a := by
  simp only [offsetParameter,circleOffset_zero,circlePoint_parameter]

theorem continuousAt_offsetParameter_zero (a : ℝ) : ContinuousAt (offsetParameter a) 0 := by
  apply ContinuousAt.div
  · exact (continuous_circleOffset (circlePoint a)).continuousAt.snd
  · exact continuousAt_const.add (continuous_circleOffset (circlePoint a)).continuousAt.fst
  · rw [circleOffset_zero,circlePoint_one_add_x]
    exact div_ne_zero (by norm_num) (ne_of_gt (circle_denominator_pos a))

theorem exists_circle_offset_parameter_radius (a ε : ℝ) (hε : 0<ε) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ δ : ℝ, |δ|<ρ →
      circlePoint (offsetParameter a δ)=circleOffset (circlePoint a) δ ∧
      |offsetParameter a δ-a|<ε ∧
      (0<δ → a<offsetParameter a δ) ∧ (δ<0 → offsetParameter a δ<a) := by
  have hp := continuousAt_offsetParameter_zero a
  have hnear : ∀ᶠ δ : ℝ in 𝓝 0, offsetParameter a δ ∈ Set.Ioo (a-ε) (a+ε) :=
    hp.eventually (isOpen_Ioo.mem_nhds (by rw [offsetParameter_zero]; constructor <;> linarith))
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0, |δ|<1 := by
    apply Metric.eventually_nhds_iff.mpr
    exact ⟨1,by norm_num,by intro delta; simp [Real.dist_eq]⟩
  have hcut : ∀ᶠ δ : ℝ in 𝓝 0, (circleOffset (circlePoint a) δ).1 ≠ -1 :=
    (continuous_circleOffset (circlePoint a)).continuousAt.fst.eventually_ne
      (by simpa using circlePoint_avoids_cut a)
  have hprodcont : ContinuousAt (fun δ : ℝ => 1+a*offsetParameter a δ) 0 :=
    continuousAt_const.add (continuousAt_const.mul hp)
  have hprod : ∀ᶠ δ : ℝ in 𝓝 0, 0<1+a*offsetParameter a δ :=
    continuousAt_const.eventually_lt hprodcont (by rw [offsetParameter_zero]; nlinarith [sq_nonneg a])
  have hevent : ∀ᶠ δ : ℝ in 𝓝 0,
      circlePoint (offsetParameter a δ)=circleOffset (circlePoint a) δ ∧
      |offsetParameter a δ-a|<ε ∧
      (0<δ → a<offsetParameter a δ) ∧ (δ<0 → offsetParameter a δ<a) := by
    filter_upwards [hnear,hsmall,hcut,hprod] with δ hnear hsmall hcut hprod
    have hunit : squaredLength (circlePoint a)=1 := circlePoint_on_unit_circle a
    have he := circlePoint_surjective_away_cut (circleOffset (circlePoint a) δ)
      (circleOffset_on_circle _ hunit δ hsmall.le) hcut
    change circlePoint (offsetParameter a δ)=circleOffset (circlePoint a) δ at he
    have hdet : det2 (circlePoint a) (circlePoint (offsetParameter a δ))=δ := by
      rw [he]
      exact circleOffset_side _ hunit δ
    refine ⟨he,?_,?_,?_⟩
    · exact abs_lt.mpr ⟨by linarith [hnear.1],by linarith [hnear.2]⟩
    · intro hδ
      apply (circle_det_pos_iff a _ hprod).mp
      rwa [hdet]
    · intro hδ
      apply (circle_det_neg_iff a _ hprod).mp
      rwa [hdet]
  obtain ⟨ρ,hρ,hh⟩ := Metric.eventually_nhds_iff.mp hevent
  exact ⟨ρ,hρ,fun δ hδ => hh (by simpa [Real.dist_eq] using hδ)⟩

end Zarankiewicz

end

end OAI
