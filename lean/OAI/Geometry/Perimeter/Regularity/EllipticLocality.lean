import OAI.Geometry.Perimeter.Regularity.GeoComposition

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem gradient_eqOn {f g : Euc n → ℝ} {U : Set (Euc n)} (hU : IsOpen U)
    (h : EqOn f g U) : EqOn (gradient f) (gradient g) U := by
  intro x hx
  unfold gradient
  congr 1
  exact Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy ↦ h hy))

 theorem fderiv_eqOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : Euc n → V} {U : Set (Euc n)} (hU : IsOpen U)
    (h : EqOn f g U) : EqOn (fderiv ℝ f) (fderiv ℝ g) U := by
  intro x hx
  exact Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy ↦ h hy))

 theorem flux_pairing_eq {V W : Euc n → Euc n} {U : Set (Euc n)}
    (h : EqOn V W U) (φ : SmoothLocalTest U) :
    (fun x ↦ inner ℝ (V x) (gradient φ.val x)) = fun x ↦ inner ℝ (W x) (gradient φ.val x) := by
  funext x
  by_cases hx : x∈U
  · rw [h hx]
  · have hx' : x∉tsupport φ.val := fun hh ↦ hx (φ.property.2.2 hh)
    simp only [gradient,fderiv_of_notMem_tsupport ℝ hx',map_zero,inner_zero_right]

 theorem WeakFluxEquation.congr {V W : Euc n → Euc n} {U : Set (Euc n)}
    (h : WeakFluxEquation V U) (he : EqOn V W U) : WeakFluxEquation W U := by
  intro φ
  rw [←flux_pairing_eq he φ]
  exact h φ

 theorem WeakLinearEquation.congr {A B : Euc n → Euc n →L[ℝ] Euc n}
    {f g : Euc n → ℝ} {F G : Euc n → Euc n} {U : Set (Euc n)} (hU : IsOpen U)
    (h : WeakLinearEquation A f F U) (hA : EqOn A B U) (hf : EqOn f g U)
    (hF : EqOn F G U) : WeakLinearEquation B g G U := by
  have hAf : EqOn (fun x ↦ A x (gradient f x)) (fun x ↦ B x (gradient g x)) U :=
    fun x hx ↦ by dsimp only; rw [hA hx,gradient_eqOn hU hf hx]
  intro φ
  change (∫ x, inner ℝ (B x (gradient g x)) (gradient φ.val x)) = _
  rw [←flux_pairing_eq hAf φ,←flux_pairing_eq hF φ]
  exact h φ

 theorem compact_continuous_bound {V : Type*} [NormedAddCommGroup V]
    {f : Euc n → V} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B := by
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max 0 B,le_max_left _ _,fun x ↦ ?_⟩
  by_cases hx : x∈tsupport f
  · exact (hB x hx).trans (le_max_right _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact le_max_left _ _

 theorem local_compact_triple {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} {U : Set (Euc n)} {k l : ℕ∞}
    (hU : IsOpen U) {p : Euc n} (hp : p∈U)
    (hA : ContDiffOn ℝ k A U) (hf : ContDiffOn ℝ l f U) (hF : ContDiffOn ℝ k F U) :
    ∃ W : Set (Euc n), IsOpen W ∧ p∈W ∧ W⊆U ∧
      ∃ B g G, ContDiff ℝ k B ∧ HasCompactSupport B ∧ ContDiff ℝ l g ∧ HasCompactSupport g ∧
        ContDiff ℝ k G ∧ HasCompactSupport G ∧ EqOn B A W ∧ EqOn g f W ∧ EqOn G F W := by
  obtain ⟨a,ha,haU,B,hB,hBc,heB⟩ := local_compact_extension hU hp hA
  obtain ⟨b,hb,hbU,g,hg,hgc,heg⟩ := local_compact_extension hU hp hf
  obtain ⟨c,hc,hcU,G,hG,hGc,heG⟩ := local_compact_extension hU hp hF
  let r := min a (min b c)
  have hr : 0<r := lt_min ha (lt_min hb hc)
  have hra : r ≤ 2*a := (min_le_left a (min b c)).trans (by linarith)
  have hrb : r ≤ 2*b := ((min_le_right a (min b c)).trans (min_le_left b c)).trans (by linarith)
  have hrc : r ≤ 2*c := ((min_le_right a (min b c)).trans (min_le_right b c)).trans (by linarith)
  refine ⟨Metric.ball p r,Metric.isOpen_ball,Metric.mem_ball_self hr,
    (Metric.ball_subset_closedBall.trans ?_),B,g,G,hB,hBc,hg,hgc,hG,hGc,?_,?_,?_⟩
  · exact (Metric.closedBall_subset_closedBall (by linarith : r ≤ 4*a)).trans haU
  · exact fun x hx ↦ heB x (Metric.ball_subset_ball hra hx)
  · exact fun x hx ↦ heg x (Metric.ball_subset_ball hrb hx)
  · exact fun x hx ↦ heG x (Metric.ball_subset_ball hrc hx)

end RPISingularHarnack

end

end OAI
