import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowLocal

namespace OAI

/-! Local C⁴ flows on the open domain of the autonomous lift. A compactly
supported extension is used only in a neighborhood of the initial point. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem flow_c4_extension_near {f : FlowPhase → FlowPhase} {S : Set FlowPhase}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 4 f S) {a : FlowPhase} (ha : a ∈ S) :
    ∃ g : FlowPhase → FlowPhase, ContDiff ℝ 4 g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds ha)
  let b : ContDiffBump a := ⟨r/4,r/2,by positivity,by linarith⟩
  let g : FlowPhase → FlowPhase := fun x => b x • f x
  have hbS : tsupport b ⊆ S := by
    rw [b.tsupport_eq]
    intro x hx
    apply hrS
    change dist x a < r
    have h : dist x a ≤ r/2 := hx
    linarith
  refine ⟨g,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact b.contDiff.contDiffAt.smul (hf.contDiffAt (hS.mem_nhds (hbS hx)))
    · have heq : g =ᶠ[𝓝 x] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change b y • f y = 0
        simp only [hy,Pi.zero_apply,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · filter_upwards [b.eventuallyEq_one] with x hx
    change b x • f x = f x
    simpa only [Pi.one_apply,one_smul] using congrArg (fun z : ℝ => z • f x) hx

theorem flow_c4_local_on {f : FlowPhase → FlowPhase} {S : Set FlowPhase}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 4 f S) {a : FlowPhase} (ha : a ∈ S) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ S ∧ ∃ Φ : (ℝ × FlowPhase) → FlowPhase,
      ContDiffOn ℝ 4 Φ (Ioo (-r) r ×ˢ Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, Φ (0,x) = x) ∧
      ∀ t ∈ Ioo (-r) r, ∀ x ∈ Metric.ball a r,
        Φ (t,x) ∈ S ∧ HasDerivAt (fun s => Φ (s,x)) (f (Φ (t,x))) t := by
  obtain ⟨g,hg,hgf⟩ := flow_c4_extension_near hS hf ha
  obtain ⟨r,hr,Φ,hΦ,hΦ0,hΦder⟩ := flow_c4_local g hg a
  have hcenter : ((0:ℝ),a) ∈ Ioo (-r) r ×ˢ Metric.ball a r :=
    ⟨⟨neg_neg_of_pos hr,hr⟩,Metric.mem_ball_self hr⟩
  have hcont : ContinuousAt Φ (0,a) :=
    (hΦ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds hcenter)).continuousAt
  have hΦa : Φ (0,a) = a := hΦ0 a (Metric.mem_ball_self hr)
  have hnear : ∀ᶠ z in 𝓝 ((0:ℝ),a), Φ z ∈ S ∧ g (Φ z) = f (Φ z) := by
    have hh : ∀ᶠ y in 𝓝 (Φ (0,a)), y ∈ S ∧ g y = f y := by
      rw [hΦa]
      exact (show ∀ᶠ y in 𝓝 a, y ∈ S from hS.mem_nhds ha).and hgf
    exact hcont.eventually hh
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min (r/2) (ε/2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
  have hdom : Ioo (-δ) δ ×ˢ Metric.ball a δ ⊆ Ioo (-r) r ×ˢ Metric.ball a r := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1],hz.1.2.trans hδr⟩,lt_trans hz.2 hδr⟩
  have himg : ∀ t ∈ Ioo (-δ) δ, ∀ x ∈ Metric.ball a δ,
      Φ (t,x) ∈ S ∧ g (Φ (t,x)) = f (Φ (t,x)) := by
    intro t ht x hx
    apply hεsub
    change dist (t,x) (0,a) < ε
    rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
    exact ⟨(abs_lt.mpr ht).trans hδε,lt_trans hx hδε⟩
  refine ⟨δ,hδ,?_,Φ,hΦ.mono hdom,?_,?_⟩
  · intro x hx
    have h0 : Φ (0,x) = x := hΦ0 x (lt_trans hx hδr)
    exact h0 ▸ (himg 0 ⟨neg_neg_of_pos hδ,hδ⟩ x hx).1
  · intro x hx
    exact hΦ0 x (lt_trans hx hδr)
  · intro t ht x hx
    refine ⟨(himg t ht x hx).1,?_⟩
    rw [←(himg t ht x hx).2]
    have hz := hdom (show (t,x) ∈ Ioo (-δ) δ ×ˢ Metric.ball a δ from ⟨ht,hx⟩)
    exact hΦder t hz.1 x hz.2

end ContinuumCoulomb

end

end OAI
