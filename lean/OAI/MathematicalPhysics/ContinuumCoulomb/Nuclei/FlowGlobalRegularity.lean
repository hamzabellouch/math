import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowLocal

namespace OAI

/-! C⁴ spatial dependence of complete Lipschitz flows in the four-dimensional
autonomous phase space. Local regularity propagates by uniqueness. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace ContinuumCoulomb

theorem flow_global_add {f : FlowPhase → FlowPhase} {K : ℝ≥0}
    (hLip : LipschitzWith K f) (G : FlowPhase → ℝ → FlowPhase)
    (h0 : ∀ x, G x 0 = x) (hG : ∀ x t, HasDerivAt (G x) (f (G x t)) t)
    (x : FlowPhase) (s t : ℝ) : G x (s+t) = G (G x s) t := by
  have heq : (fun u => G x (s+u)) = G (G x s) := by
    apply ODE_solution_unique_univ (s := fun _ => univ) (t₀ := 0)
      (fun _ => hLip.lipschitzOnWith)
    · intro u
      refine ⟨?_,mem_univ _⟩
      have hi : HasDerivAt (fun q : ℝ => s+q) 1 u := (hasDerivAt_id u).const_add s
      have hc := (hG x (s+u)).scomp u hi
      rw [one_smul] at hc
      apply hc.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun _ => rfl)
    · intro u
      exact ⟨hG (G x s) u,mem_univ _⟩
    · simp only [add_zero,h0]
  exact congrFun heq t

theorem flow_global_local {f : FlowPhase → FlowPhase} (hf : ContDiff ℝ 4 f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (G : FlowPhase → ℝ → FlowPhase)
    (h0 : ∀ x, G x 0 = x) (hG : ∀ x t, HasDerivAt (G x) (f (G x t)) t)
    (a : FlowPhase) :
    ∃ r : ℝ, 0 < r ∧
      ContDiffOn ℝ 4 (fun z : ℝ × FlowPhase => G z.2 z.1)
        (Ioo (-r) r ×ˢ Metric.ball a r) := by
  obtain ⟨r,hr,Φ,hΦ,hΦ0,hΦder⟩ := flow_c4_local f hf a
  refine ⟨r,hr,hΦ.congr ?_⟩
  intro z hz
  have heq : EqOn (G z.2) (fun t => Φ (t,z.2)) (Ioo (-r) r) := by
    apply ODE_solution_unique_of_mem_Ioo (s := fun _ => univ)
      (fun _ _ => hLip.lipschitzOnWith) (t₀ := 0)
      (show (0:ℝ) ∈ Ioo (-r) r from ⟨neg_neg_of_pos hr,hr⟩)
    · exact fun t _ => ⟨hG z.2 t,mem_univ _⟩
    · exact fun t ht => ⟨hΦder t ht z.2 hz.2,mem_univ _⟩
    · rw [h0,hΦ0 z.2 hz.2]
  exact heq hz.1

theorem flow_global_spatial_C4 {f : FlowPhase → FlowPhase} (hf : ContDiff ℝ 4 f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (G : FlowPhase → ℝ → FlowPhase)
    (h0 : ∀ x, G x 0 = x) (hG : ∀ x t, HasDerivAt (G x) (f (G x t)) t)
    (t : ℝ) : ContDiff ℝ 4 (fun x => G x t) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  let P : ℝ → Prop := fun s => ContDiffAt ℝ 4 (fun y => G y s) x
  have hloc : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro s
    obtain ⟨r,hr,hlocal⟩ := flow_global_local hf hLip G h0 hG (G x s)
    have hnear : ∀ᶠ u in 𝓝 s, |u-s| < r ∧ G x u ∈ Metric.ball (G x s) r := by
      exact ((continuousAt_id.sub continuousAt_const).abs.eventually
        (Iio_mem_nhds (by simpa using hr))).and
        ((hG x s).continuousAt.eventually (Metric.ball_mem_nhds (G x s) hr))
    filter_upwards [hnear] with u hu
    apply propext
    have htime : u-s ∈ Ioo (-r) r := abs_lt.mp hu.1
    have hback : s-u ∈ Ioo (-r) r := by
      constructor <;> linarith [htime.1,htime.2]
    have hreg (v : ℝ) (hv : v ∈ Ioo (-r) r)
        (y : FlowPhase) (hy : y ∈ Metric.ball (G x s) r) :
        ContDiffAt ℝ 4 (fun z => G z v) y := by
      exact (hlocal.contDiffAt
        ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds ⟨hv,hy⟩)).comp y
          (contDiffAt_const.prodMk contDiffAt_id)
    constructor
    · intro huP
      have hcomp := (hreg (s-u) hback (G x u) hu.2).comp x huP
      have heq : (fun y => G (G y u) (s-u)) = fun y => G y s := by
        funext y
        rw [←flow_global_add hLip G h0 hG]
        congr 1
        ring
      change ContDiffAt ℝ 4 (fun y => G y s) x
      rw [←heq]
      exact hcomp
    · intro hsP
      have hcomp := (hreg (u-s) htime (G x s) (Metric.mem_ball_self hr)).comp x hsP
      have heq : (fun y => G (G y s) (u-s)) = fun y => G y u := by
        funext y
        rw [←flow_global_add hLip G h0 hG]
        congr 1
        ring
      change ContDiffAt ℝ 4 (fun y => G y u) x
      rw [←heq]
      exact hcomp
  have hP0 : P 0 := by
    change ContDiffAt ℝ 4 (fun y => G y 0) x
    apply (contDiffAt_id : ContDiffAt ℝ 4 (id : FlowPhase → FlowPhase) x).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall h0
  change P t
  rw [hloc.apply_eq_of_preconnectedSpace t 0]
  exact hP0

theorem flow_global_joint_C4 {f : FlowPhase → FlowPhase} (hf : ContDiff ℝ 4 f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (G : FlowPhase → ℝ → FlowPhase)
    (h0 : ∀ x, G x 0 = x) (hG : ∀ x t, HasDerivAt (G x) (f (G x t)) t) :
    ContDiff ℝ 4 (fun z : ℝ × FlowPhase => G z.2 z.1) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨s,x⟩
  obtain ⟨r,hr,hlocal⟩ := flow_global_local hf hLip G h0 hG (G x s)
  have hat : ContDiffAt ℝ 4 (fun z : ℝ × FlowPhase => G z.2 z.1) (0,G x s) :=
    hlocal.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds
      ⟨⟨neg_neg_of_pos hr,hr⟩,Metric.mem_ball_self hr⟩)
  have hmap : ContDiffAt ℝ 4
      (fun z : ℝ × FlowPhase => (z.1-s,G z.2 s)) (s,x) :=
    (contDiffAt_fst.sub contDiffAt_const).prodMk
      ((flow_global_spatial_C4 hf hLip G h0 hG s).contDiffAt.comp (s,x) contDiffAt_snd)
  have hat' : ContDiffAt ℝ 4 (fun z : ℝ × FlowPhase => G z.2 z.1) (s-s,G x s) := by
    rw [sub_self]
    exact hat
  have hc := hat'.comp (s,x) hmap
  have heq : (fun z : ℝ × FlowPhase => G (G z.2 s) (z.1-s)) =
      fun z => G z.2 z.1 := by
    funext z
    rw [←flow_global_add hLip G h0 hG]
    congr 1
    ring
  exact heq ▸ hc

end ContinuumCoulomb

end

end OAI
