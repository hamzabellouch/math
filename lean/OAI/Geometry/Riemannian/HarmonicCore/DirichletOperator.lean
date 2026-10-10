import OAI.Geometry.Riemannian.HarmonicCore.MaximumPrinciple
import OAI.Geometry.Riemannian.HarmonicCore.BoundaryContinuity

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution

namespace HarmonicCounterexample.Main.SmoothMetric3

def compactSmoothData : Submodule ℝ (E3 → ℝ) where
  carrier := {H | ContDiff ℝ ∞ H ∧ HasCompactSupport H}
  zero_mem' := ⟨contDiff_const,HasCompactSupport.zero⟩
  add_mem' := fun hH hK ↦ ⟨hH.1.add hK.1,hH.2.add hK.2⟩
  smul_mem' := fun c _ hH ↦ ⟨hH.1.const_smul c,hH.2.smul_left⟩

abbrev CompactSmoothData := ↥compactSmoothData

noncomputable def classicalExtension (g : SmoothMetric3) (R : ℝ) (hR : 0<R)
    (H : CompactSmoothData) : E3 → ℝ :=
  Classical.choose (g.metric_classical_dirichlet R hR H.property.1 H.property.2)

lemma classicalExtension_spec (g : SmoothMetric3) (R : ℝ) (hR : 0<R) (H : CompactSmoothData) :
    ContinuousOn (g.classicalExtension R hR H) (Metric.closedBall 0 R) ∧
      ContDiffOn ℝ ∞ (g.classicalExtension R hR H) (Metric.ball 0 R) ∧
      (∀ p, ‖p‖=R → g.classicalExtension R hR H p=(H:E3 → ℝ) p) ∧
      (∀ x ∈ Metric.ball (0:E3) R, g.laplacian (g.classicalExtension R hR H) x=0) :=
  Classical.choose_spec (g.metric_classical_dirichlet R hR H.property.1 H.property.2)

lemma classicalExtension_C2 (g : SmoothMetric3) (R : ℝ) (hR : 0<R) (H : CompactSmoothData)
    (x : E3) (hx : x ∈ Metric.ball (0:E3) R) :
    ContDiffAt ℝ 2 (g.classicalExtension R hR H) x :=
  (((g.classicalExtension_spec R hR H).2.1 x hx).contDiffAt (Metric.isOpen_ball.mem_nhds hx)).of_le (by norm_cast)

lemma classicalExtension_congr_boundary (g : SmoothMetric3) (R : ℝ) (hR : 0<R)
    (H K : CompactSmoothData) (hHK : ∀ x, ‖x‖=R → (H:E3 → ℝ) x=(K:E3 → ℝ) x) :
    EqOn (g.classicalExtension R hR H) (g.classicalExtension R hR K) (Metric.closedBall 0 R) := by
  obtain ⟨hHc,hHs,hHb,hHl⟩ := g.classicalExtension_spec R hR H
  obtain ⟨hKc,hKs,hKb,hKl⟩ := g.classicalExtension_spec R hR K
  refine g.harmonic_unique_closedBall R hR.le hHc hKc
    (g.classicalExtension_C2 R hR H) (g.classicalExtension_C2 R hR K) hHl hKl ?_
  intro x hx
  have hx' : ‖x‖=R := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
  rw [hHb x hx',hKb x hx',hHK x hx']

noncomputable def ballDirichlet (g : SmoothMetric3) (R : ℝ) (hR : 0<R) :
    CompactSmoothData →ₗ[ℝ] C(Metric.closedBall (0:E3) R,ℝ) where
  toFun H := ⟨fun x ↦ g.classicalExtension R hR H x,
    (g.classicalExtension_spec R hR H).1.domRestrict⟩
  map_add' H K := by
    obtain ⟨hHc,hHs,hHb,hHl⟩ := g.classicalExtension_spec R hR H
    obtain ⟨hKc,hKs,hKb,hKl⟩ := g.classicalExtension_spec R hR K
    obtain ⟨hAc,hAs,hAb,hAl⟩ := g.classicalExtension_spec R hR (H+K)
    have hu := g.harmonic_unique_closedBall R hR.le hAc (hHc.add hKc)
      (g.classicalExtension_C2 R hR (H+K))
      (fun x hx ↦ (g.classicalExtension_C2 R hR H x hx).add (g.classicalExtension_C2 R hR K x hx))
      hAl (fun x hx ↦ by rw [g.laplacian_add_at (g.classicalExtension_C2 R hR H x hx)
        (g.classicalExtension_C2 R hR K x hx),hHl x hx,hKl x hx,add_zero])
      (fun x hx ↦ by
        have hs : ‖x‖=R := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
        simp only [Pi.add_apply,hAb x hs,hHb x hs,hKb x hs]
        rfl)
    ext x
    exact hu x.property
  map_smul' c H := by
    obtain ⟨hHc,hHs,hHb,hHl⟩ := g.classicalExtension_spec R hR H
    obtain ⟨hAc,hAs,hAb,hAl⟩ := g.classicalExtension_spec R hR (c • H)
    have hu := g.harmonic_unique_closedBall R hR.le hAc (hHc.const_smul c)
      (g.classicalExtension_C2 R hR (c • H))
      (fun x hx ↦ (g.classicalExtension_C2 R hR H x hx).const_smul c)
      hAl (fun x hx ↦ by rw [g.laplacian_smul_at (g.classicalExtension_C2 R hR H x hx),hHl x hx,mul_zero])
      (fun x hx ↦ by
        have hs : ‖x‖=R := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
        simp only [Pi.smul_apply,hAb x hs,hHb x hs]
        rfl)
    ext x
    exact hu x.property

lemma ballDirichlet_boundary (g : SmoothMetric3) (R : ℝ) (hR : 0<R) (H : CompactSmoothData)
    (p : E3) (hp : ‖p‖=R) :
    g.ballDirichlet R hR H ⟨p,by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.le⟩=(H:E3 → ℝ) p :=
  (g.classicalExtension_spec R hR H).2.2.1 p hp

lemma ballDirichlet_positive (g : SmoothMetric3) (R : ℝ) (hR : 0<R) (H : CompactSmoothData)
    (hpos : ∀ p, ‖p‖=R → 0 ≤ (H:E3 → ℝ) p) :
    ∀ x : Metric.closedBall (0:E3) R, 0 ≤ g.ballDirichlet R hR H x := by
  obtain ⟨hHc,hHs,hHb,hHl⟩ := g.classicalExtension_spec R hR H
  intro x
  exact g.harmonic_positive_closedBall R hR.le hHc (g.classicalExtension_C2 R hR H) hHl
    (fun p hp ↦ by
      have hs : ‖p‖=R := by simpa only [Metric.mem_sphere,dist_zero_right] using hp
      rw [hHb p hs]
      exact hpos p hs) x x.property

lemma ballDirichlet_constant (g : SmoothMetric3) (R : ℝ) (hR : 0<R) (H : CompactSmoothData)
    (c : ℝ) (hc : ∀ p, ‖p‖=R → (H:E3 → ℝ) p=c) :
    ∀ x : Metric.closedBall (0:E3) R, g.ballDirichlet R hR H x=c := by
  obtain ⟨hHc,hHs,hHb,hHl⟩ := g.classicalExtension_spec R hR H
  intro x
  exact g.harmonic_constant_closedBall R c hR.le hHc (g.classicalExtension_C2 R hR H) hHl
    (fun p hp ↦ by
      have hs : ‖p‖=R := by simpa only [Metric.mem_sphere,dist_zero_right] using hp
      rw [hHb p hs,hc p hs]) x x.property



noncomputable def boundaryUnit (R : ℝ) (hR : 0<R) : CompactSmoothData :=
  let χ : ContDiffBump (0:E3) := ⟨R,R+1,hR,by linarith⟩
  ⟨χ,χ.contDiff,χ.hasCompactSupport⟩

lemma boundaryUnit_eq (R : ℝ) (hR : 0<R) (p : E3) (hp : ‖p‖=R) :
    (boundaryUnit R hR:E3 → ℝ) p=1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall,dist_zero_right] using hp.le

noncomputable def squareData (H : CompactSmoothData) : CompactSmoothData :=
  ⟨fun x ↦ (H:E3 → ℝ) x^2,H.property.1.pow 2,by
    rw [show (fun x ↦ (H:E3 → ℝ) x^2) = (H:E3 → ℝ)*(H:E3 → ℝ) by
      ext x
      exact pow_two _]
    exact H.property.2.mul_right⟩

theorem ballDirichlet_square (g : SmoothMetric3) (R : ℝ) (hR : 0<R)
    (H : CompactSmoothData) (x : Metric.closedBall (0:E3) R) :
    (g.ballDirichlet R hR H x)^2 ≤ g.ballDirichlet R hR (squareData H) x := by
  let c := g.ballDirichlet R hR H x
  let B := boundaryUnit R hR
  let Q := squareData H-(2*c) • H+c^2 • B
  have hQ : ∀ p, ‖p‖=R → 0 ≤ (Q:E3 → ℝ) p := by
    intro p hp
    change 0 ≤ (H:E3 → ℝ) p^2-(2*c)*(H:E3 → ℝ) p+c^2*(B:E3 → ℝ) p
    rw [boundaryUnit_eq R hR p hp]
    nlinarith [sq_nonneg ((H:E3 → ℝ) p-c)]
  have hh := g.ballDirichlet_positive R hR Q hQ x
  have hB := g.ballDirichlet_constant R hR B 1 (boundaryUnit_eq R hR) x
  change 0 ≤ g.ballDirichlet R hR (squareData H-(2*c) • H+c^2 • B) x at hh
  rw [map_add,map_sub,map_smul,map_smul] at hh
  simp only [ContinuousMap.add_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul,hB] at hh
  dsimp [c] at hh
  nlinarith

theorem ballDirichlet_abs_le (g : SmoothMetric3) (R : ℝ) (hR : 0<R)
    (H : CompactSmoothData) (M : ℝ)
    (hM : ∀ p, ‖p‖=R → |(H:E3 → ℝ) p| ≤ M)
    (x : Metric.closedBall (0:E3) R) : |g.ballDirichlet R hR H x| ≤ M := by
  let B := boundaryUnit R hR
  have hB := g.ballDirichlet_constant R hR B 1 (boundaryUnit_eq R hR) x
  have hi : 0 ≤ g.ballDirichlet R hR (M • B-H) x := by
    apply g.ballDirichlet_positive R hR
    intro p hp
    change 0 ≤ M*(B:E3 → ℝ) p-(H:E3 → ℝ) p
    rw [boundaryUnit_eq R hR p hp]
    simpa only [mul_one] using sub_nonneg.mpr (le_abs_self _ |>.trans (hM p hp))
  have lo : 0 ≤ g.ballDirichlet R hR (M • B+H) x := by
    apply g.ballDirichlet_positive R hR
    intro p hp
    change 0 ≤ M*(B:E3 → ℝ) p+(H:E3 → ℝ) p
    rw [boundaryUnit_eq R hR p hp]
    have hh := (abs_le.mp (hM p hp)).1
    linarith
  rw [map_sub,map_smul] at hi
  rw [map_add,map_smul] at lo
  simp only [ContinuousMap.add_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul,hB,mul_one] at hi lo
  exact abs_le.mpr ⟨by linarith,by linarith⟩


lemma compact_smooth_restriction (r R : ℝ) (hr : 0<r) (hrR : r<R)
    {F : E3 → ℝ} (hF : ContDiffOn ℝ ∞ F (Metric.ball (0:E3) R)) :
    ∃ K : CompactSmoothData, EqOn (K:E3 → ℝ) F (Metric.closedBall 0 r) := by
  let χ : ContDiffBump (0:E3) := ⟨(r+R)/2,(r+3*R)/4,by linarith,by linarith⟩
  have hχin : tsupport (χ:E3 → ℝ) ⊆ Metric.ball 0 R := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [χ]; linarith)
  have hs : ContDiff ℝ ∞ (fun x ↦ χ x*F x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.ball (0:E3) R
    · exact χ.contDiffAt.mul (hF.contDiffAt (Metric.isOpen_ball.mem_nhds hx))
    · have hz : (χ:E3 → ℝ) =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun hn ↦ hx (hχin hn))
      apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy,zero_mul]
  refine ⟨⟨fun x ↦ χ x*F x,hs,χ.hasCompactSupport.mul_right⟩,?_⟩
  intro x hx
  change χ x*F x=F x
  rw [χ.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (by dsimp [χ]; linarith) hx),one_mul]

theorem exact_dirichlet_restriction (g : SmoothMetric3) (r R : ℝ)
    (hr : 0<r) (hrR : r<R) (H : CompactSmoothData) :
    ∃ K : CompactSmoothData,
      EqOn (K:E3 → ℝ) (g.classicalExtension R (hr.trans hrR) H) (Metric.closedBall 0 r) ∧
      EqOn (g.classicalExtension r hr K) (g.classicalExtension R (hr.trans hrR) H)
        (Metric.closedBall 0 r) := by
  have hR : 0<R := hr.trans hrR
  obtain ⟨hHc,hHs,hHb,hHl⟩ := g.classicalExtension_spec R hR H
  obtain ⟨K,hK⟩ := compact_smooth_restriction r R hr hrR hHs
  refine ⟨K,hK,?_⟩
  obtain ⟨hKc,hKs,hKb,hKl⟩ := g.classicalExtension_spec r hr K
  have hsub : Metric.closedBall (0:E3) r ⊆ Metric.ball 0 R := Metric.closedBall_subset_ball hrR
  refine g.harmonic_unique_closedBall r hr.le hKc (hHs.continuousOn.mono hsub)
    (g.classicalExtension_C2 r hr K)
    (fun x hx ↦ g.classicalExtension_C2 R hR H x (Metric.ball_subset_ball hrR.le hx))
    hKl (fun x hx ↦ hHl x (Metric.ball_subset_ball hrR.le hx)) ?_
  intro p hp
  have hs : ‖p‖=r := by simpa only [Metric.mem_sphere,dist_zero_right] using hp
  rw [hKb p hs]
  exact hK (by simpa only [Metric.mem_closedBall,dist_zero_right] using hs.le)

theorem metric_classical_dirichlet_smooth (g : SmoothMetric3) (R : ℝ) (hR : 0<R)
    {H : E3 → ℝ} (hH : ContDiff ℝ ∞ H) :
    ∃ U : E3 → ℝ, ContinuousOn U (Metric.closedBall 0 R) ∧
      ContDiffOn ℝ ∞ U (Metric.ball 0 R) ∧
      (∀ p, ‖p‖=R → U p=H p) ∧
      (∀ x ∈ Metric.ball (0:E3) R, g.laplacian U x=0) := by
  obtain ⟨K,hK⟩ := compact_smooth_restriction R (R+1) hR (by linarith) hH.contDiffOn
  obtain ⟨U,hUc,hUs,hUb,hUL⟩ := g.metric_classical_dirichlet R hR K.property.1 K.property.2
  refine ⟨U,hUc,hUs,fun p hp ↦ ?_,hUL⟩
  rw [hUb p hp]
  exact hK (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.le)

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
