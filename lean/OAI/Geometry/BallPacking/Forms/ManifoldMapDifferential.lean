import Mathlib
import OAI.Geometry.BallPacking.Surfaces.QuadricInfinityDiffeomorph
import OAI.Geometry.BallPacking.Kahler.PhaseArea

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped Manifold
open scoped ContDiff Topology
open Set Function Manifold
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

def manifoldMapDifferential (g : N → M) (x : N) : F →L[ℝ] E :=
  mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def manifoldPullbackTwoForm (Ω : ℝ → ManifoldTwoForm E M) (e : N → M)
    (t : ℝ) (b : N) : F →L[ℝ] F →L[ℝ] ℝ :=
  (Ω t (e b)).bilinearComp (manifoldMapDifferential (E := E) (F := F) e b)
    (manifoldMapDifferential (E := E) (F := F) e b)

def manifoldPullbackOneForm (α : ℝ → ManifoldOneForm E M) (e : N → M)
    (t : ℝ) (b : N) : F →L[ℝ] ℝ :=
  (α t (e b)).comp (manifoldMapDifferential (E := E) (F := F) e b)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartTwoForm_manifoldPullback {Ω : ℝ → ManifoldTwoForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target) :
    chartTwoForm (manifoldPullbackTwoForm Ω e p.1) b p.2 =
      euclideanPullbackTwoForm Ω (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := ((he.mdifferentiable (by simp) _).hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackTwoForm,hd,chartTwoForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v w
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartOneForm_manifoldPullback {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target) :
    chartOneForm (manifoldPullbackOneForm α e p.1) b p.2 =
      euclideanPullbackOneForm α (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := ((he.mdifferentiable (by simp) _).hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackOneForm,hd,chartOneForm,manifoldPullbackOneForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v
  rfl

theorem manifoldPullbackTwoForm_smooth {Ω : ℝ → ManifoldTwoForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (b : N) :
    ContDiffOn ℝ ∞ (fun q : ℝ × F => chartTwoForm (manifoldPullbackTwoForm Ω e q.1) b q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,F) b).target) := by
  intro p hp
  have hg := he.contMDiffAt.comp p.2 ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2))
  apply ((euclideanPullbackTwoForm_contDiffAt hΩ hg).congr_of_eventuallyEq _).contDiffWithinAt
  have hh := continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2)
  filter_upwards [hh] with q hq
  exact chartTwoForm_manifoldPullback he hq

theorem manifoldPullbackOneForm_smooth {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (b : N) :
    ContDiffOn ℝ ∞ (fun q : ℝ × F => chartOneForm (manifoldPullbackOneForm α e q.1) b q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,F) b).target) := by
  intro p hp
  have hg := he.contMDiffAt.comp p.2 ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2))
  apply ((euclideanPullbackOneForm_contDiffAt hα hg).congr_of_eventuallyEq _).contDiffWithinAt
  have hh := continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2)
  filter_upwards [hh] with q hq
  exact chartOneForm_manifoldPullback he hq

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldExteriorOneForm (α : ManifoldOneForm E M) : ManifoldTwoForm E M :=
  fun x => (euclideanExteriorOneForm (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)).bilinearComp
    (chartDifferential x x) (chartDifferential x x)

theorem chartOneForm_transition {α : ManifoldOneForm E M} {b c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    chartOneForm α b y =
      staticPullbackOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y := by
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have he := euclideanPullbackOneForm_chart (α := fun _ => α) (p := (0,y)) hi hc
  simpa only [euclideanPullbackOneForm,chartOneForm,chartDifferential_inverse hy,
    staticPullbackOneForm,Function.comp_apply] using he

theorem chartOneForm_exterior_transition {α : ManifoldOneForm E M} {b c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source)
    (hα : ContDiffAt ℝ ∞ (chartOneForm α c)
      (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))) :
    euclideanExteriorOneForm (chartOneForm α b) y =
      (euclideanExteriorOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y) := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
    (by simpa only [extChartAt_source] using hc)
  have ht : ContDiffAt ℝ ∞
      (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y :=
    (ho.comp y hi).contDiffAt
  have he : chartOneForm α b =ᶠ[𝓝 y]
      staticPullbackOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy,
      hi.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)]
      with z hz hzc
    exact chartOneForm_transition hz hzc
  calc
    _ = euclideanExteriorOneForm
        (staticPullbackOneForm (chartOneForm α c)
          (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm)) y := by
      unfold euclideanExteriorOneForm
      rw [he.fderiv_eq]
    _ = _ := staticPullbackOneForm_exterior hα ht

theorem manifoldExteriorOneForm_chart {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {b : M} {y : E} (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target) :
    chartTwoForm (manifoldExteriorOneForm α) b y =
      euclideanExteriorOneForm (chartOneForm α b) y := by
  let x := (extChartAt 𝓘(ℝ,E) b).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have ho := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := x)
    (by simpa only [extChartAt_source] using hx)
  let A : E →L[ℝ] E := (chartDifferential x x).comp
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) b).symm y)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) x ∘ (extChartAt 𝓘(ℝ,E) b).symm) A y :=
    hasMFDerivAt_iff_hasFDerivAt.mp (ho.hasMFDerivAt.comp y hi.hasMFDerivAt)
  have he := hf.fderiv
  dsimp only [A,chartDifferential] at he
  rw [chartOneForm_exterior_transition hy hx ((hα x).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds
      ((extChartAt 𝓘(ℝ,E) x).map_source hx)))]
  change fderiv ℝ (extChartAt 𝓘(ℝ,E) x ∘ (extChartAt 𝓘(ℝ,E) b).symm) y = _ at he
  rw [he]
  simp only [chartTwoForm,manifoldExteriorOneForm,chartDifferential_inverse hy]
  rfl

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclidean_manifold_pullback_germ {α : ManifoldOneForm E M}
    {g : F → M} {x : F} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x)
    {c : M} (hc : g x ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    (fun y => euclideanPullbackOneForm (fun _ => α) g (0,y)) =ᶠ[𝓝 x]
      staticPullbackOneForm (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c ∘ g) := by
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  filter_upwards [hg',hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)] with y hy hcy
  exact euclideanPullbackOneForm_chart (α := fun _ => α) (p := (0,y))
    (hy.mdifferentiableAt (by simp)) hcy

theorem euclidean_manifold_pullback_chart_exterior {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {g : F → M} {x : F} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x)
    {c : M} (hc : g x ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    euclideanExteriorOneForm (fun y => euclideanPullbackOneForm (fun _ => α) g (0,y)) x =
      (euclideanExteriorOneForm (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c (g x))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) x) (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) x) := by
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
    (by simpa only [extChartAt_source] using hc)
  have hgc : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) x := (ho.comp x hg).contDiffAt
  have ha := (hα c).contDiffAt ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds
    ((extChartAt 𝓘(ℝ,E) c).map_source hc))
  have he := euclidean_manifold_pullback_germ (α := α) hg hc
  calc
    _ = euclideanExteriorOneForm
        (staticPullbackOneForm (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c ∘ g)) x := by
      unfold euclideanExteriorOneForm
      rw [he.fderiv_eq]
    _ = _ := staticPullbackOneForm_exterior ha hgc

theorem euclidean_manifold_pullback_exterior {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {g : F → M} {x : F} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x) :
    euclideanExteriorOneForm (fun y => euclideanPullbackOneForm (fun _ => α) g (0,y)) x =
      (manifoldExteriorOneForm α (g x)).bilinearComp
        (manifoldMapDifferential (E := E) (F := F) g x)
        (manifoldMapDifferential (E := E) (F := F) g x) := by
  let c := g x
  have hc : g x ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have ho := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)
  let A : F →L[ℝ] E := (chartDifferential c (g x)).comp
    (manifoldMapDifferential (E := E) (F := F) g x)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A x :=
    hasMFDerivAt_iff_hasFDerivAt.mp
      (ho.hasMFDerivAt.comp x (hg.mdifferentiableAt (by simp)).hasMFDerivAt)
  have hd := hf.fderiv
  have hfd : fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) x =
      (chartDifferential (E := E) c (g x)).comp
        (manifoldMapDifferential (E := E) (F := F) g x) := hd
  rw [euclidean_manifold_pullback_chart_exterior hα hg hc,hfd]
  rfl

variable {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem manifold_pullback_exterior {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {g : N → M} (hg : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g) (b : N) :
    manifoldExteriorOneForm (E := F) (M := N)
      (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =
      manifoldPullbackTwoForm (E := E) (F := F) (fun _ => manifoldExteriorOneForm α) g 0 b := by
  let y := extChartAt 𝓘(ℝ,F) b b
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy : y ∈ (extChartAt 𝓘(ℝ,F) b).target := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he : (extChartAt 𝓘(ℝ,F) b).symm y=b := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hc : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y :=
    hg.contMDiffAt.comp y hi
  have hh : chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =ᶠ[𝓝 y]
      fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy] with z hz
    exact chartOneForm_manifoldPullback (α := fun _ => α) (b := b) (p := (0,z)) hg hz
  have hder : euclideanExteriorOneForm
      (chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b) y =
      (manifoldExteriorOneForm α (g b)).bilinearComp
        (manifoldMapDifferential (E := E) (F := F) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
        (manifoldMapDifferential (E := E) (F := F) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y) := by
    calc
      _ = euclideanExteriorOneForm
          (fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z)) y := by
        unfold euclideanExteriorOneForm
        rw [hh.fderiv_eq]
      _ = _ := by simpa only [Function.comp_apply,he] using euclidean_manifold_pullback_exterior hα hc
  have hd := mfderiv_comp y ((hg.mdifferentiable (by simp)) _)
    (hi.mdifferentiableAt (by simp))
  have hD : manifoldMapDifferential (E := E) (F := F)
      (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y =
      (manifoldMapDifferential (E := E) (F := F) g b).comp
        (chartDifferential (E := F) b b).inverse := by
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y = _
    rw [hd]
    rw [← chartDifferential_inverse hy]
    change (manifoldMapDifferential (E := E) (F := F) g
      ((extChartAt 𝓘(ℝ,F) b).symm y)).comp
      (chartDifferential (E := F) b ((extChartAt 𝓘(ℝ,F) b).symm y)).inverse = _
    rw [he]
  have H : (chartDifferential (E := F) b b).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,F)) hb using 1
  change (euclideanExteriorOneForm
    (chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b) y).bilinearComp
      (chartDifferential (E := F) b b) (chartDifferential (E := F) b b)=_
  rw [hder,hD]
  ext u v
  change manifoldExteriorOneForm α (g b)
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g b ((chartDifferential (E := F) b b).inverse (chartDifferential (E := F) b b u)))
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g b ((chartDifferential (E := F) b b).inverse (chartDifferential (E := F) b b v)))=_
  rw [H.inverse_apply_self,H.inverse_apply_self]
  rfl

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vector_chartOneForm (α : E → E →L[ℝ] ℝ) (c y : E) :
    chartOneForm α c y=α y := by
  simp only [chartOneForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,ContinuousLinearMap.comp_id,id_eq]

theorem vector_chartTwoForm (Ω : E → E →L[ℝ] E →L[ℝ] ℝ) (c y : E) :
    chartTwoForm Ω c y=Ω y := by
  ext v w
  simp only [chartTwoForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,id_eq,
    ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply]

theorem vector_exteriorOneForm (α : E → E →L[ℝ] ℝ) :
    manifoldExteriorOneForm α=euclideanExteriorOneForm α := by
  funext y
  simp only [manifoldExteriorOneForm,
    chartDifferential,extChartAt_model_space_eq_id,PartialEquiv.refl_coe,
    mfderiv_eq_fderiv,fderiv_id,id_eq]
  rw [show chartOneForm α y=α from funext (vector_chartOneForm α y)]
  ext v w
  rfl

theorem vector_oneForm_smooth {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α) :
    SmoothOneFormFamily (fun _ : ℝ => α) := by
  intro c
  simpa only [vector_chartOneForm,Function.comp_def] using
    (hα.comp contDiff_snd).contDiffOn

theorem vector_twoForm_smooth {Ω : E → E →L[ℝ] E →L[ℝ] ℝ} (hΩ : ContDiff ℝ ∞ Ω) :
    SmoothTwoForm Ω := by
  intro c
  rw [show chartTwoForm Ω c=Ω from funext (vector_chartTwoForm Ω c)]
  exact hΩ.contDiffOn

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

def phaseInclusion (x : locus a) : PlanePhase (Option (Fin m)) := affinePhase m x.val

theorem phaseInclusion_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin m))) ∞ (phaseInclusion a) :=
  (affinePhase m).contDiff.contMDiff.comp (real_inclusion_contMDiff a)

def curveFSPrimitive (c : ℝ) : ManifoldOneForm RealModel (locus a) :=
  manifoldPullbackOneForm (fun _ => affineFSPrimitive c) (phaseInclusion a) 0

def curveFSForm (c : ℝ) : ManifoldTwoForm RealModel (locus a) :=
  manifoldPullbackTwoForm (fun _ => affineFSForm c) (phaseInclusion a) 0

theorem curveFSPrimitive_smooth (c : ℝ) :
    SmoothOneFormFamily (fun _ : ℝ => curveFSPrimitive a c) := by
  have hα : SmoothOneFormFamily (fun _ : ℝ =>
      (affineFSPrimitive c : PlanePhase (Option (Fin m)) → _)) :=
    vector_oneForm_smooth (affineFSPrimitive_smooth c)
  intro b
  exact manifoldPullbackOneForm_smooth (α := fun _ : ℝ =>
    (affineFSPrimitive c : PlanePhase (Option (Fin m)) → _))
    (phaseInclusion_smooth a) hα b

theorem curveFSForm_smooth (c : ℝ) : SmoothTwoForm (curveFSForm a c) := by
  have hΩ : SmoothTwoForm (affineFSForm c : PlanePhase (Option (Fin m)) → _) :=
    vector_twoForm_smooth (affineFSForm_smooth c)
  have hΩf : SmoothTwoFormFamily (fun _ : ℝ =>
      (affineFSForm c : PlanePhase (Option (Fin m)) → _)) := SmoothTwoFormFamily.const hΩ
  have hs : SmoothTwoFormFamily (fun t : ℝ =>
      manifoldPullbackTwoForm (fun _ => (affineFSForm c : PlanePhase (Option (Fin m)) → _))
        (phaseInclusion a) t) :=
    manifoldPullbackTwoForm_smooth (Ω := fun _ =>
      (affineFSForm c : PlanePhase (Option (Fin m)) → _)) (phaseInclusion_smooth a) hΩf
  exact hs.eval 0

theorem curveFSPrimitive_exterior (c : ℝ) :
    manifoldExteriorOneForm (curveFSPrimitive a c)=curveFSForm a c := by
  have hα : ∀ z : PlanePhase (Option (Fin m)),ContDiffOn ℝ ∞
      (chartOneForm (affineFSPrimitive c) z) (extChartAt 𝓘(ℝ,PlanePhase (Option (Fin m))) z).target := by
    intro z
    rw [show chartOneForm (affineFSPrimitive c) z=affineFSPrimitive c from
      funext (vector_chartOneForm (affineFSPrimitive c) z)]
    exact (affineFSPrimitive_smooth c).contDiffOn
  funext x
  change manifoldExteriorOneForm (manifoldPullbackOneForm
    (fun _ => (affineFSPrimitive c : PlanePhase (Option (Fin m)) → _)) (phaseInclusion a) 0) x=_
  rw [manifold_pullback_exterior hα (phaseInclusion_smooth a) x]
  rw [vector_exteriorOneForm,← affineFSForm_eq_exterior]
  rfl

theorem curveFSForm_skew (c : ℝ) (x : locus a) (v w : RealModel) :
    curveFSForm a c x v w= -curveFSForm a c x w v :=
  affineFSForm_skew c _ _ _

theorem phase_chart_function (b : locus a) :
    (phaseInclusion a ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm)=
      affinePhase m ∘ (normalChartAt a b).inclusionChart b ∘ Complex.equivRealProdCLM.symm := by
  funext y
  have he : chartAt RealModel b=realChart a b := rfl
  simp only [mfld_simps,he,realChart,Function.comp_apply,phaseInclusion,
    NormalChart.inclusionChart]
  rfl

theorem realChart_complex_target (b : locus a) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    Complex.equivRealProdCLM.symm y∈((normalChartAt a b).sliceChart b).target := by
  have he : chartAt RealModel b=realChart a b := rfl
  simp only [mfld_simps,he,realChart] at hy
  exact hy

theorem phase_chart_derivative (b : locus a) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    manifoldMapDifferential (E := PlanePhase (Option (Fin m))) (F := RealModel)
      (phaseInclusion a ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y=
    realPhaseDerivative (fderiv ℂ ((normalChartAt a b).inclusionChart b)
      (Complex.equivRealProdCLM.symm y)) := by
  change mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin m))) _ y=_
  rw [mfderiv_eq_fderiv,phase_chart_function]
  have hdf := (((normalChartAt a b).inclusionChart_smooth b).contDiffAt
    (((normalChartAt a b).sliceChart b).open_target.mem_nhds
      (realChart_complex_target a b hy))).differentiableAt (by simp)
  exact ((affinePhase m).hasFDerivAt.comp y
    ((hdf.hasFDerivAt.restrictScalars ℝ).comp y Complex.equivRealProdCLM.symm.hasFDerivAt)).fderiv

theorem curveFSForm_positive {c : ℝ} (hc : 0<c) (b : locus a) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0<chartTwoForm (curveFSForm a c) b y (1,0) (0,1) := by
  rw [curveFSForm,chartTwoForm_manifoldPullback (phaseInclusion_smooth a) (p := (0,y)) hy]
  change 0<affineFSForm c _
    (manifoldMapDifferential (E := PlanePhase (Option (Fin m))) (F := RealModel)
      (phaseInclusion a ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (1,0))
    (manifoldMapDifferential (E := PlanePhase (Option (Fin m))) (F := RealModel)
      (phaseInclusion a ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (0,1))
  rw [phase_chart_derivative a b hy]
  apply affineFSForm_holomorphic_positive hc
  exact (normalChartAt a b).inclusionChart_derivative_one_ne b (realChart_complex_target a b hy)

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
