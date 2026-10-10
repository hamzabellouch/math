import Mathlib
import OAI.Geometry.BallPacking.Forms.ManifoldMapDifferential

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold
open scoped ContDiff Manifold Topology

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartOneForm_manifoldPullback_at {α : ℝ → ManifoldOneForm E M} {e : N → M}
    {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e ((extChartAt 𝓘(ℝ,F) b).symm p.2)) :
    chartOneForm (manifoldPullbackOneForm α e p.1) b p.2 =
      euclideanPullbackOneForm α (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := (he.hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackOneForm,hd,chartOneForm,manifoldPullbackOneForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v
  rfl

theorem manifoldPullbackOneForm_smooth_on {α : ℝ → ManifoldOneForm E M}
    {e : N → M} {U : Set N} (hU : IsOpen U)
    (he : ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e U)
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (b : N) :
    ContDiffOn ℝ ∞ (fun q : ℝ × F => chartOneForm (manifoldPullbackOneForm α e q.1) b q.2)
      (univ ×ˢ ((extChartAt 𝓘(ℝ,F) b).target ∩ (extChartAt 𝓘(ℝ,F) b).symm ⁻¹' U)) := by
  intro p hp
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2.1)
  have hg := (he.contMDiffAt (hU.mem_nhds hp.2.2)).comp p.2 hi
  apply ((euclideanPullbackOneForm_contDiffAt hα hg).congr_of_eventuallyEq _).contDiffWithinAt
  have ht := continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp.2.1)
  have hu := (hi.continuousAt.comp continuousAt_snd).preimage_mem_nhds (hU.mem_nhds hp.2.2)
  filter_upwards [ht,hu] with q hqt hqu
  exact chartOneForm_manifoldPullback_at hqt
    ((he.contMDiffAt (hU.mem_nhds hqu)).mdifferentiableAt (by simp))

theorem manifold_pullback_exterior_on {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {g : N → M} {U : Set N} (hU : IsOpen U)
    (hg : ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g U) {b : N} (hbU : b ∈ U) :
    manifoldExteriorOneForm (E := F) (M := N)
      (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =
      manifoldPullbackTwoForm (E := E) (F := F) (fun _ => manifoldExteriorOneForm α) g 0 b := by
  let y := extChartAt 𝓘(ℝ,F) b b
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy : y ∈ (extChartAt 𝓘(ℝ,F) b).target := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he : (extChartAt 𝓘(ℝ,F) b).symm y=b := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hgy : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g ((extChartAt 𝓘(ℝ,F) b).symm y) := by
    rw [he]
    exact hg.contMDiffAt (hU.mem_nhds hbU)
  have hc : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y :=
    hgy.comp y hi
  have hu : ∀ᶠ z in 𝓝 y, (extChartAt 𝓘(ℝ,F) b).symm z ∈ U :=
    hi.continuousAt.preimage_mem_nhds (hU.mem_nhds (he.symm ▸ hbU))
  have hh : chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =ᶠ[𝓝 y]
      fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy,hu] with z hz hzU
    exact chartOneForm_manifoldPullback_at (α := fun _ => α) (b := b) (p := (0,z)) hz
      ((hg.contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt (by simp))
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
  have hd := mfderiv_comp y (hgy.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  have hD : manifoldMapDifferential (E := E) (F := F)
      (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y =
      (manifoldMapDifferential (E := E) (F := F) g b).comp
        (chartDifferential (E := F) b b).inverse := by
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y = _
    rw [hd,← chartDifferential_inverse hy]
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

section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def parameterEuclideanPullbackOneForm (α : P → ManifoldOneForm E M) (g : F → M)
    (p : P × F) : F →L[ℝ] ℝ :=
  (α p.1 (g p.2)).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)

theorem parameterEuclideanPullbackOneForm_contDiffAt
    {α : P → ManifoldOneForm E M} {g : F → M} {p : P × F}
    (hα : ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (α q.1) (g p.2) q.2)
      (p.1,extChartAt 𝓘(ℝ,E) (g p.2) (g p.2)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (parameterEuclideanPullbackOneForm α g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : P × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := hα.comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by simp)).comp p contDiffAt_snd
  apply (hform.clm_comp hder).congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackOneForm_chart (α := fun _ => α q.1) (p := (0,q.2))
    (hq.mdifferentiableAt (by simp)) hqc

end

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclidean_manifold_pullback_exterior_at {α : ManifoldOneForm E M}
    {g : F → M} {x : F} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x)
    (hα : ContDiffAt ℝ ∞ (chartOneForm α (g x)) (extChartAt 𝓘(ℝ,E) (g x) (g x))) :
    euclideanExteriorOneForm (fun y => euclideanPullbackOneForm (fun _ => α) g (0,y)) x =
      (manifoldExteriorOneForm α (g x)).bilinearComp
        (manifoldMapDifferential (E := E) (F := F) g x)
        (manifoldMapDifferential (E := E) (F := F) g x) := by
  let c := g x
  have hc : g x ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
    (by simpa only [extChartAt_source] using hc)
  have hgc : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) x := (ho.comp x hg).contDiffAt
  have he := euclidean_manifold_pullback_germ (α := α) hg hc
  let A : F →L[ℝ] E := (chartDifferential c (g x)).comp
    (manifoldMapDifferential (E := E) (F := F) g x)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A x :=
    hasMFDerivAt_iff_hasFDerivAt.mp
      ((ho.mdifferentiableAt (by simp)).hasMFDerivAt.comp x
        (hg.mdifferentiableAt (by simp)).hasMFDerivAt)
  have hd := hf.fderiv
  have hfd : fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) x =
      (chartDifferential (E := E) c (g x)).comp
        (manifoldMapDifferential (E := E) (F := F) g x) := hd
  calc
    _ = euclideanExteriorOneForm
        (staticPullbackOneForm (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c ∘ g)) x := by
      unfold euclideanExteriorOneForm
      rw [he.fderiv_eq]
    _ = _ := by
      rw [staticPullbackOneForm_exterior
        (g := extChartAt 𝓘(ℝ,E) c ∘ g) hα hgc,hfd]
      rfl

end

section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def parameterManifoldPullbackOneForm (α : P → ManifoldOneForm E M) (g : N → M)
    (p : P) : ManifoldOneForm F N :=
  manifoldPullbackOneForm (fun _ => α p) g 0

omit [NormedSpace ℝ P] in

theorem parameterManifoldPullback_chart_germ
    (α : P → ManifoldOneForm E M) {g : N → M} (p : P) {b : N}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    (fun q : P × F => chartOneForm (parameterManifoldPullbackOneForm α g q.1) b q.2)
      =ᶠ[𝓝 (p,extChartAt 𝓘(ℝ,F) b b)]
    parameterEuclideanPullbackOneForm α (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) := by
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hn₁ : {x | ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) 1 g x} ∈
      𝓝 ((extChartAt 𝓘(ℝ,F) b).symm (extChartAt 𝓘(ℝ,F) b b)) := by
    rw [he]; exact hn
  have hn' := (hi.continuousAt.comp (f := Prod.snd) (continuousAt_snd (p := (p,extChartAt 𝓘(ℝ,F) b b)))).preimage_mem_nhds hn₁
  filter_upwards [hn',continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)] with q hq hqt
  exact chartOneForm_manifoldPullback_at (α := fun _ => α q.1) (p := (0,q.2)) hqt
    (hq.mdifferentiableAt (by simp))

theorem parameterManifoldPullbackOneForm_contDiffAt
    {α : P → ManifoldOneForm E M} {g : N → M} {p : P} {b : N}
    (hα : ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (α q.1) (g b) q.2)
      (p,extChartAt 𝓘(ℝ,E) (g b) (g b)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    ContDiffAt ℝ ∞
      (fun q : P × F => chartOneForm (parameterManifoldPullbackOneForm α g q.1) b q.2)
      (p,extChartAt 𝓘(ℝ,F) b b) := by
  let y := extChartAt 𝓘(ℝ,F) b b
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy : y∈(extChartAt 𝓘(ℝ,F) b).target := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he : (extChartAt 𝓘(ℝ,F) b).symm y=b := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hg' : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g ((extChartAt 𝓘(ℝ,F) b).symm y) := by
    rw [he]; exact hg
  have hα' : ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (α q.1) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y) q.2)
      (p,extChartAt 𝓘(ℝ,E) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
        ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)) := by
    simpa only [Function.comp_apply,he] using hα
  have hs := parameterEuclideanPullbackOneForm_contDiffAt
    (α := α) (g := g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (p := (p,y)) hα' (hg'.comp y hi)
  exact hs.congr_of_eventuallyEq (parameterManifoldPullback_chart_germ α p hg)

theorem manifold_pullback_exterior_at {α : ManifoldOneForm E M}
    {g : N → M} {b : N}
    (hα : ContDiffAt ℝ ∞ (chartOneForm α (g b))
      (extChartAt 𝓘(ℝ,E) (g b) (g b)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    manifoldExteriorOneForm (E := F) (M := N)
      (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =
      manifoldPullbackTwoForm (E := E) (F := F) (fun _ => manifoldExteriorOneForm α) g 0 b := by
  let y := extChartAt 𝓘(ℝ,F) b b
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy : y ∈ (extChartAt 𝓘(ℝ,F) b).target := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he : (extChartAt 𝓘(ℝ,F) b).symm y=b := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hgy : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g ((extChartAt 𝓘(ℝ,F) b).symm y) := by
    rw [he]
    exact hg
  have hc : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y :=
    hgy.comp y hi
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hgy.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hu := hi.continuousAt.preimage_mem_nhds hn
  have hh : chartOneForm (E := F) (M := N)
        (manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) b =ᶠ[𝓝 y]
      fun z => euclideanPullbackOneForm (fun _ => α) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (0,z) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy,hu] with z hz hzU
    exact chartOneForm_manifoldPullback_at (α := fun _ => α) (b := b) (p := (0,z)) hz
      (hzU.mdifferentiableAt (by simp))
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
      _ = _ := by
        have hα' : ContDiffAt ℝ ∞
            (chartOneForm α ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y))
            (extChartAt 𝓘(ℝ,E) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
              ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)) := by
          simpa only [Function.comp_apply,he] using hα
        simpa only [Function.comp_apply,he] using euclidean_manifold_pullback_exterior_at hc hα'
  have hd := mfderiv_comp y (hgy.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  have hD : manifoldMapDifferential (E := E) (F := F)
      (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y =
      (manifoldMapDifferential (E := E) (F := F) g b).comp
        (chartDifferential (E := F) b b).inverse := by
    change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y = _
    rw [hd,← chartDifferential_inverse hy]
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

section

variable {P E V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

instance (priority := 50) flatProduct_chartedSpace : ChartedSpace (E × V) (M × V) :=
  prodChartedSpace E M V V

instance (priority := 50) flatProduct_manifold [IsManifold 𝓘(ℝ,E) ∞ M] :
    IsManifold 𝓘(ℝ,E × V) ∞ (M × V) := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact IsManifold.prod M V

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_fst_smooth : ContMDiff 𝓘(ℝ,E × V) 𝓘(ℝ,E) ∞
    (Prod.fst : M × V → M) := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact contMDiff_fst

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_snd_smooth : ContMDiff 𝓘(ℝ,E × V) 𝓘(ℝ,V) ∞
    (Prod.snd : M × V → V) := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact contMDiff_snd

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem flatProduct_fst_derivative (z : M × V) :
    mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,E) (Prod.fst : M × V → M) z=
      ContinuousLinearMap.fst ℝ E V := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact mfderiv_fst

def productHorizontalLift (Γ : V → ManifoldOneForm E M) : ManifoldOneForm (E × V) (M × V) :=
  fun z => (Γ z.2 z.1).comp (ContinuousLinearMap.fst ℝ E V)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M] [ChartedSpace E M] in
@[simp] theorem productHorizontalLift_apply (Γ : V → ManifoldOneForm E M)
    (z : M × V) (v : E × V) : productHorizontalLift Γ z v=Γ z.2 z.1 v.1 := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M] [ChartedSpace E M] in
@[simp] theorem productHorizontalLift_vertical (Γ : V → ManifoldOneForm E M)
    (z : M × V) (v : V) : productHorizontalLift Γ z (0,v)=0 := by
  simp

variable [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
 theorem productHorizontalLift_chart (Γ : V → ManifoldOneForm E M) (c : M × V)
    {y : E × V} (hy : y∈(extChartAt 𝓘(ℝ,E × V) c).target) :
    chartOneForm (productHorizontalLift Γ) c y=
      parameterEuclideanPullbackOneForm Γ
        (Prod.fst ∘ (extChartAt 𝓘(ℝ,E × V) c).symm)
        (((extChartAt 𝓘(ℝ,E × V) c).symm y).2,y) := by
  let v := ((extChartAt 𝓘(ℝ,E × V) c).symm y).2
  have he : chartOneForm (productHorizontalLift Γ) c y=
      chartOneForm (manifoldPullbackOneForm (E := E) (F := E × V)
        (fun _ => Γ v) (Prod.fst : M × V → M) 0) c y := by
    simp only [chartOneForm,productHorizontalLift,manifoldPullbackOneForm,
      manifoldMapDifferential,flatProduct_fst_derivative]
    rfl
  exact he.trans (chartOneForm_manifoldPullback (α := fun _ => Γ v)
    (p := (0,y)) flatProduct_fst_smooth hy)

theorem productHorizontalLift_smooth {Γ : P × V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (fun p => productHorizontalLift (fun v => Γ (p,v))) := by
  intro c q hq
  let g : E × V → M := Prod.fst ∘ (extChartAt 𝓘(ℝ,E × V) c).symm
  let v : E × V → V := Prod.snd ∘ (extChartAt 𝓘(ℝ,E × V) c).symm
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E × V)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hq.2)
  have hg : ContMDiffAt 𝓘(ℝ,E × V) 𝓘(ℝ,E) ∞ g q.2 :=
    flatProduct_fst_smooth.contMDiffAt.comp q.2 hi
  have hv : ContDiffAt ℝ ∞ v q.2 :=
    (flatProduct_snd_smooth.contMDiffAt.comp q.2 hi).contDiffAt
  have hx : ((q.1,v q.2),extChartAt 𝓘(ℝ,E) (g q.2) (g q.2))∈
      univ ×ˢ (extChartAt 𝓘(ℝ,E) (g q.2)).target :=
    ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) (g q.2)).map_source (mem_extChartAt_source _)⟩
  have hs := parameterEuclideanPullbackOneForm_contDiffAt
    (α := Γ) (p := ((q.1,v q.2),q.2))
    ((hΓ (g q.2)).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target _)).mem_nhds hx)) hg
  have hc := hs.comp q ((contDiffAt_fst.prodMk (hv.comp q contDiffAt_snd)).prodMk contDiffAt_snd)
  apply (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E × V)) c).mem_nhds hq.2)] with z hz
  exact productHorizontalLift_chart (fun w => Γ (z.1,w)) c hz

end

section

variable {F E V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def flatProductMap (g : F → M) : F × V → M × V := Prod.map g id

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem flatProductMap_smoothAt {g : F → M} {x : F × V}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1) :
    ContMDiffAt 𝓘(ℝ,F × V) 𝓘(ℝ,E × V) ∞ (flatProductMap g) x := by
  have h := hg.prodMap (contMDiffAt_id (I := 𝓘(ℝ,V)) (x := x.2))
  simp +instances only [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at h
  exact h

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem flatProductMap_derivative {g : F → M} {x : F × V}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1) :
    mfderiv 𝓘(ℝ,F × V) 𝓘(ℝ,E × V) (flatProductMap g) x=
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V) := by
  have hf := (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : F × V → F)).contMDiff.contMDiffAt (x := x)
  have hs := (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : F × V → V)).contMDiff.contMDiffAt (x := x)
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  have hd := mfderiv_prodMk (I := 𝓘(ℝ,F × V)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,V))
    (f := g ∘ Prod.fst) (g := Prod.snd) (x := x)
    ((hg.comp x hf).mdifferentiableAt (by simp)) (hs.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ,F × V) ((𝓘(ℝ,E)).prod 𝓘(ℝ,V))
    (fun y : F × V => (g y.1,y.2)) x=_
  apply hd.trans
  erw [mfderiv_comp x (hg.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv,mfderiv_eq_fderiv,fderiv_fst,fderiv_snd]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem productHorizontalLift_pullback_apply (Γ : V → ManifoldOneForm E M)
    {g : F → M} {x : F × V} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1)
    (w : F × V) :
    euclideanPullbackOneForm (fun _ => productHorizontalLift Γ) (flatProductMap g) (0,x) w=
      euclideanPullbackOneForm (fun _ => Γ x.2) g (0,x.1) w.1 := by
  change Γ x.2 (g x.1)
    ((mfderiv 𝓘(ℝ,F × V) 𝓘(ℝ,E × V) (flatProductMap g) x w).1)=
      Γ x.2 (g x.1) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1 w.1)
  rw [flatProductMap_derivative hg]
  rfl

theorem productHorizontalLift_exterior_pullback {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {g : F → M} {x : F × V}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1) :
    euclideanExteriorOneForm
      (fun y => euclideanPullbackOneForm (fun _ => productHorizontalLift Γ) (flatProductMap g) (0,y)) x=
      (manifoldExteriorOneForm (productHorizontalLift Γ) (flatProductMap g x)).bilinearComp
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V))
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V)) := by
  have hfam : SmoothOneFormFamily (fun _ : ℝ => productHorizontalLift Γ) := by
    apply productHorizontalLift_smooth (Γ := fun p : ℝ × V => Γ p.2)
    intro c
    have hm : ContDiffOn ℝ ∞ (fun p : (ℝ × V) × E => (p.1.2,p.2))
        (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
    exact (hΓ c).comp hm (fun _ hp => ⟨mem_univ _,hp.2⟩)
  have he := euclidean_manifold_pullback_exterior_at (flatProductMap_smoothAt hg)
    (hfam.spatial_smooth 0 (flatProductMap g x) (mem_extChartAt_target _))
  simpa only [manifoldMapDifferential,flatProductMap_derivative hg] using he

end

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem bilinearComp_equiv_isInvertible {A : E →L[ℝ] E →L[ℝ] ℝ}
    (c : F ≃L[ℝ] E) (hA : A.IsInvertible) :
    (A.bilinearComp (c : F →L[ℝ] E) (c : F →L[ℝ] E)).IsInvertible := by
  obtain ⟨a,rfl⟩ := hA
  refine ⟨(c.trans a).trans (c.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)),?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem bilinearComp_equiv_isInvertible_iff {A : E →L[ℝ] E →L[ℝ] ℝ}
    (c : F ≃L[ℝ] E) :
    (A.bilinearComp (c : F →L[ℝ] E) (c : F →L[ℝ] E)).IsInvertible ↔ A.IsInvertible := by
  constructor
  · intro h
    have he : (A.bilinearComp (c : F →L[ℝ] E) (c : F →L[ℝ] E)).bilinearComp
        (c.symm : E →L[ℝ] F) (c.symm : E →L[ℝ] F)=A := by
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
    rw [← he]
    exact bilinearComp_equiv_isInvertible c.symm h
  · exact bilinearComp_equiv_isInvertible c

end PackingSufficiencySupport.Hamiltonian
end

end OAI
