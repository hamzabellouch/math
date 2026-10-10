import Mathlib
import OAI.Geometry.BallPacking.Moser.SymplecticFamily

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem spatialDifferential_contDiffAt {f : ℝ × E → ℝ} {p : ℝ × E}
    (hf : ContDiffAt ℝ ∞ f p) : ContDiffAt ℝ ∞ (spatialDifferential f) p :=
  (hf.fderiv_right (by simp)).clm_comp contDiffAt_const

theorem spatialDifferential_fderivAt {f : ℝ × E → ℝ} {p : ℝ × E}
    (hf : ContDiffAt ℝ ∞ f p) (v : ℝ × E) (w : E) :
    fderiv ℝ (spatialDifferential f) p v w =
      fderiv ℝ (fderiv ℝ f) p v (0,w) := by
  have hd := ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hh := hd.clm_comp (hasFDerivAt_const (ContinuousLinearMap.inr ℝ ℝ E) p)
  rw [show fderiv ℝ (spatialDifferential f) p = _ from hh.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.inr_apply]

theorem spatialDifferential_closedAt {f : ℝ × E → ℝ} {p : ℝ × E}
    (hf : ContDiffAt ℝ ∞ f p) (v w : E) :
    fderiv ℝ (spatialDifferential f) p (0,v) w -
      fderiv ℝ (spatialDifferential f) p (0,w) v = 0 := by
  rw [spatialDifferential_fderivAt hf,spatialDifferential_fderivAt hf]
  exact sub_eq_zero.mpr ((hf.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)).eq (0,v) (0,w))


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldSpatialDifferential (f : ℝ × M → ℝ) (t : ℝ) (x : M) : E →L[ℝ] ℝ :=
  mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun z => f (t,z)) x

def manifoldPotentialChart (f : ℝ × M → ℝ) (c : M) (p : ℝ × E) : ℝ :=
  f (p.1,(extChartAt 𝓘(ℝ,E) c).symm p.2)

theorem manifoldPotentialChart_contDiffAt {f : ℝ × M → ℝ}
    (hf : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f)
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    ContDiffAt ℝ ∞ (manifoldPotentialChart f c) p := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp)
  exact (hf.contMDiffAt.comp p
    (contDiffAt_fst.contMDiffAt.prodMk (hi.comp p contDiffAt_snd.contMDiffAt))).contDiffAt

theorem chartDifferential_inverse {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    (chartDifferential (E := E) c ((extChartAt 𝓘(ℝ,E) c).symm y)).inverse =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm y := by
  apply ContinuousLinearMap.inverse_eq
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ,E)) hy)
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hy)

theorem chartOneForm_manifoldSpatialDifferential {f : ℝ × M → ℝ}
    (hf : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f)
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartOneForm (manifoldSpatialDifferential f p.1) c p.2 =
      spatialDifferential (manifoldPotentialChart f c) p := by
  have hs : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun z => f (p.1,z)) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp)
  have hm := ((hs.mdifferentiable (by simp) _).hasMFDerivAt).comp p.2
    (hi.mdifferentiableAt (by simp)).hasMFDerivAt
  have hj := (manifoldPotentialChart_contDiffAt hf hp).differentiableAt (by simp)
  have ha : HasFDerivAt (fun y : E => (p.1,y)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
    convert! (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2) using 1
  have hd := hj.hasFDerivAt.comp p.2 ha
  have hdm : HasFDerivAt (fun y => f (p.1,(extChartAt 𝓘(ℝ,E) c).symm y))
      (chartOneForm (manifoldSpatialDifferential f p.1) c p.2) p.2 := by
    rw [chartOneForm,chartDifferential_inverse hp]
    exact hasMFDerivAt_iff_hasFDerivAt.mp hm
  have hdj : HasFDerivAt (fun y => f (p.1,(extChartAt 𝓘(ℝ,E) c).symm y))
      (spatialDifferential (manifoldPotentialChart f c) p) p.2 := by
    convert! hd using 1
  exact hdm.unique hdj


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def euclideanPullbackTwoForm (Ω : ℝ → ManifoldTwoForm E M) (g : F → M)
    (p : ℝ × F) : F →L[ℝ] F →L[ℝ] ℝ :=
  (Ω p.1 (g p.2)).bilinearComp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)

def euclideanPullbackOneForm (α : ℝ → ManifoldOneForm E M) (g : F → M)
    (p : ℝ × F) : F →L[ℝ] ℝ :=
  (α p.1 (g p.2)).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)

theorem euclideanPullbackTwoForm_chart {Ω : ℝ → ManifoldTwoForm E M} {g : F → M}
    {p : ℝ × F} {c : M} (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    euclideanPullbackTwoForm Ω g p =
      (chartTwoForm (Ω p.1) c (extChartAt 𝓘(ℝ,E) c (g p.2))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2) := by
  have hd := ((mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)).hasMFDerivAt.comp p.2 hg.hasMFDerivAt)
  let A : F →L[ℝ] E :=
    (chartDifferential c (g p.2)).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A p.2 :=
    hasMFDerivAt_iff_hasFDerivAt.mp hd
  have hdf := hf.fderiv
  dsimp only [A,chartDifferential] at hdf
  rw [hdf]
  ext v w
  exact (chartTwoForm_apply_chart hc _ _).symm

theorem euclideanPullbackOneForm_chart {α : ℝ → ManifoldOneForm E M} {g : F → M}
    {p : ℝ × F} {c : M} (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    euclideanPullbackOneForm α g p =
      (chartOneForm (α p.1) c (extChartAt 𝓘(ℝ,E) c (g p.2))).comp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2) := by
  have hd := ((mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)).hasMFDerivAt.comp p.2 hg.hasMFDerivAt)
  let A : F →L[ℝ] E :=
    (chartDifferential c (g p.2)).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A p.2 :=
    hasMFDerivAt_iff_hasFDerivAt.mp hd
  have hdf := hf.fderiv
  dsimp only [A,chartDifferential] at hdf
  rw [hdf]
  have hC : (chartDifferential (E := E) c (g p.2)).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hc using 1
  ext v
  change α p.1 (g p.2) _ = α p.1 ((extChartAt 𝓘(ℝ,E) c).symm
    (extChartAt 𝓘(ℝ,E) c (g p.2))) _
  rw [(extChartAt 𝓘(ℝ,E) c).left_inv hc]
  change _ = α p.1 (g p.2) ((chartDifferential c (g p.2)).inverse
    (chartDifferential c (g p.2) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2 v)))
  erw [hC.inverse_apply_self]
  rfl

theorem euclideanPullbackTwoForm_contDiffAt
    {Ω : ℝ → ManifoldTwoForm E M} {g : F → M} {p : ℝ × F}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (euclideanPullbackTwoForm Ω g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : ℝ × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := ((hΩ c).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) c).map_source hc⟩)).comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by simp)).comp p contDiffAt_snd
  have hsm := smooth_bilinear_flip ((smooth_bilinear_flip (hform.clm_comp hder)).clm_comp hder)
  apply hsm.congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackTwoForm_chart (hq.mdifferentiableAt (by simp)) hqc

theorem euclideanPullbackOneForm_contDiffAt
    {α : ℝ → ManifoldOneForm E M} {g : F → M} {p : ℝ × F}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (euclideanPullbackOneForm α g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : ℝ × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := ((hα c).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) c).map_source hc⟩)).comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by simp)).comp p contDiffAt_snd
  have hsm := hform.clm_comp hder
  apply hsm.congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackOneForm_chart (hq.mdifferentiableAt (by simp)) hqc


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def chartSupportedOneForm (c : M) (α : E → E →L[ℝ] ℝ) : ManifoldOneForm E M := by
  classical
  exact fun x => if x ∈ (extChartAt 𝓘(ℝ,E) c).source then
    (α (extChartAt 𝓘(ℝ,E) c x)).comp (chartDifferential c x) else 0

theorem chartSupportedOneForm_chart {c b : M} {α : E → E →L[ℝ] ℝ} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    chartOneForm (chartSupportedOneForm c α) b y =
      (α (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))).comp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y) := by
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have ho := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)
  let A : E →L[ℝ] E :=
    (chartDifferential c ((extChartAt 𝓘(ℝ,E) b).symm y)).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) b).symm y)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) A y :=
    hasMFDerivAt_iff_hasFDerivAt.mp (ho.hasMFDerivAt.comp y hi.hasMFDerivAt)
  have he := hf.fderiv
  dsimp only [A,chartDifferential] at he
  simp only [chartOneForm,chartSupportedOneForm,ite_eq_left hc,chartDifferential_inverse hy,he]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem chartSupportedOneForm_zero {c : M} {α : E → E →L[ℝ] ℝ} {K : Set E}
    (hα : ∀ y ∉ K, α y=0) {x : M}
    (hx : x ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K) : chartSupportedOneForm c α x=0 := by
  classical
  unfold chartSupportedOneForm
  split_ifs with hc
  · have hn : extChartAt 𝓘(ℝ,E) c x ∉ K := by
      intro hk
      exact hx ⟨extChartAt 𝓘(ℝ,E) c x,hk,(extChartAt 𝓘(ℝ,E) c).left_inv hc⟩
    rw [hα _ hn]
    exact ContinuousLinearMap.zero_comp _
  · rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartSupportedOneForm_compact [T2Space M] {c : M} {α : E → E →L[ℝ] ℝ}
    {K : Set E} (hKc : IsCompact K) (hK : K ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hα : ∀ y ∉ K, α y=0) : HasCompactSupport (chartSupportedOneForm c α) := by
  apply HasCompactSupport.intro (hKc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,E)) c).mono hK))
  exact fun x hx => chartSupportedOneForm_zero hα hx

theorem chartSupportedOneForm_smooth [T2Space M] {c : M}
    {α : P × E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α)
    {K : Set E} (hKc : IsCompact K) (hK : K ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hzero : ∀ p y, y ∉ K → α (p,y)=0) (b : M) :
    ContDiffOn ℝ ∞ (fun q : P × E =>
      chartOneForm (chartSupportedOneForm c (fun y => α (q.1,y))) b q.2)
        (univ ×ˢ (extChartAt 𝓘(ℝ,E) b).target) := by
  intro p hp
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hp.2)
  let x := (extChartAt 𝓘(ℝ,E) b).symm p.2
  by_cases hc : x ∈ (extChartAt 𝓘(ℝ,E) c).source
  · have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hc)
    have ht : ContDiffAt ℝ ∞
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) p.2 :=
      (ho.comp p.2 hi).contDiffAt
    have hv := hα.contDiffAt.comp p (contDiffAt_fst.prodMk (ht.comp p contDiffAt_snd))
    have hd := (ht.fderiv_right (m := ∞) (by simp)).comp p contDiffAt_snd
    apply ((hv.clm_comp hd).congr_of_eventuallyEq _).contDiffWithinAt
    have hb := continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hp.2)
    have hcn := (hi.continuousAt.comp continuousAt_snd).preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
    filter_upwards [hb,hcn] with q hqb hqc
    exact chartSupportedOneForm_chart hqb hqc
  · have hcomp : IsCompact ((extChartAt 𝓘(ℝ,E) c).symm '' K) :=
      hKc.image_of_continuousOn ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,E)) c).mono hK)
    have hx : x ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K := by
      rintro ⟨y,hy,he⟩
      exact hc (he ▸ (extChartAt 𝓘(ℝ,E) c).map_target (hK hy))
    have hn := (hi.continuousAt.comp continuousAt_snd).preimage_mem_nhds
      (hcomp.isClosed.isOpen_compl.mem_nhds hx)
    apply ((contDiffAt_const (c := (0 : E →L[ℝ] ℝ))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hn] with q hq
    change (chartSupportedOneForm c (fun y => α (q.1,y))
      ((extChartAt 𝓘(ℝ,E) b).symm q.2)).comp _ = 0
    change (extChartAt 𝓘(ℝ,E) b).symm q.2 ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K at hq
    rw [chartSupportedOneForm_zero (hzero q.1) hq]
    exact ContinuousLinearMap.zero_comp _



def chartSupportedTwoForm (c : M) (α : E → E →L[ℝ] E →L[ℝ] ℝ) : ManifoldTwoForm E M := by
  classical
  exact fun x => if x ∈ (extChartAt 𝓘(ℝ,E) c).source then
    (α (extChartAt 𝓘(ℝ,E) c x)).bilinearComp (chartDifferential c x) (chartDifferential c x) else 0

theorem chartSupportedTwoForm_chart {c b : M} {α : E → E →L[ℝ] E →L[ℝ] ℝ} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    chartTwoForm (chartSupportedTwoForm c α) b y =
      (α (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y) := by
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have ho := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)
  let A : E →L[ℝ] E :=
    (chartDifferential c ((extChartAt 𝓘(ℝ,E) b).symm y)).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) b).symm y)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) A y :=
    hasMFDerivAt_iff_hasFDerivAt.mp (ho.hasMFDerivAt.comp y hi.hasMFDerivAt)
  have he := hf.fderiv
  dsimp only [A,chartDifferential] at he
  simp only [chartTwoForm,chartSupportedTwoForm,ite_eq_left hc,chartDifferential_inverse hy,he]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem chartSupportedTwoForm_zero {c : M} {α : E → E →L[ℝ] E →L[ℝ] ℝ} {K : Set E}
    (hα : ∀ y ∉ K, α y=0) {x : M}
    (hx : x ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K) : chartSupportedTwoForm c α x=0 := by
  classical
  unfold chartSupportedTwoForm
  split_ifs with hc
  · have hn : extChartAt 𝓘(ℝ,E) c x ∉ K := by
      intro hk
      exact hx ⟨extChartAt 𝓘(ℝ,E) c x,hk,(extChartAt 𝓘(ℝ,E) c).left_inv hc⟩
    rw [hα _ hn]
    ext u v; rfl
  · rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartSupportedTwoForm_compact [T2Space M] {c : M} {α : E → E →L[ℝ] E →L[ℝ] ℝ}
    {K : Set E} (hKc : IsCompact K) (hK : K ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hα : ∀ y ∉ K, α y=0) : HasCompactSupport (chartSupportedTwoForm c α) := by
  apply HasCompactSupport.intro (hKc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,E)) c).mono hK))
  exact fun x hx => chartSupportedTwoForm_zero hα hx

theorem chartSupportedTwoForm_smooth [T2Space M] {c : M}
    {α : P × E → E →L[ℝ] E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α)
    {K : Set E} (hKc : IsCompact K) (hK : K ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hzero : ∀ p y, y ∉ K → α (p,y)=0) (b : M) :
    ContDiffOn ℝ ∞ (fun q : P × E =>
      chartTwoForm (chartSupportedTwoForm c (fun y => α (q.1,y))) b q.2)
        (univ ×ˢ (extChartAt 𝓘(ℝ,E) b).target) := by
  intro p hp
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hp.2)
  let x := (extChartAt 𝓘(ℝ,E) b).symm p.2
  by_cases hc : x ∈ (extChartAt 𝓘(ℝ,E) c).source
  · have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hc)
    have ht : ContDiffAt ℝ ∞
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) p.2 :=
      (ho.comp p.2 hi).contDiffAt
    have hv := hα.contDiffAt.comp p (contDiffAt_fst.prodMk (ht.comp p contDiffAt_snd))
    have hd := (ht.fderiv_right (m := ∞) (by simp)).comp p contDiffAt_snd
    have hsm := smooth_bilinear_flip ((smooth_bilinear_flip (hv.clm_comp hd)).clm_comp hd)
    apply (hsm.congr_of_eventuallyEq _).contDiffWithinAt
    have hb := continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hp.2)
    have hcn := (hi.continuousAt.comp continuousAt_snd).preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
    filter_upwards [hb,hcn] with q hqb hqc
    exact chartSupportedTwoForm_chart hqb hqc
  · have hcomp : IsCompact ((extChartAt 𝓘(ℝ,E) c).symm '' K) :=
      hKc.image_of_continuousOn ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,E)) c).mono hK)
    have hx : x ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K := by
      rintro ⟨y,hy,he⟩
      exact hc (he ▸ (extChartAt 𝓘(ℝ,E) c).map_target (hK hy))
    have hn := (hi.continuousAt.comp continuousAt_snd).preimage_mem_nhds
      (hcomp.isClosed.isOpen_compl.mem_nhds hx)
    apply ((contDiffAt_const (c := (0 : E →L[ℝ] E →L[ℝ] ℝ))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hn] with q hq
    change (chartSupportedTwoForm c (fun y => α (q.1,y))
      ((extChartAt 𝓘(ℝ,E) b).symm q.2)).bilinearComp _ _ = 0
    change (extChartAt 𝓘(ℝ,E) b).symm q.2 ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K at hq
    rw [chartSupportedTwoForm_zero (hzero q.1) hq]
    ext u v; rfl


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem euclideanExteriorOneForm_zero_outside {α : E → E →L[ℝ] ℝ} {K : Set E}
    (hK : IsClosed K) (hzero : ∀ x ∉ K, α x=0) {x : E} (hx : x ∉ K) :
    euclideanExteriorOneForm α x=0 := by
  have he : α =ᶠ[𝓝 x] fun _ => (0 : E →L[ℝ] ℝ) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact hzero y hy
  unfold euclideanExteriorOneForm
  rw [he.fderiv_eq]
  ext u v
  simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

theorem chartSupportedOneForm_exterior {c b : M} {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) {K : Set E} (hKc : IsCompact K)
    (hK : K ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hzero : ∀ y ∉ K, α y=0) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target) :
    euclideanExteriorOneForm (chartOneForm (chartSupportedOneForm c α) b) y =
      chartTwoForm (chartSupportedTwoForm c (euclideanExteriorOneForm α)) b y := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)
  let x := (extChartAt 𝓘(ℝ,E) b).symm y
  by_cases hc : x ∈ (extChartAt 𝓘(ℝ,E) c).source
  · have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hc)
    have ht : ContDiffAt ℝ ∞
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y :=
      (ho.comp y hi).contDiffAt
    have he : chartOneForm (chartSupportedOneForm c α) b =ᶠ[𝓝 y]
        staticPullbackOneForm α (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) := by
      filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy,
        hi.continuousAt.preimage_mem_nhds
          ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)] with z hzb hzc
      exact chartSupportedOneForm_chart hzb hzc
    rw [chartSupportedTwoForm_chart hy hc]
    calc
      _ = euclideanExteriorOneForm
          (staticPullbackOneForm α (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm)) y := by
        unfold euclideanExteriorOneForm
        rw [he.fderiv_eq]
      _ = _ := staticPullbackOneForm_exterior hα.contDiffAt ht
  · have hcomp : IsCompact ((extChartAt 𝓘(ℝ,E) c).symm '' K) :=
      hKc.image_of_continuousOn ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,E)) c).mono hK)
    have hx : x ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K := by
      rintro ⟨z,hz,he⟩
      exact hc (he ▸ (extChartAt 𝓘(ℝ,E) c).map_target (hK hz))
    have he : chartOneForm (chartSupportedOneForm c α) b =ᶠ[𝓝 y]
        fun _ => (0 : E →L[ℝ] ℝ) := by
      filter_upwards [hi.continuousAt.preimage_mem_nhds
        (hcomp.isClosed.isOpen_compl.mem_nhds hx)] with z hz
      change (chartSupportedOneForm c α ((extChartAt 𝓘(ℝ,E) b).symm z)).comp _ = 0
      change (extChartAt 𝓘(ℝ,E) b).symm z ∉ (extChartAt 𝓘(ℝ,E) c).symm '' K at hz
      rw [chartSupportedOneForm_zero hzero hz]
      exact ContinuousLinearMap.zero_comp _
    have hd : ∀ z ∉ K, euclideanExteriorOneForm α z=0 :=
      fun z hz => euclideanExteriorOneForm_zero_outside hKc.isClosed hzero hz
    have hz := chartSupportedTwoForm_zero hd hx
    calc
      euclideanExteriorOneForm (chartOneForm (chartSupportedOneForm c α) b) y =
          (0 : E →L[ℝ] E →L[ℝ] ℝ) := by
        unfold euclideanExteriorOneForm
        rw [he.fderiv_eq]
        ext u v
        simp
      _ = _ := by
        change 0 = (chartSupportedTwoForm c _ x).bilinearComp _ _
        rw [hz]
        ext u v
        rfl


end

open scoped ContDiff Manifold Topology
open MeasureTheory Set Function Manifold
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

theorem chart_supported_area_primitive {A : ℝ} (hA : 0<A) (a : Plane) (c : M)
    (hbox : Metric.closedBall a A ⊆ (extChartAt 𝓘(ℝ,Plane) c).target)
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, A ≤ |x-a.1| ∨ A ≤ |y-a.2| → f (p,(x,y))=0)
    (hmass : ∀ p, (∫ x, f (p,x))=0) :
    ∃ α : P → ManifoldOneForm Plane M,
      (∀ b, ContDiffOn ℝ ∞ (fun q : P × Plane => chartOneForm (α q.1) b q.2)
        (univ ×ˢ (extChartAt 𝓘(ℝ,Plane) b).target)) ∧
      (∀ p x, x ∉ (extChartAt 𝓘(ℝ,Plane) c).symm '' Metric.closedBall a A → α p x=0) ∧
      (∀ p b y, y ∈ (extChartAt 𝓘(ℝ,Plane) b).target →
        euclideanExteriorOneForm (chartOneForm (α p) b) y =
          chartTwoForm (chartSupportedTwoForm c (fun z => f (p,z) • planarArea)) b y) ∧
      (∀ p, (∀ z, f (p,z)=0) → ∀ x, α p x=0) := by
  obtain ⟨β,hβ,hβzero,hβd,hβall⟩ := translated_spatial_covector_primitive hA a hf hzero hmass
  have hbzero (p : P) (z : Plane) (hz : z ∉ Metric.closedBall a A) : β (p,z)=0 := by
    have hh : A < max |z.1-a.1| |z.2-a.2| := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
        Real.norm_eq_abs,not_le] using hz
    exact hβzero p z.1 z.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  refine ⟨fun p => chartSupportedOneForm c (fun z => β (p,z)),?_,?_,?_,?_⟩
  · intro b
    exact chartSupportedOneForm_smooth hβ (isCompact_closedBall a A) hbox hbzero b
  · intro p x hx
    exact chartSupportedOneForm_zero (hbzero p) hx
  · intro p b y hy
    have hp : ContDiff ℝ ∞ (fun z => β (p,z)) := hβ.comp (contDiff_const.prodMk contDiff_id)
    rw [chartSupportedOneForm_exterior hp (isCompact_closedBall a A) hbox (hbzero p) hy]
    have he : euclideanExteriorOneForm (fun z => β (p,z)) = fun z => f (p,z) • planarArea :=
      funext (hβd p)
    rw [he]
  · intro p hp x
    have he : (fun z => β (p,z)) = fun _ => (0 : Plane →L[ℝ] ℝ) := funext (hβall p hp)
    dsimp only
    rw [he]
    unfold chartSupportedOneForm
    split_ifs <;> simp

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in

theorem chart_primitive_support_compact {A : ℝ} {a : Plane} {c : M}
    (hbox : Metric.closedBall a A ⊆ (extChartAt 𝓘(ℝ,Plane) c).target) :
    IsCompact ((extChartAt 𝓘(ℝ,Plane) c).symm '' Metric.closedBall a A) ∧
      (extChartAt 𝓘(ℝ,Plane) c).symm '' Metric.closedBall a A ⊆
        (extChartAt 𝓘(ℝ,Plane) c).source := by
  refine ⟨(isCompact_closedBall a A).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) c).mono hbox),?_⟩
  rintro x ⟨y,hy,rfl⟩
  exact (extChartAt 𝓘(ℝ,Plane) c).map_target (hbox hy)



end PackingSufficiencySupport.Hamiltonian
end

end OAI
