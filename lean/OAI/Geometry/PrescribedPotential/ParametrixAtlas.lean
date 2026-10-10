import Mathlib
import OAI.Geometry.PrescribedPotential.AtlasLocalization
import OAI.Geometry.PrescribedPotential.ChartParametrix
import OAI.Geometry.PrescribedPotential.LocalRegularity

namespace OAI

/-! Parametrix Atlas. -/

section

 

noncomputable section
open Set Filter Topology Manifold IsManifold
open scoped ContDiff SchwartzMap BoundedContinuousFunction ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace Anticanonical.ComplexAtlas
open EllipticKernel
variable {d : ℕ} {X : Type*} [TopologicalSpace X] (A : ComplexAtlas d X)

def euclideanChart (i : Fin A.count) : OpenPartialHomeomorph X (EC d) :=
  (A.chart i).trans (coordinateEquiv d).symm.toHomeomorph.toOpenPartialHomeomorph

@[simp] lemma euclideanChart_source (i : Fin A.count) :
    (A.euclideanChart i).source = (A.chart i).source := by
  simp [euclideanChart]

@[simp] lemma euclideanChart_target (i : Fin A.count) :
    (A.euclideanChart i).target = (coordinateEquiv d) ⁻¹' (A.chart i).target := by
  ext x
  simp [euclideanChart]

@[simp] lemma euclideanChart_apply (i : Fin A.count) (x : X) :
    A.euclideanChart i x = (coordinateEquiv d).symm (A.chart i x) := rfl

@[simp] lemma euclideanChart_symm_apply (i : Fin A.count) (y : EC d) :
    (A.euclideanChart i).symm y = (A.chart i).symm (coordinateEquiv d y) := rfl

lemma euclidean_transition_smooth (i j : Fin A.count) :
    ContDiffOn ℝ ∞ ((A.euclideanChart i).symm.trans (A.euclideanChart j))
      ((A.euclideanChart i).symm.trans (A.euclideanChart j)).source := by
  let e := (A.euclideanChart i).symm.trans (A.euclideanChart j)
  have he : (e : EC d → EC d) =
      (coordinateEquiv d).symm ∘ A.transition i j ∘ coordinateEquiv d := rfl
  rw [he]
  apply (coordinateEquiv d).symm.contDiff.comp_contDiffOn
  apply (A.real_smooth_transition i j).comp (coordinateEquiv d).contDiff.contDiffOn
  intro z hz
  exact ⟨by simpa using hz.1, by simpa using hz.2⟩

end Anticanonical.ComplexAtlas

namespace Anticanonical.SourceSmooth
open EllipticKernel SobolevChart FrozenPoisson MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

 
structure ParametrixPatch (g : KaehlerMetric A) where
  index : Fin A.count
  center : EC d
  mem_target : center ∈ (A.euclideanChart index).target
  domain : Set (EC d)
  isOpen_domain : IsOpen domain
  center_mem : center ∈ domain
  domain_sub : domain ⊆ (A.euclideanChart index).target
  coefficient : SmoothCoefficients (BasisIndex d) (EC d)
  small : perturbationBound (stdOrthonormalBasis ℝ (EC d)) (coefficientBCF coefficient) *
    ellipticBound (g.matrix index (coordinateEquiv d center))
      (g.positive index _ (by simpa using mem_target)) < 1
  equals : ∀ y ∈ domain, ∀ k l,
    extendedCoefficient (g.matrix index (coordinateEquiv d center))
      (coefficientBCF coefficient) k l y =
      (traceBilin (g.matrix index (coordinateEquiv d y))
        (rankTwo (stdOrthonormalBasis ℝ (EC d) k) (stdOrthonormalBasis ℝ (EC d) l)) : ℂ)

namespace ParametrixPatch
variable (g : KaehlerMetric A)

def source (p : ParametrixPatch g) : Set X :=
  (A.euclideanChart p.index).source ∩ (A.euclideanChart p.index) ⁻¹' p.domain

lemma isOpen_source (p : ParametrixPatch g) : IsOpen p.source :=
  (A.euclideanChart p.index).isOpen_inter_preimage p.isOpen_domain

lemma source_sub (p : ParametrixPatch g) : p.source ⊆ (A.chart p.index).source :=
  fun _ hx => by simpa using hx.1

lemma exists_at (x : X) : ∃ p : ParametrixPatch g, x ∈ p.source := by
  obtain ⟨i, hi⟩ := A.covers x
  let e := A.euclideanChart i
  have hxe : x ∈ e.source := by simpa [e] using hi
  have hx : e x ∈ e.target := e.mapsTo hxe
  let H : EC d → Matrix (Fin d) (Fin d) ℂ := fun z => g.matrix i (coordinateEquiv d z)
  have hH : ContDiffOn ℝ ∞ H e.target :=
    (g.smooth i).comp (coordinateEquiv d).contDiff.contDiffOn (fun z hz => by simpa [e] using hz)
  have hh : ∀ z ∈ e.target, (H z).PosDef := fun z hz => g.positive i _ (by simpa [e] using hz)
  let b := stdOrthonormalBasis ℝ (EC d)
  obtain ⟨a, hat, hac, has, hag⟩ := local_coefficient_extension e.open_target H hH hh hx b
  let a' : SmoothCoefficients (BasisIndex d) (EC d) :=
    fun k l => (hac k l).toSchwartzMap (hat k l).1
  have hae : coefficientBCF a' = a := by funext k l; ext y; rfl
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp (inter_mem (e.open_target.mem_nhds hx) hag)
  let p : ParametrixPatch g :=
    { index := i
      center := e x
      mem_target := hx
      domain := V
      isOpen_domain := hVo
      center_mem := hxV
      domain_sub := fun y hy => (hVsub hy).1
      coefficient := a'
      small := by rw [hae]; exact has
      equals := by
        intro y hy k l
        rw [hae]
        change (traceBilin (H (e x)) (rankTwo (b k) (b l)) : ℂ) + a k l y = _
        rw [(hVsub hy).2 k l]
        ring }
  exact ⟨p, hxe, hxV⟩

 
theorem finite_cover [CompactSpace X] :
    ∃ S : Finset (ParametrixPatch g), ∀ x : X, ∃ p ∈ S, x ∈ p.source := by
  classical
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun p : ParametrixPatch g => p.source)
    (fun p => p.isOpen_source) (by
      intro x _
      obtain ⟨p, hp⟩ := exists_at g x
      exact mem_iUnion.mpr ⟨p, hp⟩)
  refine ⟨S, fun x => ?_⟩
  obtain ⟨p, hp, hx⟩ := mem_iUnion₂.mp (hS (mem_univ x))
  exact ⟨p, hp, hx⟩

end ParametrixPatch
end Anticanonical.SourceSmooth

end
end

end OAI
