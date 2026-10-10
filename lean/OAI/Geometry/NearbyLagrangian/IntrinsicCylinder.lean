import Mathlib
import OAI.Geometry.NearbyLagrangian.CylinderCutoffs
import OAI.Geometry.NearbyLagrangian.CylinderTransport
import OAI.Geometry.NearbyLagrangian.Isotopies
import OAI.Geometry.NearbyLagrangian.SymplecticCylinder

namespace OAI

/-! Intrinsic cylinder charts and generating-family transport. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.IntrinsicCylinder
open scoped Manifold ContDiff Topology
open Set TopologicalSpace CotangentGeometry PolarCylinder

local instance (n : ℕ) : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) :=
  ⟨by simp⟩
local instance (n : ℕ) : ChartedSpace (BaseVector n) (Base n) :=
  inferInstanceAs (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 9))
    (EuclideanSpace ℝ (Fin n))) (Base n))
local instance (n : ℕ) : IsManifold 𝓘(ℝ, BaseVector n) ∞ (Base n) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓡 9) (I' := 𝓡 n) (Sphere 9) (Sphere n)
local instance (n : ℕ) : ChartedSpace (CotangentVector n) (NearbyLagrangian.Cotangent n) :=
  inferInstanceAs (ChartedSpace (ModelProd (BaseVector n) (BaseVector n →L[ℝ] ℝ))
    (NearbyLagrangian.Cotangent n))

lemma baseModel_eq (n : ℕ) : baseModel n = 𝓘(ℝ, BaseVector n) :=
  modelWithCornersSelf_prod.symm
lemma cotangentModel_eq (n : ℕ) : NearbyLagrangian.cotangentModel n =
    CotangentGeometry.cotangentModel (E := BaseVector n) := by
  unfold NearbyLagrangian.cotangentModel CotangentGeometry.cotangentModel
  rw [baseModel_eq]
lemma liouville_eq {n : ℕ}
    (z : NearbyLagrangian.Cotangent n) (v : TangentSpace (NearbyLagrangian.cotangentModel n) z) :
    CotangentGeometry.liouville (E := BaseVector n) (M := Base n) z v =
      NearbyLagrangian.liouville z v := by
  unfold CotangentGeometry.liouville NearbyLagrangian.liouville
  simp only [NearbyLagrangian.cotangentModel, baseModel, CotangentGeometry.cotangentModel]
  rfl
lemma liouvilleInChart_eq {n : ℕ}
    (z : NearbyLagrangian.Cotangent n) (x : CotangentVector n) :
    CotangentGeometry.liouvilleInChart (E := BaseVector n) (M := Base n) z x =
      NearbyLagrangian.liouvilleInChart z x := by
  unfold CotangentGeometry.liouvilleInChart NearbyLagrangian.liouvilleInChart
  rw [cotangentModel_eq]
  apply congrArg (fun p : (TangentSpace (NearbyLagrangian.cotangentModel n)
      ((extChartAt (NearbyLagrangian.cotangentModel n) z).symm x)) →L[ℝ] ℝ => p.comp _)
  apply ContinuousLinearMap.ext
  intro v
  exact liouville_eq _ _
lemma symplectic_eq {n : ℕ}
    (z : NearbyLagrangian.Cotangent n) (u v : TangentSpace (NearbyLagrangian.cotangentModel n) z) :
    CotangentGeometry.symplecticForm (E := BaseVector n) (M := Base n) z u v =
      NearbyLagrangian.symplecticForm z u v := by
  have he : CotangentGeometry.liouvilleInChart (E := BaseVector n) (M := Base n) z =
      NearbyLagrangian.liouvilleInChart z := funext (liouvilleInChart_eq z)
  unfold CotangentGeometry.symplecticForm NearbyLagrangian.symplecticForm
  rw [cotangentModel_eq, he]
  rfl

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin (10+(n+1)))
abbrev Normal := EuclideanSpace ℝ (Fin 2)
abbrev normalPhase (ν : ℝ) := openPhase (radialSquare ν)
abbrev ambientPhase (n : ℕ) (ν : ℝ) := openPhase (euclideanCylinderOpen 9 n ν)

def sourceCylinderChart (n : ℕ) {ν : ℝ} (hν : ν < 1) :
    Diffeomorph ((NearbyLagrangian.cotangentModel n).prod 𝓘(ℝ,Normal × Normal))
      𝓘(ℝ,Ambient n × Ambient n)
      (NearbyLagrangian.Cotangent n × normalPhase ν) (ambientPhase n ν) ∞ where
  toEquiv := (cotangentCylinderChart (radialSquare ν) (euclideanCylinderOpen 9 n ν)
    (flatEuclideanCylinderSquareDiffeomorph 9 n hν)).toEquiv
  contMDiff_toFun := by
    rw [cotangentModel_eq]
    exact (cotangentCylinderChart (radialSquare ν) (euclideanCylinderOpen 9 n ν)
      (flatEuclideanCylinderSquareDiffeomorph 9 n hν)).contMDiff
  contMDiff_invFun := by
    rw [cotangentModel_eq]
    exact (cotangentCylinderChart (radialSquare ν) (euclideanCylinderOpen 9 n ν)
      (flatEuclideanCylinderSquareDiffeomorph 9 n hν)).symm.contMDiff

lemma sourceCylinderChart_apply (n : ℕ) {ν : ℝ} (hν : ν < 1) :
    (sourceCylinderChart n hν : NearbyLagrangian.Cotangent n × normalPhase ν → ambientPhase n ν) =
      (fun z => (cotangentCylinderChart (radialSquare ν) (euclideanCylinderOpen 9 n ν)
        (flatEuclideanCylinderSquareDiffeomorph 9 n hν)).toEquiv z) := rfl

def sourceCylinderDerivative (n : ℕ) {ν : ℝ} (hν : ν < 1)
    (z : NearbyLagrangian.Cotangent n × normalPhase ν) :
    (CotangentVector n × (Normal × Normal)) →L[ℝ] (Ambient n × Ambient n) :=
  mfderiv ((NearbyLagrangian.cotangentModel n).prod 𝓘(ℝ,Normal × Normal))
    𝓘(ℝ,Ambient n × Ambient n) (fun x => (sourceCylinderChart n hν).toEquiv x) z

lemma sourceCylinderDerivative_eq (n : ℕ) {ν : ℝ} (hν : ν < 1)
    (z : NearbyLagrangian.Cotangent n × normalPhase ν) :
    sourceCylinderDerivative n hν z =
      mfderiv ((CotangentGeometry.cotangentModel (E:=BaseVector n)).prod
        𝓘(ℝ,Normal × Normal)) 𝓘(ℝ,Ambient n × Ambient n)
        (fun x => (cotangentCylinderChart (radialSquare ν) (euclideanCylinderOpen 9 n ν)
          (flatEuclideanCylinderSquareDiffeomorph 9 n hν)).toEquiv x) z := by
  unfold sourceCylinderDerivative
  change mfderiv ((NearbyLagrangian.cotangentModel n).prod 𝓘(ℝ,Normal × Normal))
    𝓘(ℝ,Ambient n × Ambient n)
    (fun x => (cotangentCylinderChart (radialSquare ν) (euclideanCylinderOpen 9 n ν)
      (flatEuclideanCylinderSquareDiffeomorph 9 n hν)).toEquiv x) z = _
  rw [cotangentModel_eq]

theorem sourceCylinderChart_symplectic (n : ℕ) {ν : ℝ} (hν : ν < 1)
    (z : NearbyLagrangian.Cotangent n × normalPhase ν)
    (u v : CotangentVector n × (Normal × Normal)) :
    inner ℝ (sourceCylinderDerivative n hν z u).2 (sourceCylinderDerivative n hν z v).1 -
      inner ℝ (sourceCylinderDerivative n hν z v).2 (sourceCylinderDerivative n hν z u).1 =
      NearbyLagrangian.symplecticForm z.1 u.1 v.1 +
        inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1 := by
  rw [sourceCylinderDerivative_eq]
  erw [← symplectic_eq]
  exact cotangentCylinderChart_symplectic (E:=BaseVector n) (M:=Base n)
    (radialSquare ν) (euclideanCylinderOpen 9 n ν)
    (flatEuclideanCylinderSquareDiffeomorph 9 n hν) z u v

end NearbyLagrangian.IntrinsicCylinder

namespace NearbyLagrangian.IntrinsicCylinder
open scoped Manifold ContDiff Topology
open Set TopologicalSpace CotangentGeometry PolarCylinder
local instance (n : ℕ) : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) := ⟨by simp⟩
local instance (n : ℕ) : ChartedSpace (BaseVector n) (Base n) :=
  inferInstanceAs (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 9))
    (EuclideanSpace ℝ (Fin n))) (Base n))
local instance (n : ℕ) : IsManifold 𝓘(ℝ, BaseVector n) ∞ (Base n) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓡 9) (I' := 𝓡 n) (Sphere 9) (Sphere n)
local instance (n : ℕ) : ChartedSpace (CotangentVector n) (NearbyLagrangian.Cotangent n) :=
  inferInstanceAs (ChartedSpace (ModelProd (BaseVector n) (BaseVector n →L[ℝ] ℝ))
    (NearbyLagrangian.Cotangent n))

def centralTube (n : ℕ) {ν : ℝ} (hν : ν < 1) (νc : ℝ) : Set (Ambient n) :=
  centralSpatial (radialSquare ν) (euclideanCylinderOpen 9 n ν)
    (flatEuclideanCylinderSquareDiffeomorph 9 n hν) (radialSquare νc)

lemma centralTube_open (n : ℕ) {ν : ℝ} (hν : ν < 1) (νc : ℝ) :
    IsOpen (centralTube n hν νc) :=
  centralSpatial_isOpen _ _ _ (radialSquare νc).isOpen

lemma centralTube_subset (n : ℕ) {ν : ℝ} (hν : ν < 1) (νc : ℝ) :
    centralTube n hν νc ⊆ (euclideanCylinderOpen 9 n ν : Set (Ambient n)) :=
  centralSpatial_subset _ _ _ _

lemma sourceCylinder_centralImage (n : ℕ) {ν : ℝ} (hν : ν < 1) (νc : ℝ) :
    (fun z : NearbyLagrangian.Cotangent n × normalPhase ν =>
      (sourceCylinderChart n hν z : Ambient n × Ambient n)) ''
        {z | (z.2 : Normal × Normal).1 ∈ radialSquare νc} =
      centralTube n hν νc ×ˢ univ := by
  simp_rw [sourceCylinderChart_apply]
  exact cotangentCylinderChart_centralImage _ _ _ _

lemma sourceCylinder_zeroImage (n : ℕ) {ν : ℝ} (hν : ν < 1) (νc : ℝ) :
    (fun z : NearbyLagrangian.Cotangent n × normalPhase ν =>
      (sourceCylinderChart n hν z : Ambient n × Ambient n)) ''
        {z | z.1 ∈ range (NearbyLagrangian.zeroSection (n:=n)) ∧
          (z.2 : Normal × Normal).1 ∈ radialSquare νc ∧ (z.2 : Normal × Normal).2 = 0} =
      range (fun x : centralTube n hν νc => ((x:Ambient n),(0:Ambient n))) := by
  simp_rw [sourceCylinderChart_apply]
  exact cotangentCylinderChart_zeroImage _ _ _ _

end NearbyLagrangian.IntrinsicCylinder

namespace NearbyLagrangian.IntrinsicCylinder
open scoped Manifold ContDiff Topology
open Set TopologicalSpace CotangentGeometry PolarCylinder SmoothFlow RadialExtension Transport

def initialCylinder (n : ℕ) {ν : ℝ} (hν : ν < 1)
    (i : Base n → NearbyLagrangian.Cotangent n) : Set (Ambient n × Ambient n) :=
  (fun z : NearbyLagrangian.Cotangent n × normalPhase ν =>
    (sourceCylinderChart n hν z : Ambient n × Ambient n)) ''
      {z | z.1 ∈ range i ∧ (z.2 : Normal × Normal).2 = 0}

theorem exists_intrinsic_cylinder_transport {n : ℕ}
    {νc ν : ℝ} (hνc : 0 < νc) (hνcν : νc < ν) (hν : ν < 1)
    {i : Base n → NearbyLagrangian.Cotangent n} (hi : IsHamiltonianImage i) :
    ∃ (K : ℝ × (Ambient n × Ambient n) → ℝ)
      (F : SupportedHamiltonianEvolution (ambientPhase n ν) K),
      (fun z => evolution F.flow ((0,z),1)) '' initialCylinder n hν i ∩
        (centralTube n hν νc ×ˢ univ) =
      range (fun x : centralTube n hν νc => ((x:Ambient n),(0:Ambient n))) := by
  rcases hi with ⟨H,φ,h,hr⟩
  have he : IsSymplecticCylinderChart (normalPhase ν) (ambientPhase n ν)
      (sourceCylinderChart n hν) (fun z u v => NearbyLagrangian.symplecticForm z u v) :=
    sourceCylinderChart_symplectic n hν
  obtain ⟨K,F,hF⟩ := h.reverse.cylinder_extension hνc hνcν (normalPhase ν) rfl
    (ambientPhase n ν) (sourceCylinderChart n hν) he
  have him : reverseIsotopy φ 1 '' range i = range (NearbyLagrangian.zeroSection (n:=n)) := by
    rw [← Set.range_comp]
    exact reverseIsotopy_range_endpoint h.2.2.2.1 hr
  have ht := hF (range i) (range (NearbyLagrangian.zeroSection (n:=n))) him
  rw [sourceCylinder_centralImage,sourceCylinder_zeroImage] at ht
  refine ⟨K,F,?_⟩
  simpa only [initialCylinder,image_image,Function.comp_def] using ht

end NearbyLagrangian.IntrinsicCylinder

end

end OAI
