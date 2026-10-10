import Mathlib
import OAI.Geometry.NearbyLagrangian.IntrinsicCylinder
import OAI.Geometry.NearbyLagrangian.CoreEndpoint
import OAI.Geometry.NearbyLagrangian.CylinderFamilies

namespace OAI

/-! Regularity, injectivity and restoration for intrinsic cylinder families. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Set Filter TopologicalSpace ContinuousLinearMap InnerProductSpace
variable {E R G V M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance cylinderRegularityBaseChartedSpace (U : Opens R) : ChartedSpace (E × R) (M × U) :=
  inferInstanceAs (ChartedSpace (ModelProd E R) (M × U))
local instance cylinderRegularityBaseIsManifold (U : Opens R) : IsManifold 𝓘(ℝ,E × R) ∞ (M × U) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,E)) (I':=𝓘(ℝ,R)) M U

lemma contMDiffAt_intrinsicVertical {A : M × V → ℝ} {q : M × V}
    (hA : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A q) :
    ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,V →L[ℝ] ℝ) ∞
      (fun y : M × V => fderiv ℝ (fun v => A (y.1,v)) y.2) q := by
  let F : (M × V) → V → ℝ := fun x v => A (x.1,v)
  have hF : ContMDiffAt ((𝓘(ℝ,E).prod 𝓘(ℝ,V)).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞
      (Function.uncurry F) (q,q.2) :=
    hA.comp (q,q.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
  have h := hF.mfderiv (m:=∞) F Prod.snd contMDiffAt_snd (by simp)
  erw [inTangentCoordinates_model_space] at h
  simpa only [F,mfderiv_eq_fderiv] using h

omit [CompleteSpace R] [CompleteSpace G] [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem cylinderFamily_regular (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A)
    (q : M × V) (a : U)
    (hreg : Function.Surjective (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,V →L[ℝ] ℝ)
      (fun y : M × V => fderiv ℝ (fun v => A (y.1,v)) y.2) q)) :
    Function.Surjective (fderiv ℝ
      (fun y : G × V => fderiv ℝ (fun v => cylinderFamily U W e A (y.1,v)) y.2)
      ((e (q.1,a):G),q.2)) := by
  let j : M × V → G × V := fun y => ((e (y.1,a):G),y.2)
  have hp : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,E × R) ∞
      (fun y : M × V => (y.1,a)) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst.prodMk contMDiff_const
  have hj : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,G × V) ∞ j := by
    exact (contMDiff_subtype_val.comp (e.contMDiff.comp hp)).prodMk_space contMDiff_snd
  have hc : ContMDiffAt 𝓘(ℝ,G × V) 𝓘(ℝ,V →L[ℝ] ℝ) ∞
      (fun y : G × V => fderiv ℝ (fun v => cylinderFamily U W e A (y.1,v)) y.2)
      (j q) := by
    let F : (G × V) → V → ℝ := fun y v => cylinderFamily U W e A (y.1,v)
    have hjj : ContDiffAt ℝ ∞ (fun z : (G × V) × V => (z.1.1,z.2)) (j q,(j q).2) :=
      (contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd
    have hf0 := contDiffAt_cylinderFamily U W e hA (e (q.1,a)) q.2
    have hf : ContDiffAt ℝ ∞ (Function.uncurry F) (j q,(j q).2) := by
      convert hf0.comp (j q,(j q).2) hjj using 1
      funext z
      rfl
    exact (hf.fderiv (m:=∞) contDiffAt_snd (by simp)).contMDiffAt
  have hd := mfderiv_comp q (hc.mdifferentiableAt (by simp))
    (hj.mdifferentiableAt (by simp))
  have heq : (fun y : M × V => fderiv ℝ
      (fun v => cylinderFamily U W e A ((j y).1,v)) (j y).2) =
      (fun y : M × V => fderiv ℝ (fun v => A (y.1,v)) y.2) := by
    funext y
    exact cylinderFamily_vertical U W e A (y.1,a) y.2
  simp only [Function.comp_def] at hd
  erw [heq,mfderiv_eq_fderiv] at hd
  intro z
  obtain ⟨v,hv⟩ := hreg z
  refine ⟨mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,G × V) j q v,?_⟩
  exact (congrArg (fun L => L v) hd).symm.trans hv

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Set Filter TopologicalSpace ContinuousLinearMap InnerProductSpace Transport
variable {E R G V M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance cylinderRegularityPhaseChartedSpace (U : Opens R) : ChartedSpace (E × R) (M × U) :=
  inferInstanceAs (ChartedSpace (ModelProd E R) (M × U))
local instance cylinderRegularityPhaseIsManifold (U : Opens R) : IsManifold 𝓘(ℝ,E × R) ∞ (M × U) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,E)) (I':=𝓘(ℝ,R)) M U

omit [CompleteSpace R] [CompleteSpace G] [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma cylinderFamily_vertical_joint (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A)
    (x : W) (v : V) :
    verticalDifferential (cylinderFamily U W e A) x v =
      fderiv ℝ (fun w => cylinderFamily U W e A ((x:G),w)) v :=
  verticalDifferential_eq_partial ((contDiffAt_cylinderFamily U W e hA x v).differentiableAt (by simp))

omit [CompleteSpace R] [IsManifold 𝓘(ℝ,E) ∞ M] in

def cylinderCriticalPhaseEquiv (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A) :
    CylinderCritical U W e A ≃ PhaseCritical W (cylinderFamily U W e A) where
  toFun q := ⟨q.val,q.property.1,by
    rw [cylinderFamily_vertical_joint U W e hA ⟨q.val.1,q.property.1⟩]
    exact q.property.2⟩
  invFun q := ⟨q.val,q.property.1,by
    rw [← cylinderFamily_vertical_joint U W e hA ⟨q.val.1,q.property.1⟩]
    exact q.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [CompleteSpace R] [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma phaseGenerate_cylinderFamily (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A)
    (q : G × V) (hq : q.1 ∈ W) :
    phaseGenerate (cylinderFamily U W e A) q = cylinderGenerate U W e A q := by
  apply Prod.ext
  · rfl
  change (toDual ℝ G).symm (baseDifferential _ _ _) = _
  rw [baseDifferential_eq_partial q
    ((contDiffAt_cylinderFamily U W e hA ⟨q.1,hq⟩ q.2).differentiableAt (by simp))]
  rfl

omit [CompleteSpace R] [CompleteSpace G] [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem cylinderFamily_morseOn (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A)
    (hreg : ∀ q : IntrinsicCritical A,
      Function.Surjective (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,V →L[ℝ] ℝ)
        (fun y : M × V => fderiv ℝ (fun v => A (y.1,v)) y.2) q.val)) :
    MorseOn W (cylinderFamily U W e A) := by
  intro x hx v hv
  let r : PhaseCritical W (cylinderFamily U W e A) := ⟨(x,v),hx,hv⟩
  obtain ⟨q,hq⟩ := (cylinderCriticalPhaseEquiv U W e hA).surjective r
  obtain ⟨⟨s,a⟩,hs⟩ := (cylinderCriticalEquiv U W e A).surjective q
  have hpoint : ((e (s.val.1,a):G),s.val.2) = (x,v) :=
    (congrArg Subtype.val hs).trans (congrArg Subtype.val hq)
  have hh := cylinderFamily_regular U W e hA s.val a (hreg s)
  rw [hpoint] at hh
  have he : (fun y : G × V => verticalDifferential (cylinderFamily U W e A) y.1 y.2) =ᶠ[𝓝 (x,v)]
      (fun y : G × V => fderiv ℝ (fun w => cylinderFamily U W e A (y.1,w)) y.2) := by
    filter_upwards [continuous_fst.continuousAt.eventually (W.isOpen.mem_nhds hx)] with y hy
    exact cylinderFamily_vertical_joint U W e hA ⟨y.1,hy⟩ y.2
  rw [he.fderiv_eq]
  exact hh

theorem cylinderFamily_phase_range (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A) :
    range (fun q : PhaseCritical W (cylinderFamily U W e A) =>
      phaseGenerate (cylinderFamily U W e A) q.val) =
      (fun z : Cotangent (E:=E) (M:=M) × openPhase U =>
        (cotangentCylinderChart U W e z:G × G)) ''
        {z | z.1 ∈ range (fun q : IntrinsicCritical A => intrinsicGenerate (E:=E) A q.val) ∧
          (z.2:R × R).2 = 0} := by
  rw [← cylinderGenerate_range U W e hA]
  ext z
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨(cylinderCriticalPhaseEquiv U W e hA).symm q,
      (phaseGenerate_cylinderFamily U W e hA q.val q.property.1).symm⟩
  · rintro ⟨q,rfl⟩
    exact ⟨cylinderCriticalPhaseEquiv U W e hA q,
      phaseGenerate_cylinderFamily U W e hA q.val q.property.1⟩

theorem cylinderFamily_phase_injective (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A)
    (hi : Function.Injective (fun q : IntrinsicCritical A => intrinsicGenerate (E:=E) A q.val)) :
    Function.Injective (fun q : PhaseCritical W (cylinderFamily U W e A) =>
      phaseGenerate (cylinderFamily U W e A) q.val) := by
  intro q r h
  have he := cylinderGenerate_injective U W e hA hi
    (a₁ := (cylinderCriticalPhaseEquiv U W e hA).symm q)
    (a₂ := (cylinderCriticalPhaseEquiv U W e hA).symm r)
  apply Subtype.ext
  apply congrArg Subtype.val (he ?_)
  exact (phaseGenerate_cylinderFamily U W e hA q.val q.property.1).symm.trans
    (h.trans (phaseGenerate_cylinderFamily U W e hA r.val r.property.1))

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.IntrinsicCylinder
open scoped Manifold ContDiff Topology
open Set Filter TopologicalSpace CotangentGeometry PolarCylinder SmoothFlow Transport Tubes
local instance cylinderRegularityFinrank (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) := ⟨by simp⟩
local instance cylinderRegularityIntrinsicChartedSpace (n : ℕ) : ChartedSpace (BaseVector n) (Base n) :=
  inferInstanceAs (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 9))
    (EuclideanSpace ℝ (Fin n))) (Base n))
local instance cylinderRegularityIntrinsicIsManifold (n : ℕ) : IsManifold 𝓘(ℝ, BaseVector n) ∞ (Base n) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓡 9) (I' := 𝓡 n) (Sphere 9) (Sphere n)

local instance cylinderRegularityNormalChartedSpace (n : ℕ) (U : Opens Normal) :
    ChartedSpace (BaseVector n × Normal) (Base n × U) :=
  inferInstanceAs (ChartedSpace (ModelProd (BaseVector n) Normal) (Base n × U))
local instance cylinderRegularityNormalIsManifold (n : ℕ) (U : Opens Normal) :
    IsManifold 𝓘(ℝ,BaseVector n × Normal) ∞ (Base n × U) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,BaseVector n)) (I':=𝓘(ℝ,Normal)) (Base n) U

theorem exists_intrinsic_restored_endpoint {n m : ℕ}
    {νc ν : ℝ} (hνc : 0 < νc) (hνcν : νc < ν) (hν : ν < 1)
    (v₀ : Sphere n) (a : C(Sphere 9, Tube m m))
    {A : Base n × Euclidean (m+m) → ℝ}
    (hA : ContMDiff ((NearbyLagrangian.baseModel n).prod 𝓘(ℝ,Euclidean (m+m))) 𝓘(ℝ,ℝ) ∞ A)
    (hg : ContMDiff ((NearbyLagrangian.baseModel n).prod 𝓘(ℝ,Euclidean (m+m))) 𝓘(ℝ,ℝ) 1
      (fun q : Base n × Euclidean (m+m) => (a q.1.1).val q.2))
    (hreg : ∀ q : IntrinsicCritical A,
      Function.Surjective (mfderiv ((NearbyLagrangian.baseModel n).prod 𝓘(ℝ,Euclidean (m+m)))
        𝓘(ℝ,Euclidean (m+m) →L[ℝ] ℝ)
        (fun y : Base n × Euclidean (m+m) => fderiv ℝ (fun v => A (y.1,v)) y.2) q.val))
    (hinj : Function.Injective (fun q : IntrinsicCritical A =>
      intrinsicGenerate (E:=BaseVector n) A q.val))
    (R₀ : ℝ) (htail : ∀ q : Base n, ∀ w, R₀ ≤ ‖w‖ → A (q,w) = (a q.1).val w)
    {i : Base n → NearbyLagrangian.Cotangent n}
    (hrange : range (fun q : IntrinsicCritical A => intrinsicGenerate (E:=BaseVector n) A q.val) = range i)
    (hi : IsHamiltonianImage i) :
    ∃ (t : ℕ) (R : ℝ)
      (δ : C(Sphere 9,Tube (transportIndex m (10+(n+1)) t) (transportIndex m (10+(n+1)) t)))
      (H : Sphere 9 × Euclidean (transportIndex m (10+(n+1)) t + transportIndex m (10+(n+1)) t) → ℝ)
      (σ : Sphere 9 → Euclidean (transportIndex m (10+(n+1)) t + transportIndex m (10+(n+1)) t)),
      1 ≤ R ∧ ((addBalancedFor m (10+(n+1)) t).comp a).Homotopic δ ∧
      (∀ q : Sphere 9 × Euclidean (transportIndex m (10+(n+1)) t + transportIndex m (10+(n+1)) t), q.2 ≠ 0 →
        ContMDiffAt ((𝓡 9).prod 𝓘(ℝ,Euclidean (transportIndex m (10+(n+1)) t + transportIndex m (10+(n+1)) t)))
          𝓘(ℝ,ℝ) ∞ (fun q => (δ q.1).val q.2) q) ∧
      ContMDiff ((𝓡 9).prod 𝓘(ℝ,Euclidean (transportIndex m (10+(n+1)) t + transportIndex m (10+(n+1)) t)))
        𝓘(ℝ,ℝ) ∞ H ∧
      (∀ q, 2*R ≤ ‖q.2‖ → H q = (δ q.1).val q.2) ∧
      ContMDiff (𝓡 9) 𝓘(ℝ,Euclidean (transportIndex m (10+(n+1)) t + transportIndex m (10+(n+1)) t)) ∞ σ ∧
      (∀ b w, fderiv ℝ (fun w => H (b,w)) w = 0 ↔ w = σ b) ∧
      (∀ b, Function.Bijective (fderiv ℝ (fderiv ℝ (fun w => H (b,w))) (σ b))) := by
  rw [baseModel_eq] at hA hg hreg
  let U := radialSquare ν
  let W := euclideanCylinderOpen 9 n ν
  let e := flatEuclideanCylinderSquareDiffeomorph 9 n hν
  let G : Base n × Euclidean (m+m) → ℝ := fun q => (a q.1.1).val q.2
  let F := cylinderFamily U W e A
  let g := cylinderFamily U W e G
  have hF (x : Ambient n) (hx : x ∈ W) (w : Euclidean (m+m)) : ContDiffAt ℝ ∞ F (x,w) :=
    contDiffAt_cylinderFamily U W e hA ⟨x,hx⟩ w
  have hgs (x : Ambient n) (hx : x ∈ W) (w : Euclidean (m+m)) : ContDiffAt ℝ 1 g (x,w) :=
    contDiffAt_cylinderFamily_one U W e hg ⟨x,hx⟩ w
  have hgh (x : Ambient n) (hx : x ∈ W) (r : ℝ) (hr : 0 < r) (w : Euclidean (m+m)) :
      g (x,r • w) = r^2*g (x,w) := by
    simp only [g,cylinderFamily_apply U W e G ⟨x,hx⟩,G]
    exact (a (e.symm ⟨x,hx⟩).1.1).val.homogeneity r hr w
  have hgr (x : Ambient n) (hx : x ∈ W) (w : Euclidean (m+m)) (hw : w ≠ 0) :
      verticalDifferential g x w ≠ 0 := by
    rw [verticalDifferential_eq_partial ((hgs x hx w).differentiableAt one_ne_zero)]
    have he : (fun w => g (x,w)) = (a (e.symm ⟨x,hx⟩).1.1).val := by
      funext w
      exact cylinderFamily_apply U W e G ⟨x,hx⟩ w
    rw [he]
    exact (a (e.symm ⟨x,hx⟩).1.1).val.regular w hw
  have hFt (x : Ambient n) (hx : x ∈ W) (w : Euclidean (m+m)) (hw : R₀ ≤ ‖w‖) :
      F (x,w) = g (x,w) := by
    rw [show F (x,w) = A ((e.symm ⟨x,hx⟩).1,w) from cylinderFamily_apply U W e A ⟨x,hx⟩ w]
    rw [show g (x,w) = G ((e.symm ⟨x,hx⟩).1,w) from cylinderFamily_apply U W e G ⟨x,hx⟩ w]
    exact htail _ w hw
  obtain ⟨K,T,hT⟩ := exists_intrinsic_cylinder_transport hνc hνcν hν hi
  have hFrange : range (fun q : PhaseCritical W F => phaseGenerate F q.val) = initialCylinder n hν i := by
    rw [cylinderFamily_phase_range U W e hA,hrange]
    simp only [initialCylinder,sourceCylinderChart_apply]
    rfl
  have hcenter : range (fun q : PhaseCritical W F => evolution T.flow ((0,phaseGenerate F q.val),1)) ∩
      (centralTube n hν νc ×ˢ univ) = range (fun x : centralTube n hν νc => ((x:Ambient n),(0:Ambient n))) := by
    rw [← hFrange] at hT
    rw [← Set.range_comp] at hT
    exact hT
  have hν0 : 0 < ν := hνc.trans hνcν
  have hzν : (0:Normal) ∈ U := by
    rw [mem_radialSquare_iff]
    simpa only [map_zero,Prod.fst_zero,Prod.snd_zero,mem_Ioo,neg_lt_zero] using And.intro (And.intro hν0 hν0) (And.intro hν0 hν0)
  have hzc : (0:Normal) ∈ radialSquare νc := by
    rw [mem_radialSquare_iff]
    simpa only [map_zero,Prod.fst_zero,Prod.snd_zero,mem_Ioo,neg_lt_zero] using And.intro (And.intro hνc hνc) (And.intro hνc hνc)
  let j : Sphere 9 → Ambient n := fun b => (e ((b,v₀),⟨0,hzν⟩):Ambient n)
  have hj : ContMDiff (𝓡 9) 𝓘(ℝ,Ambient n) ∞ j := by
    have hs : ContMDiff (𝓡 9) 𝓘(ℝ,BaseVector n × Normal) ∞
        (fun b : Sphere 9 => (((b,v₀):Base n),(⟨0,hzν⟩:U))) := by
      rw [modelWithCornersSelf_prod,modelWithCornersSelf_prod]
      exact (contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const
    exact contMDiff_subtype_val.comp (e.contMDiff.comp hs)
  have hjC (b : Sphere 9) : j b ∈ centralTube n hν νc :=
    ⟨((b,v₀),⟨0,hzν⟩),hzc,rfl⟩
  have href (b : Sphere 9) (w : Euclidean (m+m)) : g (j b,w) = (a b).val w :=
    cylinderFamily_at_chart U W e G ((b,v₀),⟨0,hzν⟩) w
  exact exists_core_restored_endpoint W (centralTube_open n hν νc) (centralTube_subset n hν νc)
    hF hgs hgh hgr R₀ hFt (cylinderFamily_morseOn U W e hA hreg)
    (cylinderFamily_phase_injective U W e hA hinj) T hcenter hj hjC a href

end NearbyLagrangian.IntrinsicCylinder

end

end OAI
