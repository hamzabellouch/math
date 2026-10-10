import Mathlib
import OAI.Geometry.NearbyLagrangian.SymplecticCylinder

namespace OAI

/-! Generating families in cylinder coordinates and their critical equivalences. -/

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
local instance cylinderFamiliesFamilyChartedSpace (U : Opens R) : ChartedSpace (E × R) (M × U) :=
  inferInstanceAs (ChartedSpace (ModelProd E R) (M × U))
local instance cylinderFamiliesFamilyManifold (U : Opens R) : IsManifold 𝓘(ℝ,E × R) ∞ (M × U) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,E)) (I':=𝓘(ℝ,R)) M U

def cylinderFamily (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    (A : M × V → ℝ) (q : G × V) : ℝ := by
  classical
  exact if h : q.1 ∈ W then A ((e.symm ⟨q.1,h⟩).1,q.2) else 0

omit [CompleteSpace R] [CompleteSpace G] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma cylinderFamily_apply (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    (A : M × V → ℝ) (x : W) (v : V) :
    cylinderFamily U W e A ((x:G),v) = A ((e.symm x).1,v) := by
  classical
  exact dite_eq_left x.property

omit [CompleteSpace R] [CompleteSpace G] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma cylinderFamily_at_chart (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    (A : M × V → ℝ) (q : M × U) (v : V) :
    cylinderFamily U W e A ((e q:G),v) = A (q.1,v) := by
  rw [cylinderFamily_apply,e.symm_apply_apply]

omit [CompleteSpace R] [CompleteSpace G] [IsManifold 𝓘(ℝ,E) ∞ M] in

lemma cylinderFamily_vertical (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    (A : M × V → ℝ) (q : M × U) (v : V) :
    fderiv ℝ (fun w => cylinderFamily U W e A ((e q:G),w)) v =
      fderiv ℝ (fun w => A (q.1,w)) v := by
  congr 1
  funext w
  exact cylinderFamily_at_chart U W e A q w

omit [CompleteSpace R] [CompleteSpace G] [IsManifold 𝓘(ℝ,E) ∞ M] in

lemma contDiffAt_cylinderFamily (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A)
    (x : W) (v : V) : ContDiffAt ℝ ∞ (cylinderFamily U W e A) ((x:G),v) := by
  let O : Opens (G × V) := ⟨(W:Set G) ×ˢ univ,W.isOpen.prod isOpen_univ⟩
  let r : O → W := fun z => ⟨z.val.1,z.property.1⟩
  have hr : ContMDiff 𝓘(ℝ,G × V) 𝓘(ℝ,G) ∞ r := by
    apply (ContMDiff.subtypeVal_comp_iff W _).mp
    exact contDiff_fst.contMDiff.comp contMDiff_subtype_val
  have ht : ContMDiff 𝓘(ℝ,G × V) 𝓘(ℝ,V) ∞ (fun z : O => z.val.2) :=
    contDiff_snd.contMDiff.comp contMDiff_subtype_val
  have hq : ContMDiff 𝓘(ℝ,G × V) 𝓘(ℝ,E) ∞ (fun z : O => (e.symm (r z)).1) := by
    have hp : ContMDiff 𝓘(ℝ,E × R) 𝓘(ℝ,E) ∞ (Prod.fst : M × U → M) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_fst
    exact hp.comp (e.symm.contMDiff.comp hr)
  have hs : ContMDiff 𝓘(ℝ,G × V) 𝓘(ℝ,ℝ) ∞
      (fun z : O => cylinderFamily U W e A z.val) := by
    have hh := hA.comp (hq.prodMk ht)
    convert hh using 1
    funext z
    exact cylinderFamily_apply U W e A (r z) z.val.2
  exact (contMDiffAt_subtype_iff.mp
    (hs.contMDiffAt (x:=⟨((x:G),v),⟨x.property,mem_univ _⟩⟩))).contDiffAt

omit [CompleteSpace R] [CompleteSpace G] [IsManifold 𝓘(ℝ,E) ∞ M] in

lemma contDiffAt_cylinderFamily_one (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) 1 A)
    (x : W) (v : V) : ContDiffAt ℝ 1 (cylinderFamily U W e A) ((x:G),v) := by
  let O : Opens (G × V) := ⟨(W:Set G) ×ˢ univ,W.isOpen.prod isOpen_univ⟩
  let r : O → W := fun z => ⟨z.val.1,z.property.1⟩
  have hr : ContMDiff 𝓘(ℝ,G × V) 𝓘(ℝ,G) ∞ r := by
    apply (ContMDiff.subtypeVal_comp_iff W _).mp
    exact contDiff_fst.contMDiff.comp contMDiff_subtype_val
  have ht : ContMDiff 𝓘(ℝ,G × V) 𝓘(ℝ,V) ∞ (fun z : O => z.val.2) :=
    contDiff_snd.contMDiff.comp contMDiff_subtype_val
  have hq : ContMDiff 𝓘(ℝ,G × V) 𝓘(ℝ,E) ∞ (fun z : O => (e.symm (r z)).1) := by
    have hp : ContMDiff 𝓘(ℝ,E × R) 𝓘(ℝ,E) ∞ (Prod.fst : M × U → M) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_fst
    exact hp.comp (e.symm.contMDiff.comp hr)
  have hs : ContMDiff 𝓘(ℝ,G × V) 𝓘(ℝ,ℝ) 1
      (fun z : O => cylinderFamily U W e A z.val) := by
    have hh := hA.comp ((hq.prodMk ht).of_le (by simp))
    convert hh using 1
    funext z
    exact cylinderFamily_apply U W e A (r z) z.val.2
  exact (contMDiffAt_subtype_iff.mp
    (hs.contMDiffAt (x:=⟨((x:G),v),⟨x.property,mem_univ _⟩⟩))).contDiffAt

omit [CompleteSpace G] in

lemma scalar_mfderiv_open (W : Opens G) {f : G → ℝ} (x : W)
    (hf : DifferentiableAt ℝ f (x:G)) :
    mfderiv 𝓘(ℝ,G) 𝓘(ℝ,ℝ) (fun y : W => f y) x = fderiv ℝ f (x:G) := by
  have hh := mfderiv_comp x hf.mdifferentiableAt
    ((contMDiff_subtype_val (I:=𝓘(ℝ,G)) (U:=W) (n:=∞)).mdifferentiableAt (by simp))
  erw [mfderiv_openVal,comp_id,mfderiv_eq_fderiv] at hh
  exact hh

omit [CompleteSpace R] [CompleteSpace G] [IsManifold 𝓘(ℝ,E) ∞ M] in

lemma cylinderFamily_base (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A)
    (q : M × U) (v : V) :
    fderiv ℝ (fun x => cylinderFamily U W e A (x,v)) (e q:G) =
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun b => A (b,v)) q.1).comp (fst ℝ E R)).comp
        (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E × R) e.symm (e q)) := by
  have hAv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun b => A (b,v)) :=
    hA.comp (contMDiff_id.prodMk contMDiff_const)
  have hK : ContMDiff 𝓘(ℝ,E × R) 𝓘(ℝ,ℝ) ∞ (fun p : M × U => A (p.1,v)) := by
    rw [modelWithCornersSelf_prod]
    exact hAv.comp contMDiff_fst
  have hD : mfderiv 𝓘(ℝ,E × R) 𝓘(ℝ,ℝ) (fun p : M × U => A (p.1,v)) q =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun b => A (b,v)) q.1).comp (fst ℝ E R) := by
    rw [modelWithCornersSelf_prod]
    erw [mfderiv_comp q (hAv.mdifferentiableAt (by simp)) mdifferentiableAt_fst,mfderiv_fst]
    rfl
  have hF : DifferentiableAt ℝ (fun x => cylinderFamily U W e A (x,v)) (e q:G) :=
    by
      have hc : DifferentiableAt ℝ (cylinderFamily U W e A) ((e q:G),v) :=
        (contDiffAt_cylinderFamily U W e hA (e q) v).differentiableAt (by simp)
      have hi : DifferentiableAt ℝ (fun x : G => (x,v)) (e q:G) :=
        differentiableAt_id.prodMk (differentiableAt_const v)
      exact hc.comp (e q:G) hi
  rw [← scalar_mfderiv_open W (e q) hF]
  have heq : (fun x : W => cylinderFamily U W e A ((x:G),v)) =
      (fun x : W => A ((e.symm x).1,v)) := by
    funext x
    exact cylinderFamily_apply U W e A x v
  rw [heq]
  erw [mfderiv_comp (e q) (hK.mdifferentiableAt (by simp))
    (e.symm.contMDiff.mdifferentiableAt (by simp)),e.symm_apply_apply,hD]
  rfl

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Set Filter TopologicalSpace ContinuousLinearMap InnerProductSpace
variable {E R G V M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance cylinderFamiliesGenerateChartedSpace (U : Opens R) : ChartedSpace (E × R) (M × U) :=
  inferInstanceAs (ChartedSpace (ModelProd E R) (M × U))
local instance cylinderFamiliesGenerateManifold (U : Opens R) : IsManifold 𝓘(ℝ,E × R) ∞ (M × U) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,E)) (I':=𝓘(ℝ,R)) M U

def intrinsicGenerate (A : M × V → ℝ) (q : M × V) : Cotangent (E:=E) (M:=M) :=
  ⟨q.1,mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun b => A (b,q.2)) q.1⟩

def cylinderGenerate (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    (A : M × V → ℝ) (q : G × V) : G × G :=
  (q.1,(toDual ℝ G).symm (fderiv ℝ (fun x => cylinderFamily U W e A (x,q.2)) q.1))

lemma cylinderGenerate_at_chart (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A)
    (q : M × V) (a : U) :
    cylinderGenerate U W e A ((e (q.1,a):G),q.2) =
      (cotangentCylinderChart U W e
        (intrinsicGenerate (E:=E) A q,⟨((a:R),0),⟨a.property,mem_univ _⟩⟩) : G × G) := by
  apply Prod.ext
  · rfl
  change (toDual ℝ G).symm (fderiv ℝ (fun x => cylinderFamily U W e A (x,q.2))
      (e (q.1,a):G)) = _
  rw [cylinderFamily_base U W e hA]
  let p : E →L[ℝ] ℝ := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun b => A (b,q.2)) q.1
  let D : G →L[ℝ] E × R := mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E × R) e.symm (e (q.1,a))
  change (toDual ℝ G).symm ((p.comp (fst ℝ E R)).comp D) =
    (toDual ℝ G).symm ((p.comp (fst ℝ E R) + ((toDual ℝ R) (0:R)).comp (snd ℝ E R)).comp D)
  simp only [map_zero,zero_comp,add_zero]

abbrev IntrinsicCritical (A : M × V → ℝ) :=
  {q : M × V // fderiv ℝ (fun v => A (q.1,v)) q.2 = 0}
abbrev CylinderCritical (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞) (A : M × V → ℝ) :=
  {q : G × V // q.1 ∈ W ∧ fderiv ℝ (fun v => cylinderFamily U W e A (q.1,v)) q.2 = 0}

def cylinderCriticalEquiv (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    (A : M × V → ℝ) : IntrinsicCritical A × U ≃ CylinderCritical U W e A where
  toFun q := ⟨((e (q.1.val.1,q.2):G),q.1.val.2), (e _).property,by
    rw [cylinderFamily_vertical]
    exact q.1.property⟩
  invFun q := (⟨((e.symm ⟨q.val.1,q.property.1⟩).1,q.val.2),by
    have hh := cylinderFamily_vertical U W e A (e.symm ⟨q.val.1,q.property.1⟩) q.val.2
    simp only [e.apply_symm_apply] at hh
    exact hh.symm.trans q.property.2⟩,(e.symm ⟨q.val.1,q.property.1⟩).2)
  left_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      change ((e.symm (e (q.1.val.1,q.2))).1,q.1.val.2) = q.1.val
      rw [e.symm_apply_apply]
    · change (e.symm (e (q.1.val.1,q.2))).2 = q.2
      exact congrArg Prod.snd (e.symm_apply_apply (q.1.val.1,q.2))
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (e.apply_symm_apply ⟨q.val.1,q.property.1⟩)
    · rfl

theorem cylinderGenerate_range (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A) :
    range (fun q : CylinderCritical U W e A => cylinderGenerate U W e A q.val) =
      (fun z : Cotangent (E:=E) (M:=M) × openPhase U =>
        (cotangentCylinderChart U W e z : G × G)) ''
        {z | z.1 ∈ range (fun q : IntrinsicCritical A => intrinsicGenerate (E:=E) A q.val) ∧
          (z.2:R × R).2 = 0} := by
  ext z
  constructor
  · rintro ⟨q,rfl⟩
    obtain ⟨⟨r,a⟩,rfl⟩ := (cylinderCriticalEquiv U W e A).surjective q
    refine ⟨(intrinsicGenerate (E:=E) A r.val,⟨((a:R),0),⟨a.property,mem_univ _⟩⟩),⟨⟨r,rfl⟩,rfl⟩,?_⟩
    exact (cylinderGenerate_at_chart U W e hA r.val a).symm
  · rintro ⟨⟨q,a⟩,⟨⟨r,rfl⟩,ha⟩,rfl⟩
    let b : U := ⟨(a:R × R).1,a.property.1⟩
    have hab : a = (⟨((b:R),0),⟨b.property,mem_univ _⟩⟩ : openPhase U) := by
      apply Subtype.ext
      exact Prod.ext rfl ha
    rw [hab]
    exact ⟨cylinderCriticalEquiv U W e A (r,b),cylinderGenerate_at_chart U W e hA r.val b⟩

theorem cylinderGenerate_injective (U : Opens R) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × R) 𝓘(ℝ,G) (M × U) W ∞)
    {A : M × V → ℝ}
    (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,V)) 𝓘(ℝ,ℝ) ∞ A)
    (hi : Function.Injective (fun q : IntrinsicCritical A => intrinsicGenerate (E:=E) A q.val)) :
    Function.Injective (fun q : CylinderCritical U W e A => cylinderGenerate U W e A q.val) := by
  intro q r h
  obtain ⟨⟨q,a⟩,rfl⟩ := (cylinderCriticalEquiv U W e A).surjective q
  obtain ⟨⟨r,b⟩,rfl⟩ := (cylinderCriticalEquiv U W e A).surjective r
  have hq := cylinderGenerate_at_chart U W e hA q.val a
  have hr := cylinderGenerate_at_chart U W e hA r.val b
  have hh := (cotangentCylinderChart U W e).injective (Subtype.ext (hq.symm.trans (h.trans hr)))
  have hqr : q = r := hi (congrArg Prod.fst hh)
  have hab : a = b := by
    apply Subtype.ext
    exact congrArg (fun z : Cotangent (E:=E) (M:=M) × openPhase U => (z.2:R × R).1) hh
  cases hqr
  cases hab
  rfl

end NearbyLagrangian.CotangentGeometry

end

end OAI
