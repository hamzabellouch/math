import Mathlib

namespace OAI

/-! Polar and Euclidean cylinder diffeomorphisms. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.PolarCylinder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

def radialWindow (ν : ℝ) : Opens ℝ := ⟨Ioo (-ν) ν,isOpen_Ioo⟩
def annulus (ν : ℝ) : Opens E :=
  ⟨{w | ‖w‖ ∈ Ioo (1-ν) (1+ν)}, isOpen_Ioo.preimage continuous_norm⟩

lemma radial_pos {ν : ℝ} (hν : ν < 1) (α : radialWindow ν) : 0 < 1+(α:ℝ) := by
  have h := α.property.1
  change -ν < (α:ℝ) at h
  linarith
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma annulus_norm_pos {ν : ℝ} (hν : ν < 1) (w : annulus (E:=E) ν) : 0 < ‖(w:E)‖ := by
  have h := w.property.1
  change 1-ν < ‖(w:E)‖ at h
  linarith
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma annulus_ne_zero {ν : ℝ} (hν : ν < 1) (w : annulus (E:=E) ν) : (w:E) ≠ 0 :=
  norm_pos_iff.mp (annulus_norm_pos hν w)

def polarMap {ν : ℝ} (hν : ν < 1)
    (p : Metric.sphere (0:E) 1 × radialWindow ν) : annulus (E:=E) ν :=
  ⟨(1+(p.2:ℝ)) • (p.1:E), by
    have hn : ‖(p.1:E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.property
    change 1-ν < ‖(1+(p.2:ℝ)) • (p.1:E)‖ ∧ ‖(1+(p.2:ℝ)) • (p.1:E)‖ < 1+ν
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (radial_pos hν p.2),hn,mul_one]
    exact ⟨by have h := p.2.property.1; change -ν < (p.2:ℝ) at h; linarith,
      by have h := p.2.property.2; change (p.2:ℝ) < ν at h; linarith⟩⟩

def polarInv {ν : ℝ} (hν : ν < 1) (w : annulus (E:=E) ν) :
    Metric.sphere (0:E) 1 × radialWindow ν :=
  (⟨‖(w:E)‖⁻¹ • (w:E), by
    rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (annulus_norm_pos hν w)),inv_mul_cancel₀
        (ne_of_gt (annulus_norm_pos hν w))]⟩,
   ⟨‖(w:E)‖-1,by
    have h := w.property
    change 1-ν < ‖(w:E)‖ ∧ ‖(w:E)‖ < 1+ν at h
    change -ν < ‖(w:E)‖-1 ∧ ‖(w:E)‖-1 < ν
    constructor <;> linarith [h.1,h.2]⟩)

omit [FiniteDimensional ℝ E] in
lemma polarInv_polarMap {ν : ℝ} (hν : ν < 1)
    (p : Metric.sphere (0:E) 1 × radialWindow ν) : polarInv hν (polarMap hν p) = p := by
  have hn : ‖(p.1:E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.property
  have hr : ‖(1+(p.2:ℝ)) • (p.1:E)‖ = 1+(p.2:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (radial_pos hν p.2),hn,mul_one]
  apply Prod.ext
  · apply Subtype.ext
    change ‖(1+(p.2:ℝ)) • (p.1:E)‖⁻¹ • ((1+(p.2:ℝ)) • (p.1:E)) = (p.1:E)
    rw [hr,smul_smul,inv_mul_cancel₀ (ne_of_gt (radial_pos hν p.2)),one_smul]
  · apply Subtype.ext
    change ‖(1+(p.2:ℝ)) • (p.1:E)‖-1 = (p.2:ℝ)
    rw [hr]
    ring

omit [FiniteDimensional ℝ E] in
lemma polarMap_polarInv {ν : ℝ} (hν : ν < 1) (w : annulus (E:=E) ν) :
    polarMap hν (polarInv hν w) = w := by
  apply Subtype.ext
  change (1+(‖(w:E)‖-1)) • (‖(w:E)‖⁻¹ • (w:E)) = (w:E)
  rw [show 1+(‖(w:E)‖-1)=‖(w:E)‖ by ring,smul_smul,
    mul_inv_cancel₀ (ne_of_gt (annulus_norm_pos hν w)),one_smul]

omit [FiniteDimensional ℝ E] in
lemma contMDiff_polarMap {ν : ℝ} (hν : ν < 1) :
    ContMDiff (𝓘(ℝ,EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,E) ∞ (polarMap (E:=E) hν) := by
  apply (ContMDiff.subtypeVal_comp_iff (annulus (E:=E) ν) _).mp
  exact (contMDiff_const.add (contMDiff_subtype_val.comp contMDiff_snd)).smul
    (contMDiff_coe_sphere.comp contMDiff_fst)

omit [FiniteDimensional ℝ E] in
lemma contMDiff_polarInv {ν : ℝ} (hν : ν < 1) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ,ℝ)) ∞ (polarInv (E:=E) hν) := by
  have hn : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun w : annulus (E:=E) ν => ‖(w:E)‖) := by
    intro w
    exact (contDiffAt_norm ℝ (annulus_ne_zero hν w)).comp_contMDiffAt
      contMDiff_subtype_val.contMDiffAt
  have hi : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
      (fun w : annulus (E:=E) ν => (polarInv hν w).1) := by
    exact ((hn.inv₀ (fun w => ne_of_gt (annulus_norm_pos hν w))).smul
      contMDiff_subtype_val).codRestrict_sphere (fun w => (polarInv hν w).1.property)
  have hr : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞
      (fun w : annulus (E:=E) ν => (polarInv hν w).2) := by
    apply (ContMDiff.subtypeVal_comp_iff (radialWindow ν) _).mp
    exact hn.sub contMDiff_const
  exact hi.prodMk hr

def polarDiffeomorph {ν : ℝ} (hν : ν < 1) :
    Diffeomorph (𝓘(ℝ,EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,E)
      (Metric.sphere (0:E) 1 × radialWindow ν) (annulus (E:=E) ν) ∞ where
  toFun := polarMap hν
  invFun := polarInv hν
  left_inv := polarInv_polarMap hν
  right_inv := polarMap_polarInv hν
  contMDiff_toFun := contMDiff_polarMap hν
  contMDiff_invFun := contMDiff_polarInv hν

end NearbyLagrangian.PolarCylinder

namespace NearbyLagrangian.PolarCylinder
open scoped Manifold ContDiff Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {n m : ℕ}
  [Fact (Module.finrank ℝ E = n+1)] [Fact (Module.finrank ℝ F = m+1)]

def productPolarDiffeomorph {ν : ℝ} (hν : ν < 1) :
    Diffeomorph
      ((𝓘(ℝ,EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ,EuclideanSpace ℝ (Fin m))).prod
        (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)))
      (𝓘(ℝ,E).prod 𝓘(ℝ,F))
      ((Metric.sphere (0:E) 1 × Metric.sphere (0:F) 1) ×
        (radialWindow ν × radialWindow ν))
      (annulus (E:=E) ν × annulus (E:=F) ν) ∞ where
  toFun p := (polarMap hν (p.1.1,p.2.1),polarMap hν (p.1.2,p.2.2))
  invFun p := (((polarInv hν p.1).1,(polarInv hν p.2).1),
    ((polarInv hν p.1).2,(polarInv hν p.2).2))
  left_inv p := by
    simp only [polarInv_polarMap]
  right_inv p := by
    simp only [Prod.mk.eta,polarMap_polarInv]
  contMDiff_toFun :=
    ((contMDiff_polarMap (E:=E) (n:=n) hν).comp
      (contMDiff_fst.fst.prodMk contMDiff_snd.fst)).prodMk
    ((contMDiff_polarMap (E:=F) (n:=m) hν).comp
      (contMDiff_fst.snd.prodMk contMDiff_snd.snd))
  contMDiff_invFun :=
    (((contMDiff_polarInv (E:=E) (n:=n) hν).comp contMDiff_fst).fst.prodMk
      ((contMDiff_polarInv (E:=F) (n:=m) hν).comp contMDiff_snd).fst).prodMk
    (((contMDiff_polarInv (E:=E) (n:=n) hν).comp contMDiff_fst).snd.prodMk
      ((contMDiff_polarInv (E:=F) (n:=m) hν).comp contMDiff_snd).snd)

end NearbyLagrangian.PolarCylinder

namespace NearbyLagrangian.PolarCylinder
open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def productOpen (U : Opens E) (V : Opens F) : Opens (E × F) :=
  ⟨(U:Set E) ×ˢ (V:Set F),U.isOpen.prod V.isOpen⟩

def productOpenDiffeomorph (U : Opens E) (V : Opens F) :
    Diffeomorph (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,E × F) (U × V) (productOpen U V) ∞ where
  toFun z := ⟨((z.1:E),(z.2:F)),z.1.property,z.2.property⟩
  invFun z := (⟨z.val.1,z.property.1⟩,⟨z.val.2,z.property.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (productOpen U V) _).mp
    exact (contMDiff_subtype_val.comp contMDiff_fst).prodMk_space
      (contMDiff_subtype_val.comp contMDiff_snd)
  contMDiff_invFun := by
    have hv : ContMDiff 𝓘(ℝ,E × F) 𝓘(ℝ,E × F) ∞
        (Subtype.val : productOpen U V → E × F) := contMDiff_subtype_val
    apply ContMDiff.prodMk
    · apply (ContMDiff.subtypeVal_comp_iff U _).mp
      exact contDiff_fst.contMDiff.comp hv
    · apply (ContMDiff.subtypeVal_comp_iff V _).mp
      exact contDiff_snd.contMDiff.comp hv

def linearOpen (e : E ≃L[ℝ] F) (U : Opens E) : Opens F :=
  ⟨e '' (U:Set E),e.toHomeomorph.isOpenMap _ U.isOpen⟩

def linearOpenDiffeomorph (e : E ≃L[ℝ] F) (U : Opens E) :
    Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) U (linearOpen e U) ∞ where
  toFun x := ⟨e (x:E),x,x.property,rfl⟩
  invFun y := ⟨e.symm (y:F), by
    obtain ⟨x,hx,hxy⟩ := y.property
    rw [← hxy,e.symm_apply_apply]
    exact hx⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (linearOpen e U) _).mp
    exact e.contDiff.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact e.symm.contDiff.contMDiff.comp contMDiff_subtype_val

def euclideanCylinderOpen (n m : ℕ) (ν : ℝ) :
    Opens (EuclideanSpace ℝ (Fin ((n+1)+(m+1)))) :=
  linearOpen EuclideanSpace.finAddEquivProd.symm
    (productOpen (annulus (E:=EuclideanSpace ℝ (Fin (n+1))) ν)
      (annulus (E:=EuclideanSpace ℝ (Fin (m+1))) ν))

def euclideanCylinderDiffeomorph (n m : ℕ) {ν : ℝ} (hν : ν < 1) :
    Diffeomorph
      ((𝓘(ℝ,EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ,EuclideanSpace ℝ (Fin m))).prod
        (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin ((n+1)+(m+1))))
      ((Metric.sphere (0:EuclideanSpace ℝ (Fin (n+1))) 1 ×
        Metric.sphere (0:EuclideanSpace ℝ (Fin (m+1))) 1) ×
        (radialWindow ν × radialWindow ν))
      (euclideanCylinderOpen n m ν) ∞ := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) := ⟨by simp⟩
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+1))) = m+1) := ⟨by simp⟩
  exact (productPolarDiffeomorph (E:=EuclideanSpace ℝ (Fin (n+1)))
    (F:=EuclideanSpace ℝ (Fin (m+1))) (n:=n) (m:=m) hν).trans
    ((productOpenDiffeomorph _ _).trans
      (linearOpenDiffeomorph EuclideanSpace.finAddEquivProd.symm _))

end NearbyLagrangian.PolarCylinder

namespace NearbyLagrangian
open scoped Manifold ContDiff
variable {E E' F F' A A' B B' M M' N N' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace B']
  {I : ModelWithCorners ℝ E A} {I' : ModelWithCorners ℝ E' A'}
  {J : ModelWithCorners ℝ F B} {J' : ModelWithCorners ℝ F' B'}
  [TopologicalSpace M] [ChartedSpace A M] [TopologicalSpace M'] [ChartedSpace A' M']
  [TopologicalSpace N] [ChartedSpace B N] [TopologicalSpace N'] [ChartedSpace B' N']

def generalProductDiffeomorph (e : Diffeomorph I I' M M' ∞)
    (f : Diffeomorph J J' N N' ∞) : Diffeomorph (I.prod J) (I'.prod J') (M × N) (M' × N') ∞ where
  toEquiv := e.toEquiv.prodCongr f.toEquiv
  contMDiff_toFun := (e.contMDiff.comp contMDiff_fst).prodMk (f.contMDiff.comp contMDiff_snd)
  contMDiff_invFun := (e.symm.contMDiff.comp contMDiff_fst).prodMk (f.symm.contMDiff.comp contMDiff_snd)

end NearbyLagrangian

namespace NearbyLagrangian.PolarCylinder
open scoped Manifold ContDiff Topology
open Set TopologicalSpace

def radialCoordinates : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv

def radialSquare (ν : ℝ) : Opens (EuclideanSpace ℝ (Fin 2)) :=
  linearOpen radialCoordinates.symm (productOpen (radialWindow ν) (radialWindow ν))

def radialSquareDiffeomorph (ν : ℝ) :
    Diffeomorph 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ))
      (radialSquare ν) (radialWindow ν × radialWindow ν) ∞ :=
  (linearOpenDiffeomorph radialCoordinates.symm _).symm.trans
    (productOpenDiffeomorph (radialWindow ν) (radialWindow ν)).symm

def euclideanCylinderSquareDiffeomorph (n m : ℕ) {ν : ℝ} (hν : ν < 1) :
    Diffeomorph
      ((𝓘(ℝ,EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ,EuclideanSpace ℝ (Fin m))).prod
        𝓘(ℝ,EuclideanSpace ℝ (Fin 2)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin ((n+1)+(m+1))))
      ((Metric.sphere (0:EuclideanSpace ℝ (Fin (n+1))) 1 ×
        Metric.sphere (0:EuclideanSpace ℝ (Fin (m+1))) 1) × radialSquare ν)
      (euclideanCylinderOpen n m ν) ∞ :=
  (generalProductDiffeomorph (Diffeomorph.refl _ _ ∞) (radialSquareDiffeomorph ν)).trans
    (euclideanCylinderDiffeomorph n m hν)

local instance (n m : ℕ) (ν : ℝ) :
    ChartedSpace ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2))
      ((Metric.sphere (0:EuclideanSpace ℝ (Fin (n+1))) 1 ×
        Metric.sphere (0:EuclideanSpace ℝ (Fin (m+1))) 1) × radialSquare ν) :=
  inferInstanceAs (ChartedSpace (ModelProd (ModelProd (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin m))) (EuclideanSpace ℝ (Fin 2))) _)

def flatEuclideanCylinderSquareDiffeomorph (n m : ℕ) {ν : ℝ} (hν : ν < 1) :
    Diffeomorph
      𝓘(ℝ,(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2))
      𝓘(ℝ,EuclideanSpace ℝ (Fin ((n+1)+(m+1))))
      ((Metric.sphere (0:EuclideanSpace ℝ (Fin (n+1))) 1 ×
        Metric.sphere (0:EuclideanSpace ℝ (Fin (m+1))) 1) × radialSquare ν)
      (euclideanCylinderOpen n m ν) ∞ := by
  rw [modelWithCornersSelf_prod,modelWithCornersSelf_prod]
  exact euclideanCylinderSquareDiffeomorph n m hν

lemma mem_radialSquare_iff (ν : ℝ) (a : EuclideanSpace ℝ (Fin 2)) :
    a ∈ radialSquare ν ↔ (radialCoordinates a).1 ∈ Ioo (-ν) ν ∧
      (radialCoordinates a).2 ∈ Ioo (-ν) ν := by
  change (∃ x, x ∈ (productOpen (radialWindow ν) (radialWindow ν) : Set (ℝ × ℝ)) ∧
    radialCoordinates.symm x = a) ↔ _
  constructor
  · rintro ⟨x,hx,rfl⟩
    change x.1 ∈ Ioo (-ν) ν ∧ x.2 ∈ Ioo (-ν) ν at hx
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx
  · intro ha
    exact ⟨radialCoordinates a,ha,radialCoordinates.symm_apply_apply a⟩

end NearbyLagrangian.PolarCylinder

end

end OAI
