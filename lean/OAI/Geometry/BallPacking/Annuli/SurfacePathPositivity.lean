import Mathlib
import OAI.Geometry.BallPacking.Layers.ConstructedSurfaceLayers

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : E →L[ℝ] E →L[ℝ] ℝ}

theorem surfaceFirstPrimitive_coupling (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S) (H : E → ℝ) (a b w : Plane → ℝ) (ℓ : ℝ) :
    (fun x => surfaceFirstPrimitive Φ S H a b w (ℓ,x)) =
      horizontalOneForm
        (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ (fun s => ℓ*S s)) +
          baseCoefficient a ∘ hamiltonianBaseShear Φ (fun s => ℓ*S s) (contDiff_const.mul hS))
        (weightedSecondCoefficient b w (surfaceFirstLayer S H (Φ.map ℓ).symm) ∘
          hamiltonianBaseShear Φ (fun s => ℓ*S s) (contDiff_const.mul hS)) := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  have hd := ((hS.differentiable (by simp) p.1.1).hasDerivAt.const_mul ℓ).deriv
  simp only [surfaceFirstPrimitive,horizontalOneForm_apply,Pi.add_apply,Function.comp_apply,
    firstBaseCoefficient,baseShearPrimitiveCoefficient,baseCoefficient,weightedSecondCoefficient,
    surfaceFirstLayer,hamiltonianBaseShear,hd]
  dsimp
  ring

theorem surfaceFirstPath_isInvertible [FiniteDimensional ℝ E]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {S : ℝ → ℝ} {H : E → ℝ} {a b w : Plane → ℝ}
    (hS : ContDiff ℝ ∞ S) (hH : ContDiff ℝ ∞ H)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w)
    (ℓ : ℝ) (p : Plane × E)
    (hbase : 0<fderiv ℝ b p.1 (1,0)-fderiv ℝ a p.1 (0,1))
    (hwzero : fderiv ℝ w p.1 (1,0)=0) (hwpos : 0 ≤ w p.1)
    (hSpos : 0 ≤ deriv S p.1.1)
    (hHpos : 0 ≤ H ((Φ.map ℓ).symm (Φ.map (ℓ*S p.1.1) p.2))) :
    (Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E) +
      euclideanExteriorOneForm (fun x => surfaceFirstPrimitive Φ S H a b w (ℓ,x)) p).IsInvertible := by
  rw [surfaceFirstPrimitive_coupling Φ hS]
  apply baseShear_weighted_isInvertible hΩ hskew Φ (contDiff_const.mul hS) ha hb hw
    (surfaceFirstLayer_smooth hS hH (Φ.map_inverse_smooth ℓ)) p hbase hwzero hwpos
  rw [surfaceFirstLayer_firstDerivative hS hH (Φ.map_inverse_smooth ℓ)]
  exact mul_nonneg hSpos hHpos

variable {ι : Type*} [Fintype ι]
@[fun_prop] theorem surfaceInterpolatedLayer_smooth {S : ℝ → ℝ} {K H : E → ℝ}
    {h : ι → E → ℝ} {ψ : E → E} {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hψ : ContDiff ℝ ∞ ψ)
    (hρ : ∀ i, ContDiff ℝ ∞ (ρ i)) (hρ₀ : ContDiff ℝ ∞ ρ₀) (τ : ℝ) :
    ContDiff ℝ ∞ (surfaceInterpolatedLayer S K H h ψ ρ ρ₀ τ) :=
  (contDiff_const.mul (surfaceFirstLayer_smooth hS hH hψ)).add
    (contDiff_const.mul (surfaceFinalLayer_smooth (hK.sub hH) (surfaceRemainder_smooth hK hH hh hψ) hh hρ hρ₀))

theorem surfaceInterpolatedLayer_firstDerivative {S : ℝ → ℝ} {K H : E → ℝ}
    {h : ι → E → ℝ} {ψ : E → E} {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hψ : ContDiff ℝ ∞ ψ)
    (hρ : ∀ i, ContDiff ℝ ∞ (ρ i)) (hρ₀ : ContDiff ℝ ∞ ρ₀) (τ : ℝ) (p : ℝ × E) :
    fderiv ℝ (surfaceInterpolatedLayer S K H h ψ ρ ρ₀ τ) p (1,0) =
      (1-τ)*(deriv S p.1*H (ψ p.2)) +
        τ*((∑ i, deriv (ρ i) p.1*h i p.2)+deriv ρ₀ p.1*surfaceRemainder K H h ψ p.2) := by
  have hF := (surfaceFirstLayer_smooth hS hH hψ).differentiable (by simp) p
  have hG := (surfaceFinalLayer_smooth (hK.sub hH) (surfaceRemainder_smooth hK hH hh hψ) hh hρ hρ₀).differentiable (by simp) p
  have hd := (hF.hasFDerivAt.const_mul (1-τ)).add (hG.hasFDerivAt.const_mul τ)
  change HasFDerivAt (surfaceInterpolatedLayer S K H h ψ ρ ρ₀ τ) _ p at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,
    surfaceFirstLayer_firstDerivative hS hH hψ,
    surfaceFinalLayer_firstDerivative (hK.sub hH) (surfaceRemainder_smooth hK hH hh hψ) hh hρ hρ₀]

theorem surfaceInterpolatedLayer_firstDerivative_nonneg {S : ℝ → ℝ} {K H : E → ℝ}
    {h : ι → E → ℝ} {ψ : E → E} {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hψ : ContDiff ℝ ∞ ψ)
    (hρ : ∀ i, ContDiff ℝ ∞ (ρ i)) (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) (p : ℝ × E)
    (hSpos : 0 ≤ deriv S p.1) (hHpos : 0 ≤ H (ψ p.2))
    (hclock : ∀ i, 0 ≤ deriv (ρ i) p.1) (hclock₀ : 0 ≤ deriv ρ₀ p.1)
    (hcap : ∀ i, 0 ≤ h i p.2) (hres : 0 ≤ surfaceRemainder K H h ψ p.2) :
    0 ≤ fderiv ℝ (surfaceInterpolatedLayer S K H h ψ ρ ρ₀ τ) p (1,0) := by
  rw [surfaceInterpolatedLayer_firstDerivative hS hK hH hh hψ hρ hρ₀]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hτ.2) (mul_nonneg hSpos hHpos))
    (mul_nonneg hτ.1 (add_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hclock i) (hcap i)))
      (mul_nonneg hclock₀ hres)))


def surfaceSecondPrimitive (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (K H : E → ℝ) (h : ι → E → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (a b w : Plane → ℝ) (p : ℝ × (Plane × E)) : (Plane × E) →L[ℝ] ℝ :=
  horizontalOneForm
    (fun x => a x.1 + deriv S x.1.1 * Φ.hamiltonian (S x.1.1,Φ.map (S x.1.1) x.2))
    (fun x => b x.1 + w x.1 * surfaceInterpolatedLayer S K H h (Φ.map 1).symm ρ ρ₀ p.1
      (x.1.1,Φ.map (S x.1.1) x.2)) p.2

theorem surfaceSecondPrimitive_coupling (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S) (K H : E → ℝ) (h : ι → E → ℝ)
    (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (a b w : Plane → ℝ) (τ : ℝ) :
    (fun x => surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (τ,x)) =
      horizontalOneForm
        (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ S) +
          baseCoefficient a ∘ hamiltonianBaseShear Φ S hS)
        (weightedSecondCoefficient b w (surfaceInterpolatedLayer S K H h (Φ.map 1).symm ρ ρ₀ τ) ∘
          hamiltonianBaseShear Φ S hS) := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  simp only [surfaceSecondPrimitive,horizontalOneForm_apply,Pi.add_apply,Function.comp_apply,
    firstBaseCoefficient,baseShearPrimitiveCoefficient,baseCoefficient,weightedSecondCoefficient,
    hamiltonianBaseShear]
  dsimp
  ring

theorem surfaceSecondPrimitive_zero (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (K H : E → ℝ) (h : ι → E → ℝ)
    (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (a b w : Plane → ℝ) (p : Plane × E) :
    surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (0,p)=surfaceFirstPrimitive Φ S H a b w (1,p) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [surfaceSecondPrimitive,surfaceFirstPrimitive,surfaceInterpolatedLayer,surfaceFirstLayer,
    horizontalOneForm_apply,one_mul,zero_mul,sub_zero]
  ring

theorem surfaceSecondPrimitive_collars (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (K H : E → ℝ) (h : ι → E → ℝ)
    (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (a b w : Plane → ℝ) (τ : ℝ) (p : Plane × E)
    (hd : deriv S p.1.1=0) :
    (S p.1.1=0 → (∀ i, ρ i p.1.1=0) → ρ₀ p.1.1=0 →
      surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (τ,p)=
        horizontalOneForm (baseCoefficient a) (fun x => b x.1+τ*w x.1*(K x.2-H x.2)) p) ∧
    (S p.1.1=1 → (∀ i, ρ i p.1.1=1) → ρ₀ p.1.1=1 →
      surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (τ,p)=
        horizontalOneForm (baseCoefficient a) (fun x => b x.1+w x.1*H x.2+τ*w x.1*(K x.2-H x.2)) p) := by
  have he := surfaceInterpolatedLayer_endpoints Φ S K H h ρ ρ₀ τ p.1.1 p.2
  constructor
  · intro hs hc hc₀
    apply ContinuousLinearMap.ext
    intro v
    simp only [surfaceSecondPrimitive,horizontalOneForm_apply,baseCoefficient,hd,zero_mul,add_zero,
      he.1 hs hc hc₀]
    ring
  · intro hs hc hc₀
    apply ContinuousLinearMap.ext
    intro v
    simp only [surfaceSecondPrimitive,horizontalOneForm_apply,baseCoefficient,hd,zero_mul,add_zero,
      he.2 hs hc hc₀]
    ring

theorem surfaceSecondPath_isInvertible [FiniteDimensional ℝ E]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {S : ℝ → ℝ} {K H : E → ℝ} {h : ι → E → ℝ}
    {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ} {a b w : Plane → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w)
    (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) (p : Plane × E)
    (hbase : 0<fderiv ℝ b p.1 (1,0)-fderiv ℝ a p.1 (0,1))
    (hwzero : fderiv ℝ w p.1 (1,0)=0) (hwpos : 0 ≤ w p.1)
    (hSpos : 0 ≤ deriv S p.1.1)
    (hHpos : 0 ≤ H ((Φ.map 1).symm (Φ.map (S p.1.1) p.2)))
    (hclock : ∀ i, 0 ≤ deriv (ρ i) p.1.1) (hclock₀ : 0 ≤ deriv ρ₀ p.1.1)
    (hcap : ∀ i, 0 ≤ h i (Φ.map (S p.1.1) p.2))
    (hres : 0 ≤ surfaceRemainder K H h (Φ.map 1).symm (Φ.map (S p.1.1) p.2)) :
    (Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E) +
      euclideanExteriorOneForm (fun x => surfaceSecondPrimitive Φ S K H h ρ ρ₀ a b w (τ,x)) p).IsInvertible := by
  rw [surfaceSecondPrimitive_coupling Φ hS]
  apply baseShear_weighted_isInvertible hΩ hskew Φ hS ha hb hw
    (surfaceInterpolatedLayer_smooth hS hK hH hh (Φ.map_inverse_smooth 1) hρ hρ₀ τ) p hbase hwzero hwpos
  exact surfaceInterpolatedLayer_firstDerivative_nonneg hS hK hH hh (Φ.map_inverse_smooth 1)
    hρ hρ₀ τ hτ _ hSpos hHpos hclock hclock₀ hcap hres

end

def complexUnitDirection (z : ℂ) : Circle := by
  classical
  exact if hz : z=0 then 1 else ⟨((‖z‖⁻¹:ℝ):ℂ)*z,by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩

theorem complexUnitDirection_coe {z : ℂ} (hz : z≠0) :
    (complexUnitDirection z : ℂ)=((‖z‖⁻¹:ℝ):ℂ)*z := by
  simp only [complexUnitDirection]
  erw [dite_eq_right hz]

theorem complexUnitDirection_smoothAt {z : ℂ} (hz : z≠0) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,CircleModel) ∞ complexUnitDirection z := by
  let U : TopologicalSpace.Opens ℂ := ⟨{z : ℂ | z≠0},isOpen_compl_singleton⟩
  let f : U → ℂ := fun w => ((‖w.val‖⁻¹:ℝ):ℂ)*w.val
  have hf : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f := by
    intro w
    apply (contMDiffAt_subtype_iff (U := U)
      (f := fun w : ℂ => ((‖w‖⁻¹:ℝ):ℂ)*w)).mpr
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp w.val
      ((contDiffAt_norm ℝ w.property).inv (norm_ne_zero_iff.mpr w.property))).mul
        contDiffAt_id).contMDiffAt
  have hm : ∀ w : U,f w∈Metric.sphere (0:ℂ) 1 := by
    intro w
    rw [show f w=(complexUnitDirection w.val : ℂ) from (complexUnitDirection_coe w.property).symm]
    exact (complexUnitDirection w.val).property
  let := finrank_real_complex_fact'
  have hd : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,CircleModel) ∞ (fun w : U => complexUnitDirection w.val) := by
    have hh := hf.codRestrict_sphere (n := 1) hm
    apply hh.congr
    intro w
    apply Subtype.ext
    exact complexUnitDirection_coe w.property
  exact contMDiffAt_subtype_iff.mp (hd ⟨z,hz⟩)

def cylinderComplexMap (q : HandleCylinder) : ℂ := (Real.exp q.1 : ℂ)*(q.2 : ℂ)

def cylinderComplexInverse (z : ℂ) : HandleCylinder := (Real.log ‖z‖,complexUnitDirection z)

theorem cylinderComplexMap_smooth :
    ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℂ) ∞ cylinderComplexMap := by
  rw [show 𝓘(ℝ,CylinderModel)=(𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod]
  have hf := ((Complex.ofRealCLM.contDiff.contMDiff.comp Real.contDiff_exp.contMDiff).comp
    (contMDiff_fst : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞ (@Prod.fst ℝ Circle)))
  have hg := circle_coe_smooth.comp
    (contMDiff_snd : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,CircleModel) ∞ (@Prod.snd ℝ Circle))
  have hm : ContMDiff ((𝓘(ℝ,ℂ)).prod 𝓘(ℝ,ℂ)) 𝓘(ℝ,ℂ) ∞ (fun z : ℂ × ℂ => z.1*z.2) := by
    rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod]
    exact (show ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1*z.2) from contDiff_fst.mul contDiff_snd).contMDiff
  exact hm.comp (hf.prodMk hg)

theorem cylinderComplexInverse_smoothAt {z : ℂ} (hz : z≠0) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,CylinderModel) ∞ cylinderComplexInverse z := by
  rw [show 𝓘(ℝ,CylinderModel)=(𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod]
  exact (((contDiffAt_norm ℝ hz).log (norm_ne_zero_iff.mpr hz)).contMDiffAt).prodMk
    (complexUnitDirection_smoothAt hz)

@[simp] theorem cylinderComplexMap_norm (q : HandleCylinder) :
    ‖cylinderComplexMap q‖=Real.exp q.1 := by
  rw [cylinderComplexMap,norm_mul,Circle.norm_coe,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

theorem cylinderComplexMap_ne_zero (q : HandleCylinder) : cylinderComplexMap q≠0 := by
  rw [← norm_ne_zero_iff,cylinderComplexMap_norm]
  exact (Real.exp_pos _).ne'

theorem cylinderComplex_left_inv (q : HandleCylinder) :
    cylinderComplexInverse (cylinderComplexMap q)=q := by
  apply Prod.ext
  · simp [cylinderComplexInverse]
  · apply Subtype.ext
    rw [show (cylinderComplexInverse (cylinderComplexMap q)).2=complexUnitDirection (cylinderComplexMap q) from rfl,
      complexUnitDirection_coe (cylinderComplexMap_ne_zero q),cylinderComplexMap_norm]
    simp only [cylinderComplexMap,← mul_assoc,← Complex.ofReal_mul,
      inv_mul_cancel₀ (Real.exp_pos q.1).ne',Complex.ofReal_one,one_mul]

theorem cylinderComplex_right_inv {z : ℂ} (hz : z≠0) :
    cylinderComplexMap (cylinderComplexInverse z)=z := by
  simp only [cylinderComplexMap,cylinderComplexInverse,
    Real.exp_log (norm_pos_iff.mpr hz),complexUnitDirection_coe hz,← mul_assoc,
    ← Complex.ofReal_mul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),Complex.ofReal_one,one_mul]

def cylinderComplexDiffeomorph : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℂ)
    HandleCylinder ℂ ∞ where
  toFun := cylinderComplexMap
  invFun := cylinderComplexInverse
  source := univ
  target := {z | z≠0}
  map_source' q _ := cylinderComplexMap_ne_zero q
  map_target' _ _ := mem_univ _
  left_inv' q _ := cylinderComplex_left_inv q
  right_inv' _ hz := cylinderComplex_right_inv hz
  open_source := isOpen_univ
  open_target := isOpen_compl_singleton
  contMDiffOn_toFun := cylinderComplexMap_smooth.contMDiffOn
  contMDiffOn_invFun := fun _ hz => (cylinderComplexInverse_smoothAt hz).contMDiffWithinAt

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter

variable (m : ℕ)

def realAnnulusChart : OpenPartialHomeomorph RealModel (Surface m) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph.trans (annulusChart m).symm

@[simp] theorem realAnnulusChart_source :
    (realAnnulusChart m).source=Complex.equivRealProdCLM.symm ⁻¹' annulusDomain m := by
  simp [realAnnulusChart]

@[simp] theorem realAnnulusChart_target : (realAnnulusChart m).target=annulusBranch m := by
  simp [realAnnulusChart]

@[simp] theorem realAnnulusChart_apply (x : RealModel) :
    realAnnulusChart m x=annulusInverse m (Complex.equivRealProdCLM.symm x) := rfl

@[simp] theorem realAnnulusChart_symm_apply (x : Surface m) :
    (realAnnulusChart m).symm x=Complex.equivRealProdCLM (annulusCoordinate m x.val) := rfl

theorem realAnnulusChart_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realAnnulusChart m) (realAnnulusChart m).source := by
  intro x hx
  rw [realAnnulusChart_source] at hx
  apply real_contMDiffWithinAt_of_ambient
  have hc := ((annulusPoint_contDiffAt m hx).restrict_scalars ℝ).comp x
    Complex.equivRealProdCLM.symm.contDiff.contDiffAt
  apply hc.contDiffWithinAt.congr
  · intro y hy
    have hyD : Complex.equivRealProdCLM.symm y∈annulusDomain m := by
      simpa only [realAnnulusChart_source,mem_preimage] using hy
    rw [realAnnulusChart_apply,annulusInverse_val m hyD.1]
    rfl
  · rw [realAnnulusChart_apply,annulusInverse_val m hx.1]
    rfl

theorem realAnnulusChart_symm_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realAnnulusChart m).symm := by
  have hc := (Complex.equivRealProdCLM.contDiff.contMDiff).comp
    (((annulusCoordinate m).restrictScalars ℝ).contDiff.contMDiff.comp
      (real_inclusion_contMDiff (parameters m)))
  exact hc

def annulusDiffeomorph : PartialDiffeomorph 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel)
    RealModel (Surface m) ∞ where
  __ := realAnnulusChart m
  contMDiffOn_toFun := realAnnulusChart_smooth m
  contMDiffOn_invFun := (realAnnulusChart_symm_smooth m).contMDiffOn

@[simp] theorem annulusDiffeomorph_source :
    (annulusDiffeomorph m).source=Complex.equivRealProdCLM.symm ⁻¹' annulusDomain m :=
  realAnnulusChart_source m

@[simp] theorem annulusDiffeomorph_target :
    (annulusDiffeomorph m).target=annulusBranch m := realAnnulusChart_target m

theorem unitCircle_subset_diffeomorph {x : RealModel}
    (hx : ‖Complex.equivRealProdCLM.symm x‖=1) : x∈(annulusDiffeomorph m).source := by
  rw [annulusDiffeomorph_source]
  exact unitCircle_subset_domain m hx

def transverseAnnulusPoint (z : ℂ) : Affine (m+2) :=
  (plus z,fun j => if j=0 then minus z
    else Complex.I*Complex.sqrt (parameters m j-plus z^2))

@[simp] theorem transverseAnnulusPoint_zero (z : ℂ) :
    (transverseAnnulusPoint m z).2 0=minus z := by simp [transverseAnnulusPoint]

theorem transverseAnnulusPoint_mem {z : ℂ} (hz : z≠0) :
    transverseAnnulusPoint m z∈locus (parameters m) := by
  rw [mem_locus]
  intro j
  by_cases hj : j=0
  · subst j
    simp only [transverseAnnulusPoint,ite_true,parameters_zero]
    linear_combination -(plus_sq_sub_minus_sq hz)
  · simp only [transverseAnnulusPoint,ite_eq_right hj,mul_pow,Complex.I_sq,sqrt_sq_complex]
    ring

def transverseAnnulusDomain : Set ℂ := {z | z≠0 ∧
  ∀ j : Fin (m+2),j≠0 → 0<(parameters m j-plus z^2).re}

theorem transverseAnnulusDomain_isOpen : IsOpen (transverseAnnulusDomain m) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hc := ((plus_contDiffAt hz.1).pow 2).continuousAt
  have h0 : ∀ᶠ w in 𝓝 z,w≠0 := isOpen_compl_singleton.mem_nhds hz.1
  have hj : ∀ j : Fin (m+2),∀ᶠ w in 𝓝 z,j≠0 → 0<(parameters m j-plus w^2).re := by
    intro j
    by_cases h : j=0
    · exact Filter.Eventually.of_forall (fun _ hn => (hn h).elim)
    · exact ((Complex.continuous_re.continuousAt.comp (continuousAt_const.sub hc)).eventually
        (Ioi_mem_nhds (hz.2 j h))).mono (fun _ hw _ => hw)
  filter_upwards [h0,Filter.eventually_all.mpr hj] with w hw0 hwj
  exact ⟨hw0,hwj⟩

theorem unitCircle_subset_transverseDomain {z : ℂ} (hz : ‖z‖=1) :
    z∈transverseAnnulusDomain m := by
  have hz0 : z≠0 := by intro h; simp [h] at hz
  have hp : plus z=(z.re : ℂ) := by
    rw [plus,Complex.inv_eq_conj hz,Complex.add_conj]
    push_cast
    ring
  have hn : z.re^2≤1 := by
    have he := Complex.normSq_eq_norm_sq z
    rw [hz,one_pow] at he
    simp only [Complex.normSq_apply] at he
    nlinarith [sq_nonneg z.im]
  refine ⟨hz0,?_⟩
  intro j hj
  have hjp : 0<(j.val : ℝ) := by exact_mod_cast Fin.pos_iff_ne_zero.mpr hj
  simp only [parameters,hp,← Complex.ofReal_pow,Complex.sub_re,
    Complex.add_re,Complex.natCast_re,Complex.one_re,Complex.ofReal_re]
  linarith

theorem transverseAnnulusPoint_contDiffAt {z : ℂ} (hz : z∈transverseAnnulusDomain m) :
    ContDiffAt ℂ ∞ (transverseAnnulusPoint m) z := by
  apply ContDiffAt.prodMk (plus_contDiffAt hz.1)
  apply contDiffAt_pi.mpr
  intro j
  by_cases hj : j=0
  · subst j
    simpa only [ite_true] using minus_contDiffAt hz.1
  · have hb : ContDiffAt ℂ ∞ (fun w : ℂ => parameters m j-plus w^2) z :=
      contDiffAt_const.sub ((plus_contDiffAt hz.1).pow 2)
    have hr := (sqrt_contDiffAt (hz.2 j hj)).comp z hb
    simpa only [transverseAnnulusPoint,ite_eq_right hj] using
      (contDiffAt_const.mul hr : ContDiffAt ℂ ∞ (fun w => Complex.I*Complex.sqrt (parameters m j-plus w^2)) z)

def transverseCoordinate : Affine (m+2) →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ (Fin (m+2) → ℂ))+
  ((ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ ℂ (Fin (m+2) → ℂ)))

@[simp] theorem transverseCoordinate_apply (x : Affine (m+2)) :
    transverseCoordinate m x=x.1+x.2 0 := rfl

@[simp] theorem transverseCoordinate_point (z : ℂ) :
    transverseCoordinate m (transverseAnnulusPoint m z)=z := by
  simp [transverseCoordinate_apply,transverseAnnulusPoint]

theorem transverseCoordinate_mul {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    transverseCoordinate m x*(x.1-x.2 0)=1 := by
  have h0 := mem_locus.mp hx 0
  simp only [parameters_zero] at h0
  change (x.1+x.2 0)*(x.1-x.2 0)=1
  linear_combination -h0

theorem transverseCoordinate_ne_zero {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    transverseCoordinate m x≠0 := by
  intro h
  have he := transverseCoordinate_mul m hx
  rw [h,zero_mul] at he
  exact zero_ne_one he

theorem inverse_transverseCoordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    (transverseCoordinate m x)⁻¹=x.1-x.2 0 := by
  apply mul_left_cancel₀ (transverseCoordinate_ne_zero m hx)
  rw [mul_inv_cancel₀ (transverseCoordinate_ne_zero m hx),transverseCoordinate_mul m hx]

theorem plus_transverseCoordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    plus (transverseCoordinate m x)=x.1 := by
  rw [plus,inverse_transverseCoordinate m hx,transverseCoordinate_apply]
  ring

theorem minus_transverseCoordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    minus (transverseCoordinate m x)=x.2 0 := by
  rw [minus,inverse_transverseCoordinate m hx,transverseCoordinate_apply]
  ring

def transverseBranch : Set (Surface m) := {x | transverseCoordinate m x.val∈transverseAnnulusDomain m ∧
  ∀ j : Fin (m+2),j≠0 → 0<(x.val.2 j).im}

theorem transverseAnnulusPoint_positive {z : ℂ} (hz : z∈transverseAnnulusDomain m) :
    ∀ j : Fin (m+2),j≠0 → 0<((transverseAnnulusPoint m z).2 j).im := by
  intro j hj
  simpa only [transverseAnnulusPoint,ite_eq_right hj,Complex.mul_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add] using sqrt_re_pos (hz.2 j hj)

theorem transverseAnnulusPoint_coordinate {x : Surface m} (hx : x∈transverseBranch m) :
    transverseAnnulusPoint m (transverseCoordinate m x.val)=x.val := by
  apply Prod.ext (plus_transverseCoordinate m x.property)
  funext j
  by_cases hj : j=0
  · subst j
    exact (transverseAnnulusPoint_zero m _).trans (minus_transverseCoordinate m x.property)
  · have hp : 0<(-Complex.I*x.val.2 j).re := by
      simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,
        Complex.I_im,neg_zero,zero_mul,neg_mul,one_mul,zero_sub,neg_neg] using hx.2 j hj
    have he : parameters m j-plus (transverseCoordinate m x.val)^2=(-Complex.I*x.val.2 j)^2 := by
      rw [plus_transverseCoordinate m x.property,mul_pow,neg_pow,Complex.I_sq]
      have hjx := mem_locus.mp x.property j
      linear_combination hjx
    simp only [transverseAnnulusPoint,ite_eq_right hj,he,sqrt_of_sq_pos hp]
    rw [← mul_assoc]
    simp

def transverseAnnulusInverse (z : ℂ) : Surface m := by
  classical
  exact if h : z≠0 then ⟨transverseAnnulusPoint m z,transverseAnnulusPoint_mem m h⟩ else annulusBasepoint m

@[simp] theorem transverseAnnulusInverse_val {z : ℂ} (hz : z≠0) :
    (transverseAnnulusInverse m z).val=transverseAnnulusPoint m z := by
  simp only [transverseAnnulusInverse,dite_eq_left hz]

theorem transverseBranch_isOpen : IsOpen (transverseBranch m) := by
  have hc : Continuous (fun x : Surface m => transverseCoordinate m x.val) :=
    (transverseCoordinate m).continuous.comp continuous_subtype_val
  have hw : ∀ j : Fin (m+2),Continuous (fun x : Surface m => (x.val.2 j).im) :=
    fun j => Complex.continuous_im.comp
      ((continuous_apply j).comp (continuous_snd.comp continuous_subtype_val))
  change IsOpen ((fun x : Surface m => transverseCoordinate m x.val) ⁻¹' transverseAnnulusDomain m ∩
    {x : Surface m | ∀ j,j≠0 → 0<(x.val.2 j).im})
  refine ((transverseAnnulusDomain_isOpen m).preimage hc).inter ?_
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (hw j)

def transverseAnnulusChart : OpenPartialHomeomorph (Surface m) ℂ where
  toFun x := transverseCoordinate m x.val
  invFun := transverseAnnulusInverse m
  source := transverseBranch m
  target := transverseAnnulusDomain m
  map_source' _ hx := hx.1
  map_target' z hz := by
    refine ⟨?_,?_⟩
    · rw [transverseAnnulusInverse_val m hz.1,transverseCoordinate_point]
      exact hz
    · rw [transverseAnnulusInverse_val m hz.1]
      exact transverseAnnulusPoint_positive m hz
  left_inv' x hx := by
    apply Subtype.ext
    rw [transverseAnnulusInverse_val m hx.1.1]
    exact transverseAnnulusPoint_coordinate m hx
  right_inv' z hz := by
    rw [transverseAnnulusInverse_val m hz.1,transverseCoordinate_point]
  open_source := transverseBranch_isOpen m
  open_target := transverseAnnulusDomain_isOpen m
  continuousOn_toFun := ((transverseCoordinate m).continuous.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_induced_rng.mpr
    have hc : ContinuousOn (transverseAnnulusPoint m) (transverseAnnulusDomain m) :=
      fun z hz => (transverseAnnulusPoint_contDiffAt m hz).continuousAt.continuousWithinAt
    rw [continuousOn_iff_continuous_domRestrict] at hc
    exact hc.congr fun z => (transverseAnnulusInverse_val m z.property.1).symm

def realTransverseChart : OpenPartialHomeomorph RealModel (Surface m) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph.trans (transverseAnnulusChart m).symm

@[simp] theorem realTransverseChart_source :
    (realTransverseChart m).source=Complex.equivRealProdCLM.symm ⁻¹' transverseAnnulusDomain m := by
  simp [realTransverseChart,transverseAnnulusChart]

@[simp] theorem realTransverseChart_target : (realTransverseChart m).target=transverseBranch m := by
  simp [realTransverseChart,transverseAnnulusChart]

@[simp] theorem realTransverseChart_apply (x : RealModel) :
    realTransverseChart m x=transverseAnnulusInverse m (Complex.equivRealProdCLM.symm x) := rfl

@[simp] theorem realTransverseChart_symm_apply (x : Surface m) :
    (realTransverseChart m).symm x=Complex.equivRealProdCLM (transverseCoordinate m x.val) := rfl

theorem realTransverseChart_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realTransverseChart m) (realTransverseChart m).source := by
  intro x hx
  rw [realTransverseChart_source] at hx
  apply real_contMDiffWithinAt_of_ambient
  have hc := ((transverseAnnulusPoint_contDiffAt m hx).restrict_scalars ℝ).comp x
    Complex.equivRealProdCLM.symm.contDiff.contDiffAt
  apply hc.contDiffWithinAt.congr
  · intro y hy
    have hyD : Complex.equivRealProdCLM.symm y∈transverseAnnulusDomain m := by
      simpa only [realTransverseChart_source,mem_preimage] using hy
    rw [realTransverseChart_apply,transverseAnnulusInverse_val m hyD.1]
    rfl
  · rw [realTransverseChart_apply,transverseAnnulusInverse_val m hx.1]
    rfl

theorem realTransverseChart_symm_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realTransverseChart m).symm := by
  exact (Complex.equivRealProdCLM.contDiff.contMDiff).comp
    (((transverseCoordinate m).restrictScalars ℝ).contDiff.contMDiff.comp
      (real_inclusion_contMDiff (parameters m)))

def transverseDiffeomorph : PartialDiffeomorph 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel)
    RealModel (Surface m) ∞ where
  __ := realTransverseChart m
  contMDiffOn_toFun := realTransverseChart_smooth m
  contMDiffOn_invFun := (realTransverseChart_symm_smooth m).contMDiffOn

@[simp] theorem transverseDiffeomorph_source :
    (transverseDiffeomorph m).source=Complex.equivRealProdCLM.symm ⁻¹' transverseAnnulusDomain m :=
  realTransverseChart_source m

@[simp] theorem transverseDiffeomorph_target :
    (transverseDiffeomorph m).target=transverseBranch m := realTransverseChart_target m

theorem unitCircle_subset_transverseDiffeomorph {x : RealModel}
    (hx : ‖Complex.equivRealProdCLM.symm x‖=1) : x∈(transverseDiffeomorph m).source := by
  rw [transverseDiffeomorph_source]
  exact unitCircle_subset_transverseDomain m hx

end PackingSufficiencySupport.DiagonalQuadrics.Explicit
end

end OAI
