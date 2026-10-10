import Mathlib
import OAI.Geometry.BallPacking.BallMaps.CubicBubbleSeparated
import OAI.Geometry.BallPacking.Models.LiouvilleRadialCalculus
import OAI.Geometry.BallPacking.Normal.TailLineCoordinates

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian
open scoped BigOperators
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

abbrev ConeModel (m : ℕ) := RealModel × (Fin m → ℂ)
abbrev ConeSpace := locus a × (Fin m → ℂ)
abbrev ConeTarget (m : ℕ) := PlanePhase (Option (Fin m)) × PlanePhase (Fin m)

 def movingConeCoordinates (Ψ : ℝ × ConeSpace a → Affine m) (p : ℝ × ConeSpace a) : ConeTarget m :=
  (affinePhase m (Ψ p),complexCartesian p.2.2)

 theorem movingConeCoordinates_smooth {Ψ : ℝ × ConeSpace a → Affine m}
    (hΨ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,Affine m) ∞ Ψ) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,ConeTarget m) ∞
      (movingConeCoordinates a Ψ) := by
  apply ContMDiff.prodMk_space
  · exact (affinePhase m).contDiff.contMDiff.comp hΨ
  · have hs : ContMDiff 𝓘(ℝ,ConeModel m) 𝓘(ℝ,Fin m → ℂ) ∞
        (Prod.snd : ConeSpace a → Fin m → ℂ) := by
      simpa only [modelWithCornersSelf_prod] using
        (contMDiff_snd : ContMDiff ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,Fin m → ℂ))
          𝓘(ℝ,Fin m → ℂ) ∞ (Prod.snd : ConeSpace a → Fin m → ℂ))
    exact (complexCartesian (ι := Fin m)).contDiff.contMDiff.comp (hs.comp contMDiff_snd)

 def centralConeCoordinates (p : ConeSpace a) : ConeTarget m :=
  (affinePhase m p.1.val,complexCartesian p.2)

 def centralConePrimitive (c d : ℝ) : ManifoldOneForm (ConeModel m) (ConeSpace a) :=
  manifoldPullbackOneForm (fun _ => conePrimitive c d) (centralConeCoordinates a) 0

 omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
 theorem movingConeCoordinates_zero {Ψ : ℝ × ConeSpace a → Affine m}
    (hΨ : ∀ p,Ψ (0,p)=p.1.val) :
    (fun p => movingConeCoordinates a Ψ (0,p))=centralConeCoordinates a := by
  funext p
  simp only [movingConeCoordinates,centralConeCoordinates,hΨ]

 omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
 theorem movingConeCoordinates_nonzero {Ψ : ℝ × ConeSpace a → Affine m}
    {t : ℝ} (ht : t≠0) {p : ConeSpace a} (he : equations a (Ψ (t,p))=t•p.2) :
    movingConeCoordinates a Ψ (t,p)=normalConeCoordinates a t (Ψ (t,p)) := by
  apply Prod.ext
  · rfl
  apply congrArg (complexCartesian (ι := Fin m))
  change p.2=fun j => (t:ℂ)⁻¹*equations a (Ψ (t,p)) j
  funext j
  rw [he]
  simp only [Pi.smul_apply,Complex.real_smul]
  rw [← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht),one_mul]

 theorem exists_actual_normal_exact_family {K : Set (locus a)} {H : Set (Fin m → ℂ)}
    (hK : IsCompact K) (hH : IsCompact H) (c d : ℝ) :
    ∃ Ψ : ℝ × ConeSpace a → Affine m, ∃ Γ : ℝ → ManifoldOneForm (ConeModel m) (ConeSpace a),
      ∃ ε : ℝ,0<ε ∧ ∃ U : Set (ConeSpace a),IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,Affine m) ∞ Ψ ∧
      SmoothOneFormFamily Γ ∧ Γ 0=centralConePrimitive a c d ∧
      (∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Ψ (t,p.val))) ∧
      (∀ t∈Icc (-ε) ε,t≠0 → ∀ p∈U,
        manifoldExteriorOneForm (Γ t) p=
          (normalAmbientForm a c d t (Ψ (t,p))).bilinearComp
            (manifoldMapDifferential (E := Affine m) (F := ConeModel m) (fun q => Ψ (t,q)) p)
            (manifoldMapDifferential (E := Affine m) (F := ConeModel m) (fun q => Ψ (t,q)) p)) := by
  obtain ⟨Ψ,ε,hε,U,hU,hKU,hΨ,hΨ0,hEQ,hemb⟩ := exists_actual_normal_tube a hK hH
  have hs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,Affine m) ∞ Ψ := by
    simpa only [modelWithCornersSelf_prod] using hΨ
  let g := movingConeCoordinates a Ψ
  have hg := movingConeCoordinates_smooth a hs
  let Γ := movingPrimitivePullback (E := ConeModel m) (conePrimitive c d) g
  refine ⟨Ψ,Γ,ε,hε,U,hU,hKU,hs,movingPrimitivePullback_smooth (conePrimitive_smooth c d) hg,?_,hemb,?_⟩
  · change manifoldPullbackOneForm (fun _ => conePrimitive c d)
      (fun p => movingConeCoordinates a Ψ (0,p)) 0=centralConePrimitive a c d
    rw [movingConeCoordinates_zero a hΨ0]
    rfl
  · intro t ht ht0 p hp
    have he : (fun q => g (t,q)) =ᶠ[𝓝 p] normalConeCoordinates a t ∘ (fun q => Ψ (t,q)) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact movingConeCoordinates_nonzero a ht0 (hEQ q hq t ht)
    have hh := movingPrimitivePullback_exterior_comp (conePrimitive_smooth c d) hg
      (normalConeCoordinates_smooth a t) (hs.comp (contMDiff_const.prodMk contMDiff_id)) he
    rw [← normalAmbientPrimitive_eq_cone a c d t] at hh
    exact hh

abbrev NormalModel (m : ℕ) := RealModel × PlanePhase (Fin m)
abbrev NormalSpace := locus a × PlanePhase (Fin m)

def normalCouplingPrimitive : ManifoldOneForm (NormalModel m) (NormalSpace a) :=
  productHorizontalLift (normalHorizontalPrimitive (q := m) a 2 ∘ planeMoments)+verticalLiouville

theorem normalCouplingPrimitive_smooth :
    SmoothOneFormFamily (fun _ : ℝ => normalCouplingPrimitive a) := by
  have hh : SmoothOneFormFamily (fun _ : ℝ => productHorizontalLift
      (normalHorizontalPrimitive (q := m) a 2 ∘ planeMoments)) := by
    apply productHorizontalLift_smooth (Γ := fun p : ℝ × PlanePhase (Fin m) =>
      normalHorizontalPrimitive (q := m) a 2 (planeMoments p.2))
    exact ((normalHorizontalPrimitive_smooth (q := m) a 2).comp planeMoments_smooth).comp contDiff_snd
  exact hh.add verticalLiouville_smooth

theorem normalCouplingPrimitive_exterior (x : NormalSpace a) :
    manifoldExteriorOneForm (normalCouplingPrimitive a) x=
      globalHorizontalCoupling phaseArea (normalHorizontalPrimitive (q := m) a 2 ∘ planeMoments) x := by
  have hh : SmoothOneFormFamily (fun _ : ℝ => productHorizontalLift
      (normalHorizontalPrimitive (q := m) a 2 ∘ planeMoments)) := by
    apply productHorizontalLift_smooth (Γ := fun p : ℝ × PlanePhase (Fin m) =>
      normalHorizontalPrimitive (q := m) a 2 (planeMoments p.2))
    exact ((normalHorizontalPrimitive_smooth (q := m) a 2).comp planeMoments_smooth).comp contDiff_snd
  rw [normalCouplingPrimitive,manifoldExteriorOneForm_add_at
    (hh.spatial_smooth 0 x (mem_extChartAt_target _))
    (verticalLiouville_smooth.spatial_smooth 0 x (mem_extChartAt_target _)),verticalLiouville_exterior]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change (_ : ℝ)+_=_+_
  exact add_comm _ _

theorem normalCoupling_invertible {d : ℝ} (hd : d<1/2) {x : NormalSpace a}
    (hx : Real.pi*phaseSq x.2≤d) :
    (manifoldExteriorOneForm (normalCouplingPrimitive a) x).IsInvertible := by
  rw [normalCouplingPrimitive_exterior]
  apply globalToricCoupling_isInvertible (normalHorizontalPrimitive_smooth (q := m) a 2) x
  have hex : manifoldExteriorOneForm (normalHorizontalPrimitive (q := m) a 2 (planeMoments x.2))=
      equalNormalCoefficient m 2 (planeMoments x.2) • curveFSForm a (1/Real.pi) :=
    funext (normalHorizontalPrimitive_exterior a 2 (planeMoments x.2))
  rw [hex]
  have hc : 0<equalNormalCoefficient m 2 (planeMoments x.2) := by
    change 0<1-2*(∑ j,planeMoments x.2 j)
    have he : (∑ j,planeMoments x.2 j)=Real.pi*phaseSq x.2 := by
      simp only [planeMoments,radialArea,radiusSq,phaseSq,phaseDot_apply,pow_two,← Finset.mul_sum]
    rw [he]
    linarith
  change 0<equalNormalCoefficient m 2 (planeMoments x.2)*
    chartTwoForm (curveFSForm a (1/Real.pi)) x.1 (extChartAt 𝓘(ℝ,RealModel) x.1 x.1) (1,0) (0,1)
  exact mul_pos hc (curveFSForm_positive a (one_div_pos.mpr Real.pi_pos) x.1 (mem_extChartAt_target _))

def normalPhaseCoordinates (x : NormalSpace a) : ConeTarget m :=
  (phaseInclusion a x.1,x.2)

theorem normalPhaseCoordinates_smooth :
    ContMDiff 𝓘(ℝ,NormalModel m) 𝓘(ℝ,ConeTarget m) ∞ (normalPhaseCoordinates a) :=
  ((phaseInclusion_smooth a).comp flatProduct_fst_smooth).prodMk_space flatProduct_snd_smooth

theorem normalPhaseCoordinates_derivative (x : NormalSpace a) :
    manifoldMapDifferential (E := ConeTarget m) (F := NormalModel m) (normalPhaseCoordinates a) x=
      (manifoldMapDifferential (E := PlanePhase (Option (Fin m))) (F := RealModel)
        (phaseInclusion a) x.1).prodMap (ContinuousLinearMap.id ℝ (PlanePhase (Fin m))) := by
  have hf := (((phaseInclusion_smooth a).comp flatProduct_fst_smooth).mdifferentiable (by simp) x).hasMFDerivAt
  have hs := ((flatProduct_snd_smooth (E := RealModel) (M := locus a) (V := PlanePhase (Fin m))).mdifferentiable (by simp) x).hasMFDerivAt
  have hd : HasMFDerivAt 𝓘(ℝ,NormalModel m) 𝓘(ℝ,ConeTarget m) (normalPhaseCoordinates a) x
      ((mfderiv 𝓘(ℝ,NormalModel m) 𝓘(ℝ,PlanePhase (Option (Fin m)))
        (phaseInclusion a ∘ Prod.fst) x).prod
        (mfderiv 𝓘(ℝ,NormalModel m) 𝓘(ℝ,PlanePhase (Fin m)) Prod.snd x)) :=
    ⟨hf.1.prodMk hs.1,hf.2.prodMk hs.2⟩
  apply hd.mfderiv.trans
  erw [mfderiv_comp x ((phaseInclusion_smooth a).mdifferentiable (by simp) x.1)
    (flatProduct_fst_smooth.mdifferentiable (by simp) x),flatProduct_fst_derivative,flatProduct_snd_derivative]
  rfl

theorem centralConeCoordinates_smooth :
    ContMDiff 𝓘(ℝ,ConeModel m) 𝓘(ℝ,ConeTarget m) ∞ (centralConeCoordinates a) :=
  ((phaseInclusion_smooth a).comp flatProduct_fst_smooth).prodMk_space
    ((complexCartesian (ι := Fin m)).contDiff.contMDiff.comp flatProduct_snd_smooth)

theorem cone_radial_primitive {d : ℝ} (hd : 0<d)
    {Ξ : NormalSpace a → ConeSpace a}
    (hΞ : ContMDiff 𝓘(ℝ,NormalModel m) 𝓘(ℝ,ConeModel m) ∞ Ξ)
    {x : NormalSpace a} (hx : phaseSq x.2<d/Real.pi)
    (he : centralConeCoordinates a ∘ Ξ =ᶠ[𝓝 x]
      normalRadial (d/Real.pi) ∘ normalPhaseCoordinates a) :
    manifoldPullbackOneForm (fun _ => centralConePrimitive a (1/Real.pi) d) Ξ 0 x=
      normalCouplingPrimitive a x := by
  have hD := manifoldMapDifferential_comp
    ((centralConeCoordinates_smooth a).mdifferentiable (by simp) (Ξ x))
    (hΞ.mdifferentiable (by simp) x)
  have hr := ((normalRadial_smoothOn (d/Real.pi)).contDiffAt
    ((isOpen_univ.prod (phaseOpenBall_open (d/Real.pi))).mem_nhds
      (show normalPhaseCoordinates a x∈univ×ˢphaseOpenBall (d/Real.pi) from ⟨mem_univ _,hx⟩)))
  have hDr := manifoldMapDifferential_comp (hr.contMDiffAt.mdifferentiableAt (by simp))
    ((normalPhaseCoordinates_smooth a).mdifferentiable (by simp) x)
  have heD : manifoldMapDifferential (E := ConeTarget m) (F := NormalModel m)
      (centralConeCoordinates a ∘ Ξ) x=
      manifoldMapDifferential (E := ConeTarget m) (F := NormalModel m)
      (normalRadial (d/Real.pi) ∘ normalPhaseCoordinates a) x := he.mfderiv_eq
  apply ContinuousLinearMap.ext
  intro v
  change conePrimitive (1/Real.pi) d (centralConeCoordinates a (Ξ x))
    (((manifoldMapDifferential (E := ConeTarget m) (F := ConeModel m) (centralConeCoordinates a) (Ξ x)).comp
      (manifoldMapDifferential (E := ConeModel m) (F := NormalModel m) Ξ x)) v)=_
  rw [← hD,heD,hDr]
  have hep := he.eq_of_nhds
  change centralConeCoordinates a (Ξ x)=normalRadial (d/Real.pi) (normalPhaseCoordinates a x) at hep
  rw [hep]
  change conePrimitive (1/Real.pi) d (normalRadial (d/Real.pi) (normalPhaseCoordinates a x))
    (mfderiv 𝓘(ℝ,ConeTarget m) 𝓘(ℝ,ConeTarget m) (normalRadial (d/Real.pi))
      (normalPhaseCoordinates a x) (manifoldMapDifferential (E := ConeTarget m) (F := NormalModel m)
        (normalPhaseCoordinates a) x v))=_
  erw [mfderiv_eq_fderiv,conePrimitive_radial_pullback hd (p := normalPhaseCoordinates a x) ⟨mem_univ _,hx⟩,normalPhaseCoordinates_derivative]
  simp only [normalCouplingPrimitive,Pi.add_apply,add_apply,productHorizontalLift_apply,verticalLiouville_apply,
    normalHorizontalPrimitive,normalPhaseCoordinates,Function.comp_apply,Pi.smul_apply,smul_apply,smul_eq_mul]
  congr 1
  change (1-2*Real.pi*phaseSq x.2)*curveFSPrimitive a (1/Real.pi) x.1 v.1=
    equalNormalCoefficient m 2 (planeMoments x.2)*curveFSPrimitive a (1/Real.pi) x.1 v.1
  congr 1
  simp only [equalNormalCoefficient,planeMoments,radialArea,radiusSq,phaseSq,phaseDot_apply,pow_two,← Finset.mul_sum]
  ring

abbrev LargeNormalModel (m : ℕ) := RealModel × PlanePhase (Fin (m+1))
abbrev LargeNormalSpace := locus a × PlanePhase (Fin (m+1))

 def largeCouplingPrimitive : ManifoldOneForm (LargeNormalModel m) (LargeNormalSpace a) :=
  productCouplingPrimitive phaseArea (largeHorizontalPrimitive (q := m) a ∘ planeMoments)

 theorem largeHorizontal_lift_smooth :
    SmoothOneFormFamily (fun _ : ℝ => productHorizontalLift
      (largeHorizontalPrimitive (q := m) a ∘ planeMoments)) := by
  apply productHorizontalLift_smooth (Γ := fun p : ℝ × PlanePhase (Fin (m+1)) =>
    largeHorizontalPrimitive (q := m) a (planeMoments p.2))
  exact ((largeHorizontalPrimitive_smooth (q := m) a).comp planeMoments_smooth).comp contDiff_snd

 theorem largeCouplingPrimitive_smooth :
    SmoothOneFormFamily (fun _ : ℝ => largeCouplingPrimitive a) := by
  have hv := productVerticalLiouville_smooth (E := RealModel) (M := locus a)
    (V := PlanePhase (Fin (m+1))) (phaseArea (ι := Fin (m+1)))
  have hh := largeHorizontal_lift_smooth a
  have ht := SmoothOneFormFamily.add hv hh
  convert! ht using 1

 theorem largeCouplingPrimitive_exterior (x : LargeNormalSpace a) :
    manifoldExteriorOneForm (largeCouplingPrimitive a) x=
      globalHorizontalCoupling phaseArea (largeHorizontalPrimitive (q := m) a ∘ planeMoments) x :=
  productCouplingPrimitive_exterior (E := RealModel) (M := locus a)
    (V := PlanePhase (Fin (m+1))) phaseArea phaseArea_skew
    ((largeHorizontalPrimitive_smooth (q := m) a).comp planeMoments_smooth) x

 theorem phaseMoments_sum {q : ℕ} (z : PlanePhase (Fin q)) :
    (∑ j,planeMoments z j)=Real.pi*phaseSq z := by
  simp only [planeMoments,radialArea,radiusSq,phaseSq,phaseDot_apply,pow_two,← Finset.mul_sum]

 theorem normalCouplingPrimitive_apply (x : NormalSpace a) (v : NormalModel m) :
    normalCouplingPrimitive a x v=standardLiouville x.2 v.2+
      (1-2*Real.pi*phaseSq x.2)*curveFSPrimitive a (1/Real.pi) x.1 v.1 := by
  simp only [normalCouplingPrimitive,Pi.add_apply,add_apply,productHorizontalLift_apply,
    Function.comp_apply,normalHorizontalPrimitive,Pi.smul_apply,smul_apply,smul_eq_mul,
    equalNormalCoefficient,phaseMoments_sum,verticalLiouville_apply,standardLiouville]
  ring

 theorem largeCouplingPrimitive_apply (x : LargeNormalSpace a) (v : LargeNormalModel m) :
    largeCouplingPrimitive a x v=standardLiouville x.2 v.2+
      (1-radialArea (normalHead m x.2)-2*Real.pi*phaseSq (normalTail m x.2))*
        curveFSPrimitive a (1/Real.pi) x.1 v.1 := by
  simp only [largeCouplingPrimitive,productCouplingPrimitive,Pi.add_apply,add_apply,
    productVerticalLiouville_apply,productHorizontalLift_apply,Function.comp_apply,
    largeHorizontalPrimitive,largeNormalCoefficient,Pi.smul_apply,smul_apply,smul_eq_mul]
  have he : (∑ j : Fin m,planeMoments x.2 j.succ)=Real.pi*phaseSq (normalTail m x.2) :=
    phaseMoments_sum (normalTail m x.2)
  rw [he]
  change (1/2:ℝ)*phaseArea x.2 v.2+(1-radialArea (normalHead m x.2)-2*(Real.pi*phaseSq (normalTail m x.2)))*
    curveFSPrimitive a (1/Real.pi) x.1 v.1=_
  simp only [standardLiouville,smul_apply,smul_eq_mul]
  ring

 theorem firstTailMap_primitive {s : PlanePhase (Fin (m+1)) → ℝ} (hs : ContDiff ℝ ∞ s)
    (x : LargeNormalSpace a) (hc : (1-radialArea (normalHead m x.2))*(s x.2)^2=1) :
    manifoldPullbackOneForm (fun _ => firstLinePrimitive (normalCouplingPrimitive a))
      (firstTailMap s) 0 x=largeCouplingPrimitive a x := by
  apply ContinuousLinearMap.ext
  intro v
  change firstLinePrimitive (normalCouplingPrimitive a) (firstTailMap s x)
    (manifoldMapDifferential (E := NormalModel m × Plane) (F := LargeNormalModel m) (firstTailMap s) x v)=_
  rw [firstTailMap_derivative hs,firstLinePrimitive_apply,normalCouplingPrimitive_apply,
    largeCouplingPrimitive_apply]
  change linearLiouville planarArea (normalHead m x.2) (normalHead m v.2)+
    (1-radialArea (normalHead m x.2))*(standardLiouville (s x.2 • normalTail m x.2)
      (fderiv ℝ (fun z => s z • normalTail m z) x.2 v.2)+
      (1-2*Real.pi*phaseSq (s x.2 • normalTail m x.2))*curveFSPrimitive a (1/Real.pi) x.1 v.1)=_
  have hL := linearLiouville_variable_smul phaseArea phaseArea_self (hs.differentiable (by simp) x.2)
    (normalTail m).differentiableAt v.2
  change standardLiouville (s x.2 • normalTail m x.2)
      (fderiv ℝ (fun z => s z • normalTail m z) x.2 v.2)=_ at hL
  rw [(normalTail m).fderiv] at hL
  change standardLiouville (s x.2 • normalTail m x.2)
      (fderiv ℝ (fun z => s z • normalTail m z) x.2 v.2)=
        (s x.2)^2*standardLiouville (normalTail m x.2) (normalTail m v.2) at hL
  rw [hL,phaseSq_smul,normalSplit_liouville]
  change _=standardLiouville (normalTail m x.2) (normalTail m v.2)+
    linearLiouville planarArea (normalHead m x.2) (normalHead m v.2)+_
  linear_combination
    (standardLiouville (normalTail m x.2) (normalTail m v.2)-
      2*Real.pi*phaseSq (normalTail m x.2)*curveFSPrimitive a (1/Real.pi) x.1 v.1)*hc

 theorem largeCouplingPrimitive_invertible {x : LargeNormalSpace a}
    (hx : 0<1-radialArea (normalHead m x.2)-2*Real.pi*phaseSq (normalTail m x.2)) :
    (manifoldExteriorOneForm (largeCouplingPrimitive a) x).IsInvertible := by
  rw [largeCouplingPrimitive_exterior]
  apply globalToricCoupling_isInvertible (largeHorizontalPrimitive_smooth (q := m) a) x
  have hex : manifoldExteriorOneForm (largeHorizontalPrimitive (q := m) a (planeMoments x.2))=
      largeNormalCoefficient m (planeMoments x.2) • curveFSForm a (1/Real.pi) :=
    funext (largeHorizontalPrimitive_exterior a (planeMoments x.2))
  rw [hex]
  have he : largeNormalCoefficient m (planeMoments x.2)=
      1-radialArea (normalHead m x.2)-2*Real.pi*phaseSq (normalTail m x.2) := by
    have ht : (∑ j : Fin m,planeMoments x.2 j.succ)=Real.pi*phaseSq (normalTail m x.2) :=
      phaseMoments_sum (normalTail m x.2)
    simp only [largeNormalCoefficient,ht]
    change 1-radialArea (normalHead m x.2)-2*(Real.pi*phaseSq (normalTail m x.2))=_
    ring
  change 0<largeNormalCoefficient m (planeMoments x.2)*
    chartTwoForm (curveFSForm a (1/Real.pi)) x.1 (extChartAt 𝓘(ℝ,RealModel) x.1 x.1) (1,0) (0,1)
  rw [he]
  exact mul_pos hx (curveFSForm_positive a (one_div_pos.mpr Real.pi_pos) x.1 (mem_extChartAt_target _))

end

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 theorem exists_compact_first_tail_bridge {b d : ℝ} (hb : b<1)
    {K : Set (LargeNormalSpace a)} (hK : IsCompact K)
    (hKb : ∀ x∈K,radialArea (normalHead m x.2)<b)
    (hKd : ∀ x∈K,Real.pi*phaseSq (normalTail m x.2)<d*(1-radialArea (normalHead m x.2))) :
    ∃ H : LargeNormalSpace a → NormalSpace a × Plane,
      ContMDiff 𝓘(ℝ,LargeNormalModel m) 𝓘(ℝ,NormalModel m × Plane) ∞ H ∧
      ∃ D : Set (LargeNormalSpace a),IsOpen D ∧ K⊆D ∧
        Topology.IsEmbedding (fun x : D => H x.val) ∧
        (∀ x,radialArea (H x).2=radialArea (normalHead m x.2)) ∧
        (∀ x∈D,radialArea (H x).2<b ∧ phaseSq (H x).1.2<d/Real.pi) ∧
        (∀ x∈D,manifoldPullbackOneForm (fun _ => firstLinePrimitive (normalCouplingPrimitive a)) H 0 x=
          largeCouplingPrimitive a x) := by
  let U : Set (PlanePhase (Fin (m+1))) := {z | radialArea (normalHead m z)<b ∧
    Real.pi*phaseSq (normalTail m z)<d*(1-radialArea (normalHead m z))}
  have hU : IsOpen U :=
    (isOpen_lt (radialArea_smooth.continuous.comp (normalHead m).continuous) continuous_const).inter
      (isOpen_lt (continuous_const.mul (phaseSq_smooth.continuous.comp (normalTail m).continuous))
        (continuous_const.mul (continuous_const.sub (radialArea_smooth.continuous.comp (normalHead m).continuous))))
  let σ : PlanePhase (Fin (m+1)) → ℝ := fun z => (Real.sqrt (1-radialArea (normalHead m z)))⁻¹
  have hσ : ContDiffOn ℝ ∞ σ U :=
    (((contDiffOn_const.sub ((radialArea_smooth.comp (normalHead m).contDiff).contDiffOn)).sqrt
      (fun z hz => (sub_pos.mpr (hz.1.trans hb)).ne')).inv
        (fun z hz => (Real.sqrt_pos.mpr (sub_pos.mpr (hz.1.trans hb))).ne'))
  obtain ⟨χ,_hχ,_hχc,_hχU,_hχr,_hχ1,hs,_hsc,hse⟩ := exists_smooth_compact_extension
    (hK.image continuous_snd) hU (by rintro z ⟨x,hx,rfl⟩; exact ⟨hKb x hx,hKd x hx⟩) hσ
  let s : PlanePhase (Fin (m+1)) → ℝ := fun z => χ z • σ z
  obtain ⟨O,hO,hKO,hOs⟩ := mem_nhdsSet_iff_exists.mp hse
  let D : Set (LargeNormalSpace a) := Prod.snd ⁻¹' (O∩U)
  have hD : IsOpen D := (hO.inter hU).preimage continuous_snd
  let H : LargeNormalSpace a → NormalSpace a × Plane := firstTailMap s
  have hH := firstTailMap_smooth (M := locus a) (E := RealModel) hs
  have hratio (x : LargeNormalSpace a) (hx : x∈D) :
      (1-radialArea (normalHead m x.2))*(s x.2)^2=1 := by
    have he : s x.2=σ x.2 := hOs hx.1
    rw [he]
    change (1-radialArea (normalHead m x.2))*((Real.sqrt (1-radialArea (normalHead m x.2)))⁻¹)^2=1
    rw [inv_pow,Real.sq_sqrt (sub_pos.mpr (hx.2.1.trans hb)).le,
      mul_inv_cancel₀ (sub_pos.mpr (hx.2.1.trans hb)).ne']
  let G : NormalSpace a × Plane → LargeNormalSpace a := fun y =>
    (y.1.1,(normalSplit m).symm (Real.sqrt (1-radialArea y.2) • y.1.2,y.2))
  have hG : Continuous G := by
    exact continuous_fst.fst.prodMk ((normalSplit m).symm.continuous.comp
      (((Real.continuous_sqrt.comp (continuous_const.sub (radialArea_smooth.continuous.comp continuous_snd))).smul
        continuous_fst.snd).prodMk continuous_snd))
  have hGH (x : LargeNormalSpace a) (hx : x∈D) : G (H x)=x := by
    apply Prod.ext
    · rfl
    have he : s x.2=σ x.2 := hOs hx.1
    change (normalSplit m).symm
      (Real.sqrt (1-radialArea (normalHead m x.2)) • (s x.2 • normalTail m x.2),normalHead m x.2)=x.2
    rw [he,smul_smul]
    change (normalSplit m).symm
      ((Real.sqrt (1-radialArea (normalHead m x.2))*
        (Real.sqrt (1-radialArea (normalHead m x.2)))⁻¹) • normalTail m x.2,normalHead m x.2)=x.2
    rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr (sub_pos.mpr (hx.2.1.trans hb))).ne',one_smul]
    exact (normalSplit m).symm_apply_apply x.2
  have hemb : Topology.IsEmbedding (fun x : D => H x.val) := by
    apply Topology.IsEmbedding.of_comp (hH.continuous.comp continuous_subtype_val) hG
    convert Topology.IsEmbedding.subtypeVal (p := fun x => x∈D) using 1
    funext x
    exact hGH x.val x.property
  refine ⟨H,hH,D,hD,fun x hx => ⟨hKO ⟨x,hx,rfl⟩,hKb x hx,hKd x hx⟩,hemb,
    fun _ => rfl,?_,fun x hx => firstTailMap_primitive a hs x (hratio x hx)⟩
  intro x hx
  refine ⟨hx.2.1,?_⟩
  change phaseSq (s x.2 • normalTail m x.2)<d/Real.pi
  rw [phaseSq_smul]
  apply (lt_div_iff₀ Real.pi_pos).mpr
  have hu : 0<1-radialArea (normalHead m x.2) := sub_pos.mpr (hx.2.1.trans hb)
  apply (mul_lt_mul_iff_of_pos_left hu).mp
  calc
    (1-radialArea (normalHead m x.2))*((s x.2)^2*phaseSq (normalTail m x.2)*Real.pi)=
        Real.pi*phaseSq (normalTail m x.2) := by rw [← mul_assoc,← mul_assoc,hratio x hx]; ring
    _<d*(1-radialArea (normalHead m x.2)) := hx.2.2
    _=(1-radialArea (normalHead m x.2))*d := mul_comm _ _

 theorem exists_compact_radial_bridge {d : ℝ} (hd : 0<d)
    {K : Set (NormalSpace a)} (hK : IsCompact K)
    (hKd : ∀ p∈K,phaseSq p.2<d/Real.pi) :
    ∃ Ξ : NormalSpace a → ConeSpace a,
      ContMDiff 𝓘(ℝ,NormalModel m) 𝓘(ℝ,ConeModel m) ∞ Ξ ∧
      ∃ D : Set (NormalSpace a),IsOpen D ∧ K⊆D ∧
        (∀ p∈D,phaseSq p.2<d/Real.pi) ∧
        Topology.IsEmbedding (fun p : D => Ξ p.val) ∧
        EqOn (centralConeCoordinates a ∘ Ξ)
          (normalRadial (d/Real.pi) ∘ normalPhaseCoordinates a) D := by
  let H := Prod.snd '' K
  have hH : IsCompact H := hK.image continuous_snd
  have hHd : H⊆phaseOpenBall (d/Real.pi) := by
    rintro _ ⟨p,hp,rfl⟩
    exact hKd p hp
  obtain ⟨χ,_hχ,_hχc,_hχs,_hχr,_hχ1,hF,_hFc,hFe⟩ :=
    exists_smooth_compact_extension hH (phaseOpenBall_open (d/Real.pi)) hHd
      (fsAffineMap_smoothOn (d/Real.pi))
  let F : PlanePhase (Fin m) → PlanePhase (Fin m) := fun u => χ u • fsAffineMap (d/Real.pi) u
  obtain ⟨O,hO,hHO,hOF⟩ := mem_nhdsSet_iff_exists.mp hFe
  let D : Set (NormalSpace a) := Prod.snd ⁻¹' (O∩phaseOpenBall (d/Real.pi))
  have hD : IsOpen D := (hO.inter (phaseOpenBall_open (d/Real.pi))).preimage continuous_snd
  let A : NormalSpace a → ℝ := fun p => 1+phaseSq (phaseInclusion a p.1)
  have hA : ContMDiff 𝓘(ℝ,NormalModel m) 𝓘(ℝ,ℝ) ∞ A :=
    contMDiff_const.add (phaseSq_smooth.contMDiff.comp
      ((phaseInclusion_smooth a).comp flatProduct_fst_smooth))
  let Ξ : NormalSpace a → ConeSpace a :=
    fun p => (p.1,complexCartesian.symm (A p • F p.2))
  have hΞ : ContMDiff 𝓘(ℝ,NormalModel m) 𝓘(ℝ,ConeModel m) ∞ Ξ := by
    have hs := (complexCartesian (ι := Fin m)).symm.contDiff.contMDiff.comp
      (hA.smul (hF.contMDiff.comp flatProduct_snd_smooth))
    rw [show 𝓘(ℝ,ConeModel m)=(𝓘(ℝ,RealModel)).prod 𝓘(ℝ,Fin m → ℂ) from modelWithCornersSelf_prod]
    exact (flatProduct_fst_smooth (E := RealModel) (M := locus a) (V := PlanePhase (Fin m))).prodMk hs
  let R : ConeSpace a → NormalSpace a := fun p => (p.1,fsBallMap (d/Real.pi)
    ((1+phaseSq (phaseInclusion a p.1))⁻¹ • complexCartesian p.2))
  have hR : Continuous R := by
    apply continuous_fst.prodMk
    apply (fsBallMap_smooth (d/Real.pi)).continuous.comp
    exact (((continuous_const.add (phaseSq_smooth.continuous.comp
      ((phaseInclusion_smooth a).continuous.comp continuous_fst))).inv₀
      (fun p => (fs_den_pos (phaseInclusion a p.1)).ne')).smul
        ((complexCartesian (ι := Fin m)).continuous.comp continuous_snd))
  have hRI (p : NormalSpace a) (hp : p∈D) : R (Ξ p)=p := by
    have hFp : F p.2=fsAffineMap (d/Real.pi) p.2 := hOF hp.1
    simp only [R,Ξ,ContinuousLinearEquiv.apply_symm_apply,A,hFp,smul_smul,
      inv_mul_cancel₀ (fs_den_pos (phaseInclusion a p.1)).ne',one_smul,
      fsBallMap_fsAffineMap (div_pos hd Real.pi_pos) hp.2]
  refine ⟨Ξ,hΞ,D,hD,?_,fun _ hp => hp.2,?_,?_⟩
  · intro p hp
    exact ⟨hHO ⟨p,hp,rfl⟩,hKd p hp⟩
  · apply Topology.IsEmbedding.of_comp (hΞ.continuous.comp continuous_subtype_val) hR
    have he : R ∘ (fun p : D => Ξ p.val)=Subtype.val := funext fun p => hRI p.val p.property
    change Topology.IsEmbedding (R ∘ (fun p : D => Ξ p.val))
    rw [he]
    exact Topology.IsEmbedding.subtypeVal
  · intro p hp
    have hFp : F p.2=fsAffineMap (d/Real.pi) p.2 := hOF hp.1
    simp only [Function.comp_apply,centralConeCoordinates,Ξ,ContinuousLinearEquiv.apply_symm_apply,
      normalRadial,normalPhaseCoordinates,phaseInclusion,A,hFp]

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem movingPrimitivePullback_comp_eq
    {α : F → F →L[ℝ] ℝ} {g : ℝ × M → F} {A : G → F} {h : M → G}
    (hA : ContDiff ℝ ∞ A) (hh : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ h)
    {t : ℝ} {x : M} (he : (fun y => g (t,y)) =ᶠ[𝓝 x] A ∘ h) :
    movingPrimitivePullback (E := E) α g t x=
      (primitivePullback α A (h x)).comp (manifoldMapDifferential (E := G) (F := E) h x) := by
  have hd : manifoldMapDifferential (E := F) (F := E) (fun y => g (t,y)) x=
      (fderiv ℝ A (h x)).comp (manifoldMapDifferential (E := G) (F := E) h x) := by
    unfold manifoldMapDifferential
    rw [he.mfderiv_eq]
    rw [mfderiv_comp x (hA.contMDiff.mdifferentiable (by simp) (h x))
      (hh.mdifferentiable (by simp) x)]
    rw [mfderiv_eq_fderiv]
    ext tangent
    rfl
  simp only [movingPrimitivePullback,manifoldPullbackOneForm,hd,he.eq_of_nhds,
    primitivePullback,ContinuousLinearMap.comp_assoc,Function.comp_apply]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 theorem exists_actual_normal_primitive_family {K : Set (locus a)} {H : Set (Fin m → ℂ)}
    (hK : IsCompact K) (hH : IsCompact H) (c d : ℝ) :
    ∃ Ψ : ℝ × ConeSpace a → Affine m, ∃ Γ : ℝ → ManifoldOneForm (ConeModel m) (ConeSpace a),
      ∃ ε : ℝ,0<ε ∧ ∃ U : Set (ConeSpace a),IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,Affine m) ∞ Ψ ∧
      SmoothOneFormFamily Γ ∧ Γ 0=centralConePrimitive a c d ∧
      (∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Ψ (t,p.val))) ∧
      (∀ t∈Icc (-ε) ε,t≠0 → ∀ p∈U,
        Γ t p=(normalAmbientPrimitive a c d t (Ψ (t,p))).comp
          (manifoldMapDifferential (E := Affine m) (F := ConeModel m) (fun q => Ψ (t,q)) p)) := by
  obtain ⟨Ψ,ε,hε,U,hU,hKU,hΨ,hΨ0,hEQ,hemb⟩ := exists_actual_normal_tube a hK hH
  have hs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ConeModel m)) 𝓘(ℝ,Affine m) ∞ Ψ := by
    simpa only [modelWithCornersSelf_prod] using hΨ
  let g := movingConeCoordinates a Ψ
  have hg := movingConeCoordinates_smooth a hs
  let Γ := movingPrimitivePullback (E := ConeModel m) (conePrimitive c d) g
  refine ⟨Ψ,Γ,ε,hε,U,hU,hKU,hs,movingPrimitivePullback_smooth (conePrimitive_smooth c d) hg,?_,hemb,?_⟩
  · change manifoldPullbackOneForm (fun _ => conePrimitive c d)
      (fun p => movingConeCoordinates a Ψ (0,p)) 0=centralConePrimitive a c d
    rw [movingConeCoordinates_zero a hΨ0]
    rfl
  · intro t ht ht0 p hp
    have he : (fun q => g (t,q)) =ᶠ[𝓝 p] normalConeCoordinates a t ∘ (fun q => Ψ (t,q)) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact movingConeCoordinates_nonzero a ht0 (hEQ q hq t ht)
    have hh := movingPrimitivePullback_comp_eq (α := conePrimitive c d)
      (normalConeCoordinates_smooth a t) (hs.comp (contMDiff_const.prodMk contMDiff_id)) he
    rw [← normalAmbientPrimitive_eq_cone a c d t] at hh
    exact hh

 theorem exists_actual_radial_primitive_family {d : ℝ} (hd : 0<d)
    {K : Set (NormalSpace a)} (hK : IsCompact K)
    (hKd : ∀ x∈K,phaseSq x.2<d/Real.pi) :
    ∃ A : ℝ × NormalSpace a → Affine m,∃ Γ : ℝ → ManifoldOneForm (NormalModel m) (NormalSpace a),
      ∃ ε : ℝ,0<ε ∧ ∃ U : Set (NormalSpace a),IsOpen U ∧ K⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,NormalModel m)) 𝓘(ℝ,Affine m) ∞ A ∧
      SmoothOneFormFamily Γ ∧ EqOn (Γ 0) (normalCouplingPrimitive a) U ∧
      (∀ t∈Ioc (0:ℝ) ε,Topology.IsEmbedding (fun x : U => A (t,x.val))) ∧
      (∀ t∈Ioc (0:ℝ) ε,∀ x∈U,Γ t x=
        (normalAmbientPrimitive a (1/Real.pi) d t (A (t,x))).comp
          (manifoldMapDifferential (E := Affine m) (F := NormalModel m) (fun y => A (t,y)) x)) := by
  obtain ⟨Ξ,hΞ,D,hD,hKD,hDd,hΞemb,hΞeq⟩ := exists_compact_radial_bridge a hd hK hKd
  have hIK : IsCompact (Ξ '' K) := hK.image hΞ.continuous
  obtain ⟨Ψ,Γ,ε,hε,V,hV,hVK,hΨ,hΓ,hΓ0,hΨemb,hΓprim⟩ :=
    exists_actual_normal_primitive_family a (hIK.image continuous_fst) (hIK.image continuous_snd) (1/Real.pi) d
  have hKV : MapsTo Ξ K V := by
    intro x hx
    exact hVK ⟨⟨Ξ x,⟨x,hx,rfl⟩,rfl⟩,⟨Ξ x,⟨x,hx,rfl⟩,rfl⟩⟩
  let Δ : ℝ → ManifoldOneForm (NormalModel m) (NormalSpace a) :=
    manifoldPullbackOneForm (E := ConeModel m) (F := NormalModel m) Γ Ξ
  let A : ℝ × NormalSpace a → Affine m := fun p => Ψ (p.1,Ξ p.2)
  let U := D∩Ξ ⁻¹' V
  have hU : IsOpen U := hD.inter (hV.preimage hΞ.continuous)
  have hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,NormalModel m)) 𝓘(ℝ,Affine m) ∞ A :=
    hΨ.comp (contMDiff_fst.prodMk (hΞ.comp contMDiff_snd))
  have htI {t : ℝ} (ht : t∈Ioc (0:ℝ) ε) : t∈Icc (-ε) ε := ⟨by linarith [ht.1],ht.2⟩
  refine ⟨A,Δ,ε,hε,U,hU,fun x hx => ⟨hKD hx,hKV hx⟩,hA,
    manifoldPullbackOneForm_smooth hΞ hΓ,?_,?_,?_⟩
  · intro x hx
    have he := cone_radial_primitive a hd hΞ (hDd x hx.1)
      (hΞeq.eventuallyEq_of_mem (hD.mem_nhds hx.1))
    simpa only [Δ,manifoldPullbackOneForm,hΓ0] using he
  · intro t ht
    exact (hΨemb t (htI ht) (ne_of_gt ht.1)).comp
      (((hΞemb.comp (Topology.IsEmbedding.inclusion inter_subset_left)).codRestrict V)
        (fun x : U => x.property.2))
  · intro t ht x hx
    have hs : ContMDiff 𝓘(ℝ,ConeModel m) 𝓘(ℝ,Affine m) ∞ (fun p => Ψ (t,p)) :=
      hΨ.comp (contMDiff_const.prodMk contMDiff_id)
    change (Γ t (Ξ x)).comp (manifoldMapDifferential (E := ConeModel m) (F := NormalModel m) Ξ x)=_
    rw [hΓprim t (htI ht) (ne_of_gt ht.1) (Ξ x) hx.2]
    have hdiff := manifoldMapDifferential_comp
      (hs.mdifferentiable (by simp) (Ξ x)) (hΞ.mdifferentiable (by simp) x)
    change manifoldMapDifferential (E := Affine m) (F := NormalModel m) (fun y => A (t,y)) x=_ at hdiff
    rw [hdiff,ContinuousLinearMap.comp_assoc]

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped Manifold ContDiff Topology
open Set Function Manifold

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

 theorem firstLineBaseMap_isEmbedding_on {g : M → N} {U : Set M}
    (hg : Topology.IsEmbedding (fun x : U => g x.val)) :
    Topology.IsEmbedding (fun x : Prod.fst ⁻¹' U => firstLineBaseMap g x.val) := by
  let j : (Prod.fst ⁻¹' U : Set (M × Plane)) → U × Plane :=
    fun x => (⟨x.val.1,x.property⟩,x.val.2)
  have hjc : Continuous j :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  let k : U × Plane → M × Plane := Prod.map Subtype.val id
  have hkc : Continuous k := continuous_subtype_val.prodMap continuous_id
  have hj : Topology.IsEmbedding j := by
    apply Topology.IsEmbedding.of_comp hjc hkc
    exact Topology.IsEmbedding.subtypeVal
  exact (hg.prodMap Topology.IsEmbedding.id).comp hj

 theorem firstLineMoving_smooth {A : ℝ × M → N}
    (hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ A) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E × Plane)) 𝓘(ℝ,F × Plane) ∞
      (fun p : ℝ × (M × Plane) => firstLineBaseMap (fun x => A (p.1,x)) p.2) := by
  rw [show 𝓘(ℝ,F × Plane)=(𝓘(ℝ,F)).prod 𝓘(ℝ,Plane) from modelWithCornersSelf_prod]
  exact (hA.comp (contMDiff_fst.prodMk
    ((flatProduct_fst_smooth (E := E) (M := M) (V := Plane)).comp contMDiff_snd))).prodMk
      ((flatProduct_snd_smooth (E := E) (M := M) (V := Plane)).comp contMDiff_snd)

 theorem firstLineBaseMap_primitive_eq {g : M → N}
    (hg : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g) (α : ManifoldOneForm F N)
    (β : ManifoldOneForm E M) {x : M × Plane}
    (he : (α (g x.1)).comp (manifoldMapDifferential (E := F) (F := E) g x.1)=β x.1) :
    manifoldPullbackOneForm (fun _ => firstLinePrimitive α) (firstLineBaseMap g) 0 x=
      firstLinePrimitive β x := by
  rw [firstLineBaseMap_primitive hg]
  apply ContinuousLinearMap.ext
  intro v
  rw [firstLinePrimitive_apply,firstLinePrimitive_apply]
  change linearLiouville planarArea x.2 v.2+(1-radialArea x.2)*
    ((α (g x.1)).comp (manifoldMapDifferential (E := F) (F := E) g x.1)) v.1=_
  rw [he]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 theorem exists_actual_large_normal_transfer {b d : ℝ} (hb : b<1)
    (hd : 0<d) (hdhalf : d<1/2) {K : Set (LargeNormalSpace a)} (hK : IsCompact K)
    (hKb : ∀ x∈K,radialArea (normalHead m x.2)<b)
    (hKd : ∀ x∈K,Real.pi*phaseSq (normalTail m x.2)<d*(1-radialArea (normalHead m x.2))) :
    ∃ t : ℝ,0<t ∧ ∃ g : LargeNormalSpace a → Affine m × Plane,
      ∃ W : Set (LargeNormalSpace a),IsOpen W ∧ K⊆W ∧
      ContMDiff 𝓘(ℝ,LargeNormalModel m) 𝓘(ℝ,Affine m × Plane) ∞ g ∧
      Topology.IsEmbedding (fun x : W => g x.val) ∧
      (∀ x∈W,radialArea (g x).2<b) ∧
      ∀ x∈W,∀ v w,
        euclideanExteriorOneForm (firstLinePrimitive (normalAmbientPrimitive a (1/Real.pi) d t)) (g x)
          (mfderiv 𝓘(ℝ,LargeNormalModel m) 𝓘(ℝ,Affine m × Plane) g x v)
          (mfderiv 𝓘(ℝ,LargeNormalModel m) 𝓘(ℝ,Affine m × Plane) g x w)=
        globalHorizontalCoupling phaseArea (largeHorizontalPrimitive (q := m) a ∘ planeMoments) x v w := by
  let : SigmaCompactSpace (locus a) := IsClosed.sigmaCompactSpace (locus_isClosed a)
  obtain ⟨H,hH,D,hD,hKD,hHemb,_hHu,hHD,hHprim⟩ := exists_compact_first_tail_bridge a hb hK hKb hKd
  have hHK : IsCompact (Prod.fst '' (H '' K)) := (hK.image hH.continuous).image continuous_fst
  obtain ⟨A,Γ,δ,hδ,U,hU,hUK,hA,hΓ,hΓ0,hAemb,hΓprim⟩ :=
    exists_actual_radial_primitive_family a hd hHK (by
      rintro y ⟨z,⟨x,hx,rfl⟩,rfl⟩
      exact (hHD x (hKD hx)).2)
  let V : Set (LargeNormalSpace a) := D∩(fun x => (H x).1) ⁻¹' U
  have hV : IsOpen V := hD.inter (hU.preimage hH.continuous.fst)
  have hKV : K⊆V := fun x hx => ⟨hKD hx,hUK ⟨H x,⟨x,hx,rfl⟩,rfl⟩⟩
  let Δ : ℝ → ManifoldOneForm (LargeNormalModel m) (LargeNormalSpace a) :=
    manifoldPullbackOneForm (fun t => firstLinePrimitive (Γ t)) H
  have hΔ : SmoothOneFormFamily Δ :=
    manifoldPullbackOneForm_smooth hH (firstLinePrimitive_family_smooth hΓ)
  have hΔ0 (x : LargeNormalSpace a) (hx : x∈V) : Δ 0 x=largeCouplingPrimitive a x := by
    have he : firstLinePrimitive (Γ 0) (H x)=firstLinePrimitive (normalCouplingPrimitive a) (H x) := by
      apply ContinuousLinearMap.ext
      intro v
      rw [firstLinePrimitive_apply,firstLinePrimitive_apply,hΓ0 hx.2]
    change (firstLinePrimitive (Γ 0) (H x)).comp
      (manifoldMapDifferential (E := NormalModel m × Plane) (F := LargeNormalModel m) H x)=_
    rw [he]
    exact hHprim x hx.1
  have hΔext (x : LargeNormalSpace a) (hx : x∈V) :
      manifoldExteriorOneForm (Δ 0) x=manifoldExteriorOneForm (largeCouplingPrimitive a) x :=
    manifoldExteriorOneForm_congr_germ (Filter.eventually_of_mem (hV.mem_nhds hx) hΔ0)
  have hinv (x : LargeNormalSpace a) (hx : x∈K) : (manifoldExteriorOneForm (Δ 0) x).IsInvertible := by
    rw [hΔext x (hKV hx)]
    apply largeCouplingPrimitive_invertible
    have hu : 0<1-radialArea (normalHead m x.2) := sub_pos.mpr ((hKb x hx).trans hb)
    have hm := hKd x hx
    have hp := mul_pos (show 0<1-2*d by linarith) hu
    nlinarith
  let J : ℝ × LargeNormalSpace a → Affine m × Plane :=
    fun p => firstLineBaseMap (fun x => A (p.1,x)) (H p.2)
  have hJ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,LargeNormalModel m)) 𝓘(ℝ,Affine m × Plane) ∞ J :=
    by
      have hh := firstLineMoving_smooth hA
      simp +instances only [flatProduct_chartedSpace,chartedSpaceSelf_prod] at hh
      exact hh.comp (contMDiff_fst.prodMk (hH.comp contMDiff_snd))
  have hJs (t : ℝ) : ContMDiff 𝓘(ℝ,LargeNormalModel m) 𝓘(ℝ,Affine m × Plane) ∞ (fun x => J (t,x)) :=
    hJ.comp (contMDiff_const.prodMk contMDiff_id)
  have hJemb (t : ℝ) (ht : t∈Ioc (0:ℝ) δ) : Topology.IsEmbedding (fun x : V => J (t,x.val)) := by
    exact (firstLineBaseMap_isEmbedding_on (g := fun y => A (t,y)) (hAemb t ht)).comp
      ((hHemb.comp (Topology.IsEmbedding.inclusion inter_subset_left)).codRestrict
        (Prod.fst ⁻¹' U) (fun x : V => x.property.2))
  let α : ℝ → (Affine m × Plane) → (Affine m × Plane) →L[ℝ] ℝ :=
    fun t => firstLinePrimitive (normalAmbientPrimitive a (1/Real.pi) d t)
  have hα (t : ℝ) : ContDiff ℝ ∞ (α t) :=
    firstLinePrimitive_smooth (normalAmbientPrimitive_smooth a _ d t)
  have hJprim (t : ℝ) (ht : t∈Ioc (0:ℝ) δ) (x : LargeNormalSpace a) (hx : x∈V) :
      Δ t x=manifoldPullbackOneForm (fun _ => α t) (fun y => J (t,y)) 0 x := by
    have hs : ContMDiff 𝓘(ℝ,NormalModel m) 𝓘(ℝ,Affine m) ∞ (fun y => A (t,y)) :=
      hA.comp (contMDiff_const.prodMk contMDiff_id)
    have he := firstLineBaseMap_primitive_eq hs (normalAmbientPrimitive a (1/Real.pi) d t)
      (Γ t) (x := H x) (hΓprim t ht (H x).1 hx.2).symm
    simp +instances only [flatProduct_chartedSpace,chartedSpaceSelf_prod] at he
    have hc := congrArg (fun L : (NormalModel m × Plane) →L[ℝ] ℝ =>
      L.comp (manifoldMapDifferential (E := NormalModel m × Plane) (F := LargeNormalModel m) H x)) he
    have hb := firstLineBaseMap_smooth hs
    simp +instances only [flatProduct_chartedSpace,chartedSpaceSelf_prod] at hb
    have hdif := manifoldMapDifferential_comp
      (hb.mdifferentiable (by simp) (H x)) (hH.mdifferentiable (by simp) x)
    change manifoldMapDifferential (E := Affine m × Plane) (F := LargeNormalModel m)
      (fun y => J (t,y)) x=_ at hdif
    simp only [manifoldPullbackOneForm] at hc
    change (firstLinePrimitive (Γ t) (H x)).comp
      (manifoldMapDifferential (E := NormalModel m × Plane) (F := LargeNormalModel m) H x)=_
    rw [← hc,ContinuousLinearMap.comp_assoc]
    exact congrArg (fun L => (α t (J (t,x))).comp L) hdif.symm
  have hJform (t : ℝ) (ht : t∈Ioc (0:ℝ) δ) (x : LargeNormalSpace a) (hx : x∈V) :
      manifoldExteriorOneForm (Δ t) x=(euclideanExteriorOneForm (α t) (J (t,x))).bilinearComp
        (manifoldMapDifferential (E := Affine m × Plane) (F := LargeNormalModel m) (fun y => J (t,y)) x)
        (manifoldMapDifferential (E := Affine m × Plane) (F := LargeNormalModel m) (fun y => J (t,y)) x) := by
    rw [manifoldExteriorOneForm_congr_germ (Filter.eventually_of_mem (hV.mem_nhds hx) (hJprim t ht))]
    have ha' : ∀ c : Affine m × Plane, ContDiffOn ℝ ∞ (chartOneForm (α t) c)
        (extChartAt 𝓘(ℝ,Affine m × Plane) c).target := by
      intro c y _hy
      rw [show chartOneForm (α t) c=α t from funext (chartOneForm_model _ _)]
      exact (hα t).contDiffAt.contDiffWithinAt
    have he := manifold_pullback_exterior ha' (hJs t) x
    simpa only [manifoldPullbackTwoForm,manifoldExteriorOneForm_model] using he
  have hinto (t : ℝ) (_ht : t∈Ioc (0:ℝ) δ) :
      MapsTo (fun x => J (t,x)) V {y | radialArea y.2<b} :=
    fun x hx => (hHD x hx.1).1
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hginto,hgform⟩ := exists_compact_exact_fibre_embedding_into
    hΔ hK hinv hV hKV hδ hJ hJemb hinto (fun t => euclideanExteriorOneForm (α t)) hJform
  refine ⟨t,ht.1,g,W∩V,hW.inter hV,fun x hx => ⟨hKW hx,hKV hx⟩,hg,
    hgemb.comp (Topology.IsEmbedding.inclusion inter_subset_left),
    fun x hx => hginto hx.1,?_⟩
  intro x hx v w
  have he := hgform x hx.1 v w
  rw [hΔext x hx.2,largeCouplingPrimitive_exterior] at he
  exact he

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
