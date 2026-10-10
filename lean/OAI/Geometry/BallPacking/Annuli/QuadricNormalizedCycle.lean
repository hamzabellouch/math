import Mathlib
import OAI.Geometry.BallPacking.Annuli.QuadricCylinderChart

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

variable (m : ℕ)

def unitTransverseCycle (t : ℝ) : Surface m := transverseCycle m (2*Real.pi*t-Real.pi/2)

theorem unitTransverseCycle_smooth :
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,RealModel) ∞ (unitTransverseCycle m) :=
  (transverseCycle_smooth m).comp ((contDiff_const.mul contDiff_id).sub contDiff_const).contMDiff

theorem unitTransverseCycle_periodic : Periodic (unitTransverseCycle m) 1 := by
  intro t
  change transverseCycle m (2*Real.pi*(t+1)-Real.pi/2)=_
  rw [show 2*Real.pi*(t+1)-Real.pi/2=(2*Real.pi*t-Real.pi/2)+2*Real.pi by ring]
  exact transverseCycle_periodic m _

theorem unitTransverseCycle_pullback (t : ℝ) :
    curveOneForm (compactDualForm m) (unitTransverseCycle m) t=
      (2*Real.pi)*dualAlongCycle m (2*Real.pi*t-Real.pi/2) := by
  let h : ℝ → ℝ := fun t => 2*Real.pi*t-Real.pi/2
  have hd : HasDerivAt h (2*Real.pi) t := by
    simpa only [h,id_eq,mul_one] using ((hasDerivAt_id t).const_mul (2*Real.pi)).sub_const (Real.pi/2)
  have he := mfderiv_comp t ((transverseCycle_smooth m).mdifferentiableAt (by simp))
    (hasMFDerivAt_iff_hasFDerivAt.mpr hd.hasFDerivAt).mdifferentiableAt
  have he' := congrArg (fun D : ℝ →L[ℝ] RealModel => D 1) he
  have hh : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) h t 1=2*Real.pi := by
    have hh := congrArg (fun D : ℝ →L[ℝ] ℝ => D 1)
      (mfderiv_eq_fderiv (f := h) (x := t))
    have hh' : fderiv ℝ h t 1=2*Real.pi := by
      rw [hd.hasFDerivAt.fderiv]
      simp
    exact hh.trans hh'
  change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,RealModel) (transverseCycle m ∘ h) t 1=
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,RealModel) (transverseCycle m) (h t)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) h t 1) at he'
  rw [hh] at he'
  change (compactDualForm m (transverseCycle m (h t)))
    ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,RealModel) (transverseCycle m ∘ h) t) 1)=_
  rw [he']
  let L : ℝ →L[ℝ] ℝ := (compactDualForm m (transverseCycle m (h t))).comp
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,RealModel) (transverseCycle m) (h t))
  change L (2*Real.pi) = (2*Real.pi)*L 1
  simpa only [smul_eq_mul, mul_one] using L.map_smul (2*Real.pi) (1:ℝ)

theorem compactDualForm_unit_period :
    ∫ t in (0:ℝ)..1,curveOneForm (compactDualForm m) (unitTransverseCycle m) t=1 := by
  simp_rw [unitTransverseCycle_pullback,sub_eq_add_neg]
  rw [intervalIntegral.integral_const_mul]
  change (2*Real.pi) • (∫ t in (0:ℝ)..1,dualAlongCycle m (2*Real.pi*t+ -(Real.pi/2)))=1
  rw [intervalIntegral.smul_integral_comp_mul_add]
  simpa only [dualAlongCycle,mul_zero,zero_add,mul_one,
    show 2*Real.pi+ -(Real.pi/2)=Real.pi+Real.pi/2 by ring] using compactDualForm_period m

theorem compactDualForm_not_exact : ¬∃ f : Surface m → ℝ,
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ f ∧
      manifoldScalarDifferential (E := RealModel) f=compactDualForm m := by
  rintro ⟨f,hf,he⟩
  have hs := (hf.comp (unitTransverseCycle_smooth m)).contDiff
  have hd : ∀ t,HasDerivAt (f ∘ unitTransverseCycle m)
      (curveOneForm (compactDualForm m) (unitTransverseCycle m) t) t := by
    intro t
    rw [← he,curveOneForm_scalar hf (unitTransverseCycle_smooth m)]
    exact (hs.differentiable (by simp) t).hasDerivAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((curveOneForm_smooth (compactDualForm_smooth m) (unitTransverseCycle_smooth m)).continuous.intervalIntegrable 0 1)
  rw [compactDualForm_unit_period] at hi
  have hp := unitTransverseCycle_periodic m 0
  simp only [zero_add] at hp
  simp only [Function.comp_apply,hp,sub_self] at hi
  exact one_ne_zero hi

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem curveOneForm_affine {α : ManifoldOneForm E M} {q : ℝ → M}
    (hq : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ q) (a b t : ℝ) :
    curveOneForm α (fun s => q (a*s+b)) t=a*curveOneForm α q (a*t+b) := by
  let h : ℝ → ℝ := fun s => a*s+b
  have hd : HasDerivAt h a t := by
    simpa only [h,id_eq,mul_one] using ((hasDerivAt_id t).const_mul a).add_const b
  have he := mfderiv_comp t (hq.mdifferentiableAt (by simp))
    (hasMFDerivAt_iff_hasFDerivAt.mpr hd.hasFDerivAt).mdifferentiableAt
  have he' := congrArg (fun D : ℝ →L[ℝ] E => D 1) he
  have hh : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) h t 1=a := by
    have hh := congrArg (fun D : ℝ →L[ℝ] ℝ => D 1)
      (mfderiv_eq_fderiv (f := h) (x := t))
    have hh' : fderiv ℝ h t 1=a := by
      rw [hd.hasFDerivAt.fderiv]
      simp
    exact hh.trans hh'
  change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (q ∘ h) t 1=
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) q (h t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) h t 1) at he'
  rw [hh] at he'
  change α (q (h t)) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (q ∘ h) t 1)=_
  rw [he']
  let L : ℝ →L[ℝ] ℝ := (α (q (h t))).comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) q (h t))
  change L a = a * L 1
  simpa only [smul_eq_mul, mul_one] using L.map_smul a (1:ℝ)

theorem curveOneForm_periodic {α : ManifoldOneForm E M} {q : ℝ → M}
    (hq : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ q) {T : ℝ} (hp : Periodic q T) :
    Periodic (curveOneForm α q) T := by
  have he : (fun s => q (1*s+T))=q := by ext s; simp only [one_mul,hp s]
  intro t
  have hd := curveOneForm_affine (α := α) hq 1 T t
  rw [he,one_mul,one_mul] at hd
  exact hd.symm

theorem curveOneForm_period_integral {α : ManifoldOneForm E M} {q : ℝ → M}
    (hq : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ q) {T : ℝ} (hp : Periodic q T) (b c : ℝ) :
    (∫ t in b..b+T,curveOneForm α q t)=(∫ t in c..c+T,curveOneForm α q t) := by
  exact (curveOneForm_periodic hq hp).intervalIntegral_add_eq _ _

end

theorem cylinderFormB_curve (α : ℝ → ManifoldOneForm CylinderModel HandleCylinder)
    (p a t : ℝ) : cylinderFormB α (p,(a,t))=
      curveOneForm (α p) (fun s => (a,circleTurn s)) t := by
  let j : ℝ → Plane := fun s => (a,s)
  have hj : HasFDerivAt j (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    (hasFDerivAt_const a t).prodMk (hasFDerivAt_id t)
  have hg := ((cylinderCover_smooth.mdifferentiableAt (by simp)).hasMFDerivAt.comp t
    (hasMFDerivAt_iff_hasFDerivAt.mpr hj)).mfderiv
  change α p (a,circleTurn t)
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (a,t) (0,1))=
    α p (a,circleTurn t)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CylinderModel) (cylinderCover ∘ j) t 1)
  rw [hg]
  rfl

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem curveOneForm_parameter_pullback (α : ℝ → ManifoldOneForm E M)
    {g : N → M} {q : ℝ → N} {t p : ℝ}
    (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g (q t))
    (hq : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,F) q t) :
    curveOneForm (parameterManifoldPullbackOneForm (E := E) (F := F) α g p) q t=
      curveOneForm (α p) (g ∘ q) t := by
  have hd := mfderiv_comp t hg hq
  change α p (g (q t)) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g (q t)
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F) q t 1))=
    α p (g (q t)) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (g ∘ q) t 1)
  rw [hd]
  rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

variable (m : ℕ)

theorem transverseCycle_Acoordinate (θ : ℝ) :
    transverseCoordinate m (transverseCycle m θ).val=(Circle.exp θ : ℂ) := by
  change (Real.cos θ : ℂ)+Complex.I*(Real.sin θ : ℂ)=_
  rw [Circle.coe_exp,Complex.exp_mul_I]
  rw [← Complex.ofReal_cos,← Complex.ofReal_sin,mul_comm Complex.I]

theorem transverseCycle_transverseBranch (θ : ℝ) :
    transverseCycle m θ∈transverseBranch m := by
  refine ⟨?_,?_⟩
  · rw [transverseCycle_Acoordinate]
    exact unitCircle_subset_transverseDomain m (Circle.norm_coe _)
  · intro j hj
    change 0<(if j=0 then Complex.I*(Real.sin θ : ℂ)
      else Complex.I*(Real.sqrt ((j.val : ℝ)+1-Real.cos θ^2) : ℂ)).im
    simp only [ite_eq_right hj,Complex.mul_im,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,zero_add,Complex.ofReal_re]
    apply Real.sqrt_pos.mpr
    have hjp : 0<(j.val : ℝ) := by exact_mod_cast Fin.pos_iff_ne_zero.mpr hj
    nlinarith [Real.cos_sq_le_one θ]

theorem transverseCylinder_core_cycle (t : ℝ) :
    transverseCylinder m (0,circleTurn t)=transverseCycle m (2*Real.pi*t) := by
  have he := (transverseAnnulusChart m).left_inv (transverseCycle_transverseBranch m (2*Real.pi*t))
  change transverseAnnulusInverse m (transverseCoordinate m (transverseCycle m (2*Real.pi*t)).val)=_ at he
  rw [transverseCycle_Acoordinate] at he
  simpa only [transverseCylinder_apply,cylinderComplexMap,Real.exp_zero,
    Complex.ofReal_one,one_mul,circleTurn] using he

def cylinderDualForm : ℝ → ManifoldOneForm CylinderModel HandleCylinder :=
  parameterManifoldPullbackOneForm (fun _ : ℝ => compactDualForm m) (transverseCylinder m)

theorem cylinderDualForm_B (p t : ℝ) :
    cylinderFormB (cylinderDualForm m) (p,(0,t))=
      curveOneForm (compactDualForm m) (fun s => transverseCylinder m (0,circleTurn s)) t := by
  rw [cylinderFormB_curve]
  exact curveOneForm_parameter_pullback (fun _ : ℝ => compactDualForm m)
    ((transverseCylinder m).mdifferentiableAt (by simp) (transverseCylinder_core m _))
    ((cylinderCover_smooth.comp ((contDiff_const.prodMk contDiff_id).contMDiff)).mdifferentiableAt (by simp))

theorem cylinderDualForm_period (p : ℝ) : cylinderFormPeriod 0 (cylinderDualForm m) p=1 := by
  unfold cylinderFormPeriod annularMean
  simp_rw [cylinderDualForm_B]
  have he : (fun s => transverseCylinder m (0,circleTurn s))=
      (fun s => transverseCycle m (2*Real.pi*s+0)) := by
    funext s
    rw [add_zero]
    exact transverseCylinder_core_cycle m s
  rw [he]
  simp_rw [curveOneForm_affine (transverseCycle_smooth m),add_zero]
  rw [intervalIntegral.integral_const_mul]
  change (2*Real.pi) • (∫ t in (0:ℝ)..1,
    curveOneForm (compactDualForm m) (transverseCycle m) (2*Real.pi*t))=1
  rw [intervalIntegral.smul_integral_comp_mul_left]
  simp only [mul_zero,mul_one]
  have hp := curveOneForm_period_integral (α := compactDualForm m)
    (transverseCycle_smooth m) (transverseCycle_periodic m) 0 (-(Real.pi/2))
  rw [zero_add,show -(Real.pi/2)+2*Real.pi=Real.pi+Real.pi/2 by ring] at hp
  rw [hp]
  exact compactDualForm_period m

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem annularCylinderScalar_joint_smoothOn {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => F (p,(s,t))) 1) :
    ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × HandleCylinder => annularCylinderScalar F q.1 q.2)
      (V ×ˢ (I ×ˢ univ)) := by
  have hfst : ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞
      (Prod.fst : HandleCylinder → ℝ) := by
    rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
      modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hparam : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel)) 𝓘(ℝ,P) ∞
      (Prod.fst : P × HandleCylinder → P) := contMDiff_fst
  have hbase : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel)) 𝓘(ℝ,CylinderModel) ∞
      (Prod.snd : P × HandleCylinder → HandleCylinder) := contMDiff_snd
  have hpair : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel)) 𝓘(ℝ,P × ℝ) ∞
      (fun q : P × HandleCylinder => (q.1,q.2.1)) := by
    exact (contMDiff_prod_module_iff _).2 ⟨hparam,hfst.comp hbase⟩
  have hmap : ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel))
      ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) ∞
      (fun q : P × HandleCylinder => ((q.1,q.2.1),q.2.2)) :=
    hpair.prodMk (cylinder_snd_smooth.comp hbase)
  exact (annularScalarDescent_smoothOn hV hI hF hper).comp hmap.contMDiffOn
    (fun _ hq => ⟨⟨hq.1,hq.2.1⟩,hq.2.2⟩)

variable [FiniteDimensional ℝ P]

theorem normalizedAnnularPrimitive_cylinder_joint_smoothOn {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I) {A B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ)))
    (hβ : ContDiff ℝ ∞ β) (hpβ : Periodic β 1)
    (hβint : (∫ t in (0:ℝ)..1,β t)=1)
    (hpA : ∀ p∈V,∀ s∈I,Periodic (fun t => A (p,(s,t))) 1)
    (hpB : ∀ p∈V,∀ s∈I,Periodic (fun t => B (p,(s,t))) 1)
    (hclosed : ∀ p∈V,∀ s∈I,∀ t,
      fderiv ℝ (fun z => A (p,z)) (s,t) (0,1)=
      fderiv ℝ (fun z => B (p,z)) (s,t) (1,0)) :
    ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × HandleCylinder =>
        annularCylinderScalar (normalizedAnnularPrimitive a A B β) q.1 q.2)
      (V ×ˢ (I ×ˢ univ)) := by
  obtain ⟨hF,hper,_⟩ := annular_normalization hV hI hc ha hA hB hβ hpβ hβint hpA hpB hclosed
  exact annularCylinderScalar_joint_smoothOn hV hI hF hper

end
section

variable {P : Type} {E G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace G N]

theorem manifoldScalarDifferential_comp_at {f : N → ℝ} {e : M → N} {x : M}
    (hf : ContMDiffAt 𝓘(ℝ,G) 𝓘(ℝ,ℝ) ∞ f (e x))
    (he : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ e x) :
    manifoldScalarDifferential (E := E) (f ∘ e) x=
      (manifoldScalarDifferential (E := G) f (e x)).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) e x) :=
  mfderiv_comp x (hf.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))

theorem annularCylinderScalar_family_pullback_smoothOn {V : Set P} {I : Set ℝ} {U : Set M}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => F (p,(s,t))) 1)
    {e : M → HandleCylinder} (he : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) ∞ e U)
    (hmem : ∀ x∈U,(e x).1∈I) :
    ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun q : P × M => annularCylinderScalar F q.1 (e q.2)) (V ×ˢ U) := by
  have hg : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E))
      ((𝓘(ℝ,P)).prod 𝓘(ℝ,CylinderModel)) ∞
      (fun q : P × M => (q.1,e q.2)) (V ×ˢ U) :=
    contMDiffOn_fst.prodMk (he.comp contMDiffOn_snd (fun _ hq => hq.2))
  exact (annularCylinderScalar_joint_smoothOn hV hI hF hper).comp hg
    (fun q hq => ⟨hq.1,hmem q.2 hq.2,mem_univ _⟩)

theorem annularCylinderScalar_pullback_differential {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => F (p,(s,t))) 1)
    {e : M → HandleCylinder} {x : M}
    (he : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) ∞ e x)
    {p : P} (hp : p∈V) (hx : (e x).1∈I) (v : E) :
    manifoldScalarDifferential (E := E) (fun y => annularCylinderScalar F p (e y)) x v=
      fderiv ℝ (fun z => F (p,z)) ((e x).1,shortCircleArgument (e x).2)
        ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e x v).1,
          circleAngular (e x).2 (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e x v).2) := by
  have hd := manifoldScalarDifferential_comp_at (E := E) (G := CylinderModel)
    (f := annularCylinderScalar F p) (e := e)
    (annularCylinderScalar_smoothAt hV hI hF hper hp (z := e x) hx) he
  change (manifoldScalarDifferential (E := E) (annularCylinderScalar F p ∘ e) x) v=_
  rw [hd]
  let q : Plane := ((e x).1,shortCircleArgument (e x).2)
  let w : CylinderModel := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e x v
  have hq : cylinderCover q=e x := by
    apply Prod.ext
    · rfl
    · exact circleTurn_shortCircleArgument (e x).2
  let u : Plane := (w.1,circleAngular (circleTurn q.2) w.2)
  have hL : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q u=w :=
    cylinderCover_derivative_right_inverse q w
  have hc := annularCylinderScalar_differential_cover hV hI hF hper hp (q := q) hx u
  rw [hL,hq] at hc
  have ht : circleTurn q.2=(e x).2 := congrArg Prod.snd hq
  dsimp only [u] at hc
  rw [ht] at hc
  convert hc using 1
  rfl

end

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

theorem exists_closed_annular_coordinate_potential {V : Set P} {I : Set ℝ} {U : Set M}
    (hV : IsOpen V) (hI : IsOpen I) (hU : IsOpen U) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I)
    {α : P → ManifoldOneForm CylinderModel HandleCylinder}
    {A B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ)))
    (hβ : ContDiff ℝ ∞ β) (hpβ : Periodic β 1)
    (hβint : (∫ t in (0:ℝ)..1,β t)=1)
    (hpA : ∀ p∈V,∀ s∈I,Periodic (fun t => A (p,(s,t))) 1)
    (hpB : ∀ p∈V,∀ s∈I,Periodic (fun t => B (p,(s,t))) 1)
    (hα : ∀ p∈V,∀ q : Plane,q.1∈I → ContDiffAt ℝ ∞
      (chartOneForm (α p) (cylinderCover q))
      (extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q) (cylinderCover q)))
    (hclosed : ∀ p∈V,∀ z : HandleCylinder,z.1∈I → manifoldExteriorOneForm (α p) z=0)
    (hrep : ∀ p∈V,∀ q : Plane,q.1∈I →
      euclideanPullbackOneForm (fun _ => α p) cylinderCover (0,q)=
        planarCovector (A (p,q)) (B (p,q)))
    {e : M → HandleCylinder} (he : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) ∞ e U)
    (hmem : ∀ x∈U,(e x).1∈I) :
    ∃ F : P × M → ℝ,
      ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ U) ∧
      ∀ p∈V,∀ x∈U,∀ v : E,
        manifoldScalarDifferential (E := E) (fun y => F (p,y)) x v=
          α p (e x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e x v)-
            annularMean a B p*circlePeriodicDescent β (e x).2*
              circleAngular (e x).2 (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e x v).2 := by
  have hcurl : ∀ p∈V,∀ s∈I,∀ t,
      fderiv ℝ (fun z => A (p,z)) (s,t) (0,1)=
      fderiv ℝ (fun z => B (p,z)) (s,t) (1,0) := by
    intro p hp s hs t
    exact closed_cylinder_cover_equation hI
      (hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩))
      (hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩))
      (hα p hp) (hclosed p hp) (hrep p hp) hs
  obtain ⟨hF,hper,_⟩ := annular_normalization hV hI hc ha hA hB hβ hpβ hβint hpA hpB hcurl
  obtain ⟨_,hFd⟩ := closed_cylinder_normalized_potential hV hI hc ha hA hB
    hβ hpβ hβint hpA hpB hα hclosed hrep
  refine ⟨fun q => annularCylinderScalar (normalizedAnnularPrimitive a A B β) q.1 (e q.2),
    annularCylinderScalar_family_pullback_smoothOn hV hI hF hper he hmem,?_⟩
  intro p hp x hx v
  have hd := manifoldScalarDifferential_comp_at
    (annularCylinderScalar_smoothAt hV hI hF hper hp (hmem x hx))
    (he.contMDiffAt (hU.mem_nhds hx))
  change (manifoldScalarDifferential (E := E)
    (annularCylinderScalar (normalizedAnnularPrimitive a A B β) p ∘ e) x) v=_
  rw [hd]
  exact hFd p hp (e x) (hmem x hx) _

theorem exists_intrinsic_annular_coordinate_potential
    {V : Set P} {I : Set ℝ} {U : Set M}
    (hV : IsOpen V) (hI : IsOpen I) (hU : IsOpen U) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I)
    {α : P → ManifoldOneForm CylinderModel HandleCylinder}
    (hα : ∀ p∈V,∀ z : HandleCylinder,z.1∈I → ContDiffAt ℝ ∞
      (fun q : P × CylinderModel => chartOneForm (α q.1) z q.2)
      (p,extChartAt 𝓘(ℝ,CylinderModel) z z))
    (hclosed : ∀ p∈V,∀ z : HandleCylinder,z.1∈I → manifoldExteriorOneForm (α p) z=0)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfint : (∫ t in (0:ℝ)..1,f (circleTurn t))=1)
    {e : M → HandleCylinder} (he : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) ∞ e U)
    (hmem : ∀ x∈U,(e x).1∈I) :
    ∃ F : P × M → ℝ,
      ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ U) ∧
      ∀ p∈V,∀ x∈U,∀ v : E,
        manifoldScalarDifferential (E := E) (fun y => F (p,y)) x v=
          α p (e x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e x v)-
            cylinderFormPeriod a α p*f (e x).2*
              circleAngular (e x).2 (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e x v).2 := by
  have hβ : ContDiff ℝ ∞ (f ∘ circleTurn) := (hf.comp circleTurn_smooth).contDiff
  have hpβ : Periodic (f ∘ circleTurn) 1 := fun t => congrArg f (circleTurn_period_one t)
  have hα' : ∀ p∈V,∀ q : Plane,q.1∈I → ContDiffAt ℝ ∞
      (chartOneForm (α p) (cylinderCover q))
      (extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q) (cylinderCover q)) := by
    intro p hp q hq
    exact (hα p hp (cylinderCover q) hq).comp _ (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨F,hF,hd⟩ := exists_closed_annular_coordinate_potential hV hI hU hc ha
    (cylinderForm_coefficients_smooth hα).1 (cylinderForm_coefficients_smooth hα).2
    hβ hpβ hfint
    (fun p _ s _ => (cylinderForm_coefficients_periodic α p s).1)
    (fun p _ s _ => (cylinderForm_coefficients_periodic α p s).2)
    hα' hclosed (fun p _ q _ => cylinderForm_rep α p q) he hmem
  refine ⟨F,hF,?_⟩
  intro p hp x hx v
  simpa only [cylinderFormPeriod,circlePeriodicDescent,Function.comp_apply,
    circleTurn_shortCircleArgument] using hd p hp x hx v

end PackingSufficiencySupport.Hamiltonian
end

end OAI
