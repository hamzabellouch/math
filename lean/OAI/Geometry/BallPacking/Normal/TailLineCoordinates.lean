import Mathlib
import OAI.Geometry.BallPacking.Normal.MovingPrimitiveNaturality

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold

 def normalTail (q : ℕ) : PlanePhase (Fin (q+1)) →L[ℝ] PlanePhase (Fin q) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj j.succ)
 def normalHead (q : ℕ) : PlanePhase (Fin (q+1)) →L[ℝ] Plane := ContinuousLinearMap.proj 0

 def normalSplit (q : ℕ) : PlanePhase (Fin (q+1)) ≃L[ℝ] PlanePhase (Fin q) × Plane :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => (normalTail q z,normalHead q z)
      invFun := fun x => Fin.cons x.2 x.1
      left_inv := by intro z; funext j; exact Fin.cases rfl (fun _ => rfl) j
      right_inv := by intro x; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

 theorem normalSplit_liouville (q : ℕ) (z v : PlanePhase (Fin (q+1))) :
    standardLiouville z v=standardLiouville (normalTail q z) (normalTail q v)+
      linearLiouville planarArea (normalHead q z) (normalHead q v) := by
  simp only [standardLiouville,linearLiouville,smul_apply,smul_eq_mul,
    phaseArea_apply,Fin.sum_univ_succ,normalTail,normalHead,ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply,planarArea_apply]
  ring

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] {q : ℕ}

 def firstTailMap (s : PlanePhase (Fin (q+1)) → ℝ) (x : M × PlanePhase (Fin (q+1))) :
    (M × PlanePhase (Fin q)) × Plane := ((x.1,s x.2 • normalTail q x.2),normalHead q x.2)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem firstTailMap_smooth {s : PlanePhase (Fin (q+1)) → ℝ} (hs : ContDiff ℝ ∞ s) :
    ContMDiff 𝓘(ℝ,E × PlanePhase (Fin (q+1))) 𝓘(ℝ,(E × PlanePhase (Fin q)) × Plane) ∞
      (firstTailMap (M := M) s) := by
  have ht := ((hs.smul (normalTail q).contDiff).contMDiff.comp
    (flatProduct_snd_smooth (E := E) (M := M)))
  have hb : ContMDiff 𝓘(ℝ,E × PlanePhase (Fin (q+1))) 𝓘(ℝ,E × PlanePhase (Fin q)) ∞
      (fun x : M × PlanePhase (Fin (q+1)) => (x.1,s x.2 • normalTail q x.2)) := by
    rw [show 𝓘(ℝ,E × PlanePhase (Fin q))=(𝓘(ℝ,E)).prod 𝓘(ℝ,PlanePhase (Fin q)) from modelWithCornersSelf_prod]
    exact flatProduct_fst_smooth.prodMk ht
  rw [show 𝓘(ℝ,(E × PlanePhase (Fin q)) × Plane)=
    (𝓘(ℝ,E × PlanePhase (Fin q))).prod 𝓘(ℝ,Plane) from modelWithCornersSelf_prod]
  exact hb.prodMk ((normalHead q).contDiff.contMDiff.comp flatProduct_snd_smooth)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem firstTailMap_derivative {s : PlanePhase (Fin (q+1)) → ℝ} (hs : ContDiff ℝ ∞ s)
    (x : M × PlanePhase (Fin (q+1))) (v : E × PlanePhase (Fin (q+1))) :
    manifoldMapDifferential (E := (E × PlanePhase (Fin q)) × Plane)
      (F := E × PlanePhase (Fin (q+1))) (firstTailMap s) x v=
      ((v.1,fderiv ℝ (fun z => s z • normalTail q z) x.2 v.2),normalHead q v.2) := by
  have hb := (flatProduct_fst_smooth (E := E) (M := M) (V := PlanePhase (Fin (q+1)))).mdifferentiable (by simp) x
  have ht := ((hs.smul (normalTail q).contDiff).contMDiff.comp
    (flatProduct_snd_smooth (E := E) (M := M))).mdifferentiable (by simp) x
  have hh := ((normalHead q).contDiff.contMDiff.comp
    (flatProduct_snd_smooth (E := E) (M := M))).mdifferentiable (by simp) x
  have hd : HasMFDerivAt 𝓘(ℝ,E × PlanePhase (Fin (q+1)))
      𝓘(ℝ,(E × PlanePhase (Fin q)) × Plane) (firstTailMap s) x
      ((mfderiv 𝓘(ℝ,E × PlanePhase (Fin (q+1))) 𝓘(ℝ,E) Prod.fst x).prod
        (mfderiv 𝓘(ℝ,E × PlanePhase (Fin (q+1))) 𝓘(ℝ,PlanePhase (Fin q))
          (fun y : M × PlanePhase (Fin (q+1)) => s y.2 • normalTail q y.2) x) |>.prod
        (mfderiv 𝓘(ℝ,E × PlanePhase (Fin (q+1))) 𝓘(ℝ,Plane)
          (fun y : M × PlanePhase (Fin (q+1)) => normalHead q y.2) x)) := by
    rw [show 𝓘(ℝ,(E × PlanePhase (Fin q)) × Plane)=
      (𝓘(ℝ,E × PlanePhase (Fin q))).prod 𝓘(ℝ,Plane) from modelWithCornersSelf_prod]
    apply HasMFDerivAt.prodMk ?_ hh.hasMFDerivAt
    rw [show 𝓘(ℝ,E × PlanePhase (Fin q))=(𝓘(ℝ,E)).prod 𝓘(ℝ,PlanePhase (Fin q)) from modelWithCornersSelf_prod]
    exact hb.hasMFDerivAt.prodMk ht.hasMFDerivAt
  change mfderiv _ _ _ x v=_
  rw [hd.mfderiv,flatProduct_fst_derivative]
  have htD := mfderiv_comp x ((hs.smul (normalTail q).contDiff).contMDiff.mdifferentiable (by simp) x.2)
    ((flatProduct_snd_smooth (E := E) (M := M)).mdifferentiable (by simp) x)
  have hhD := mfderiv_comp x ((normalHead q).contDiff (n := ∞) |>.contMDiff.mdifferentiable (by simp) x.2)
    ((flatProduct_snd_smooth (E := E) (M := M)).mdifferentiable (by simp) x)
  erw [htD,hhD,flatProduct_snd_derivative,mfderiv_eq_fderiv,mfderiv_eq_fderiv,(normalHead q).fderiv]
  rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function
open NormalLift Hamiltonian
open scoped Manifold
open Manifold
section

variable {m : ℕ}

def regularLocus (m : ℕ) : Set (Affine m) := ⋃ c,regularCoordinate c

theorem regularLocus_isOpen (m : ℕ) : IsOpen (regularLocus m) :=
  isOpen_iUnion regularCoordinate_isOpen

theorem locus_subset_regularLocus {a : Fin m → ℂ} (ha : Injective a) (ha0 : ∀ j,a j≠0) :
    locus a⊆regularLocus m := by
  intro z hz
  obtain ⟨c,hc⟩ := exists_regularCoordinate ha ha0 hz
  exact mem_iUnion.mpr ⟨c,hc⟩

theorem regular_jacobian_surjective {z : Affine m} (hz : z∈regularLocus m) :
    Surjective (jacobian z) := by
  obtain ⟨c,hc⟩ := mem_iUnion.mp hz
  intro w
  obtain ⟨v,hv⟩ := (regularCoordinate_bijective c hc).2 (0,w)
  exact ⟨v,congrArg Prod.snd hv⟩

def realJacobian (z : Affine m) : Affine m →L[ℝ] (Fin m → ℂ) :=
  (jacobian z).restrictScalars ℝ

theorem equations_real_hasFDerivAt (a : Fin m → ℂ) (z : Affine m) :
    HasFDerivAt (equations a) (realJacobian z) z :=
  (equations_hasFDerivAt a z).restrictScalars ℝ

theorem realJacobian_contDiff :
    ContDiff ℝ ∞ (realJacobian : Affine m → Affine m →L[ℝ] (Fin m → ℂ)) := by
  have he : realJacobian (m := m)=fderiv ℝ (equations (0 : Fin m → ℂ)) :=
    funext fun z => (equations_real_hasFDerivAt 0 z).fderiv.symm
  rw [he]
  exact ((equations_contDiff 0).restrict_scalars ℝ).fderiv_right (by simp)

def normalLift (z : Affine m) : (Fin m → ℂ) →L[ℝ] Affine m :=
  finiteRightLift _ _ (realJacobian z)

theorem normalLift_projects {z : Affine m} (hz : z∈regularLocus m) (w : Fin m → ℂ) :
    realJacobian z (normalLift z w)=w :=
  finiteRightLift_right_inverse (regular_jacobian_surjective hz) w

theorem normalLift_contDiffOn :
    ContDiffOn ℝ ∞ (normalLift : Affine m → (Fin m → ℂ) →L[ℝ] Affine m) (regularLocus m) := by
  intro z hz
  exact ((finiteRightLift_contDiffAt (regular_jacobian_surjective hz)).comp z
    realJacobian_contDiff.contDiffAt).contDiffWithinAt

theorem exists_compact_normal_lift {a : Fin m → ℂ} (ha : Injective a) (ha0 : ∀ j,a j≠0)
    {K : Set (Affine m)} (hK : IsCompact K) (hKa : K⊆locus a) :
    ∃ B : Affine m → (Fin m → ℂ) →L[ℝ] Affine m,
      ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧ ∃ O : Set (Affine m),
      IsOpen O ∧ K⊆O ∧ O⊆regularLocus m ∧
      ∀ z∈O,∀ w,realJacobian z (B z w)=w := by
  obtain ⟨χ,_hχ,_hχc,_hχU,_hr,hχ1,hB,hBc,hBe⟩ := exists_smooth_compact_extension
    hK (regularLocus_isOpen m) (hKa.trans (locus_subset_regularLocus ha ha0)) normalLift_contDiffOn
  obtain ⟨O,hO,hKO,hOB⟩ := mem_nhdsSet_iff_exists.mp hBe
  refine ⟨fun z => χ z • normalLift z,hB,hBc,O∩regularLocus m,
    hO.inter (regularLocus_isOpen m),fun z hz => ⟨hKO hz,locus_subset_regularLocus ha ha0 (hKa hz)⟩,
    inter_subset_right,?_⟩
  intro z hz w
  change realJacobian z ((χ z • normalLift z) w)=w
  rw [hOB hz.1]
  exact normalLift_projects hz.2 w

end

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem exists_actual_normal_tube {K : Set (locus a)} {H : Set (Fin m → ℂ)}
    (hK : IsCompact K) (hH : IsCompact H) :
    ∃ Ψ : ℝ × (locus a × (Fin m → ℂ)) → Affine m, ∃ ε : ℝ, 0<ε ∧
      ∃ U : Set (locus a × (Fin m → ℂ)), IsOpen U ∧ K×ˢH⊆U ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,Fin m → ℂ)))
        𝓘(ℝ,Affine m) ∞ Ψ ∧
      (∀ p,Ψ (0,p)=p.1.val) ∧
      (∀ p∈U,∀ t∈Icc (-ε) ε,equations a (Ψ (t,p))=t•p.2) ∧
      ∀ t∈Icc (-ε) ε,t≠0 → Topology.IsEmbedding (fun p : U => Ψ (t,p.val)) := by
  obtain ⟨B,hB,_hBc,O,hO,hKO,_hOr,hproj⟩ := exists_compact_normal_lift
    (Fact.out : Injective a) (Fact.out : ∀ j,a j≠0)
    (hK.image continuous_subtype_val) (by rintro _ ⟨z,_hz,rfl⟩; exact z.property)
  have hdf z : fderiv ℝ (equations a) z=realJacobian z :=
    (equations_real_hasFDerivAt a z).fderiv
  obtain ⟨Φ,ε,hε,W,hW,hKW,_hWO,hΦ,hΦ0,hΦa,hparam,he,_hst,_hd⟩ :=
    exists_compact_normal_flow ((equations_contDiff a).restrict_scalars ℝ)
      hB hO (by simpa only [hdf] using hproj)
      (hK.image continuous_subtype_val) hH hKO
  let ι : locus a × (Fin m → ℂ) → Affine m × (Fin m → ℂ) := fun p => (p.1.val,p.2)
  have hι : ContMDiff ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,Fin m → ℂ))
      𝓘(ℝ,Affine m × (Fin m → ℂ)) ∞ ι := by
    apply ContMDiff.prodMk_space
    · exact (real_inclusion_contMDiff a).comp contMDiff_fst
    · exact contMDiff_snd
  let Ψ : ℝ × (locus a × (Fin m → ℂ)) → Affine m := fun p => (Φ (p.1,ι p.2)).1
  have hΨ : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,Fin m → ℂ)))
      𝓘(ℝ,Affine m) ∞ Ψ := by
    have hi : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,RealModel)).prod 𝓘(ℝ,Fin m → ℂ)))
        𝓘(ℝ,ℝ × (Affine m × (Fin m → ℂ))) ∞
        (fun p : ℝ × (locus a × (Fin m → ℂ)) => (p.1,ι p.2)) :=
      contMDiff_fst.prodMk_space (hι.comp contMDiff_snd)
    have hc := hΦ.contMDiff.comp hi
    exact (contDiff_fst.contMDiff).comp hc
  refine ⟨Ψ,ε,hε,ι ⁻¹' W,hW.preimage hι.continuous,?_,hΨ,?_,?_,?_⟩
  · intro p hp
    exact hKW ⟨⟨p.1,hp.1,rfl⟩,hp.2⟩
  · intro p
    exact congrArg Prod.fst (hΦ0 (ι p))
  · intro p hp t ht
    change equations a (Φ (t,ι p)).1=t•p.2
    rw [he _ hp _ ht]
    have hz : equations a p.1.val=0 := p.1.property
    rw [hz,zero_add]
  · intro t ht ht0
    exact tubeSlice_isEmbedding (equations_contDiff a).continuous
      hΦ.continuous hΦ0 hΦa ht0 (fun p hp => hparam p hp t ht)
      (fun p hp => he p hp t ht)

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped BigOperators
section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def normalRadial (a : ℝ) (p : PlanePhase ι × PlanePhase κ) : PlanePhase ι × PlanePhase κ :=
  (p.1,(1+phaseSq p.1) • fsAffineMap a p.2)

def normalRadialInverse (a : ℝ) (p : PlanePhase ι × PlanePhase κ) : PlanePhase ι × PlanePhase κ :=
  (p.1,fsBallMap a ((1+phaseSq p.1)⁻¹ • p.2))

theorem normalRadial_smoothOn (a : ℝ) :
    ContDiffOn ℝ ∞ (normalRadial (ι := ι) (κ := κ) a) (univ×ˢphaseOpenBall a) := by
  apply contDiffOn_fst.prodMk
  exact (contDiffOn_const.add (phaseSq_smooth.comp contDiff_fst).contDiffOn).smul
    ((fsAffineMap_smoothOn a).comp contDiffOn_snd (fun _ hp => hp.2))

theorem normalRadialInverse_smooth (a : ℝ) :
    ContDiff ℝ ∞ (normalRadialInverse (ι := ι) (κ := κ) a) := by
  apply contDiff_fst.prodMk
  exact (fsBallMap_smooth a).comp
    (((contDiff_const.add (phaseSq_smooth.comp contDiff_fst)).inv
      (fun p => (fs_den_pos p.1).ne')).smul contDiff_snd)

theorem normalRadial_leftInverse {a : ℝ} (ha : 0<a)
    {p : PlanePhase ι × PlanePhase κ} (hp : p∈univ×ˢphaseOpenBall a) :
    normalRadialInverse a (normalRadial a p)=p := by
  simp only [normalRadialInverse,normalRadial,smul_smul,inv_mul_cancel₀ (fs_den_pos p.1).ne',one_smul,
    fsBallMap_fsAffineMap ha hp.2]

theorem normalRadial_rightInverse {a : ℝ} (ha : 0<a) (p : PlanePhase ι × PlanePhase κ) :
    normalRadial a (normalRadialInverse a p)=p := by
  simp only [normalRadialInverse,normalRadial,fsAffineMap_fsBallMap ha,smul_smul,
    mul_inv_cancel₀ (fs_den_pos p.1).ne',one_smul]

theorem normalRadial_isEmbedding {a : ℝ} (ha : 0<a) :
    Topology.IsEmbedding (fun p : (univ×ˢphaseOpenBall (ι := κ) a : Set (PlanePhase ι × PlanePhase κ)) =>
      normalRadial a p.val) := by
  have hc := (normalRadial_smoothOn (ι := ι) (κ := κ) a).continuousOn.domRestrict
  have he : normalRadialInverse a ∘ (fun p : (univ×ˢphaseOpenBall (ι := κ) a : Set (PlanePhase ι × PlanePhase κ)) =>
      normalRadial a p.val)=Subtype.val := funext fun p => normalRadial_leftInverse ha p.property
  apply Topology.IsEmbedding.of_comp hc (normalRadialInverse_smooth a).continuous
  change Topology.IsEmbedding (normalRadialInverse a ∘ (fun p : (univ×ˢphaseOpenBall (ι := κ) a : Set (PlanePhase ι × PlanePhase κ)) => normalRadial a p.val))
  rw [he]
  exact Topology.IsEmbedding.subtypeVal

theorem phaseArea_radial_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : E → ℝ} {g : E → PlanePhase κ} {x : E}
    (hs : DifferentiableAt ℝ s x) (hg : DifferentiableAt ℝ g x) (v : E) :
    phaseArea (s x • g x) (fderiv ℝ (fun y => s y • g y) x v)=
      (s x)^2*phaseArea (g x) (fderiv ℝ g x v) := by
  change phaseArea (s x • g x) (fderiv ℝ (s • g) x v)=_
  rw [(hs.hasFDerivAt.smul hg.hasFDerivAt).fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,map_smul,map_add,
    smul_eq_mul,phaseArea_self,mul_zero]
  ring

theorem normalRadial_sq {a : ℝ} {p : PlanePhase ι × PlanePhase κ}
    (hp : p∈univ×ˢphaseOpenBall a) :
    phaseSq (normalRadial a p).2=(1+phaseSq p.1)^2*phaseSq p.2/(a-phaseSq p.2) := by
  rw [normalRadial,phaseSq_smul,fsAffineMap_sq hp.2]
  ring

theorem normalRadial_area {a : ℝ} {p : PlanePhase ι × PlanePhase κ}
    (hp : p∈univ×ˢphaseOpenBall a) (v : PlanePhase ι × PlanePhase κ) :
    phaseArea (normalRadial a p).2 (fderiv ℝ (fun q => (normalRadial a q).2) p v)=
      (1+phaseSq p.1)^2/(a-phaseSq p.2)*phaseArea p.2 v.2 := by
  let s : PlanePhase ι × PlanePhase κ → ℝ :=
    fun q => (1+phaseSq q.1)*(Real.sqrt (a-phaseSq q.2))⁻¹
  have hs : DifferentiableAt ℝ s p := by
    apply DifferentiableAt.mul
    · exact (contDiffAt_const.add (phaseSq_smooth.contDiffAt.comp p contDiffAt_fst)).differentiableAt (by simp)
    · exact (((contDiffAt_const.sub (phaseSq_smooth.contDiffAt.comp p contDiffAt_snd)).sqrt
        (sub_pos.mpr hp.2).ne').inv (Real.sqrt_pos.mpr (sub_pos.mpr hp.2)).ne').differentiableAt (by simp)
  have he : (fun q : PlanePhase ι × PlanePhase κ => (normalRadial a q).2)=fun q => s q • q.2 := by
    funext q
    simp only [normalRadial,fsAffineMap,smul_smul,s]
  rw [he]
  rw [show (normalRadial a p).2=s p • p.2 from congrFun he p]
  rw [phaseArea_radial_derivative hs differentiableAt_snd,fderiv_snd]
  simp only [s,mul_pow,inv_pow,Real.sq_sqrt (sub_pos.mpr hp.2).le,
    div_eq_mul_inv]
  rfl

def coneDenominator (p : PlanePhase ι × PlanePhase κ) : ℝ :=
  (1+phaseSq p.1)^2+phaseSq p.2

theorem coneDenominator_pos (p : PlanePhase ι × PlanePhase κ) : 0<coneDenominator p :=
  add_pos_of_pos_of_nonneg (sq_pos_of_pos (fs_den_pos p.1)) (phaseSq_nonneg p.2)

def conePrimitive (c d : ℝ) (p : PlanePhase ι × PlanePhase κ) :
    (PlanePhase ι × PlanePhase κ) →L[ℝ] ℝ :=
  ((1-2*d) • affineFSPrimitive c p.1).comp (ContinuousLinearMap.fst ℝ _ _)+
    (c*d/(2*coneDenominator p)) •
      ((2*(1+phaseSq p.1)) • (phaseArea p.1).comp (ContinuousLinearMap.fst ℝ _ _)+
        (phaseArea p.2).comp (ContinuousLinearMap.snd ℝ _ _))

theorem conePrimitive_apply (c d : ℝ) (p v : PlanePhase ι × PlanePhase κ) :
    conePrimitive c d p v=(1-2*d)*affineFSPrimitive c p.1 v.1+
      c*d/(2*coneDenominator p)*(2*(1+phaseSq p.1)*phaseArea p.1 v.1+phaseArea p.2 v.2) := rfl

theorem conePrimitive_smooth (c d : ℝ) :
    ContDiff ℝ ∞ (conePrimitive (ι := ι) (κ := κ) c d) := by
  have hden : ContDiff ℝ ∞ (coneDenominator : PlanePhase ι × PlanePhase κ → ℝ) :=
    ((contDiff_const.add (phaseSq_smooth.comp contDiff_fst)).pow 2).add
      (phaseSq_smooth.comp contDiff_snd)
  have hcoef : ContDiff ℝ ∞ (fun p : PlanePhase ι × PlanePhase κ => c*d/(2*coneDenominator p)) :=
    contDiff_const.div (contDiff_const.mul hden)
      (fun p => mul_ne_zero (by norm_num) (coneDenominator_pos p).ne')
  have hbase : ContDiff ℝ ∞ (fun p : PlanePhase ι × PlanePhase κ =>
      ((1-2*d) • affineFSPrimitive c p.1).comp (ContinuousLinearMap.fst ℝ (PlanePhase ι) (PlanePhase κ))) :=
    (((affineFSPrimitive_smooth (ι := ι) c).comp contDiff_fst).const_smul (1-2*d)).clm_comp contDiff_const
  have hb : ContDiff ℝ ∞ (fun p : PlanePhase ι × PlanePhase κ =>
      (phaseArea p.1).comp (ContinuousLinearMap.fst ℝ (PlanePhase ι) (PlanePhase κ))) :=
    ((phaseArea (ι := ι)).contDiff.comp contDiff_fst).clm_comp contDiff_const
  have hv : ContDiff ℝ ∞ (fun p : PlanePhase ι × PlanePhase κ =>
      (phaseArea p.2).comp (ContinuousLinearMap.snd ℝ (PlanePhase ι) (PlanePhase κ))) :=
    ((phaseArea (ι := κ)).contDiff.comp contDiff_snd).clm_comp contDiff_const
  exact hbase.add (hcoef.smul
    (((contDiff_const.mul (contDiff_const.add (phaseSq_smooth.comp contDiff_fst))).smul hb).add hv))

theorem coneDenominator_normalRadial {a : ℝ} {p : PlanePhase ι × PlanePhase κ}
    (hp : p∈univ×ˢphaseOpenBall a) :
    coneDenominator (normalRadial a p)=(1+phaseSq p.1)^2*a/(a-phaseSq p.2) := by
  have hpa : phaseSq p.2<a := hp.2
  rw [coneDenominator,normalRadial_sq hp]
  change (1+phaseSq p.1)^2+(1+phaseSq p.1)^2*phaseSq p.2/(a-phaseSq p.2)=_
  field_simp [(sub_pos.mpr hpa).ne']
  ring

theorem conePrimitive_radial_pullback {d : ℝ} (hd : 0<d)
    {p : PlanePhase ι × PlanePhase κ} (hp : p∈univ×ˢphaseOpenBall (d/Real.pi))
    (v : PlanePhase ι × PlanePhase κ) :
    conePrimitive (1/Real.pi) d (normalRadial (d/Real.pi) p)
      (fderiv ℝ (normalRadial (d/Real.pi)) p v)=
      (1-2*Real.pi*phaseSq p.2)*affineFSPrimitive (1/Real.pi) p.1 v.1+
        (1/2:ℝ)*phaseArea p.2 v.2 := by
  have hdiff := ((normalRadial_smoothOn (d/Real.pi)).contDiffAt
    ((isOpen_univ.prod (phaseOpenBall_open (d/Real.pi))).mem_nhds hp)).differentiableAt (by simp)
  have hfst : (fderiv ℝ (normalRadial (d/Real.pi)) p v).1=v.1 := by
    have hh := hdiff.hasFDerivAt.fst.fderiv
    change fderiv ℝ (Prod.fst : PlanePhase ι × PlanePhase κ → PlanePhase ι) p=_ at hh
    rw [fderiv_fst] at hh
    exact congrArg (fun L => L v) hh.symm
  have hsnd : (fderiv ℝ (normalRadial (d/Real.pi)) p v).2=
      fderiv ℝ (fun q => (normalRadial (d/Real.pi) q).2) p v :=
    congrArg (fun L => L v) hdiff.hasFDerivAt.snd.fderiv.symm
  rw [conePrimitive_apply,hfst,hsnd,normalRadial_area hp,coneDenominator_normalRadial hp]
  change (1-2*d)*affineFSPrimitive (1/Real.pi) p.1 v.1+
    (1/Real.pi)*d/(2*((1+phaseSq p.1)^2*(d/Real.pi)/(d/Real.pi-phaseSq p.2)))*
      (2*(1+phaseSq p.1)*phaseArea p.1 v.1+
        (1+phaseSq p.1)^2/(d/Real.pi-phaseSq p.2)*phaseArea p.2 v.2)=_
  have hpa : phaseSq p.2<d/Real.pi := hp.2
  have hpd : 0<d-Real.pi*phaseSq p.2 := by
    have hh := (lt_div_iff₀ Real.pi_pos).mp hpa
    nlinarith
  simp only [affineFSPrimitive,smul_apply,smul_eq_mul]
  field_simp [Real.pi_ne_zero,hd.ne',(fs_den_pos p.1).ne',(sub_pos.mpr hpa).ne',hpd.ne']
  ring

end

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 def joinedVeronese (p : (ι → ℂ) × (κ → ℂ)) : VeroneseIndex ι ⊕ κ → ℂ :=
  Sum.elim (veronese p.1) p.2

 def joinedVeroneseDerivative (p : (ι → ℂ) × (κ → ℂ)) :
    ((ι → ℂ) × (κ → ℂ)) →L[ℂ] (VeroneseIndex ι ⊕ κ → ℂ) :=
  ContinuousLinearMap.pi fun i => match i with
  | .inl j => (ContinuousLinearMap.proj j).comp
      ((veroneseDerivative p.1).comp (ContinuousLinearMap.fst ℂ _ _))
  | .inr j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ _ _)

 theorem joinedVeronese_smooth : ContDiff ℂ ∞ (joinedVeronese (ι := ι) (κ := κ)) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact (contDiff_apply ℂ ℂ i).comp (veronese_contDiff.comp contDiff_fst)
  | inr i => exact (contDiff_apply ℂ ℂ i).comp contDiff_snd

 theorem joinedVeronese_hasFDerivAt (p : (ι → ℂ) × (κ → ℂ)) :
    HasFDerivAt joinedVeronese (joinedVeroneseDerivative p) p := by
  apply hasFDerivAt_pi.mpr
  intro i
  cases i with
  | inl i =>
      exact (ContinuousLinearMap.proj i : (VeroneseIndex ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp p
        ((veronese_hasFDerivAt p.1).comp p (hasFDerivAt_fst (p := p)))
  | inr i =>
      exact (ContinuousLinearMap.proj i : (κ → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp p (hasFDerivAt_snd (p := p))

 theorem joinedVeronese_sq (p : (ι → ℂ) × (κ → ℂ)) :
    1+phaseSq (complexCartesian (joinedVeronese p))=
      (1+phaseSq (complexCartesian p.1))^2+phaseSq (complexCartesian p.2) := by
  rw [complexCartesian_sq,Fintype.sum_sum_type]
  change 1+((∑ j,Complex.normSq (veronese p.1 j))+(∑ j,Complex.normSq (p.2 j)))=_
  rw [← complexCartesian_sq,← complexCartesian_sq,← add_assoc,veronese_sq]

 theorem joinedVeronese_pairing (p v : (ι → ℂ) × (κ → ℂ)) :
    complexPairing (joinedVeronese p) (joinedVeroneseDerivative p v)=
      2*(1+complexPairing p.1 p.1)*complexPairing p.1 v.1+complexPairing p.2 v.2 := by
  change (∑ i,star (joinedVeronese p i)*(joinedVeroneseDerivative p v i))=_
  rw [Fintype.sum_sum_type]
  change complexPairing (veronese p.1) (veroneseDerivative p.1 v.1)+complexPairing p.2 v.2=_
  rw [veronese_pairing]

 theorem joinedVeronese_area (p v : (ι → ℂ) × (κ → ℂ)) :
    phaseArea (complexCartesian (joinedVeronese p))
      (complexCartesian (joinedVeroneseDerivative p v))=
      2*(1+phaseSq (complexCartesian p.1))*phaseArea (complexCartesian p.1) (complexCartesian v.1)+
        phaseArea (complexCartesian p.2) (complexCartesian v.2) := by
  rw [← complexPairing_im,joinedVeronese_pairing,complexPairing_self,complexCartesian_sq]
  simp [Complex.mul_im,complexPairing_im]

 theorem joinedVeronese_real_derivative (p : (ι → ℂ) × (κ → ℂ))
    (v : (ι → ℂ) × (κ → ℂ)) :
    fderiv ℝ (fun q => complexCartesian (joinedVeronese q)) p v=
      complexCartesian (joinedVeroneseDerivative p v) := by
  have hd := complexCartesian.toContinuousLinearMap.hasFDerivAt.comp p
    ((joinedVeronese_hasFDerivAt p).restrictScalars ℝ)
  change HasFDerivAt (fun q => complexCartesian (joinedVeronese q)) _ p at hd
  rw [hd.fderiv]
  rfl

 theorem joinedVeronese_primitive (c d : ℝ) (p v : (ι → ℂ) × (κ → ℂ)) :
    (1-2*d)*affineFSPrimitive c (complexCartesian p.1) (complexCartesian v.1)+
      d*primitivePullback (affineFSPrimitive c) (fun q => complexCartesian (joinedVeronese q)) p v=
      conePrimitive c d (complexCartesian p.1,complexCartesian p.2)
        (complexCartesian v.1,complexCartesian v.2) := by
  rw [primitivePullback,ContinuousLinearMap.comp_apply,joinedVeronese_real_derivative,
    conePrimitive_apply]
  simp only [affineFSPrimitive,smul_apply,smul_eq_mul,joinedVeronese_area]
  rw [joinedVeronese_sq]
  unfold coneDenominator
  ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

 def normalGraph (a : Fin m → ℂ) (t : ℝ) (z : Affine m) :
    (Option (Fin m) → ℂ) × (Fin m → ℂ) :=
  (affineComplex m z,fun j => (t:ℂ)⁻¹*equations a z j)

 theorem normalGraph_smooth (a : Fin m → ℂ) (t : ℝ) : ContDiff ℂ ∞ (normalGraph a t) :=
  (affineComplex m).contDiff.prodMk (contDiff_pi.mpr fun j =>
    contDiff_const.mul ((contDiff_apply ℂ ℂ j).comp (equations_contDiff a)))

 theorem normalPolynomial_eq_joined (a : Fin m → ℂ) (t : ℝ) (z : Affine m) :
    normalPolynomial a t z=joinedVeronese (normalGraph a t z) := by
  funext i
  cases i <;> rfl

 def normalConeCoordinates (a : Fin m → ℂ) (t : ℝ) (z : Affine m) :
    PlanePhase (Option (Fin m)) × PlanePhase (Fin m) :=
  (affinePhase m z,complexCartesian (normalGraph a t z).2)

 theorem normalConeCoordinates_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℝ ∞ (normalConeCoordinates a t) :=
  (affinePhase m).contDiff.prodMk
    ((complexCartesian (ι := Fin m)).contDiff.comp (((normalGraph_smooth a t).restrict_scalars ℝ).snd))

 theorem normalGraph_derivative_fst (a : Fin m → ℂ) (t : ℝ) (z v : Affine m) :
    (fderiv ℝ (normalGraph a t) z v).1=affineComplex m v := by
  have hd := (((normalGraph_smooth a t).restrict_scalars ℝ).differentiable (by simp) z).hasFDerivAt.fst.fderiv
  change fderiv ℝ (affineComplex m) z=_ at hd
  have he : fderiv ℝ (affineComplex m) z=(affineComplex m).restrictScalars ℝ :=
    (((affineComplex m).hasFDerivAt (x := z)).restrictScalars ℝ).fderiv
  rw [he] at hd
  exact congrArg (fun L => L v) hd.symm

 theorem normalConeCoordinates_derivative (a : Fin m → ℂ) (t : ℝ) (z v : Affine m) :
    fderiv ℝ (normalConeCoordinates a t) z v=
      (complexCartesian (fderiv ℝ (normalGraph a t) z v).1,
        complexCartesian (fderiv ℝ (normalGraph a t) z v).2) := by
  have hd := (((normalGraph_smooth a t).restrict_scalars ℝ).differentiable (by simp) z).hasFDerivAt
  have h₁ := (complexCartesian (ι := Option (Fin m))).toContinuousLinearMap.hasFDerivAt.comp z hd.fst
  have h₂ := (complexCartesian (ι := Fin m)).toContinuousLinearMap.hasFDerivAt.comp z hd.snd
  have hh := h₁.prodMk h₂
  have he : (fun x => (complexCartesian (normalGraph a t x).1,complexCartesian (normalGraph a t x).2))=
      normalConeCoordinates a t := by
    funext x; exact Prod.ext (complexCartesian_affineComplex x) rfl
  change HasFDerivAt (fun x => (complexCartesian (normalGraph a t x).1,
    complexCartesian (normalGraph a t x).2)) _ z at hh
  rw [he] at hh
  rw [hh.fderiv]
  rfl

 theorem normalPolynomial_derivative_joined (a : Fin m → ℂ) (t : ℝ) (z v : Affine m) :
    fderiv ℝ (fun x => complexCartesian (normalPolynomial a t x)) z v=
      fderiv ℝ (fun p => complexCartesian (joinedVeronese p)) (normalGraph a t z)
        (fderiv ℝ (normalGraph a t) z v) := by
  have hgC : ContDiff ℂ ∞ (joinedVeronese (ι := Option (Fin m)) (κ := Fin m)) :=
    joinedVeronese_smooth
  have hg : ContDiff ℝ ∞ (fun p : (Option (Fin m) → ℂ) × (Fin m → ℂ) =>
      complexCartesian (joinedVeronese p)) :=
    (complexCartesian (ι := NormalPolynomialIndex m)).contDiff.comp
      (hgC.restrict_scalars ℝ)
  have hd := (hg.differentiable (by simp) (normalGraph a t z)).hasFDerivAt.comp z
    (((normalGraph_smooth a t).restrict_scalars ℝ).differentiable (by simp) z).hasFDerivAt
  have he : (fun x => complexCartesian (normalPolynomial a t x))=
      (fun p => complexCartesian (joinedVeronese p)) ∘ normalGraph a t := by
    funext x; rw [normalPolynomial_eq_joined]; rfl
  rw [he,hd.fderiv]
  rfl

 theorem normalAmbientPrimitive_eq_cone (a : Fin m → ℂ) (c d t : ℝ) :
    normalAmbientPrimitive a c d t=primitivePullback (conePrimitive c d) (normalConeCoordinates a t) := by
  funext z
  apply ContinuousLinearMap.ext
  intro v
  have hh := joinedVeronese_primitive c d (normalGraph a t z) (fderiv ℝ (normalGraph a t) z v)
  rw [normalGraph_derivative_fst,complexCartesian_affineComplex] at hh
  simp only [normalGraph,complexCartesian_affineComplex] at hh
  change (1-2*d)*affineFSPrimitive c (affinePhase m z) (affinePhase m v)+
    d*affineFSPrimitive c (complexCartesian (joinedVeronese (normalGraph a t z)))
      (fderiv ℝ (fun p => complexCartesian (joinedVeronese p)) (normalGraph a t z)
        (fderiv ℝ (normalGraph a t) z v))=_ at hh
  change (1-2*d)*affineFSPrimitive c (affinePhase m z) (affinePhase m v)+
    d*affineFSPrimitive c (complexCartesian (normalPolynomial a t z))
      (fderiv ℝ (fun x => complexCartesian (normalPolynomial a t x)) z v)=
    conePrimitive c d (normalConeCoordinates a t z)
      (fderiv ℝ (normalConeCoordinates a t) z v)
  rw [normalPolynomial_derivative_joined,normalConeCoordinates_derivative,normalPolynomial_eq_joined,
    normalGraph_derivative_fst,complexCartesian_affineComplex]
  exact hh

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
