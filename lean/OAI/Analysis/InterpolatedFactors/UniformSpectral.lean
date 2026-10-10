import OAI.Analysis.InterpolatedFactors.Haar

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.CyclicSpectral
open MeasureTheory ProbabilityTheory Set
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (ξ : E)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

abbrev UniformAlgebra := C(Icc (0:ℝ) 1,ℂ)

def cdfMap : C(Space A,Icc (0:ℝ) 1) :=
  ⟨fun x => ⟨cdf (realMeasure A hA ξ) x,cdf_nonneg _ _,cdf_le_one _ _⟩,
    ((ProbabilityTransform.continuous_cdf (realMeasure A hA ξ)).comp
      continuous_subtype_val).subtype_mk _⟩

def uniformHom : UniformAlgebra →⋆ₐ[ℂ] (E →L[ℂ] E) :=
  (complexHom A hA).comp (ContinuousMap.compStarAlgHom' ℂ ℂ (cdfMap A hA ξ))

def uniformState (f : UniformAlgebra) : ℂ :=
  ∫ x:ℝ, f (projIcc 0 1 (by norm_num) x) ∂volume.restrict (Icc (0:ℝ) 1)

theorem uniformHom_state (f : UniformAlgebra) :
    inner ℂ ξ (uniformHom A hA ξ f ξ)=uniformState f := by
  let g : ℝ → ℂ := fun x => f (projIcc 0 1 (by norm_num) x)
  have hg : Continuous g := f.continuous.comp continuous_projIcc
  have he (x : ℝ) : g (cdf (realMeasure A hA ξ) x)=f ⟨cdf (realMeasure A hA ξ) x,
      cdf_nonneg _ _,cdf_le_one _ _⟩ := by
    dsimp only [g]
    congr 1
    exact projIcc_of_mem (by norm_num) ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have hi := integral_map (μ := measure A hA ξ) measurable_subtype_coe.aemeasurable
    (hg.comp (ProbabilityTransform.continuous_cdf (realMeasure A hA ξ))).aestronglyMeasurable
  have hj := integral_map (μ := realMeasure A hA ξ)
    (ProbabilityTransform.continuous_cdf (realMeasure A hA ξ)).aemeasurable hg.aestronglyMeasurable
  rw [ProbabilityTransform.map_cdf] at hj
  rw [uniformHom,StarAlgHom.comp_apply,← integral_complex]
  calc
    _ = ∫ x : Space A, g (cdf (realMeasure A hA ξ) x) ∂measure A hA ξ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (he x).symm
    _ = ∫ x : ℝ, g (cdf (realMeasure A hA ξ) x) ∂realMeasure A hA ξ := hi.symm
    _ = uniformState f := hj.symm

def uniformPhase : UniformAlgebra :=
  ⟨fun x => ProbabilityTransform.phase x,ProbabilityTransform.phase_continuous.comp continuous_subtype_val⟩

theorem uniformHom_phase : uniformHom A hA ξ uniformPhase=(haarUnitary A hA ξ : E →L[ℂ] E) := rfl

theorem uniformHom_mem (M : StarSubalgebra ℂ (E →L[ℂ] E))
    (hM : IsClosed (M : Set (E →L[ℂ] E))) (hAM : A∈M) (f : UniformAlgebra) :
    uniformHom A hA ξ f∈M := complexHom_mem A hA M hM hAM _
end FreeGroupFactorMain.CyclicSpectral

section
open scoped ENNReal

namespace FreeGroupFactorMain.CyclicSpectral

section
open MeasureTheory
variable {H : Type u_2} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def evaluate : C(Space A,ℝ) →ₗ[ℝ] H :=
  (((ContinuousLinearMap.apply ℂ H ξ).restrictScalars ℝ).comp (cfcL hA)).toLinearMap

 theorem evaluate_norm (f : C(Space A,ℝ)) :
    ‖evaluate A hA ξ f‖=‖ContinuousMap.toLp 2 (measure A hA ξ) ℝ f‖ := by
  have hs : ‖evaluate A hA ξ f‖^2=‖ContinuousMap.toLp 2 (measure A hA ξ) ℝ f‖^2 := by
    calc
      _ = ∫ x, (f x)^2 ∂measure A hA ξ := (integral_sq A hA ξ f).symm
      _ = inner ℝ (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f)
          (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f) := by
        rw [MeasureTheory.ContinuousMap.inner_toLp]
        congr 1
        funext x
        simp only [pow_two,RCLike.conj_to_real]
      _ = _ := real_inner_self_eq_norm_sq _
  nlinarith [norm_nonneg (evaluate A hA ξ f),norm_nonneg (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f)]

def realize : Lp ℝ 2 (measure A hA ξ) →L[ℝ] H :=
  (evaluate A hA ξ).extendOfNorm (ContinuousMap.toLp 2 (measure A hA ξ) ℝ).toLinearMap

 theorem realize_continuous (f : C(Space A,ℝ)) :
    realize A hA ξ (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f)=cfcHom hA f ξ := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange ℝ (measure A hA ξ) ℝ (p := 2) (by norm_num)
  · refine ⟨1,fun g => ?_⟩
    change ‖evaluate A hA ξ g‖ ≤ 1 * ‖ContinuousMap.toLp 2 (measure A hA ξ) ℝ g‖
    rw [one_mul,evaluate_norm]

 theorem realize_norm (f : Lp ℝ 2 (measure A hA ξ)) : ‖realize A hA ξ f‖=‖f‖ := by
  have hd := ContinuousMap.toLp_denseRange ℝ (measure A hA ξ) ℝ (p := 2) (by norm_num : (2:ℝ≥0∞)≠∞)
  refine hd.induction_on (p := fun f => ‖realize A hA ξ f‖=‖f‖) f
    (isClosed_eq ((realize A hA ξ).continuous.norm) continuous_norm) ?_
  intro q
  rw [realize_continuous]
  exact evaluate_norm A hA ξ q

def isometry : Lp ℝ 2 (measure A hA ξ) →ₗᵢ[ℝ] H where
  toLinearMap := (realize A hA ξ).toLinearMap
  norm_map' := realize_norm A hA ξ

end
section
open MeasureTheory Filter
variable {H : Type u_3} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

 theorem mul_memLp (g : C(Space A,ℝ)) (f : Lp ℝ 2 (measure A hA ξ)) :
    MemLp (fun x => g x*f x) 2 (measure A hA ξ) := by
  apply (Lp.memLp f).of_le_mul (c := ‖g‖)
  · exact g.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · exact Eventually.of_forall (fun x => by rw [norm_mul];exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _))

def multiply (g : C(Space A,ℝ)) : Lp ℝ 2 (measure A hA ξ) →L[ℝ] Lp ℝ 2 (measure A hA ξ) :=
  LinearMap.mkContinuous
  { toFun := fun f => (mul_memLp A hA ξ g f).toLp (fun x => g x*f x)
    map_add' := by
      intro f k
      apply Lp.ext
      filter_upwards [(mul_memLp A hA ξ g (f+k)).coeFn_toLp,
        (mul_memLp A hA ξ g f).coeFn_toLp,(mul_memLp A hA ξ g k).coeFn_toLp,
        Lp.coeFn_add f k,Lp.coeFn_add ((mul_memLp A hA ξ g f).toLp _) ((mul_memLp A hA ξ g k).toLp _)] with x h₁ h₂ h₃ h₄ h₅
      simp only [h₁,h₅,Pi.add_apply,h₂,h₃,h₄]
      exact mul_add _ _ _
    map_smul' := by
      intro c f
      apply Lp.ext
      filter_upwards [(mul_memLp A hA ξ g (c • f)).coeFn_toLp,
        (mul_memLp A hA ξ g f).coeFn_toLp,Lp.coeFn_smul c f,
        Lp.coeFn_smul c ((mul_memLp A hA ξ g f).toLp _)] with x h₁ h₂ h₃ h₄
      simp only [RingHom.id_apply,h₁,h₄,Pi.smul_apply,smul_eq_mul,h₂,h₃]
      ring }
  ‖g‖ (by
    intro f
    change ‖(mul_memLp A hA ξ g f).toLp (fun x => g x*f x)‖ ≤ ‖g‖ * ‖f‖
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(mul_memLp A hA ξ g f).coeFn_toLp] with x hx
    rw [hx,norm_mul]
    exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _))

 theorem multiply_ae (g : C(Space A,ℝ)) (f : Lp ℝ 2 (measure A hA ξ)) :
    multiply A hA ξ g f =ᵐ[measure A hA ξ] (fun x => g x*f x) :=
  (mul_memLp A hA ξ g f).coeFn_toLp

 theorem multiply_continuous (g f : C(Space A,ℝ)) :
    multiply A hA ξ g (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f)=
      ContinuousMap.toLp 2 (measure A hA ξ) ℝ (g*f) := by
  apply Lp.ext
  filter_upwards [multiply_ae A hA ξ g (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f),
    f.coeFn_toLp (𝕜 := ℝ) (p := 2) (measure A hA ξ),
    (g*f).coeFn_toLp (𝕜 := ℝ) (p := 2) (measure A hA ξ)] with x h₁ h₂ h₃
  rw [h₁,h₂,h₃]
  rfl

 theorem realize_multiply (g : C(Space A,ℝ)) (f : Lp ℝ 2 (measure A hA ξ)) :
    realize A hA ξ (multiply A hA ξ g f)=cfcHom hA g (realize A hA ξ f) := by
  have hd := ContinuousMap.toLp_denseRange ℝ (measure A hA ξ) ℝ (p := 2) (by norm_num : (2:ℝ≥0∞)≠∞)
  refine hd.induction_on (p := fun f => realize A hA ξ (multiply A hA ξ g f)=cfcHom hA g (realize A hA ξ f)) f (isClosed_eq ((realize A hA ξ).continuous.comp (multiply A hA ξ g).continuous)
    ((cfcHom hA g).continuous.comp (realize A hA ξ).continuous)) ?_
  intro q
  rw [multiply_continuous,realize_continuous,realize_continuous,map_mul,mul_apply_eq_comp]

 theorem realize_coordinate (f : Lp ℝ 2 (measure A hA ξ)) :
    realize A hA ξ (multiply A hA ξ ((ContinuousMap.id ℝ).restrict (spectrum ℝ A)) f)=
      A (realize A hA ξ f) := by
  rw [realize_multiply,cfcHom_id]

end
open MeasureTheory Filter
variable {H : Type u_4} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def atom (x : Space A) : Lp ℝ 2 (measure A hA ξ) :=
  indicatorConstLp 2 (measurableSet_singleton x) (measure_ne_top _ _) (1:ℝ)

 theorem atom_ae (x : Space A) :
    atom A hA ξ x =ᵐ[measure A hA ξ] ({x} : Set (Space A)).indicator (fun _ => (1:ℝ)) :=
  indicatorConstLp_coeFn

 theorem multiply_atom (x : Space A) :
    multiply A hA ξ ((ContinuousMap.id ℝ).restrict (spectrum ℝ A)) (atom A hA ξ x)=
      (x:ℝ) • atom A hA ξ x := by
  classical
  apply Lp.ext
  filter_upwards [multiply_ae A hA ξ ((ContinuousMap.id ℝ).restrict (spectrum ℝ A)) (atom A hA ξ x),
    atom_ae A hA ξ x,Lp.coeFn_smul (x:ℝ) (atom A hA ξ x)] with y h₁ h₂ h₃
  rw [h₁,h₃]
  change (y:ℝ)*atom A hA ξ x y=(x:ℝ)*atom A hA ξ x y
  rw [h₂]
  by_cases hy : y=x
  · subst y; rfl
  · simp [Set.indicator_of_notMem,hy]

 theorem realize_atom_eigen (x : Space A) :
    A (realize A hA ξ (atom A hA ξ x))=(x:ℝ) • realize A hA ξ (atom A hA ξ x) := by
  rw [← realize_coordinate,multiply_atom,map_smul]

 theorem realize_one : realize A hA ξ (ContinuousMap.toLp 2 (measure A hA ξ) ℝ (1:C(Space A,ℝ)))=ξ := by
  rw [realize_continuous,map_one,one_apply_eq_self]

 theorem realize_atom_inner (x : Space A) :
    inner ℝ ξ (realize A hA ξ (atom A hA ξ x))=(measure A hA ξ).real {x} := by
  have hm := (isometry A hA ξ).inner_map_map
    (ContinuousMap.toLp 2 (measure A hA ξ) ℝ (1:C(Space A,ℝ))) (atom A hA ξ x)
  change inner ℝ (realize A hA ξ (ContinuousMap.toLp 2 (measure A hA ξ) ℝ (1:C(Space A,ℝ))))
    (realize A hA ξ (atom A hA ξ x))=_ at hm
  rw [realize_one] at hm
  rw [hm,real_inner_comm]
  change inner ℝ (indicatorConstLp 2 (measurableSet_singleton x) (measure_ne_top _ _) (1:ℝ))
    (ContinuousMap.toLp 2 (measure A hA ξ) ℝ (1:C(Space A,ℝ)))=_
  rw [L2.inner_indicatorConstLp_one]
  calc
    _ = ∫ _ in ({x}:Set (Space A)), (1:ℝ) ∂measure A hA ξ := by
      apply setIntegral_congr_ae (measurableSet_singleton x)
      exact ((1:C(Space A,ℝ)).coeFn_toLp (𝕜 := ℝ) (p := 2) (measure A hA ξ)).mono (fun y hy _ => hy)
    _ = _ := by simp [Measure.real]

 theorem singleton_eq_zero (x : Space A)
    (he : ∀ η : H, A η=(x:ℝ) • η → inner ℝ ξ η=0) : measure A hA ξ {x}=0 := by
  have hm : (measure A hA ξ).real {x}=0 :=
    (realize_atom_inner A hA ξ x).symm.trans (he _ (realize_atom_eigen A hA ξ x))
  exact (ENNReal.toReal_eq_zero_iff _).mp hm |>.resolve_right (measure_ne_top _ _)

 theorem noAtoms (he : ∀ (r:ℝ) (η:H), A η=r • η → inner ℝ ξ η=0) :
    NullSingletonClass (measure A hA ξ) := by
  constructor
  intro x
  exact singleton_eq_zero A hA ξ x (he x)

end FreeGroupFactorMain.CyclicSpectral

end

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification MeasureTheory CyclicSpectral

instance oldBaseOp_probability (u v : ℝ) :
    IsProbabilityMeasure (measure (oldBaseOp u v (0:ℕ) 1) (oldBaseOp_selfAdjoint u v 0 1) pRoot) :=
  probability _ _ _ pRoot_norm

theorem oldBaseOp_noAtoms (u v : ℝ) (hv : 0<v) (hvu : v<u) :
    NullSingletonClass (measure (oldBaseOp u v (0:ℕ) 1) (oldBaseOp_selfAdjoint u v 0 1) pRoot) := by
  let : InnerProductSpace ℝ (PRange ℕ) := InnerProductSpace.rclikeToReal ℂ (PRange ℕ)
  apply noAtoms
  intro r η hη
  have he : oldBaseOp u v (0:ℕ) 1 η=(r:ℂ) • η := by
    exact hη.trans (by
      apply Subtype.ext
      apply Subtype.ext
      funext w
      change r • (η:H ℕ) w=(r:ℂ)*(η:H ℕ) w
      exact Complex.real_smul)
  have hh := oldBaseOp_eigen_root_zero u v hv hvu (0:ℕ) 1 (r:ℂ) η he
  change (inner ℂ (pRoot:PRange ℕ) η).re=0
  rw [hh,Complex.zero_re]

variable (u v : ℝ)

def weightedUniform (hv : 0<v) (hvu : v<u) : UniformAlgebra →⋆ₐ[ℂ] (PRange ℕ →L[ℂ] PRange ℕ) := by
  letI := oldBaseOp_noAtoms u v hv hvu
  exact uniformHom (oldBaseOp u v (0:ℕ) 1) (oldBaseOp_selfAdjoint u v 0 1) pRoot

def representedBase : StarSubalgebra ℂ (PRange ℕ →L[ℂ] PRange ℕ) :=
  (Base u v).comap (pRepresentation (ι := ℕ)).symm.toStarAlgHom

theorem pRepresentation_symm_val (T : PRange ℕ →L[ℂ] PRange ℕ) :
    ((pRepresentation (ι := ℕ)).symm T : Operator ℕ)=
      (PRange ℕ).subtypeL.comp (T.comp pProject) := by
  apply ContinuousLinearMap.ext
  intro ξ
  have he := pRepresentation_apply ((pRepresentation (ι := ℕ)).symm T) (pProject ξ)
  rw [StarAlgEquiv.apply_symm_apply,pProject_val] at he
  have hr := DFunLike.congr_fun ((pRepresentation (ι := ℕ)).symm T).property.2 ξ
  exact hr.symm.trans he.symm

theorem pRepresentation_symm_coe_continuous :
    Continuous (fun T : PRange ℕ →L[ℂ] PRange ℕ => ((pRepresentation (ι := ℕ)).symm T : Operator ℕ)) := by
  simp_rw [pRepresentation_symm_val]
  exact continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

theorem representedBase_closed : IsClosed (representedBase u v : Set (PRange ℕ →L[ℂ] PRange ℕ)) := by
  have hF : IsClosed (filledEdgeAlgebra u v (0:ℕ) 1 : Set (Operator ℕ)) := Set.isClosed_centralizer _
  exact hF.preimage pRepresentation_symm_coe_continuous

theorem oldBaseOp_mem_representedBase (hv : 0<v) (hvu : v<u) : oldBaseOp u v (0:ℕ) 1∈representedBase u v := by
  change ((pRepresentation (ι := ℕ)).symm (pRepresentation (oldBaseCorner u v 0 1)))∈Base u v
  rw [StarAlgEquiv.symm_apply_apply]
  exact diffuseBase_le_filled u v (hv.trans hvu).ne' (0:ℕ) 1 (oldBaseGenerator_mem_diffuseBase u v 0 1)

theorem weightedUniform_mem (hv : 0<v) (hvu : v<u) (a : UniformAlgebra) : weightedUniform u v hv hvu a∈representedBase u v := by
  let := oldBaseOp_noAtoms u v hv hvu
  exact uniformHom_mem _ _ _ _ (representedBase_closed u v) (oldBaseOp_mem_representedBase u v hv hvu) a

def weightedUniformBase (hv : 0<v) (hvu : v<u) : UniformAlgebra →⋆ₐ[ℂ] Base u v :=
  (((pRepresentation (ι := ℕ)).symm.toStarAlgHom).comp (weightedUniform u v hv hvu)).codRestrict
    (Base u v) (fun a => by
      simpa only [representedBase, StarSubalgebra.mem_comap, StarAlgHom.comp_apply] using
        (weightedUniform_mem u v hv hvu a))

theorem weightedUniform_state (hv : 0<v) (hvu : v<u) (a : UniformAlgebra) :
    inner ℂ (pRoot:PRange ℕ) (weightedUniform u v hv hvu a pRoot)=uniformState a := by
  let := oldBaseOp_noAtoms u v hv hvu
  exact uniformHom_state _ _ _ a

end

open FreeFock Amplification
variable {ι : Type u_5} [DecidableEq ι]

theorem pRepresentation_vacuumTrace (u v : ℝ) (hu : u≠0) (x : PCorner ι) :
    pVacuumTrace u v (x:Operator ι)=inner ℂ (pRoot:PRange ι) (pRepresentation x pRoot) := by
  have he : inner ℂ ((P:Operator ι) (vacuum u v)) ((x:Operator ι) (P (vacuum u v)))=
      vacuumTrace u v (x:Operator ι) := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (vacuum u v) ((star (P:Operator ι)*(x:Operator ι)*P : Operator ι) (vacuum u v))=_
    rw [projection_P.isSelfAdjoint.star_eq,x.property.1,x.property.2]
    rfl
  rw [pRoot_vacuum u v, map_smul,inner_smul_left,inner_smul_right] at he
  rw [pVacuumTrace,← he]
  change (u:ℂ)⁻¹*(u:ℂ)⁻¹*(star (u:ℂ)*((u:ℂ)*inner ℂ ((pRoot:PRange ι):H ι)
    ((x:Operator ι) ((pRoot:PRange ι):H ι))))=_
  rw [Complex.star_def,Complex.conj_ofReal]
  have hu' := Complex.ofReal_ne_zero.mpr hu
  calc
    _ = inner ℂ ((pRoot:PRange ι):H ι) ((x:Operator ι) ((pRoot:PRange ι):H ι)) := by field_simp
    _ = _ := by rw [← pRepresentation_apply]; rfl

theorem pAnnihilator_root (u v : ℝ) (hu : u≠0) (X : PCorner ℕ)
    (hX : X∈oldAnnihilators u v) (a : Base u v) :
    star (pRepresentation X) (pRepresentation a.val pRoot)=0 := by
  have hr (x : PCorner ℕ) : (x:Operator ℕ) (vacuum u v)=(u:ℂ) • (x:Operator ℕ) ((pRoot:PRange ℕ):H ℕ) := by
    have he := DFunLike.congr_fun x.property.2 (vacuum u v)
    change (x:Operator ℕ) (P (vacuum u v))=(x:Operator ℕ) (vacuum u v) at he
    rw [pRoot_vacuum,map_smul] at he
    exact he.symm
  have hh := hX a
  rw [hr,map_smul] at hh
  have hz : star (X:Operator ℕ) ((a.val:Operator ℕ) ((pRoot:PRange ℕ):H ℕ))=0 :=
    (smul_eq_zero.mp hh).resolve_left (Complex.ofReal_ne_zero.mpr hu)
  have he := (pRepresentation (ι := ℕ)).map_star' X
  change pRepresentation (star X)=star (pRepresentation X) at he
  rw [← he]
  apply Subtype.ext
  change (pRepresentation (star X) (pRepresentation a.val pRoot) : H ℕ)=0
  rw [pRepresentation_apply,pRepresentation_apply]
  exact hz
end FreeGroupFactorMain.WeightedFock

end

end OAI
