import OAI.Analysis.ModularRecovery.CanonicalGraph

namespace OAI

/-! Real continuous functional calculus and canonical polar operators. -/

universe u uE u𝕜

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

omit [CompleteSpace H] in
def realRestriction : (H →L[ℂ] H) →ₐ[ℝ] (H →L[ℝ] H) where
  toFun := ContinuousLinearMap.restrictScalars ℝ
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' r := by ext x; rfl

omit [CompleteSpace H] in
@[simp] lemma realRestriction_apply (a : H →L[ℂ] H) (x : H) : realRestriction a x = a x := rfl

omit [CompleteSpace H] in
lemma realRestriction_continuous : Continuous (realRestriction (H := H)) :=
  ContinuousLinearMap.continuous_restrictScalars ℝ

lemma realRestriction_star (a : H →L[ℂ] H) :
    star (realRestriction a) = realRestriction (star a) := by
  ext x
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  change (inner ℂ (a y) x).re = (inner ℂ y (star a x)).re
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

lemma realRestriction_selfAdjoint {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (realRestriction a) := by
  change star (realRestriction a) = realRestriction a
  rw [realRestriction_star,ha.star_eq]

lemma realRestriction_cfcHom_commute (a : H →L[ℂ] H) (ha : IsSelfAdjoint a)
    (b : H →L[ℝ] H) (hab : Commute (realRestriction a) b)
    (f : C(spectrum ℝ a,ℝ)) : Commute (realRestriction (cfcHom ha f)) b := by
  let F : C(spectrum ℝ a,ℝ) →ₐ[ℝ] (H →L[ℝ] H) := realRestriction.comp (cfcHom ha).toAlgHom
  change Commute (F f) b
  have hF : Continuous F := realRestriction_continuous.comp (cfcHom_continuous ha)
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    change Commute (F (algebraMap ℝ _ r)) b
    rw [F.commutes]
    exact Algebra.commute_algebraMap_left _ _
  | id =>
    change Commute (realRestriction (cfcHom ha _)) b
    rwa [cfcHom_id]
  | star_id =>
    simp only [star_trivial]
    change Commute (realRestriction (cfcHom ha _)) b
    rwa [cfcHom_id]
  | add f g hf hg => rw [map_add]; exact hf.add_left hg
  | mul f g hf hg => rw [map_mul]; exact hf.mul_left hg
  | frequently f hf =>
    rw [commute_iff_eq, ← Set.mem_ofPred (p := fun x => x*b=b*x),
      ← (isClosed_eq (by fun_prop) (by fun_prop)).closure_eq]
    exact mem_closure_of_frequently_of_tendsto hf (hF.tendsto f)

lemma realRestriction_cfc_commute (a : H →L[ℂ] H)
    (b : H →L[ℝ] H) (hab : Commute (realRestriction a) b)
    (f : ℝ → ℝ) : Commute (realRestriction (cfc f a)) b := by
  apply cfc_cases (fun x : H →L[ℂ] H => Commute (realRestriction x) b) a f
  · simpa only [map_zero] using Commute.zero_left b
  · intro hf ha
    exact realRestriction_cfcHom_commute a ha b hab ⟨_,hf.domRestrict⟩

lemma realRestriction_sqrt_commute (a : H →L[ℂ] H) (ha : 0 ≤ a)
    (b : H →L[ℝ] H) (hab : Commute (realRestriction a) b) :
    Commute (realRestriction (CFC.sqrt a)) b := by
  rw [CFC.sqrt_eq_real_sqrt a ha,cfcₙ_eq_cfc]
  exact realRestriction_cfc_commute a b hab Real.sqrt

lemma selfAdjoint_denseRange {𝕜 : Type u𝕜} {E : Type uE} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (a : E →L[𝕜] E)
    (ha : IsSelfAdjoint a) (hinj : Function.Injective a) : DenseRange a := by
  have hk : a.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have ho : a.rangeᗮ = ⊥ := by
    rw [a.orthogonal_range,← ContinuousLinearMap.star_eq_adjoint,ha.star_eq,hk]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    ((Submodule.topologicalClosure_eq_top_iff).mpr ho)

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
namespace CyclicSeparatingData

def K (S : CyclicSeparatingData H) : H →L[ℂ] H := S.A-S.A*S.A

def Q (S : CyclicSeparatingData H) : H →L[ℂ] H := CFC.sqrt S.K

lemma K_eq_mul (S : CyclicSeparatingData H) : S.K = S.A*(1-S.A) := by
  unfold K
  noncomm_ring

lemma K_positive (S : CyclicSeparatingData H) : 0 ≤ S.K := by
  rw [S.K_eq_mul]
  exact ((Commute.one_right S.A).sub_right (Commute.refl S.A)).mul_nonneg
    S.A_positive (sub_nonneg.mpr S.A_le_one)

lemma K_real (S : CyclicSeparatingData H) : realRestriction S.K = S.B*S.B := by
  ext x
  change S.A x-S.A (S.A x) = S.B (S.B x)
  have he := (S.blocks_idempotent x).1
  exact sub_eq_iff_eq_add.mpr (he.symm.trans (add_comm _ _))

lemma K_injective (S : CyclicSeparatingData H) : Function.Injective S.K := by
  intro x y hxy
  apply S.B_injective
  apply S.B_injective
  have he := congrArg (fun f : H →L[ℝ] H => f x-f y) S.K_real
  change S.K x-S.K y = S.B (S.B x)-S.B (S.B y) at he
  rw [hxy,sub_self] at he
  exact sub_eq_zero.mp he.symm

lemma Q_positive (S : CyclicSeparatingData H) : 0 ≤ S.Q := CFC.sqrt_nonneg _
lemma Q_selfAdjoint (S : CyclicSeparatingData H) : IsSelfAdjoint S.Q :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp S.Q_positive |>.isSelfAdjoint

lemma Q_sq (S : CyclicSeparatingData H) : S.Q*S.Q=S.K :=
  CFC.sqrt_mul_sqrt_self _ S.K_positive

lemma Q_commute_A (S : CyclicSeparatingData H) : Commute S.Q S.A := by
  change Commute (CFC.sqrt S.K) S.A
  rw [CFC.sqrt_eq_real_sqrt S.K S.K_positive,cfcₙ_eq_cfc]
  exact ((Commute.refl S.A).sub_left ((Commute.refl S.A).mul_left (Commute.refl S.A))).cfc_real Real.sqrt

lemma Q_commute_B (S : CyclicSeparatingData H) : Commute (realRestriction S.Q) S.B := by
  apply realRestriction_sqrt_commute _ S.K_positive
  rw [S.K_real]
  exact (Commute.refl S.B).mul_left (Commute.refl S.B)

lemma Q_injective (S : CyclicSeparatingData H) : Function.Injective S.Q := by
  intro x y hxy
  apply S.K_injective
  have he := congrArg S.Q hxy
  change (S.Q*S.Q) x = (S.Q*S.Q) y at he
  rwa [S.Q_sq] at he

lemma Q_dense (S : CyclicSeparatingData H) : DenseRange S.Q :=
  selfAdjoint_denseRange _ S.Q_selfAdjoint S.Q_injective

lemma K_dense (S : CyclicSeparatingData H) : DenseRange S.K :=
  selfAdjoint_denseRange _ (ContinuousLinearMap.nonneg_iff_isPositive.mp S.K_positive).isSelfAdjoint S.K_injective

lemma norm_B_eq_Q (S : CyclicSeparatingData H) (x : H) : ‖S.B x‖ = ‖S.Q x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq]
  rw [S.B_symmetric_real x (S.B x)]
  have hQ := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (realRestriction_selfAdjoint S.Q_selfAdjoint)) x (S.Q x)
  change inner ℝ (S.Q x) (S.Q x) = inner ℝ x (S.Q (S.Q x)) at hQ
  rw [hQ]
  congr 1
  exact congrArg (fun f : H →L[ℝ] H => f x) (S.K_real.symm.trans (congrArg realRestriction S.Q_sq.symm))

def Banti (S : CyclicSeparatingData H) : H →L⋆[ℂ] H where
  toFun := S.B
  map_add' := S.B.map_add
  map_smul' := realLinear_smul_conj S.B (fun x => (S.blocks_I x).2)
  cont := S.B.continuous

@[simp] lemma Banti_apply (S : CyclicSeparatingData H) (x : H) : S.Banti x=S.B x := rfl

def Jcl (S : CyclicSeparatingData H) : H →L⋆[ℂ] H :=
  S.Banti.toLinearMap.extendOfNorm S.Q.toLinearMap

lemma Jcl_Q (S : CyclicSeparatingData H) (x : H) : S.Jcl (S.Q x)=S.B x := by
  exact LinearMap.extendOfNorm_eq S.Q_dense ⟨1,fun y => by
    change ‖S.B y‖ ≤ 1 * ‖S.Q y‖
    simpa only [one_mul] using le_of_eq (S.norm_B_eq_Q y)⟩ x

lemma norm_Jcl (S : CyclicSeparatingData H) (x : H) : ‖S.Jcl x‖=‖x‖ := by
  refine S.Q_dense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) x
  rintro _ ⟨y,rfl⟩
  rw [S.Jcl_Q,S.norm_B_eq_Q]

lemma Jcl_commute_Q (S : CyclicSeparatingData H) (x : H) : S.Jcl (S.Q x)=S.Q (S.Jcl x) := by
  refine S.Q_dense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) x
  rintro _ ⟨y,rfl⟩
  rw [S.Jcl_Q,S.Jcl_Q]
  exact (congrArg (fun f : H →L[ℝ] H => f y) S.Q_commute_B.eq).symm

lemma Jcl_involutive (S : CyclicSeparatingData H) : Function.Involutive S.Jcl := by
  intro x
  refine S.K_dense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) x
  rintro _ ⟨y,rfl⟩
  rw [← S.Q_sq]
  change S.Jcl (S.Jcl (S.Q (S.Q y))) = S.Q (S.Q y)
  rw [S.Jcl_commute_Q,S.Jcl_Q,S.Jcl_Q]
  exact congrArg (fun f : H →L[ℝ] H => f y) (S.K_real.symm.trans (congrArg realRestriction S.Q_sq.symm))

def J (S : CyclicSeparatingData H) : H ≃ₗᵢ⋆[ℂ] H where
  toFun := S.Jcl
  map_add' := S.Jcl.map_add
  map_smul' := S.Jcl.map_smulₛₗ
  invFun := S.Jcl
  left_inv := S.Jcl_involutive
  right_inv := S.Jcl_involutive
  norm_map' := S.norm_Jcl

end CyclicSeparatingData
end BoundedRecovery

end
end

end OAI
