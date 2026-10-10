import OAI.Analysis.Naimark.Dependencies

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
section

structure TracialStage where
  carrier : Type
  [cstar : CStarAlgebra carrier]
  [order : PartialOrder carrier]
  [starOrder : StarOrderedRing carrier]
  simple : IsSimpleCStar carrier
  trace : carrier →L[ℂ] ℂ
  traceState : IsState trace
  tracial : ∀ a b, trace (a*b) = trace (b*a)
  base : CAR →⋆ₐ[ℂ] carrier
  base_injective : Function.Injective base
  baseUEP : PureUEP base

attribute [instance] TracialStage.cstar TracialStage.order TracialStage.starOrder
instance : CoeSort TracialStage Type := ⟨TracialStage.carrier⟩

namespace TracialStage

variable (X : TracialStage)

theorem traceFaithful (a : X) (ha : a ≠ 0) : 0 < (X.trace (star a*a)).re :=
  tracialState_strictPos_of_simple X.simple X.trace X.traceState X.tracial a ha

lemma infinite : ¬ FiniteDimensional ℂ X := by
  intro h
  exact carInfiniteDimensional (Module.Finite.of_injective X.base.toLinearMap X.base_injective)

def reference : X →L[ℂ] ℂ :=
  ((X.baseUEP carVector carVector_isPure).exists_unique_pure X.base_injective carVector_isPure).choose

lemma reference_spec : IsPureState X.reference ∧ restrictState X.base X.reference = carVector :=
  ⟨((X.baseUEP carVector carVector_isPure).exists_unique_pure X.base_injective carVector_isPure).choose_spec.1,
    ((X.baseUEP carVector carVector_isPure).exists_unique_pure X.base_injective carVector_isPure).choose_spec.2.1⟩

lemma reference_peaks : Peaks (fun n => X.base (carPeak n)) X.reference :=
  carPeak_peaks.extend X.base (X.baseUEP carVector carVector_isPure) X.reference
    X.reference_spec.1.1 X.reference_spec.2

@[ext] structure Hom (X Y : TracialStage) where
  map : X →⋆ₐ[ℂ] Y
  injective : Function.Injective map
  trace_map : ∀ a, Y.trace (map a) = X.trace a
  base_map : ∀ a, map (X.base a) = Y.base a
  uep : PureUEP map

namespace Hom
variable {X Y Z W : TracialStage}

def id (X : TracialStage) : Hom X X where
  map := StarAlgHom.id ℂ X
  injective := Function.injective_id
  trace_map _ := rfl
  base_map _ := rfl
  uep := PureUEP.id

def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  map := g.map.comp f.map
  injective := g.injective.comp f.injective
  trace_map a := by rw [StarAlgHom.comp_apply,g.trace_map,f.trace_map]
  base_map a := by rw [StarAlgHom.comp_apply,f.base_map,g.base_map]
  uep := f.uep.comp g.uep

@[simp] lemma comp_map (g : Hom Y Z) (f : Hom X Y) : (g.comp f).map = g.map.comp f.map := rfl
@[simp] lemma id_map : (id X).map = StarAlgHom.id ℂ X := rfl

lemma reference_map (f : Hom X Y) : restrictState f.map Y.reference = X.reference := by
  apply X.baseUEP carVector carVector_isPure
  · exact isState_restrict f.map Y.reference Y.reference_spec.1.1
  · exact X.reference_spec.1.1
  · rw [restrictState_comp]
    convert Y.reference_spec.2 using 1
    ext a
    exact congrArg Y.reference (f.base_map a)
  · exact X.reference_spec.2

end Hom

instance : CategoryTheory.Category TracialStage where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp f := by ext a; rfl
  comp_id f := by ext a; rfl
  assoc f g h := by ext a; rfl

def initial : TracialStage where
  carrier := CAR
  simple := carSimple
  trace := carTrace
  traceState := carTrace_isState
  tracial := carTrace_tracial
  base := StarAlgHom.id ℂ CAR
  base_injective := Function.injective_id
  baseUEP := PureUEP.id

end TracialStage
end

open scoped CStarAlgebra ComplexOrder
namespace TracialStage
attribute [local instance 2000] PeakingPairData.hnnCStar PeakingPairData.hnnOrder
  PeakingPairData.hnnStarOrder
variable (X : TracialStage)

def positiveTrace : X →ₚ[ℂ] ℂ := positiveOfSquares X.trace X.traceState.2

lemma positiveTrace_normalized : X.positiveTrace 1 = 1 := ((isState_iff X.trace).mp X.traceState).1
lemma positiveTrace_faithful (a : X) (h : X.positiveTrace (star a*a) = 0) : a = 0 := by
  by_contra ha
  have hh := X.traceFaithful a ha
  change X.trace (star a*a) = 0 at h
  rw [h,Complex.zero_re] at hh
  exact (lt_irrefl 0) hh

variable (Q : PeakingPairData X) (hs : Q.Separated)
  (htrace : ∀ a : X, Q.trace a = X.trace a)

def hnn : TracialStage where
  carrier := Q.HNNAlgebra
  cstar := inferInstance
  order := inferInstance
  starOrder := inferInstance
  simple := Q.hnn_simple hs X.simple
  trace := Q.hnnTrace
  traceState := Q.hnnTrace_isState
  tracial := Q.hnnTrace_tracial
  base := Q.hnnBase.comp X.base
  base_injective := Q.hnnBase_injective.comp X.base_injective
  baseUEP := X.baseUEP.comp (fun f hf => Q.hnn_unique hs X.simple f hf)

def hnnHom : Hom X (hnn X Q hs) where
  map := Q.hnnBase
  injective := Q.hnnBase_injective
  trace_map a := (Q.hnnTrace_base a).trans (htrace a)
  base_map _ := rfl
  uep f hf := Q.hnn_unique hs X.simple f hf

include htrace in
lemma hnn_reference (hf : Q.state false = X.reference) :
    restrictState Q.hnnBase (hnn X Q hs).reference = Q.state false := by
  rw [hf]
  exact (hnnHom X Q hs htrace).reference_map

include htrace in

theorem hnn_reference_join (f : X →L[ℂ] ℂ) (hf : IsPureState f)
    (h0 : Q.state false = X.reference) (h1 : Q.state true = f) :
    ∃ F : hnn X Q hs →L[ℂ] ℂ, ∃ hF : IsPureState F,
      restrictState Q.hnnBase F = f ∧
      PureStateEquivalent (hnn X Q hs).reference (hnn X Q hs).reference_spec.1 F hF := by
  obtain ⟨F,hF,hr,_⟩ := (Q.hnn_unique hs X.simple f hf).exists_unique_pure
    Q.hnnBase_injective hf
  refine ⟨F,hF,hr,?_⟩
  exact Q.hnn_join hs X.simple _ _ (hnn X Q hs).reference_spec.1 hF
    (hnn_reference X Q hs htrace h0) (hr.trans h1.symm)

end TracialStage

open scoped InnerProductSpace
namespace KOS

def projectionCutoff (t : ℝ) : ℝ := t^2 / (t^2 + (t-1)^2)

lemma projectionCutoff_den_pos (t : ℝ) : 0 < t^2 + (t-1)^2 := by
  nlinarith [sq_nonneg (t-1/2)]

lemma continuous_projectionCutoff : Continuous projectionCutoff := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact (projectionCutoff_den_pos t).ne'

lemma projectionCutoff_nonneg (t : ℝ) : 0 ≤ projectionCutoff t :=
  div_nonneg (sq_nonneg _) (projectionCutoff_den_pos t).le

lemma projectionCutoff_le_one (t : ℝ) : projectionCutoff t ≤ 1 := by
  unfold projectionCutoff
  rw [div_le_one (projectionCutoff_den_pos t)]
  nlinarith [sq_nonneg (t-1)]

@[simp] lemma projectionCutoff_zero : projectionCutoff 0 = 0 := by norm_num [projectionCutoff]
@[simp] lemma projectionCutoff_one : projectionCutoff 1 = 1 := by norm_num [projectionCutoff]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def projectionTruncate (a : A) : A := cfc projectionCutoff a

lemma projectionTruncate_nonneg (a : A) : 0 ≤ projectionTruncate a :=
  cfc_nonneg (fun t _ => projectionCutoff_nonneg t)

lemma projectionTruncate_le_one (a : A) : projectionTruncate a ≤ 1 :=
  cfc_le_one _ _ (fun t _ => projectionCutoff_le_one t)

omit [PartialOrder A] [StarOrderedRing A] in
lemma projectionTruncate_relation (a : A) (ha : IsSelfAdjoint a) :
    projectionTruncate a * (a^2 + (a-1)^2) = a^2 := by
  have hp : cfc (fun t : ℝ => t^2 + (t-1)^2) a = a^2 + (a-1)^2 := by
    rw [cfc_add a (fun t : ℝ => t^2) (fun t => (t-1)^2), cfc_pow_id (R := ℝ) a 2 ha, cfc_pow _ _ a,
      cfc_sub _ _ a, cfc_id' ℝ a ha, cfc_const_one ℝ a]
  rw [projectionTruncate, ← hp, ← cfc_mul _ _ a continuous_projectionCutoff.continuousOn (by fun_prop)]
  have he : (fun t => projectionCutoff t * (t^2 + (t-1)^2)) = fun t : ℝ => t^2 := by
    funext t
    exact div_mul_cancel₀ _ (projectionCutoff_den_pos t).ne'
  rw [he,cfc_pow_id (R := ℝ) a 2 ha]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma projectionTruncate_apply (a : A) (ha : IsSelfAdjoint a)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (hv : π a (π a v) = π a v) :
    π (projectionTruncate a) v = π a v := by
  have hd : π (a^2+(a-1)^2) v = v := by
    simp only [pow_two,map_add,map_mul,map_sub,map_one,add_apply,mul_apply_eq_comp,
      sub_apply,one_apply_eq_self,hv]
    abel
  calc
    π (projectionTruncate a) v = π (projectionTruncate a) (π (a^2+(a-1)^2) v) := by rw [hd]
    _ = π (projectionTruncate a * (a^2+(a-1)^2)) v := by rw [map_mul,mul_apply_eq_comp]
    _ = π (a^2) v := by rw [projectionTruncate_relation a ha]
    _ = π a v := by simpa only [pow_two,map_mul,mul_apply_eq_comp] using hv

theorem exact_gram_projection {ι : Type*} [Finite ι] (x y : ι → H)
    (hgram : ∀ i j, ⟪x i,x j⟫_ℂ = ⟪y i,y j⟫_ℂ)
    (horth : ∀ i j, ⟪x i,y j⟫_ℂ = 0) :
    ∃ P : H →L[ℂ] H, IsStarProjection P ∧
      (∀ i, P (x i-y i) = x i-y i) ∧
      (∀ i, P (x i+y i) = 0) := by
  let D := Submodule.span ℂ (Set.range fun i => x i-y i)
  let : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine ⟨D.starProjection, isStarProjection_starProjection, ?_, ?_⟩
  · intro i
    exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.subset_span (Set.mem_range_self i))
  · intro i
    have hs : x i+y i ∈ Dᗮ := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨j,rfl⟩ := hz
          have hj : ⟪y j,x i⟫_ℂ = 0 := inner_eq_zero_symm.mpr (horth i j)
          simp only [inner_sub_left,inner_add_right,horth j i,hj,hgram j i]
          ring
      | zero => simp
      | add a b ha hb hia hib => simp only [inner_add_left,hia,hib,add_zero]
      | smul c z hz hiz => simp only [inner_smul_left,hiz,mul_zero]
    rw [Submodule.starProjection_apply,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hs]
    rfl

end KOS

open scoped InnerProductSpace
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpaceH : CompleteSpace H]

omit completeSpaceH in
theorem difference_span_coefficients [CompleteSpace H] {ι : Type*} [Fintype ι] (b w : ι → H)
    (hb : Orthonormal ℂ b) (ho : ∀ i j, ⟪b i,w j⟫_ℂ = 0)
    {v : H} (hv : v ∈ Submodule.span ℂ (Set.range fun i => b i-w i)) :
    v = ∑ i, ⟪b i,v⟫_ℂ • (b i-w i) := by
  rw [← Fintype.range_linearCombination ℂ] at hv
  obtain ⟨c,hc⟩ := hv
  change (∑ i, c i • (b i-w i)) = v at hc
  have hi (j : ι) : ⟪b j,v⟫_ℂ = c j := by
    rw [← hc]
    simp only [smul_sub,Finset.sum_sub_distrib,inner_sub_right]
    rw [hb.inner_right_fintype]
    simp only [inner_sum,inner_smul_right,ho,mul_zero,Finset.sum_const_zero,sub_zero]
  calc
    v = ∑ i, c i • (b i-w i) := hc.symm
    _ = _ := by simp only [hi]

theorem difference_projection_bound {ι : Type*} [Fintype ι] (b w : ι → H)
    (hb : Orthonormal ℂ b) (ho : ∀ i j, ⟪b i,w j⟫_ℂ = 0)
    (v : H) (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ i, ‖⟪b i-w i,v⟫_ℂ‖ ≤ δ) :
    let D := Submodule.span ℂ (Set.range fun i => b i-w i)
    letI : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    ‖D.starProjection v‖ ≤ Fintype.card ι * δ := by
  classical
  dsimp only
  let D := Submodule.span ℂ (Set.range fun i => b i-w i)
  let : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let q := D.starProjection v
  have hq := difference_span_coefficients b w hb ho (D.starProjection_apply_mem v)
  have hcoef (i : ι) : ‖⟪b i,q⟫_ℂ‖ ≤ ‖q‖ := by
    simpa only [hb.norm_eq_one i,one_mul] using norm_inner_le_norm (b i) q
  have hn : ‖⟪q,v⟫_ℂ‖ ≤ ‖q‖ * (Fintype.card ι * δ) := by
    calc
      ‖⟪q,v⟫_ℂ‖ = ‖∑ i, starRingEnd ℂ (⟪b i,q⟫_ℂ) * ⟪b i-w i,v⟫_ℂ‖ := by
        conv_lhs => rw [show q = ∑ i, ⟪b i,q⟫_ℂ • (b i-w i) from hq]
        simp only [sum_inner,inner_smul_left]
      _ ≤ ∑ i, ‖starRingEnd ℂ (⟪b i,q⟫_ℂ) * ⟪b i-w i,v⟫_ℂ‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, ‖q‖ * δ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul,RCLike.norm_conj]
        exact mul_le_mul (hcoef i) (hv i) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by simp [mul_left_comm,mul_comm,mul_assoc]
  have he : ‖q‖^2 = (⟪q,v⟫_ℂ).re := by
    exact (D.re_inner_starProjection_eq_normSq v).symm
  have hre : (⟪q,v⟫_ℂ).re ≤ ‖⟪q,v⟫_ℂ‖ := Complex.re_le_norm _
  change ‖q‖ ≤ _
  have hC : 0 ≤ (Fintype.card ι : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
  by_cases hzero : ‖q‖ = 0
  · simpa only [hzero] using hC
  · have hpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith only [he,hn,hre]

omit completeSpaceH in
theorem gram_combination_error [CompleteSpace H] {ι : Type*} [Fintype ι] (x y : ι → H)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ)
    (c d : ι → ℂ) :
    ‖⟪∑ i, c i • x i, ∑ j, d j • x j⟫_ℂ -
      ⟪∑ i, c i • y i, ∑ j, d j • y j⟫_ℂ‖ ≤
      δ * (∑ i, ‖c i‖) * (∑ j, ‖d j‖) := by
  have he : ⟪∑ i, c i • x i, ∑ j, d j • x j⟫_ℂ -
      ⟪∑ i, c i • y i, ∑ j, d j • y j⟫_ℂ =
      ∑ i, ∑ j, (starRingEnd ℂ (c i) * d j) * (⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ) := by
    simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,
      Finset.mul_sum,← Finset.sum_sub_distrib,mul_sub,mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  calc
    _ ≤ ∑ i, ‖∑ j, (starRingEnd ℂ (c i) * d j) * (⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, δ * ‖c i‖ * ‖d j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,norm_mul,RCLike.norm_conj]
      calc
        _ = ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ * (‖c i‖ * ‖d j‖) := mul_comm _ _
        _ ≤ δ * (‖c i‖ * ‖d j‖) :=
          mul_le_mul (hgram i j) le_rfl (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hδ
        _ = _ := by ring
    _ = _ := by simp only [← Finset.mul_sum,← Finset.sum_mul]

theorem gram_zero_combination_bound {ι : Type*} [Fintype ι] (x y : ι → H)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ)
    (c : ι → ℂ) (hc : ∑ i, c i • x i = 0) :
    ‖∑ i, c i • y i‖ ≤ Real.sqrt δ * (∑ i, ‖c i‖) := by
  have hb := gram_combination_error x y δ hδ hgram c c
  rw [hc,inner_zero_left,zero_sub,norm_neg,inner_self_eq_norm_sq_to_K,
    norm_pow,RCLike.norm_coe_norm] at hb
  have hs : 0 ≤ ∑ i, ‖c i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hpos : 0 ≤ Real.sqrt δ * ∑ i, ‖c i‖ := mul_nonneg (Real.sqrt_nonneg _) hs
  apply (sq_le_sq₀ (norm_nonneg _) hpos).mp
  rw [mul_pow,Real.sq_sqrt hδ]
  nlinarith only [hb]

omit completeSpaceH in
theorem finite_orthonormal_coordinates [CompleteSpace H] {ι : Type*} [Fintype ι] (x : ι → H) :
    ∃ (m : ℕ) (b : Fin m → H) (c : Fin m → ι → ℂ) (d : ι → Fin m → ℂ),
      Orthonormal ℂ b ∧ (∀ j, ∑ i, c j i • x i = b j) ∧
      (∀ i, ∑ j, d i j • b j = x i) := by
  classical
  let M := Submodule.span ℂ (Set.range x)
  let : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let B := stdOrthonormalBasis ℂ M
  let b := fun j => (B j : H)
  have hb : Orthonormal ℂ b := B.orthonormal.comp_linearIsometry M.subtypeₗᵢ
  have hc (j) : ∃ c : ι → ℂ, ∑ i, c i • x i = b j := by
    have hj := (B j).property
    change (b j) ∈ Submodule.span ℂ (Set.range x) at hj
    rw [← Fintype.range_linearCombination ℂ] at hj
    exact hj
  choose c hc using hc
  let d := fun i j => ⟪b j,x i⟫_ℂ
  refine ⟨_,b,c,d,hb,hc,?_⟩
  intro i
  have he := congrArg (fun (v : M) => (v:H))
    (B.sum_repr' ⟨x i,Submodule.subset_span (Set.mem_range_self i)⟩)
  simpa only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_mk,Submodule.coe_inner,d,b] using he

omit completeSpaceH in
theorem gram_cross_zero [CompleteSpace H] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → H) (y : κ → H) (ho : ∀ i j, ⟪x i,y j⟫_ℂ = 0)
    (c : ι → ℂ) (d : κ → ℂ) :
    ⟪∑ i, c i • x i, ∑ j, d j • y j⟫_ℂ = 0 := by
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,ho,mul_zero,
    Finset.sum_const_zero]

theorem gram_sum_projection_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x y : ι → H) (b : κ → H) (c : κ → ι → ℂ)
    (hb : Orthonormal ℂ b) (hc : ∀ j, ∑ i, c j i • x i = b j)
    (ho : ∀ i j, ⟪x i,y j⟫_ℂ = 0)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ) (i : ι) :
    let w := fun j => ∑ l, c j l • y l
    let D := Submodule.span ℂ (Set.range fun j => b j-w j)
    letI : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    ‖D.starProjection (x i+y i)‖ ≤ Fintype.card κ * (δ * ∑ j, ∑ l, ‖c j l‖) := by
  classical
  dsimp only
  let w := fun j => ∑ l, c j l • y l
  have hobw (j k) : ⟪b j,w k⟫_ℂ = 0 := by
    rw [← hc j]
    exact gram_cross_zero x y ho (c j) (c k)
  apply difference_projection_bound b w hb hobw _ _ (by positivity)
  intro j
  have hbi : ⟪b j,y i⟫_ℂ = 0 := by
    rw [← hc j]
    simp only [sum_inner,inner_smul_left,ho,mul_zero,Finset.sum_const_zero]
  have hwi : ⟪w j,x i⟫_ℂ = 0 := by
    rw [inner_eq_zero_symm]
    simp only [w,inner_sum,inner_smul_right,ho,mul_zero,Finset.sum_const_zero]
  have he : ⟪b j-w j,x i+y i⟫_ℂ = ⟪b j,x i⟫_ℂ-⟪w j,y i⟫_ℂ := by
    rw [inner_add_right,inner_sub_left,inner_sub_left,hbi,hwi]
    abel
  rw [he,← hc j]
  have hbase := gram_combination_error x y δ hδ hgram (c j) (Pi.single i 1)
  have hbase' : ‖⟪∑ l, c j l • x l,x i⟫_ℂ - ⟪w j,y i⟫_ℂ‖ ≤ δ * ∑ l, ‖c j l‖ := by
    simpa only [Pi.single_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true,apply_ite,norm_one,norm_zero,mul_one] using hbase
  apply hbase'.trans
  apply mul_le_mul_of_nonneg_left _ hδ
  exact Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (Finset.mem_univ j)

def gramResidual {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (c : κ → ι → ℂ) (d : ι → κ → ℂ) (i : ι) : ι → ℂ :=
  Pi.single i 1 - ∑ j, d i j • c j

omit completeSpaceH in
lemma gramResidual_apply [CompleteSpace H] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (x : ι → H) (c : κ → ι → ℂ) (d : ι → κ → ℂ) (i : ι) :
    ∑ l, gramResidual c d i l • x l = x i - ∑ j, d i j • (∑ l, c j l • x l) := by
  change Fintype.linearCombination ℂ x (gramResidual c d i) = _
  rw [gramResidual,map_sub,Fintype.linearCombination_apply_single,one_smul,map_sum]
  simp only [map_smul,Fintype.linearCombination_apply]

theorem gram_difference_projection_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (x y : ι → H) (b : κ → H) (c : κ → ι → ℂ) (d : ι → κ → ℂ)
    (hc : ∀ j, ∑ i, c j i • x i = b j) (hd : ∀ i, ∑ j, d i j • b j = x i)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ) (i : ι) :
    let w := fun j => ∑ l, c j l • y l
    let D := Submodule.span ℂ (Set.range fun j => b j-w j)
    letI : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    ‖D.starProjection (x i-y i)-(x i-y i)‖ ≤
      2 * Real.sqrt δ * (∑ l, ‖gramResidual c d i l‖) := by
  classical
  dsimp only
  let w := fun j => ∑ l, c j l • y l
  let D := Submodule.span ℂ (Set.range fun j => b j-w j)
  let : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let r := ∑ l, gramResidual c d i l • y l
  have he : ∑ l, gramResidual c d i l • x l = 0 := by
    rw [gramResidual_apply]
    simp only [hc,hd,sub_self]
  have hr := gram_zero_combination_bound x y δ hδ hgram (gramResidual c d i) he
  have hm : x i-y i+r ∈ D := by
    have heq : x i-y i+r = ∑ j, d i j • (b j-w j) := by
      rw [show r = y i-∑ j, d i j • w j from gramResidual_apply y c d i]
      simp only [smul_sub,Finset.sum_sub_distrib,hd]
      abel
    rw [heq]
    exact D.sum_mem (fun j _ => D.smul_mem _ (Submodule.subset_span (Set.mem_range_self j)))
  have hp : D.starProjection (x i-y i+r) = x i-y i+r :=
    Submodule.starProjection_eq_self_iff.mpr hm
  have heq : D.starProjection (x i-y i)-(x i-y i) = r-D.starProjection r := by
    rw [map_add] at hp
    exact sub_eq_sub_iff_add_eq_add.mpr (hp.trans (add_comm _ _))
  rw [heq]
  have hrp : ‖D.starProjection r‖ ≤ ‖r‖ := by
    exact (D.starProjection.le_opNorm r).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right D.starProjection_norm_le (norm_nonneg r))
  calc
    ‖r-D.starProjection r‖ ≤ ‖r‖+‖D.starProjection r‖ := norm_sub_le _ _
    _ ≤ 2*‖r‖ := by linarith
    _ ≤ 2 * (Real.sqrt δ * (∑ l, ‖gramResidual c d i l‖)) :=
      mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _ := by ring

theorem approximate_gram_projection {ι : Type*} [Fintype ι] (x : ι → H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ι → H,
      (∀ i j, ⟪x i,y j⟫_ℂ = 0) →
      (∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ) →
      ∃ P : H →L[ℂ] H, IsStarProjection P ∧
        (∀ v, P v ∈ Submodule.span ℂ (Set.range x ∪ Set.range y)) ∧
        (∀ i, ‖P (x i-y i)-(x i-y i)‖ < ε) ∧
        (∀ i, ‖P (x i+y i)‖ < ε) := by
  classical
  obtain ⟨m,b,c,d,hb,hc,hd⟩ := finite_orthonormal_coordinates x
  let C : ℝ := 1 + m * (∑ j, ∑ l, ‖c j l‖)
  let E : ℝ := 1 + ∑ i, ∑ l, ‖gramResidual c d i l‖
  have hC : 0 < C := by dsimp [C]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  let δ : ℝ := min (ε/(2*C)) ((ε/(4*E))^2)
  have hδ : 0 < δ := lt_min (by positivity) (sq_pos_of_pos (by positivity))
  have hδC : δ*C ≤ ε/2 := by
    have hh := min_le_left (ε/(2*C)) ((ε/(4*E))^2)
    change δ ≤ ε/(2*C) at hh
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*C)).mp hh
    nlinarith only [hh']
  have hδE : Real.sqrt δ * E ≤ ε/4 := by
    have hh : δ ≤ (ε/(4*E))^2 := min_le_right _ _
    have hs : Real.sqrt δ ≤ ε/(4*E) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rwa [Real.sq_sqrt hδ.le]
    have hh' := (le_div_iff₀ (by positivity : 0 < 4*E)).mp hs
    nlinarith only [hh']
  refine ⟨δ,hδ,fun y ho hgram => ?_⟩
  let w := fun j => ∑ l, c j l • y l
  let D := Submodule.span ℂ (Set.range fun j => b j-w j)
  let : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let M := Submodule.span ℂ (Set.range x ∪ Set.range y)
  have hDM : D ≤ M := by
    apply Submodule.span_le.mpr
    rintro v ⟨j,rfl⟩
    apply M.sub_mem
    · rw [← hc j]
      exact M.sum_mem (fun i _ => M.smul_mem _ (Submodule.subset_span (Or.inl (Set.mem_range_self i))))
    · exact M.sum_mem (fun i _ => M.smul_mem _ (Submodule.subset_span (Or.inr (Set.mem_range_self i))))
  refine ⟨D.starProjection,isStarProjection_starProjection,
    fun v => hDM (D.starProjection_apply_mem v),?_,?_⟩
  · intro i
    have hi := gram_difference_projection_bound x y b c d hc hd δ hδ.le hgram i
    have hsum : (∑ l, ‖gramResidual c d i l‖) ≤ E := by
      have hh : (∑ l, ‖gramResidual c d i l‖) ≤ ∑ j, ∑ l, ‖gramResidual c d j l‖ :=
        Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun l _ => norm_nonneg (gramResidual c d j l)))
          (Finset.mem_univ i)
      dsimp only [E]
      linarith
    calc
      _ ≤ 2 * Real.sqrt δ * (∑ l, ‖gramResidual c d i l‖) := hi
      _ ≤ 2 * Real.sqrt δ * E := by gcongr
      _ ≤ ε/2 := by nlinarith only [hδE]
      _ < ε := by linarith
  · intro i
    have hi := gram_sum_projection_bound x y b c hb hc ho δ hδ.le hgram i
    have hm : (Fintype.card (Fin m) : ℝ) * (δ * ∑ j, ∑ l, ‖c j l‖) ≤ δ*C := by
      simp only [Fintype.card_fin]
      dsimp only [C]
      nlinarith only [hδ.le]
    exact (hi.trans (hm.trans hδC)).trans_lt (by linarith)

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_projection_positive_lift
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (P : H →L[ℂ] H) (hP : IsStarProjection P) (hPM : ∀ v ∈ M, P v ∈ M) :
    ∃ a : A, 0 ≤ a ∧ a ≤ 1 ∧ ∀ v ∈ M, π a v = P v := by
  obtain ⟨b,hb,_,hbM⟩ := irreducible_selfAdjoint_transitivity π hπ M P hP.isSelfAdjoint
  have hPP (v : H) : P (P v) = P v := by
    exact congrArg (fun T : H →L[ℂ] H => T v) hP.isIdempotentElem.eq
  refine ⟨projectionTruncate b,projectionTruncate_nonneg b,projectionTruncate_le_one b,?_⟩
  intro v hv
  have hbb : π b (π b v) = π b v := by
    rw [hbM v hv,hbM (P v) (hPM v hv),hPP]
  exact (projectionTruncate_apply b hb (irreducibleUnitalRepresentation π hπ) v hbb).trans (hbM v hv)

theorem approximate_gram_positive_lift
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {ι : Type*} [Fintype ι] (x : ι → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ι → H,
      (∀ i j, ⟪x i,y j⟫_ℂ = 0) →
      (∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ) →
      ∃ a : A, 0 ≤ a ∧ a ≤ 1 ∧
        (∀ i, ‖π a (x i-y i)-(x i-y i)‖ < ε) ∧
        (∀ i, ‖π a (x i+y i)‖ < ε) := by
  obtain ⟨δ,hδ,hgeom⟩ := approximate_gram_projection x ε hε
  refine ⟨δ,hδ,fun y ho hg => ?_⟩
  obtain ⟨P,hP,hPM,hd,hs⟩ := hgeom y ho hg
  let M := Submodule.span ℂ (Set.range x ∪ Set.range y)
  let : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ
    ((Set.finite_range _).union (Set.finite_range _))
  obtain ⟨a,ha,ha1,hav⟩ := finite_projection_positive_lift π hπ M P hP (fun v _ => hPM v)
  have hx (i : ι) : x i ∈ M := Submodule.subset_span (Or.inl (Set.mem_range_self i))
  have hy (i : ι) : y i ∈ M := Submodule.subset_span (Or.inr (Set.mem_range_self i))
  refine ⟨a,ha,ha1,fun i => ?_,fun i => ?_⟩
  · rw [hav _ (M.sub_mem (hx i) (hy i))]
    exact hd i
  · rw [hav _ (M.add_mem (hx i) (hy i))]
    exact hs i

end KOS

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
namespace KOS
variable {A : Type*} [CStarAlgebra A]

theorem resolvent_commutator (a : A) (ha : IsSelfAdjoint a) (b : A) :
    b * saResolvent a (-Complex.I) - saResolvent a (-Complex.I) * b =
      saResolvent a (-Complex.I) * (a*b-b*a) * saResolvent a (-Complex.I) := by
  let R := saResolvent a (-Complex.I)
  obtain ⟨hl,hr⟩ := saResolvent_inverse a ha (-Complex.I) (by simp)
  rw [Algebra.algebraMap_eq_smul_one,neg_smul,sub_neg_eq_add] at hl hr
  have he : (a+Complex.I • (1:A))*b-b*(a+Complex.I • (1:A)) = a*b-b*a := by
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
    abel
  change b*R-R*b = R*(a*b-b*a)*R
  calc
    b*R-R*b = (R*(a+Complex.I • (1:A)))*b*R-R*b*((a+Complex.I • (1:A))*R) := by
      rw [hr,hl,one_mul,mul_one]
    _ = R*((a+Complex.I • (1:A))*b-b*(a+Complex.I • (1:A)))*R := by noncomm_ring
    _ = R*(a*b-b*a)*R := by rw [he]

lemma resolvent_commutator_norm (a : A) (ha : IsSelfAdjoint a) (b : A) :
    ‖b * saResolvent a (-Complex.I) - saResolvent a (-Complex.I) * b‖ ≤ ‖b*a-a*b‖ := by
  have hR : ‖saResolvent a (-Complex.I)‖ ≤ 1 := by
    simpa using saResolvent_norm_le a ha (-Complex.I) (by simp)
  rw [resolvent_commutator a ha b]
  calc
    _ ≤ ‖saResolvent a (-Complex.I)‖ * ‖a*b-b*a‖ * ‖saResolvent a (-Complex.I)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖a*b-b*a‖ * 1 := by gcongr
    _ = ‖b*a-a*b‖ := by simp only [one_mul,mul_one,norm_sub_rev]

lemma saCayley_affine_resolvent (a : A) (ha : IsSelfAdjoint a) :
    saCayley a = 1 - (2*Complex.I) • saResolvent a (-Complex.I) := by
  have hr := (saResolvent_inverse a ha (-Complex.I) (by simp)).2
  rw [Algebra.algebraMap_eq_smul_one,neg_smul,sub_neg_eq_add] at hr
  rw [saCayley_eq a ha]
  calc
    _ = saResolvent a (-Complex.I) * (a+Complex.I • (1:A)) -
        (2*Complex.I) • saResolvent a (-Complex.I) := by
      simp only [mul_sub,mul_add,mul_smul_comm,mul_one]
      module
    _ = _ := by rw [hr]

theorem saCayley_commutator_norm (a : A) (ha : IsSelfAdjoint a) (b : A) :
    ‖b*saCayley a-saCayley a*b‖ ≤ 2*‖b*a-a*b‖ := by
  rw [saCayley_affine_resolvent a ha]
  have he : b*(1-(2*Complex.I) • saResolvent a (-Complex.I)) -
      (1-(2*Complex.I) • saResolvent a (-Complex.I))*b =
      -(2*Complex.I) • (b*saResolvent a (-Complex.I)-saResolvent a (-Complex.I)*b) := by
    simp only [mul_sub,sub_mul,mul_one,one_mul,mul_smul_comm,smul_mul_assoc]
    module
  rw [he,norm_smul]
  have hn : ‖-(2*Complex.I)‖ = (2:ℝ) := by simp
  rw [hn]
  exact mul_le_mul_of_nonneg_left (resolvent_commutator_norm a ha b) (by norm_num)

variable [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exact_gram_positive_lift (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {ι : Type*} [Finite ι] (x y : ι → H)
    (hgram : ∀ i j, ⟪x i,x j⟫_ℂ = ⟪y i,y j⟫_ℂ)
    (horth : ∀ i j, ⟪x i,y j⟫_ℂ = 0) :
    ∃ a : A, 0 ≤ a ∧ a ≤ 1 ∧
      (∀ i, π a (x i-y i) = x i-y i) ∧ (∀ i, π a (x i+y i) = 0) := by
  obtain ⟨P,hP,hd,hs⟩ := exact_gram_projection x y hgram horth
  let M := Submodule.span ℂ ((Set.range fun i => x i-y i) ∪ (Set.range fun i => x i+y i))
  let : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ
    ((Set.finite_range _).union (Set.finite_range _))
  obtain ⟨b,hb,_,hbM⟩ := irreducible_selfAdjoint_transitivity π hπ M P hP.isSelfAdjoint
  have hbd (i : ι) : π b (x i-y i) = x i-y i :=
    (hbM _ (Submodule.subset_span (Or.inl (Set.mem_range_self i)))).trans (hd i)
  have hbs (i : ι) : π b (x i+y i) = 0 :=
    (hbM _ (Submodule.subset_span (Or.inr (Set.mem_range_self i)))).trans (hs i)
  refine ⟨projectionTruncate b,projectionTruncate_nonneg b,projectionTruncate_le_one b,?_,?_⟩
  · intro i
    have hi := projectionTruncate_apply b hb (irreducibleUnitalRepresentation π hπ)
      (x i-y i) (by simp only [irreducibleUnitalRepresentation_apply,hbd])
    exact hi.trans (hbd i)
  · intro i
    have hi := projectionTruncate_apply b hb (irreducibleUnitalRepresentation π hπ)
      (x i+y i) (by simp only [irreducibleUnitalRepresentation_apply,hbs,map_zero])
    exact hi.trans (hbs i)

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]

def projectionSwitch (a : A) : A := (-Complex.I) • saCayley (a+a-1)

lemma projectionSwitch_unitary (a : A) (ha : IsSelfAdjoint a) :
    projectionSwitch a ∈ unitary A := by
  apply Unitary.smul_mem_of_mem _ (saCayley_unitary _ ((ha.add ha).sub (IsSelfAdjoint.one A)))
  simp [Unitary.mem_iff]

lemma projectionSwitch_eq (a : A) (ha : IsSelfAdjoint a) :
    projectionSwitch a = (-Complex.I) • (1:A) -
      (2:ℂ) • saResolvent (a+a-1) (-Complex.I) := by
  rw [projectionSwitch,saCayley_affine_resolvent _ ((ha.add ha).sub (IsSelfAdjoint.one A)),smul_sub,smul_smul]
  congr 1
  congr 1
  calc
    _ = -(2*(Complex.I*Complex.I)) := by ring
    _ = _ := by norm_num

lemma projectionSwitch_sub_one (a : A) (ha : IsSelfAdjoint a) :
    projectionSwitch a - 1 = (-(1+Complex.I)) •
      (saResolvent (a+a-1) (-Complex.I) * (a+a)) := by
  let R := saResolvent (a+a-1) (-Complex.I)
  have hr := (saResolvent_inverse (a+a-1) ((ha.add ha).sub (IsSelfAdjoint.one A)) (-Complex.I) (by simp)).2
  rw [Algebra.algebraMap_eq_smul_one,neg_smul,sub_neg_eq_add] at hr
  have hR : R*(a+a) = 1 + (1-Complex.I) • R := by
    calc
      R*(a+a) = R*(a+a-1+Complex.I • (1:A)) + (1-Complex.I) • R := by
        simp only [mul_add,mul_sub,mul_smul_comm,mul_one]
        module
      _ = _ := by rw [hr]
  rw [projectionSwitch_eq a ha]
  change (-Complex.I) • (1:A) - (2:ℂ) • R - 1 = -(1+Complex.I) • (R*(a+a))
  rw [hR,smul_add,smul_smul]
  have hc : -(1+Complex.I)*(1-Complex.I) = (-2:ℂ) := by
    calc
      _ = -(1-Complex.I^2) := by ring
      _ = _ := by norm_num
  rw [hc]
  module

lemma projectionSwitch_add_one (a : A) (ha : IsSelfAdjoint a) :
    projectionSwitch a + 1 = (1-Complex.I) •
      (saResolvent (a+a-1) (-Complex.I) * ((a-1)+(a-1))) := by
  let R := saResolvent (a+a-1) (-Complex.I)
  have hr := (saResolvent_inverse (a+a-1) ((ha.add ha).sub (IsSelfAdjoint.one A)) (-Complex.I) (by simp)).2
  rw [Algebra.algebraMap_eq_smul_one,neg_smul,sub_neg_eq_add] at hr
  have hR : R*((a-1)+(a-1)) = 1 - (1+Complex.I) • R := by
    calc
      R*((a-1)+(a-1)) = R*(a+a-1+Complex.I • (1:A)) - (1+Complex.I) • R := by
        simp only [mul_add,mul_sub,mul_smul_comm,mul_one]
        module
      _ = _ := by rw [hr]
  rw [projectionSwitch_eq a ha]
  change (-Complex.I) • (1:A) - (2:ℂ) • R + 1 = (1-Complex.I) • (R*((a-1)+(a-1)))
  rw [hR,smul_sub,smul_smul]
  have hc : (1-Complex.I)*(1+Complex.I) = (2:ℂ) := by
    calc
      _ = 1-Complex.I^2 := by ring
      _ = _ := by norm_num
  rw [hc]
  module

lemma projectionSwitch_commutator_norm (a : A) (ha : IsSelfAdjoint a) (b : A) :
    ‖b*projectionSwitch a-projectionSwitch a*b‖ ≤ 4*‖b*a-a*b‖ := by
  rw [projectionSwitch,mul_smul_comm,smul_mul_assoc,← smul_sub,norm_smul]
  simp only [norm_neg,Complex.norm_I,one_mul]
  apply (saCayley_commutator_norm _ ((ha.add ha).sub (IsSelfAdjoint.one A)) b).trans
  have he : b*(a+a-1)-(a+a-1)*b = (b*a-a*b)+(b*a-a*b) := by noncomm_ring
  rw [he]
  have hn := norm_add_le (b*a-a*b) (b*a-a*b)
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projectionSwitch_fixed_error (a : A) (ha : IsSelfAdjoint a)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    ‖π (projectionSwitch a) v-v‖ ≤ 4*‖π a v‖ := by
  have hR : ‖π (saResolvent (a+a-1) (-Complex.I))‖ ≤ 1 := by
    exact (NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom _).trans (by
      simpa using saResolvent_norm_le _ ((ha.add ha).sub (IsSelfAdjoint.one A)) (-Complex.I) (by simp))
  have hc : ‖(-(1+Complex.I):ℂ)‖ ≤ 2 := by
    simpa only [norm_neg,norm_one,Complex.norm_I,one_add_one_eq_two] using norm_add_le (1:ℂ) Complex.I
  have he : π (projectionSwitch a) v-v = π (projectionSwitch a-1) v := by
    simp only [map_sub,map_one,sub_apply,one_apply_eq_self]
  rw [he,projectionSwitch_sub_one a ha,map_smul,map_mul,smul_apply,mul_apply_eq_comp,
    map_add,add_apply,norm_smul]
  calc
    _ ≤ 2 * (‖π (saResolvent (a+a-1) (-Complex.I))‖ * ‖π a v+π a v‖) :=
      mul_le_mul hc ((π (saResolvent (a+a-1) (-Complex.I))).le_opNorm _) (norm_nonneg _) (by norm_num)
    _ ≤ 2 * (1 * (‖π a v‖+‖π a v‖)) := by gcongr; exact norm_add_le _ _
    _ = _ := by ring

lemma projectionSwitch_negated_error (a : A) (ha : IsSelfAdjoint a)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    ‖π (projectionSwitch a) v+v‖ ≤ 4*‖π a v-v‖ := by
  have hR : ‖π (saResolvent (a+a-1) (-Complex.I))‖ ≤ 1 := by
    exact (NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom _).trans (by
      simpa using saResolvent_norm_le _ ((ha.add ha).sub (IsSelfAdjoint.one A)) (-Complex.I) (by simp))
  have hc : ‖(1-Complex.I:ℂ)‖ ≤ 2 := by
    simpa only [norm_one,Complex.norm_I,one_add_one_eq_two] using norm_sub_le (1:ℂ) Complex.I
  have he : π (projectionSwitch a) v+v = π (projectionSwitch a+1) v := by
    simp only [map_add,map_one,add_apply,one_apply_eq_self]
  rw [he,projectionSwitch_add_one a ha,map_smul,map_mul,smul_apply,mul_apply_eq_comp,
    map_add,add_apply,map_sub,map_one,sub_apply,one_apply_eq_self,norm_smul]
  calc
    _ ≤ 2 * (‖π (saResolvent (a+a-1) (-Complex.I))‖ * ‖(π a v-v)+(π a v-v)‖) :=
      mul_le_mul hc ((π (saResolvent (a+a-1) (-Complex.I))).le_opNorm _) (norm_nonneg _) (by norm_num)
    _ ≤ 2 * (1 * (‖π a v-v‖+‖π a v-v‖)) := by gcongr; exact norm_add_le _ _
    _ = _ := by ring

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projectionSwitch_vector_error (a : A) (ha : IsSelfAdjoint a)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) :
    ‖π (projectionSwitch a) ξ-η‖ ≤
      2*(‖π a (ξ-η)-(ξ-η)‖+‖π a (ξ+η)‖) := by
  have hd := projectionSwitch_negated_error a ha π (ξ-η)
  have hs := projectionSwitch_fixed_error a ha π (ξ+η)
  have he : (2:ℂ) • (π (projectionSwitch a) ξ-η) =
      (π (projectionSwitch a) (ξ-η)+(ξ-η)) +
      (π (projectionSwitch a) (ξ+η)-(ξ+η)) := by
    simp only [map_sub,map_add]
    module
  have hn := norm_add_le (π (projectionSwitch a) (ξ-η)+(ξ-η))
    (π (projectionSwitch a) (ξ+η)-(ξ+η))
  rw [← he,norm_smul,Complex.norm_ofNat] at hn
  linarith

lemma unitary_commutator_product (v w : unitary A) (b : A) :
    ‖b * ((v:A)*(w:A))-((v:A)*(w:A))*b‖ ≤
      2*‖b‖*‖(v:A)-1‖ + ‖b*(w:A)-(w:A)*b‖ := by
  have he : b * ((v:A)*(w:A))-((v:A)*(w:A))*b =
      (b*(v:A)-(v:A)*b)*(w:A)+(v:A)*(b*(w:A)-(w:A)*b) := by noncomm_ring
  have hv : b*(v:A)-(v:A)*b = b*((v:A)-1)-((v:A)-1)*b := by noncomm_ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,hv]
  have hn := (norm_sub_le (b*((v:A)-1)) (((v:A)-1)*b)).trans
    (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  nlinarith

theorem corrected_projectionSwitch
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (a : A) (ha : IsSelfAdjoint a) (r : ℝ)
    (herr : 2*(‖π a (ξ-η)-(ξ-η)‖+‖π a (ξ+η)‖) ≤ r) (hr : r ≤ 1) :
    ∃ u : unitary A, π u ξ = η ∧ ∀ b : A,
      ‖b*(u:A)-(u:A)*b‖ ≤ 192*‖b‖*r+4*‖b*a-a*b‖ := by
  let ρ := irreducibleUnitalRepresentation π hπ
  let w : unitary A := ⟨projectionSwitch a,projectionSwitch_unitary a ha⟩
  have hw : ρ (w:A) ∈ unitary (H →L[ℂ] H) := by
    rw [Unitary.mem_iff]
    constructor
    · rw [← map_star,← map_mul,(Unitary.mem_iff.mp w.property).1,map_one]
    · rw [← map_star,← map_mul,(Unitary.mem_iff.mp w.property).2,map_one]
  have hwn : ‖π (w:A) ξ‖ = 1 :=
    ((ρ (w:A)).norm_map_of_mem_unitary hw ξ).trans hξ
  have hwe : ‖π (w:A) ξ-η‖ ≤ r :=
    (projectionSwitch_vector_error a ha ρ ξ η).trans herr
  obtain ⟨v,hv,hvn⟩ := irreducible_near_unitary_vector π hπ
    (π (w:A) ξ) η hwn hη (hwe.trans hr)
  refine ⟨v*w,?_,fun b => ?_⟩
  · change π ((v:A)*(w:A)) ξ = η
    rw [map_mul,mul_apply_eq_comp]
    exact hv
  · change ‖b*((v:A)*(w:A))-((v:A)*(w:A))*b‖ ≤ _
    refine (unitary_commutator_product v w b).trans ?_
    have hn := projectionSwitch_commutator_norm a ha b
    change ‖b*(w:A)-(w:A)*b‖ ≤ _ at hn
    have hvr : ‖(v:A)-1‖ ≤ 96*r := hvn.trans (by gcongr)
    nlinarith [norm_nonneg b]

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

def rowAverage (x : ι → A) (a : A) : A := ∑ i, x i*a*star (x i)

lemma rowAverage_selfAdjoint (x : ι → A) (a : A) (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (rowAverage x a) := by
  change star (∑ i, x i*a*star (x i)) = _
  simp only [star_sum,star_mul,star_star,ha.star_eq,mul_assoc,rowAverage]

lemma rowAverage_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (x : ι → A) (a : A) (v : H) :
    π (rowAverage x a) v = ∑ i, π (x i) (π a (π (star (x i)) v)) := by
  simp only [rowAverage,map_sum,sum_apply,map_mul,mul_apply_eq_comp]

lemma rowAverage_apply_one (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : ι → A) (v : H) :
    π (rowAverage x 1) v = ∑ i, π (x i) (π (star (x i)) v) := by
  simp only [rowAverage_apply,irreducible_map_one π hπ,one_apply_eq_self]

lemma rowAverage_error (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : ι → A) (a : A) (v : H) (ε : ℝ)
    (he : ∀ i, ‖π a (π (star (x i)) v) - π (star (x i)) v‖ ≤ ε) :
    ‖π (rowAverage x a) v - π (rowAverage x 1) v‖ ≤ (∑ i, ‖x i‖)*ε := by
  rw [rowAverage_apply,rowAverage_apply_one π hπ,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖π (x i) (π a (π (star (x i)) v)-π (star (x i)) v)‖ := by
      simpa only [map_sub] using norm_sum_le Finset.univ
        (fun i => π (x i) (π a (π (star (x i)) v))-π (x i) (π (star (x i)) v))
    _ ≤ ∑ i, ‖x i‖*ε := by
      apply Finset.sum_le_sum
      intro i _
      exact ((π (x i)).le_opNorm _).trans
        (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π _) (he i) (norm_nonneg _) (norm_nonneg _))
    _ = _ := Finset.sum_mul _ _ _ |>.symm

lemma rowAverage_small (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (x : ι → A) (a : A) (v : H) (ε : ℝ)
    (he : ∀ i, ‖π a (π (star (x i)) v)‖ ≤ ε) :
    ‖π (rowAverage x a) v‖ ≤ (∑ i, ‖x i‖)*ε := by
  rw [rowAverage_apply]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact ((π (x i)).le_opNorm _).trans
    (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π _) (he i) (norm_nonneg _) (norm_nonneg _))

lemma rowAverage_pair_error (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : ι → A) (a : A) (ξ η : H) (hfix : π (rowAverage x 1) ξ = ξ)
    (ε : ℝ)
    (hd : ∀ i, ‖π a (π (star (x i)) ξ-π (star (x i)) η)-
      (π (star (x i)) ξ-π (star (x i)) η)‖ ≤ ε)
    (hs : ∀ i, ‖π a (π (star (x i)) ξ+π (star (x i)) η)‖ ≤ ε) :
    ‖π (rowAverage x a) (ξ-η)-(ξ-η)‖ + ‖π (rowAverage x a) (ξ+η)‖ ≤
      2*(∑ i, ‖x i‖)*ε + ‖π (rowAverage x 1) η-η‖ := by
  have hd' := rowAverage_error π hπ x a (ξ-η) ε (by simpa only [map_sub] using hd)
  have hs' := rowAverage_small π x a (ξ+η) ε (by simpa only [map_add] using hs)
  have hb : ‖π (rowAverage x 1) (ξ-η)-(ξ-η)‖ = ‖π (rowAverage x 1) η-η‖ := by
    rw [map_sub,hfix]
    have he : ξ-π (rowAverage x 1) η-(ξ-η) = -(π (rowAverage x 1) η-η) := by abel
    rw [he,norm_neg]
  have hn := norm_sub_le_norm_sub_add_norm_sub (π (rowAverage x a) (ξ-η))
    (π (rowAverage x 1) (ξ-η)) (ξ-η)
  rw [hb] at hn
  linarith

variable [PartialOrder A] [StarOrderedRing A]

theorem orthogonal_row_interchange
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : ι → A) (ξ : H) (hξ : ‖ξ‖ = 1) (hfix : π (rowAverage x 1) ξ = ξ)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : H, ‖η‖ = 1 →
      (∀ i j, ⟪π (star (x i)) ξ,π (star (x j)) η⟫_ℂ = 0) →
      (∀ i j, ‖⟪π (star (x i)) ξ,π (star (x j)) ξ⟫_ℂ-
        ⟪π (star (x i)) η,π (star (x j)) η⟫_ℂ‖ ≤ δ) →
      ‖π (rowAverage x 1) η-η‖ ≤ r/4 →
      ∃ (a : A) (u : unitary A), 0 ≤ a ∧ a ≤ 1 ∧ π u ξ = η ∧
        ∀ b : A, ‖b*(u:A)-(u:A)*b‖ ≤ 192*‖b‖*r +
          4*‖b*rowAverage x a-rowAverage x a*b‖ := by
  let C : ℝ := ∑ i, ‖x i‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let ε := r/(16*(C+1))
  have hε : 0 < ε := div_pos hr (by positivity)
  obtain ⟨δ,hδ,hgeom⟩ := approximate_gram_positive_lift π hπ
    (fun i => π (star (x i)) ξ) ε hε
  refine ⟨δ,hδ,fun η hη ho hg hb => ?_⟩
  obtain ⟨a,ha,ha1,hd,hs⟩ := hgeom (fun i => π (star (x i)) η) ho hg
  have he := rowAverage_pair_error π hπ x a ξ η hfix ε
    (fun i => (hd i).le) (fun i => (hs i).le)
  have hc : 4*C*ε ≤ r/4 := by
    dsimp [ε]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have heq : 4*C*(r/(16*(C+1)))*4 = r*(C/(C+1)) := by field_simp; ring
    rw [heq]
    exact mul_le_of_le_one_right hr.le ((div_le_one (by positivity)).mpr (by linarith))
  have herr : 2*(‖π (rowAverage x a) (ξ-η)-(ξ-η)‖ +
      ‖π (rowAverage x a) (ξ+η)‖) ≤ r := by
    change _ ≤ 2*C*ε+_ at he
    linarith
  obtain ⟨u,hu,hcomm⟩ := corrected_projectionSwitch π hπ ξ η hξ hη
    (rowAverage x a) (rowAverage_selfAdjoint x a (IsSelfAdjoint.of_nonneg ha)) r herr hr1
  exact ⟨a,u,ha,ha1,hu,hcomm⟩

end KOS

open scoped InnerProductSpace ComplexStarModule
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma near_congruence_operator (ξ η : H) (s t : ℝ) (hξ : ‖ξ‖ = 1)
    (hs : ⟪ξ,η⟫_ℂ = (s:ℂ)) (ht : ‖η-ξ‖ ≤ t) (ht' : t ≤ 1/2) :
    ∃ D : H →L[ℂ] H, ‖D‖ ≤ 6*t ∧
      (1+D) η = (Real.sqrt s : ℂ) • ξ ∧
      star (1+D) ξ = ((Real.sqrt s)⁻¹ : ℝ) • ξ := by
  have ht0 : 0 ≤ t := (norm_nonneg _).trans ht
  have hss : |s-1| ≤ t := by
    have hi := norm_inner_le_norm (𝕜 := ℂ) ξ (η-ξ)
    rw [inner_sub_right,hs,inner_self_eq_norm_sq_to_K,hξ] at hi
    norm_num at hi
    have hn : ‖(s:ℂ)-1‖ = |s-1| := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [hn] at hi
    exact hi.trans ht
  have hslo : 1/2 ≤ s := by have := neg_le_of_abs_le hss; linarith
  have hsp : 0 < s := lt_of_lt_of_le (by norm_num) hslo
  have hrp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hsp
  have hrsq : (Real.sqrt s)^2 = s := Real.sq_sqrt hsp.le
  have hrlo : 1/2 ≤ Real.sqrt s := by nlinarith [Real.sqrt_nonneg s]
  have hrerr : |Real.sqrt s - 1| ≤ t := by
    apply abs_le.mpr
    obtain ⟨hl,hu⟩ := abs_le.mp hss
    constructor <;> nlinarith [Real.sqrt_nonneg s]
  have hci : |(Real.sqrt s)⁻¹-1| ≤ 2*t := by
    have he : (Real.sqrt s)⁻¹-1 = (1-Real.sqrt s)/Real.sqrt s := by field_simp
    rw [he,abs_div,abs_sub_comm,abs_of_pos hrp]
    apply (div_le_iff₀ hrp).mpr
    exact hrerr.trans (by nlinarith)
  have hsi : s⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hsp).mpr
    linarith
  let w : H := η-(s:ℂ) • ξ
  have hw : ⟪ξ,w⟫_ℂ = 0 := by
    simp only [w,inner_sub_right,inner_smul_right,hs,inner_self_eq_norm_sq_to_K,hξ]
    norm_num
  have hwn : ‖w‖ ≤ 2*t := by
    have he : w = (η-ξ)+(1-(s:ℂ)) • ξ := by dsimp [w]; module
    have hn : ‖1-(s:ℂ)‖ = |s-1| := by
      rw [norm_sub_rev,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [he]
    calc
      _ ≤ ‖η-ξ‖+‖(1-(s:ℂ)) • ξ‖ := norm_add_le _ _
      _ = ‖η-ξ‖+|s-1| := by rw [norm_smul,hn,hξ,mul_one]
      _ ≤ 2*t := by linarith
  let D : H →L[ℂ] H := ((Real.sqrt s)⁻¹-1) • InnerProductSpace.rankOne ℂ ξ ξ -
    s⁻¹ • InnerProductSpace.rankOne ℂ w ξ
  refine ⟨D,?_,?_,?_⟩
  · calc
      ‖D‖ ≤ ‖((Real.sqrt s)⁻¹-1) • InnerProductSpace.rankOne ℂ ξ ξ‖ +
          ‖s⁻¹ • InnerProductSpace.rankOne ℂ w ξ‖ := norm_sub_le _ _
      _ = |(Real.sqrt s)⁻¹-1| + s⁻¹*‖w‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          InnerProductSpace.norm_rankOne,InnerProductSpace.norm_rankOne,hξ,
          abs_of_pos (inv_pos.mpr hsp)]
        ring
      _ ≤ 6*t := by nlinarith [mul_le_mul hsi hwn (norm_nonneg w) (by norm_num : (0:ℝ)≤2)]
  · simp only [D,add_apply,one_apply_eq_self,sub_apply,smul_apply,
      InnerProductSpace.rankOne_apply,hs,Complex.coe_smul,smul_smul]
    rw [inv_mul_cancel₀ hsp.ne',one_smul]
    have hmul : (Real.sqrt s)⁻¹*s = Real.sqrt s := by
      calc
        _ = (Real.sqrt s)⁻¹*((Real.sqrt s)^2) := congrArg ((Real.sqrt s)⁻¹ * ·) hrsq.symm
        _ = _ := by rw [pow_two,← mul_assoc,inv_mul_cancel₀ hrp.ne',one_mul]
    have he : ((Real.sqrt s)⁻¹-1)*s = Real.sqrt s-s := by
      calc
        _ = (Real.sqrt s)⁻¹*s-s := by ring
        _ = _ := by rw [hmul]
    rw [he]
    dsimp [w]
    module
  · have hw' : ⟪w,ξ⟫_ℂ = 0 := inner_eq_zero_symm.mp hw
    simp only [D,star_add,star_one,star_sub,star_smul,star_trivial,
      ContinuousLinearMap.star_eq_adjoint,InnerProductSpace.adjoint_rankOne,
      add_apply,one_apply_eq_self,sub_apply,smul_apply,InnerProductSpace.rankOne_apply,
      inner_self_eq_norm_sq_to_K,hξ,hw']
    norm_num only [one_pow,Complex.ofReal_one,one_smul,zero_smul,smul_zero,sub_zero]
    module

variable {A : Type*} [CStarAlgebra A]

lemma irreducible_near_congruence
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (P : A) (hP : IsSelfAdjoint P) (ξ : H) (hξ : ‖ξ‖ = 1)
    (t : ℝ) (ht : ‖π P ξ-ξ‖ ≤ t) (ht' : t ≤ 1/2) :
    ∃ b : A, ‖b-1‖ ≤ 48*t ∧ π (b*P*star b) ξ = ξ := by
  let s : ℝ := (⟪ξ,π P ξ⟫_ℂ).re
  have hs : ⟪ξ,π P ξ⟫_ℂ = (s:ℂ) := by
    apply Complex.ext
    · rfl
    change (⟪ξ,π P ξ⟫_ℂ).im = 0
    have hp := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hP.map π)).im_inner_self_apply ξ
    exact hp
  obtain ⟨D,hD,hDη,hDξ⟩ := near_congruence_operator ξ (π P ξ) s t hξ hs ht ht'
  let M := Submodule.span ℂ ({ξ,π P ξ} : Set H)
  have : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  obtain ⟨a,ha,hact⟩ := irreducible_adjoint_transitivity π hπ M D
  have hξM : ξ ∈ M := Submodule.subset_span (by simp)
  have hηM : π P ξ ∈ M := Submodule.subset_span (by simp)
  have hA : π (1+a) (π P ξ) = (Real.sqrt s : ℂ) • ξ := by
    rw [map_add,add_apply,irreducible_map_one π hπ,one_apply_eq_self,(hact _ hηM).1]
    exact hDη
  have hA' : π (star (1+a)) ξ = ((Real.sqrt s)⁻¹ : ℝ) • ξ := by
    rw [star_add,star_one,map_add,add_apply,irreducible_map_one π hπ,
      one_apply_eq_self,(hact _ hξM).2]
    simpa only [star_add,star_one,add_apply,one_apply_eq_self] using hDξ
  have hsp : 0 < s := by
    have hi := norm_inner_le_norm (𝕜 := ℂ) ξ (π P ξ-ξ)
    rw [inner_sub_right,hs,inner_self_eq_norm_sq_to_K,hξ] at hi
    norm_num at hi
    have hn : ‖(s:ℂ)-1‖ = |s-1| := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [hn] at hi
    have hl := neg_le_of_abs_le (hi.trans ht)
    linarith
  refine ⟨1+a,by simpa using ha.trans (by linarith : 8*‖D‖ ≤ 48*t),?_⟩
  rw [map_mul,map_mul,mul_apply_eq_comp,mul_apply_eq_comp,hA',← Complex.coe_smul,
    map_smul,map_smul,hA,smul_smul,← Complex.ofReal_mul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hsp).ne',Complex.ofReal_one,one_smul]

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

omit partialOrderA starOrderedRingA in
lemma rowAverage_pair_error_approx [PartialOrder A] [StarOrderedRing A]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : ι → A) (a : A) (ξ η : H) (ε : ℝ)
    (hd : ∀ i, ‖π a (π (star (x i)) ξ-π (star (x i)) η)-
      (π (star (x i)) ξ-π (star (x i)) η)‖ ≤ ε)
    (hs : ∀ i, ‖π a (π (star (x i)) ξ+π (star (x i)) η)‖ ≤ ε) :
    ‖π (rowAverage x a) (ξ-η)-(ξ-η)‖ + ‖π (rowAverage x a) (ξ+η)‖ ≤
      2*(∑ i, ‖x i‖)*ε + ‖π (rowAverage x 1) ξ-ξ‖ +
        ‖π (rowAverage x 1) η-η‖ := by
  have hd' := rowAverage_error π hπ x a (ξ-η) ε (by simpa only [map_sub] using hd)
  have hs' := rowAverage_small π x a (ξ+η) ε (by simpa only [map_add] using hs)
  have hb : ‖π (rowAverage x 1) (ξ-η)-(ξ-η)‖ ≤
      ‖π (rowAverage x 1) ξ-ξ‖ + ‖π (rowAverage x 1) η-η‖ := by
    rw [map_sub]
    calc
      _ = ‖(π (rowAverage x 1) ξ-ξ)-(π (rowAverage x 1) η-η)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hn := norm_sub_le_norm_sub_add_norm_sub (π (rowAverage x a) (ξ-η))
    (π (rowAverage x 1) (ξ-η)) (ξ-η)
  linarith

theorem orthogonal_row_interchange_approx
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : ι → A) (ξ : H) (hξ : ‖ξ‖ = 1)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hfix : ‖π (rowAverage x 1) ξ-ξ‖ ≤ r/8) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : H, ‖η‖ = 1 →
      (∀ i j, ⟪π (star (x i)) ξ,π (star (x j)) η⟫_ℂ = 0) →
      (∀ i j, ‖⟪π (star (x i)) ξ,π (star (x j)) ξ⟫_ℂ-
        ⟪π (star (x i)) η,π (star (x j)) η⟫_ℂ‖ ≤ δ) →
      ‖π (rowAverage x 1) η-η‖ ≤ r/8 →
      ∃ (a : A) (u : unitary A), 0 ≤ a ∧ a ≤ 1 ∧ π u ξ = η ∧
        ∀ b : A, ‖b*(u:A)-(u:A)*b‖ ≤ 192*‖b‖*r +
          4*‖b*rowAverage x a-rowAverage x a*b‖ := by
  let C : ℝ := ∑ i, ‖x i‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let ε := r/(16*(C+1))
  have hε : 0 < ε := div_pos hr (by positivity)
  obtain ⟨δ,hδ,hgeom⟩ := approximate_gram_positive_lift π hπ
    (fun i => π (star (x i)) ξ) ε hε
  refine ⟨δ,hδ,fun η hη ho hg hb => ?_⟩
  obtain ⟨a,ha,ha1,hd,hs⟩ := hgeom (fun i => π (star (x i)) η) ho hg
  have he := rowAverage_pair_error_approx π hπ x a ξ η ε
    (fun i => (hd i).le) (fun i => (hs i).le)
  have hc : 4*C*ε ≤ r/4 := by
    dsimp [ε]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have heq : 4*C*(r/(16*(C+1)))*4 = r*(C/(C+1)) := by field_simp; ring
    rw [heq]
    exact mul_le_of_le_one_right hr.le ((div_le_one (by positivity)).mpr (by linarith))
  have herr : 2*(‖π (rowAverage x a) (ξ-η)-(ξ-η)‖ +
      ‖π (rowAverage x a) (ξ+η)‖) ≤ r := by
    change _ ≤ 2*C*ε+_+_ at he
    linarith
  obtain ⟨u,hu,hcomm⟩ := corrected_projectionSwitch π hπ ξ η hξ hη
    (rowAverage x a) (rowAverage_selfAdjoint x a (IsSelfAdjoint.of_nonneg ha)) r herr hr1
  exact ⟨a,u,ha,ha1,hu,hcomm⟩

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [fintypeι : Fintype ι]

def rowDefectTest (x : ι → A) : A :=
  star (rowAverage x 1-1)*(rowAverage x 1-1)

def rowFrameTests (x : ι → A) : Finset A := by
  classical
  exact (Finset.univ.image (fun ij : ι × ι => x ij.1*star (x ij.2))) ∪ {rowDefectTest x}

lemma gram_mem_rowFrameTests (x : ι → A) (i j : ι) :
    x i*star (x j) ∈ rowFrameTests x := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩)

lemma defect_mem_rowFrameTests (x : ι → A) : rowDefectTest x ∈ rowFrameTests x := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

omit fintypeι in
lemma row_frame_coefficient [Fintype ι] (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : ι → A) (v : H) (i j : ι) :
    ⟪π (star (x i)) v,π (star (x j)) v⟫_ℂ =
      vectorFunctional π v (x i*star (x j)) := by
  simp only [vectorFunctional_apply,map_mul,map_star,mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]

lemma row_defect_coefficient (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : ι → A) (v : H) :
    ‖π (rowAverage x 1) v-v‖^2 = (vectorFunctional π v (rowDefectTest x)).re := by
  rw [rowDefectTest,vectorFunctional_square,← Complex.ofReal_pow,Complex.ofReal_re]
  simp only [map_sub,sub_apply,hone,one_apply_eq_self]

lemma row_defect_zero (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : ι → A) (v : H) (h : π (rowAverage x 1) v = v) :
    vectorFunctional π v (rowDefectTest x) = 0 := by
  rw [rowDefectTest,vectorFunctional_square]
  simp only [map_sub,sub_apply,hone,one_apply_eq_self,h,sub_self,norm_zero,
    Complex.ofReal_zero,zero_pow (by norm_num : 2 ≠ 0)]

lemma row_defect_bound (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : ι → A) (v : H) (r : ℝ) (hr : 0 ≤ r)
    (h : ‖vectorFunctional π v (rowDefectTest x)‖ ≤ r^2) :
    ‖π (rowAverage x 1) v-v‖ ≤ r := by
  have hs := (Complex.re_le_norm (vectorFunctional π v (rowDefectTest x))).trans h
  rw [← row_defect_coefficient π hone x v] at hs
  nlinarith [norm_nonneg (π (rowAverage x 1) v-v)]

lemma unitary_commutator_star (u : unitary A) (b : A) :
    ‖b*star (u:A)-star (u:A)*b‖ = ‖b*(u:A)-(u:A)*b‖ := by
  have he : b*star (u:A)-star (u:A)*b =
      -(star (u:A)*(b*(u:A)-(u:A)*b)*star (u:A)) := by
    rw [mul_sub,sub_mul]
    simp only [← mul_assoc,u.property.1,one_mul]
    simp only [mul_assoc,u.property.2,mul_one]
    abel
  rw [he,norm_neg]
  change ‖(star u:A)*(b*(u:A)-(u:A)*b)*(star u:A)‖ = _
  calc
    _ = ‖(star u:A)*(b*(u:A)-(u:A)*b)‖ :=
      CStarRing.norm_mul_coe_unitary _ (star u)
    _ = _ := CStarRing.norm_coe_unitary_mul (star u) _

lemma unitary_commutator_sum (u v : unitary A) (b : A) :
    ‖b*((u*v:A))-(u*v:A)*b‖ ≤
      ‖b*(u:A)-(u:A)*b‖ + ‖b*(v:A)-(v:A)*b‖ := by
  have he : b*((u:A)*(v:A))-((u:A)*(v:A))*b =
      (b*(u:A)-(u:A)*b)*(v:A)+(u:A)*(b*(v:A)-(v:A)*b) := by noncomm_ring
  rw [he]
  simpa only [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul] using norm_add_le
    ((b*(u:A)-(u:A)*b)*(v:A)) ((u:A)*(b*(v:A)-(v:A)*b))

end KOS

open scoped InnerProductSpace
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def upperCutoff (s t : ℝ) : ℝ := max (t-s) 0

lemma continuous_upperCutoff (s : ℝ) : Continuous (upperCutoff s) := by
  unfold upperCutoff
  fun_prop

lemma upperCutoff_positive_form (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (s : ℝ) :
    0 ≤ cfc (upperCutoff s) T * (T-s • (1:H →L[ℂ] H)) * cfc (upperCutoff s) T := by
  let f := upperCutoff s
  have hid : cfc (fun t : ℝ => t-s) T = T-s • (1:H →L[ℂ] H) := by
    rw [cfc_sub _ _ T,cfc_id' ℝ T hT,cfc_const s T hT]
    rfl
  have hf : Continuous f := continuous_upperCutoff s
  rw [← hid,← cfc_mul f (fun t : ℝ => t-s) T (continuous_upperCutoff s).continuousOn (by fun_prop),
    ← cfc_mul (fun t : ℝ => f t*(t-s)) f T (hf.mul (continuous_id.sub continuous_const)).continuousOn hf.continuousOn]
  apply cfc_nonneg
  intro t _
  dsimp [f,upperCutoff]
  by_cases h : 0 ≤ t-s
  · rw [max_eq_left h]
    positivity
  · rw [max_eq_right (le_of_not_ge h)]
    simp

lemma upperCutoff_range_lower (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (s : ℝ)
    (v : H) (hv : v ∈ (cfc (upperCutoff s) T).range) :
    s*‖v‖^2 ≤ (⟪v,T v⟫_ℂ).re := by
  obtain ⟨w,rfl⟩ := hv
  let P := cfc (upperCutoff s) T
  have hP : IsSelfAdjoint P := cfc_predicate (upperCutoff s) T
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (upperCutoff_positive_form T hT s)).re_inner_nonneg_right w
  have he : ⟪w,(P*(T-s • (1:H →L[ℂ] H))*P) w⟫_ℂ =
      ⟪P w,T (P w)⟫_ℂ-(s:ℂ)*⟪P w,P w⟫_ℂ := by
    rw [mul_apply_eq_comp,mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_left]
    rw [← ContinuousLinearMap.star_eq_adjoint,hP.star_eq]
    simp only [sub_apply,smul_apply,one_apply_eq_self,inner_sub_right]
    rw [← Complex.coe_smul,inner_smul_right]
  change 0 ≤ (⟪w,(P*(T-s • (1:H →L[ℂ] H))*P) w⟫_ℂ).re at hp
  rw [he,Complex.sub_re,inner_self_eq_norm_sq_to_K] at hp
  have her : (⟪P w,P w⟫_ℂ).re = ‖P w‖^2 := by
    simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) (P w)).symm
  have hp' := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (upperCutoff_positive_form T hT s)).re_inner_nonneg_right w
  change 0 ≤ (⟪w,(P*(T-s • (1:H →L[ℂ] H))*P) w⟫_ℂ).re at hp'
  rw [he,Complex.sub_re,Complex.mul_re,her] at hp'
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hp'
  change s*‖P w‖^2 ≤ (⟪P w,T (P w)⟫_ℂ).re
  nlinarith

theorem upperCutoff_finiteDimensional_range
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (k s : ℝ) (hks : k < s)
    (hbound : ∀ v ∈ Mᗮ, ‖T v‖ ≤ k*‖v‖) :
    FiniteDimensional ℂ (cfc (upperCutoff s) T).range := by
  let P := cfc (upperCutoff s) T
  let D := P.range
  let F : D →ₗ[ℂ] M := M.orthogonalProjectionOnto.toLinearMap.comp D.subtype
  apply FiniteDimensional.of_injective F
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro v hv
  change v = 0

  have hv0 : M.orthogonalProjectionOnto (v:H) = 0 := hv
  have hvo : (v:H) ∈ Mᗮ := (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp hv0
  have hl := upperCutoff_range_lower T hT s (v:H) v.property
  have hu := (Complex.re_le_norm ⟪(v:H),T (v:H)⟫_ℂ).trans (norm_inner_le_norm (v:H) (T (v:H)))
  have hb := hbound (v:H) hvo
  have hz : ‖(v:H)‖ = 0 := by
    by_contra hn
    have hp := lt_of_le_of_ne (norm_nonneg (v:H)) (Ne.symm hn)
    have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg (v:H))
    nlinarith [mul_pos (sub_pos.mpr hks) (sq_pos_of_pos hp)]
  apply Subtype.ext
  exact norm_eq_zero.mp hz

omit [CompleteSpace H] in
lemma isCompactOperator_of_finiteDimensional_range (T : H →L[ℂ] H)
    [FiniteDimensional ℂ T.range] : IsCompactOperator T := by
  let S : H →L[ℂ] T.range := T.codRestrict T.range (fun v => ⟨v,rfl⟩)
  have hS : IsCompactOperator S := isCompactOperator_of_locallyCompactSpace_dom S
  exact hS.clm_comp T.range.subtypeL

end KOS

open scoped InnerProductSpace CStarAlgebra
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def compactPreimageIdeal (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {a | IsCompactOperator (π a)}
    (by change IsCompactOperator (π 0); simpa only [map_zero,FunLike.coe_zero] using (isCompactOperator_zero : IsCompactOperator (0:H →L[ℂ] H)))
    (fun {a b} ha hb => by change IsCompactOperator (π (a+b)); simpa only [map_add,FunLike.coe_add] using ha.add hb)
    (fun {a} ha => by change IsCompactOperator (π (-a)); simpa only [map_neg,FunLike.coe_neg] using ha.neg)
    (fun {a b} hb => by change IsCompactOperator (π (a*b)); simpa only [map_mul,ContinuousLinearMap.mul_def,ContinuousLinearMap.coe_comp] using hb.clm_comp (π a))
    (fun {a b} ha => by change IsCompactOperator (π (a*b)); simpa only [map_mul,ContinuousLinearMap.mul_def,ContinuousLinearMap.coe_comp] using ha.comp_clm (π b))

lemma compactPreimageIdeal_isClosed (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    IsClosed (compactPreimageIdeal π : Set A) := by
  have h : IsClosed {T : H →L[ℂ] H | IsCompactOperator T} :=
    isClosed_setOfPred_isCompactOperator
  simpa only [compactPreimageIdeal,TwoSidedIdeal.coe_mk',Set.preimage_ofPred_eq] using
    h.preimage (map_continuous π)

lemma mem_compactPreimageIdeal (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    a ∈ compactPreimageIdeal π ↔ IsCompactOperator (π a) := by
  simp only [compactPreimageIdeal,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq]

theorem simple_infinite_no_compacts (hA : IsSimpleCStar A)
    (hinf : ¬ FiniteDimensional ℂ A)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (a : A) (ha : IsCompactOperator (π a)) : π a = 0 := by
  rcases hA.2 (compactPreimageIdeal π) (compactPreimageIdeal_isClosed π) with hb | ht
  · have ham : a ∈ compactPreimageIdeal π := (mem_compactPreimageIdeal π a).mpr ha
    rw [hb,TwoSidedIdeal.mem_bot] at ham
    rw [ham,map_zero]
  · have h1 : (1:A) ∈ compactPreimageIdeal π := by rw [ht]; exact TwoSidedIdeal.mem_top _
    rw [mem_compactPreimageIdeal] at h1
    rw [irreducible_map_one π hπ] at h1
    let : FiniteDimensional ℂ H := isCompactOperator_id_iff_finiteDimensional.mp h1
    exact False.elim (hinf (FiniteDimensional.of_injective (irreducibleUnitalRepresentation π hπ).toAlgHom.toLinearMap
      (simple_nonzeroStarHom_injective hA π hπ.1)))

variable [PartialOrder A] [StarOrderedRing A]

theorem no_compacts_large_vector
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hno : ∀ a : A, IsCompactOperator (π a) → π a = 0)
    (a : A) (ha : 0 ≤ a) (han : ‖π a‖ = 1)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (k : ℝ) (hk : k < 1) :
    ∃ v : H, ‖v‖ = 1 ∧ v ∈ Mᗮ ∧ k < ‖π a v‖ := by
  classical
  by_contra! hn
  have hb : ∀ v ∈ Mᗮ, ‖π a v‖ ≤ k*‖v‖ := by
    intro v hv
    by_cases hz : v = 0
    · simp only [hz,map_zero,norm_zero,mul_zero,le_refl]
    · have hp := norm_pos_iff.mpr hz
      let w := (‖v‖⁻¹:ℂ) • v
      have hwn : ‖w‖ = 1 := norm_smul_inv_norm hz
      have hwM : w ∈ Mᗮ := Mᗮ.smul_mem _ hv
      have he := hn w hwn hwM
      change ‖π a ((‖v‖⁻¹:ℂ) • v)‖ ≤ k at he
      rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_norm] at he
      simpa only [mul_comm] using (inv_mul_le_iff₀ hp).mp he
  let s : ℝ := (k+1)/2
  have hks : k < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hpa : 0 ≤ π a := map_nonneg π ha
  let : FiniteDimensional ℂ (cfc (upperCutoff s) (π a)).range :=
    upperCutoff_finiteDimensional_range (π a) (IsSelfAdjoint.of_nonneg hpa) M k s hks hb
  have hc : IsCompactOperator (π (cfc (upperCutoff s) a)) := by
    rw [π.map_cfc (upperCutoff s) a (continuous_upperCutoff s).continuousOn]
    exact isCompactOperator_of_finiteDimensional_range _
  have hz : cfc (upperCutoff s) (π a) = 0 := by
    rw [← π.map_cfc (upperCutoff s) a (continuous_upperCutoff s).continuousOn]
    exact hno _ hc
  have hneq : π a ≠ 0 := by intro he; simp [he] at han
  let : Nontrivial (H →L[ℂ] H) := nontrivial_of_ne _ _ hneq
  have hspec : (1:ℝ) ∈ spectrum ℝ (π a) := by
    rw [← han]
    exact CStarAlgebra.norm_mem_spectrum_of_nonneg (π a) hpa
  have he := eqOn_of_cfc_eq_cfc (hz.trans (cfc_const_zero ℝ (π a)).symm)
    (continuous_upperCutoff s).continuousOn continuous_const.continuousOn (IsSelfAdjoint.of_nonneg hpa)
  have he1 := he hspec
  change max (1-s) 0 = 0 at he1
  rw [max_eq_left (sub_nonneg.mpr hs1.le)] at he1
  linarith

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pure_vector_approximation_orthogonal
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hi : Function.Injective π)
    (hno : ∀ a : A, IsCompactOperator (π a) → π a = 0)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : H, ‖η‖ = 1 ∧ η ∈ Mᗮ ∧
      ∀ a ∈ F, ‖⟪η,π a η⟫_ℂ-f a‖ < ε := by
  obtain ⟨x,hx,hxn,_,hsmall⟩ := pure_state_finite_excision f hf F (ε/4) (by positivity)
  have hxsa : IsSelfAdjoint x := IsSelfAdjoint.of_nonneg hx
  have hpxsa : IsSelfAdjoint (π x) := hxsa.map π
  have hnorm : ‖π x‖ = 1 := by
    rw [(NonUnitalStarAlgHom.isometry π hi).norm_map_of_map_zero (map_zero π),hxn]
  let N := M.map (π x).toLinearMap
  let : FiniteDimensional ℂ N := inferInstanceAs (FiniteDimensional ℂ (M.map (π x).toLinearMap))
  obtain ⟨ζ,hζ,hζN,hζx⟩ := no_compacts_large_vector π hno x hx hnorm N (1/2) (by norm_num)
  let η := (‖π x ζ‖:ℂ)⁻¹ • π x ζ
  have hy : 0 < ‖π x ζ‖ := lt_trans (by norm_num) hζx
  have hη : ‖η‖ = 1 := by
    simp only [η,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hy.ne']
  have hyM : π x ζ ∈ Mᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.star_eq_adjoint,
      hpxsa.star_eq]
    exact N.inner_right_of_mem_orthogonal (Submodule.mem_map.mpr ⟨v,hv,rfl⟩) hζN
  refine ⟨η,hη,Mᗮ.smul_mem _ hyM,fun a ha => ?_⟩
  have hb := compressed_vector_coefficient_bound π.toNonUnitalStarAlgHom (map_one π)
    x hxsa ζ hζ.le hy a (f a)
  change ‖⟪η,π a η⟫_ℂ-f a‖ ≤ _ at hb
  have hinv : ‖π x ζ‖⁻¹ ≤ 2 := by
    have hh : (1/2:ℝ)⁻¹ = 2 := by norm_num
    rw [← hh]
    exact (inv_le_inv₀ hy (show 0 < (1/2:ℝ) by norm_num)).mpr hζx.le
  calc
    _ ≤ ‖π x ζ‖⁻¹^2 * ‖x*(a-f a • (1:A))*x‖ := hb
    _ ≤ 4 * ‖x*(a-f a • (1:A))*x‖ := by
      gcongr
      nlinarith [inv_nonneg.mpr hy.le]
    _ < 4*(ε/4) := by gcongr; exact hsmall a ha
    _ = ε := by ring

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

theorem third_vector_two_frames
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (hi : Function.Injective π)
    (hno : ∀ a : A, IsCompactOperator (π a) → π a = 0)
    (x : ι → A) (ξ η : H) (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ ζ : H, ‖ζ‖ = 1 ∧
      (∀ i j, ⟪π (star (x i)) ξ,π (star (x j)) ζ⟫_ℂ = 0) ∧
      (∀ i j, ⟪π (star (x i)) η,π (star (x j)) ζ⟫_ℂ = 0) ∧
      ∀ a ∈ F, ‖⟪ζ,π a ζ⟫_ℂ - f a‖ < ε := by
  classical
  let Q₁ : Finset H := Finset.univ.image (fun ij : ι × ι => π (x ij.2*star (x ij.1)) ξ)
  let Q₂ : Finset H := Finset.univ.image (fun ij : ι × ι => π (x ij.2*star (x ij.1)) η)
  let M : Submodule ℂ H := Submodule.span ℂ ((Q₁ ∪ Q₂ : Finset H) : Set H)
  let : FiniteDimensional ℂ M := inferInstanceAs
    (FiniteDimensional ℂ (Submodule.span ℂ ((Q₁ ∪ Q₂ : Finset H) : Set H)))
  obtain ⟨ζ,hζ,hζM,htest⟩ := pure_vector_approximation_orthogonal
    (irreducibleUnitalRepresentation π hπ) hi hno f hf M F ε hε
  have horth (v : H) (hv : ∀ i j, π (x j*star (x i)) v ∈ M) :
      ∀ i j, ⟪π (star (x i)) v,π (star (x j)) ζ⟫_ℂ = 0 := by
    intro i j
    rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.star_eq_adjoint,
      ← map_star,star_star,← mul_apply_eq_comp,← map_mul]
    exact M.inner_right_of_mem_orthogonal (hv i j) hζM
  refine ⟨ζ,hζ,horth ξ ?_,horth η ?_,htest⟩
  · intro i j
    apply Submodule.subset_span
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩)
  · intro i j
    apply Submodule.subset_span
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩)

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

theorem row_controlled_matching
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (hi : Function.Injective π)
    (hno : ∀ a : A, IsCompactOperator (π a) → π a = 0)
    (x : ι → A) (ξ : H) (hξ : ‖ξ‖ = 1) (hfix : π (rowAverage x 1) ξ = ξ)
    (F : Finset A) (c : ℝ)
    (hcentral : ∀ b ∈ F, ∀ a : A, 0 ≤ a → a ≤ 1 →
      ‖b*rowAverage x a-rowAverage x a*b‖ ≤ c)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : H, ‖η‖ = 1 →
      (∀ a ∈ rowFrameTests x,
        ‖vectorFunctional π ξ a-vectorFunctional π η a‖ < δ) →
      ∃ u : unitary A, π u ξ = η ∧ ∀ b ∈ F,
        ‖b*(u:A)-(u:A)*b‖ ≤ 384*‖b‖*r+8*c := by
  have hone := irreducible_map_one π hπ
  have hξd : ‖π (rowAverage x 1) ξ-ξ‖ ≤ r/8 := by rw [hfix,sub_self,norm_zero]; positivity
  obtain ⟨δ₁,hδ₁,hmatch₁⟩ := orthogonal_row_interchange_approx π hπ x ξ hξ r hr hr1 hξd
  let q : ℝ := (r/16)^2
  have hq : 0 < q := sq_pos_of_pos (div_pos hr (by norm_num))
  let δ : ℝ := min (δ₁/2) q
  have hδ : 0 < δ := lt_min (by positivity) hq
  refine ⟨δ,hδ,fun η hη hclose => ?_⟩
  have hηq : ‖vectorFunctional π η (rowDefectTest x)‖ ≤ q := by
    have hh := hclose _ (defect_mem_rowFrameTests x)
    rw [row_defect_zero π hone x ξ hfix,zero_sub,norm_neg] at hh
    exact hh.le.trans (min_le_right _ _)
  have hηd : ‖π (rowAverage x 1) η-η‖ ≤ r/16 :=
    row_defect_bound π hone x η (r/16) (by positivity) hηq
  obtain ⟨δ₂,hδ₂,hmatch₂⟩ := orthogonal_row_interchange_approx π hπ x η hη r hr hr1
    (hηd.trans (by linarith))
  let α : ℝ := min (δ₁/2) (min δ₂ q)
  have hα : 0 < α := lt_min (by positivity) (lt_min hδ₂ hq)
  obtain ⟨hpη,_⟩ := irreducible_vector_pure_equivalent π hπ η hη
  obtain ⟨ζ,hζ,ho₁,ho₂,htest⟩ := third_vector_two_frames π hπ hi hno x ξ η
    (vectorFunctional π η) hpη (rowFrameTests x) α hα
  have htest' (a : A) (ha : a ∈ rowFrameTests x) :
      ‖vectorFunctional π η a-vectorFunctional π ζ a‖ < α := by
    rw [norm_sub_rev]
    exact htest a ha
  have hζq : ‖vectorFunctional π ζ (rowDefectTest x)‖ ≤ (r/8)^2 := by
    have hb := norm_sub_le_norm_sub_add_norm_sub
      (vectorFunctional π ζ (rowDefectTest x)) (vectorFunctional π η (rowDefectTest x)) 0
    simp only [sub_zero] at hb
    have hh := (htest _ (defect_mem_rowFrameTests x)).le
    have hαq : α ≤ q := (min_le_right _ _).trans (min_le_right _ _)
    change ‖vectorFunctional π ζ (rowDefectTest x)-vectorFunctional π η (rowDefectTest x)‖ ≤ α at hh
    change ‖vectorFunctional π η (rowDefectTest x)‖ ≤ (r/16)^2 at hηq
    change α ≤ (r/16)^2 at hαq
    nlinarith [sq_nonneg r]
  have hζd : ‖π (rowAverage x 1) ζ-ζ‖ ≤ r/8 :=
    row_defect_bound π hone x ζ (r/8) (by positivity) hζq
  have hg₁ (i j : ι) : ‖⟪π (star (x i)) ξ,π (star (x j)) ξ⟫_ℂ-
      ⟪π (star (x i)) ζ,π (star (x j)) ζ⟫_ℂ‖ ≤ δ₁ := by
    rw [row_frame_coefficient,row_frame_coefficient]
    have hh := hclose _ (gram_mem_rowFrameTests x i j)
    have hh' := htest' _ (gram_mem_rowFrameTests x i j)
    have hb := norm_sub_le_norm_sub_add_norm_sub
      (vectorFunctional π ξ (x i*star (x j))) (vectorFunctional π η (x i*star (x j)))
      (vectorFunctional π ζ (x i*star (x j)))
    have hd : δ ≤ δ₁/2 := min_le_left _ _
    have ha : α ≤ δ₁/2 := min_le_left _ _
    linarith
  have hg₂ (i j : ι) : ‖⟪π (star (x i)) η,π (star (x j)) η⟫_ℂ-
      ⟪π (star (x i)) ζ,π (star (x j)) ζ⟫_ℂ‖ ≤ δ₂ := by
    rw [row_frame_coefficient,row_frame_coefficient]
    exact (htest' _ (gram_mem_rowFrameTests x i j)).le.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨a₁,u₁,ha₁,ha₁',hu₁,hc₁⟩ := hmatch₁ ζ hζ ho₁ hg₁ hζd
  obtain ⟨a₂,u₂,ha₂,ha₂',hu₂,hc₂⟩ := hmatch₂ ζ hζ ho₂ hg₂ hζd
  refine ⟨star u₂*u₁,?_,fun b hb => ?_⟩
  · change π (star (u₂:A)*(u₁:A)) ξ = η
    rw [map_mul,mul_apply_eq_comp,hu₁,← hu₂,← mul_apply_eq_comp,← map_mul,
      u₂.property.1,hone,one_apply_eq_self]
  · refine (unitary_commutator_sum (star u₂) u₁ b).trans ?_
    change ‖b*star (u₂:A)-star (u₂:A)*b‖ + ‖b*(u₁:A)-(u₁:A)*b‖ ≤ _
    rw [unitary_commutator_star]
    have h₁ := hc₁ b
    have h₂ := hc₂ b
    have h₁' := hcentral b hb a₁ ha₁ ha₁'
    have h₂' := hcentral b hb a₂ ha₂ ha₂'
    linarith

end KOS

end NaimarkZFC

end

end OAI
