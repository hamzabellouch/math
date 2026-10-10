import Mathlib
import OAI.RepresentationTheory.GraphModels.Regular

namespace OAI

noncomputable section

/-! Commuting normal actions and regular multiplicities. -/

namespace GraphNormality
section
open ArithmeticGerms GermBundles
open scoped InnerProductSpace
section WeakOperatorAlgebras
variable {L W : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

def wotLift (F : (L →L[ℂ] L) →⋆ₐ[ℂ] (W →L[ℂ] W)) :
    (L →WOT[ℂ] L) →⋆ₐ[ℂ] (W →WOT[ℂ] W) where
  toFun T := ContinuousLinearMapWOT.ofCLM (F T.toCLM)
  map_one' := congrArg ContinuousLinearMapWOT.ofCLM (map_one F)
  map_mul' T S := congrArg ContinuousLinearMapWOT.ofCLM (map_mul F T.toCLM S.toCLM)
  map_add' T S := congrArg ContinuousLinearMapWOT.ofCLM (map_add F T.toCLM S.toCLM)
  map_zero' := congrArg ContinuousLinearMapWOT.ofCLM (map_zero F)
  commutes' z := congrArg ContinuousLinearMapWOT.ofCLM (F.commutes z)
  map_star' T := congrArg ContinuousLinearMapWOT.ofCLM (map_star F T.toCLM)

theorem closed_generated_commute (s t : Set (W →WOT[ℂ] W))
    (hst : s ⊆ StarSubalgebra.centralizer ℂ t)
    {x y : W →WOT[ℂ] W}
    (hx : x ∈ (StarAlgebra.adjoin ℂ s).topologicalClosure)
    (hy : y ∈ (StarAlgebra.adjoin ℂ t).topologicalClosure) : x * y = y * x := by
  have hs : (StarAlgebra.adjoin ℂ s).topologicalClosure ≤
      StarSubalgebra.centralizer ℂ t :=
    StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le hst)
      (Set.isClosed_centralizer _)
  have ht := StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer ℂ t hy
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp ht x (hs hx)).1

theorem map_mem_closed_generated (F : (L →WOT[ℂ] L) →⋆ₐ[ℂ] (W →WOT[ℂ] W))
    (hF : Continuous F) (s : Set (L →WOT[ℂ] L)) {x : L →WOT[ℂ] L}
    (hx : x ∈ (StarAlgebra.adjoin ℂ s).topologicalClosure) :
    F x ∈ (StarAlgebra.adjoin ℂ (F '' s)).topologicalClosure := by
  have h := StarSubalgebra.map_topologicalClosure_le (StarAlgebra.adjoin ℂ s) F hF
  rw [StarAlgHom.map_adjoin] at h
  exact h ⟨x, hx, rfl⟩

theorem isometries_commute_star_right (U V : W ≃ₗᵢ[ℂ] W)
    (h : ∀ x, U (V x) = V (U x)) :
    U.toContinuousLinearEquiv.toContinuousLinearMap *
        star V.toContinuousLinearEquiv.toContinuousLinearMap =
      star V.toContinuousLinearEquiv.toContinuousLinearMap *
        U.toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [LinearIsometryEquiv.star_eq_symm]
  apply ContinuousLinearMap.ext
  intro x
  change U (V.symm x) = V.symm (U x)
  apply V.injective
  rw [← h, V.apply_symm_apply, V.apply_symm_apply]

end WeakOperatorAlgebras

variable {G : Type*} [Group G]

def regularGenerator (μ : ScalarCocycle G) (g : G) :
    lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2 :=
  ContinuousLinearMapWOT.ofCLM (scalarRegular μ g).toContinuousLinearEquiv.toContinuousLinearMap

def twistedGroupAlgebra (μ : ScalarCocycle G) :
    StarSubalgebra ℂ (lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2) :=
  (StarAlgebra.adjoin ℂ (Set.range (regularGenerator μ))).topologicalClosure

theorem regularGenerator_mem (μ : ScalarCocycle G) (g : G) :
    regularGenerator μ g ∈ twistedGroupAlgebra μ :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self g))

end

section
open ArithmeticGerms GermBundles
variable {G H V J : Type*} [Group G] [Group H] [Fintype J]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable (C : VirtualGraph G H)
local instance normalActionDomainFintype : Fintype (G ⧸ C.domain) :=
  Subgroup.fintypeQuotientOfFiniteIndex
local instance normalActionCodomainFintype : Fintype (H ⧸ C.codomain) :=
  Subgroup.fintypeQuotientOfFiniteIndex
variable (μ : ScalarCocycle G) (ω : ScalarCocycle H)
variable (B : ProjectiveBundle (prodRatio μ ω) (fun _ : (G × H) ⧸ C.graph => V))
variable (b : OrthonormalBasis J ℂ V)

def coordinateOperator (s : G × H) : lp (fun _ : (G × H) ⧸ C.graph => V) 2 →WOT[ℂ]
    lp (fun _ : (G × H) ⧸ C.graph => V) 2 :=
  ContinuousLinearMapWOT.ofCLM (B.action s).toContinuousLinearEquiv.toContinuousLinearMap

theorem coordinateOperator_centralizer :
    Set.range (fun g : G => coordinateOperator C μ ω B (g,1)) ⊆
      StarSubalgebra.centralizer ℂ
        (Set.range (fun h : H => coordinateOperator C μ ω B (1,h))) := by
  rintro _ ⟨g,rfl⟩
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  rintro _ ⟨h,rfl⟩
  constructor
  · apply ContinuousLinearMapWOT.ext
    intro v
    exact (coordinate_actions_commute C μ ω B g h v).symm
  · exact congrArg ContinuousLinearMapWOT.ofCLM
      (isometries_commute_star_right (B.action (g,1)) (B.action (1,h))
        (coordinate_actions_commute C μ ω B g h)).symm

theorem firstExtension_generating_image :
    (wotLift (firstExtension C μ ω B b)) '' Set.range (regularGenerator μ) =
      Set.range (fun g : G => coordinateOperator C μ ω B (g,1)) := by
  rw [← Set.range_comp']
  congr 1
  funext g
  exact congrArg ContinuousLinearMapWOT.ofCLM (firstExtension_generator C μ ω B b g)

theorem secondExtension_generating_image :
    (wotLift (secondExtension C μ ω B b)) '' Set.range (regularGenerator (inverseCocycle ω)) =
      Set.range (fun h : H => coordinateOperator C μ ω B (1,h)) := by
  rw [← Set.range_comp']
  congr 1
  funext h
  exact congrArg ContinuousLinearMapWOT.ofCLM (secondExtension_generator C μ ω B b h)

def leftNormalAction : twistedGroupAlgebra μ →⋆ₐ[ℂ]
    (lp (fun _ : (G × H) ⧸ C.graph => V) 2 →WOT[ℂ]
      lp (fun _ : (G × H) ⧸ C.graph => V) 2) :=
  (wotLift (firstExtension C μ ω B b)).comp (twistedGroupAlgebra μ).subtype

def rightAdjointNormalAction : twistedGroupAlgebra (inverseCocycle ω) →⋆ₐ[ℂ]
    (lp (fun _ : (G × H) ⧸ C.graph => V) 2 →WOT[ℂ]
      lp (fun _ : (G × H) ⧸ C.graph => V) 2) :=
  (wotLift (secondExtension C μ ω B b)).comp (twistedGroupAlgebra (inverseCocycle ω)).subtype

theorem leftNormalAction_continuous : Continuous (leftNormalAction C μ ω B b) :=
  (firstExtension_wot_continuous C μ ω B b).comp continuous_subtype_val

theorem rightAdjointNormalAction_continuous : Continuous (rightAdjointNormalAction C μ ω B b) :=
  (secondExtension_wot_continuous C μ ω B b).comp continuous_subtype_val

theorem leftNormalAction_generator (g : G) :
    leftNormalAction C μ ω B b ⟨regularGenerator μ g, regularGenerator_mem μ g⟩ =
      coordinateOperator C μ ω B (g,1) :=
  congrArg ContinuousLinearMapWOT.ofCLM (firstExtension_generator C μ ω B b g)

theorem rightAdjointNormalAction_generator (h : H) :
    rightAdjointNormalAction C μ ω B b
      ⟨regularGenerator (inverseCocycle ω) h, regularGenerator_mem (inverseCocycle ω) h⟩ =
      coordinateOperator C μ ω B (1,h) :=
  congrArg ContinuousLinearMapWOT.ofCLM (secondExtension_generator C μ ω B b h)

theorem normalActions_commute (T : twistedGroupAlgebra μ)
    (S : twistedGroupAlgebra (inverseCocycle ω)) :
    leftNormalAction C μ ω B b T * rightAdjointNormalAction C μ ω B b S =
      rightAdjointNormalAction C μ ω B b S * leftNormalAction C μ ω B b T := by
  have hT := map_mem_closed_generated (wotLift (firstExtension C μ ω B b))
    (firstExtension_wot_continuous C μ ω B b) (Set.range (regularGenerator μ)) T.property
  have hS := map_mem_closed_generated (wotLift (secondExtension C μ ω B b))
    (secondExtension_wot_continuous C μ ω B b)
    (Set.range (regularGenerator (inverseCocycle ω))) S.property
  rw [firstExtension_generating_image] at hT
  rw [secondExtension_generating_image] at hS
  exact closed_generated_commute _ _ (coordinateOperator_centralizer C μ ω B) hT hS

end

section
open scoped InnerProductSpace
variable {I : Type*}

lemma scalarLp_inner_star_star (x y : lp (fun _ : I => ℂ) 2) :
    ⟪star x, star y⟫_ℂ = ⟪y, x⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp [RCLike.inner_apply, mul_comm]

lemma scalarLp_inner_star_comm (x y : lp (fun _ : I => ℂ) 2) :
    ⟪x, star y⟫_ℂ = ⟪y, star x⟫_ℂ := by
  simpa only [star_star] using scalarLp_inner_star_star (star x) y

def operatorTranspose (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2 where
  toFun x := star ((star T) (star x))
  map_add' x y := by simp
  map_smul' z x := by simp
  cont := continuous_star.comp ((star T).continuous.comp continuous_star)

lemma operatorTranspose_inner (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (x y : lp (fun _ : I => ℂ) 2) :
    ⟪y, operatorTranspose T x⟫_ℂ = ⟪star x, T (star y)⟫_ℂ := by
  change ⟪y, star ((star T) (star x))⟫_ℂ = _
  rw [scalarLp_inner_star_comm, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

lemma operatorTranspose_add (T S : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    operatorTranspose (T + S) = operatorTranspose T + operatorTranspose S := by
  apply ContinuousLinearMap.ext
  intro x
  simp [operatorTranspose, ContinuousLinearMap.star_eq_adjoint]

lemma operatorTranspose_smul (z : ℂ)
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    operatorTranspose (z • T) = z • operatorTranspose T := by
  apply ContinuousLinearMap.ext
  intro x
  simp [operatorTranspose]

lemma operatorTranspose_mul (T S : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    operatorTranspose (T * S) = operatorTranspose S * operatorTranspose T := by
  apply ContinuousLinearMap.ext
  intro x
  simp [operatorTranspose]

lemma operatorTranspose_star (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    operatorTranspose (star T) = star (operatorTranspose T) := by
  rw [ContinuousLinearMap.star_eq_adjoint (operatorTranspose T)]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [← inner_conj_symm, operatorTranspose_inner, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_conj_symm, operatorTranspose_inner]

lemma operatorTranspose_involutive
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    operatorTranspose (operatorTranspose T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [operatorTranspose_inner, operatorTranspose_inner, star_star, star_star]

lemma operatorTranspose_one :
    operatorTranspose (1 : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  simp [operatorTranspose]

def operatorOppositeEquiv :
    (lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)ᵐᵒᵖ ≃⋆ₐ[ℂ]
      (lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) where
  toFun T := operatorTranspose T.unop
  invFun T := MulOpposite.op (operatorTranspose T)
  left_inv T := by simp [operatorTranspose_involutive]
  right_inv T := operatorTranspose_involutive T
  map_mul' T S := operatorTranspose_mul S.unop T.unop
  map_add' T S := operatorTranspose_add T.unop S.unop
  map_smul' z T := operatorTranspose_smul z T.unop
  map_star' T := operatorTranspose_star T.unop

lemma operatorTranspose_wot_continuous :
    Continuous (fun T : lp (fun _ : I => ℂ) 2 →WOT[ℂ] lp (fun _ : I => ℂ) 2 =>
      ContinuousLinearMapWOT.ofCLM (operatorTranspose T.toCLM)) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  change Continuous (fun T : lp (fun _ : I => ℂ) 2 →WOT[ℂ] lp (fun _ : I => ℂ) 2 =>
    ⟪y, operatorTranspose T.toCLM x⟫_ℂ)
  simp_rw [operatorTranspose_inner]
  exact ContinuousLinearMapWOT.continuous_iff.mp continuous_id (star y) (star x)

end

section
open GermBundles
variable {G : Type*}

def wotTranspose (T : lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2) :
    lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2 :=
  ContinuousLinearMapWOT.ofCLM (operatorTranspose T.toCLM)

lemma wotTranspose_continuous : Continuous (wotTranspose (G := G)) :=
  operatorTranspose_wot_continuous

lemma wotTranspose_add (T S : lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2) :
    wotTranspose (T + S) = wotTranspose T + wotTranspose S :=
  congrArg ContinuousLinearMapWOT.ofCLM (operatorTranspose_add T.toCLM S.toCLM)

lemma wotTranspose_mul (T S : lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2) :
    wotTranspose (T * S) = wotTranspose S * wotTranspose T :=
  congrArg ContinuousLinearMapWOT.ofCLM (operatorTranspose_mul T.toCLM S.toCLM)

lemma wotTranspose_smul (z : ℂ)
    (T : lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2) :
    wotTranspose (z • T) = z • wotTranspose T :=
  congrArg ContinuousLinearMapWOT.ofCLM (operatorTranspose_smul z T.toCLM)

lemma wotTranspose_star (T : lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2) :
    wotTranspose (star T) = star (wotTranspose T) :=
  congrArg ContinuousLinearMapWOT.ofCLM (operatorTranspose_star T.toCLM)

lemma wotTranspose_one :
    wotTranspose (1 : lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2) = 1 :=
  congrArg ContinuousLinearMapWOT.ofCLM operatorTranspose_one

lemma wotTranspose_involutive
    (T : lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2) :
    wotTranspose (wotTranspose T) = T :=
  congrArg ContinuousLinearMapWOT.ofCLM (operatorTranspose_involutive T.toCLM)

lemma wotTranspose_zero :
    wotTranspose (0 : lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2) = 0 := by
  apply ContinuousLinearMapWOT.ext
  intro x
  change star ((star (0 : lp (fun _ : G => ℂ) 2 →L[ℂ] lp (fun _ : G => ℂ) 2)) (star x)) = 0
  simp [ContinuousLinearMap.star_eq_adjoint]

variable [Group G]

lemma wotTranspose_star_regularGenerator (ω : ScalarCocycle G) (g : G) :
    wotTranspose (star (regularGenerator ω g)) = regularGenerator (inverseCocycle ω) g := by
  apply ContinuousLinearMapWOT.ext
  intro x
  apply lp.ext
  funext k
  obtain ⟨h,rfl⟩ := (Equiv.mulLeft g).surjective k
  change (star ((star (star (scalarRegular ω g).toContinuousLinearEquiv.toContinuousLinearMap))
    (star x))) (g*h) = scalarRegular (inverseCocycle ω) g x (g*h)
  rw [star_star]
  change star (scalarRegular ω g (star x) (g*h)) = _
  rw [scalarRegular_apply, scalarRegular_apply]
  simp only [inverseCocycle, star_mul, lp.star_apply, star_star]
  rw [Circle.coe_inv_eq_conj]
  exact mul_comm _ _

lemma wotTranspose_regularGenerator (ω : ScalarCocycle G) (g : G) :
    wotTranspose (regularGenerator ω g) = star (regularGenerator (inverseCocycle ω) g) := by
  rw [← wotTranspose_star_regularGenerator, wotTranspose_star, star_star]

def transposePreimage
    (S : StarSubalgebra ℂ (lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2)) :
    StarSubalgebra ℂ (lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2) where
  carrier := {T | wotTranspose T ∈ S}
  zero_mem' := by
    change wotTranspose 0 ∈ S
    rw [wotTranspose_zero]
    exact zero_mem S
  one_mem' := by
    change wotTranspose 1 ∈ S
    rw [wotTranspose_one]
    exact one_mem S
  add_mem' hT hU := by
    change wotTranspose _ ∈ S
    rw [wotTranspose_add]
    exact add_mem hT hU
  mul_mem' hT hU := by
    change wotTranspose _ ∈ S
    rw [wotTranspose_mul]
    exact mul_mem hU hT
  algebraMap_mem' z := by
    change wotTranspose (algebraMap ℂ _ z) ∈ S
    rw [Algebra.algebraMap_eq_smul_one, wotTranspose_smul, wotTranspose_one]
    exact S.smul_mem S.one_mem z
  star_mem' hT := by
    change wotTranspose _ ∈ S
    rw [wotTranspose_star]
    exact star_mem hT

lemma wotTranspose_mem_twistedGroupAlgebra (ω : ScalarCocycle G)
    {T : lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2}
    (hT : T ∈ twistedGroupAlgebra ω) :
    wotTranspose T ∈ twistedGroupAlgebra (inverseCocycle ω) := by
  have hgen : Set.range (regularGenerator ω) ⊆
      transposePreimage (twistedGroupAlgebra (inverseCocycle ω)) := by
    rintro _ ⟨g,rfl⟩
    change wotTranspose (regularGenerator ω g) ∈ twistedGroupAlgebra (inverseCocycle ω)
    rw [wotTranspose_regularGenerator]
    exact star_mem (regularGenerator_mem _ g)
  have hclosed : IsClosed (transposePreimage (twistedGroupAlgebra (inverseCocycle ω)) :
      Set (lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2)) := by
    change IsClosed (wotTranspose ⁻¹' (twistedGroupAlgebra (inverseCocycle ω)).carrier)
    exact (StarSubalgebra.isClosed_topologicalClosure _).preimage wotTranspose_continuous
  exact StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le hgen) hclosed hT

def opTransposeOnTwisted (ω : ScalarCocycle G) :
    (twistedGroupAlgebra ω)ᵐᵒᵖ →⋆ₐ[ℂ] twistedGroupAlgebra (inverseCocycle ω) where
  toFun T := ⟨wotTranspose T.unop.val, wotTranspose_mem_twistedGroupAlgebra ω T.unop.property⟩
  map_one' := Subtype.ext wotTranspose_one
  map_mul' T S := Subtype.ext (wotTranspose_mul S.unop.val T.unop.val)
  map_add' T S := Subtype.ext (wotTranspose_add T.unop.val S.unop.val)
  map_zero' := Subtype.ext wotTranspose_zero
  commutes' z := by
    apply Subtype.ext
    change wotTranspose (algebraMap ℂ _ z) = algebraMap ℂ _ z
    rw [Algebra.algebraMap_eq_smul_one, wotTranspose_smul, wotTranspose_one]
  map_star' T := Subtype.ext (wotTranspose_star T.unop.val)

lemma opTransposeOnTwisted_continuous (ω : ScalarCocycle G) :
    Continuous (opTransposeOnTwisted ω) :=
  (wotTranspose_continuous.comp (continuous_subtype_val.comp
    MulOpposite.continuous_unop)).subtype_mk _

end

section
open ArithmeticGerms GermBundles
section RightAction
variable {G H V J : Type*} [Group G] [Group H] [Fintype J]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable (C : VirtualGraph G H)
local instance rightNormalActionDomainFintype : Fintype (G ⧸ C.domain) :=
  Subgroup.fintypeQuotientOfFiniteIndex
local instance rightNormalActionCodomainFintype : Fintype (H ⧸ C.codomain) :=
  Subgroup.fintypeQuotientOfFiniteIndex
variable (μ : ScalarCocycle G) (ω : ScalarCocycle H)
variable (B : ProjectiveBundle (prodRatio μ ω) (fun _ : (G × H) ⧸ C.graph => V))
variable (b : OrthonormalBasis J ℂ V)

def rightNormalAction : (twistedGroupAlgebra ω)ᵐᵒᵖ →⋆ₐ[ℂ]
    (lp (fun _ : (G × H) ⧸ C.graph => V) 2 →WOT[ℂ]
      lp (fun _ : (G × H) ⧸ C.graph => V) 2) :=
  (rightAdjointNormalAction C μ ω B b).comp (opTransposeOnTwisted ω)

theorem rightNormalAction_continuous : Continuous (rightNormalAction C μ ω B b) :=
  (rightAdjointNormalAction_continuous C μ ω B b).comp
    (opTransposeOnTwisted_continuous ω)

theorem rightNormalAction_adjoint_generator (h : H) :
    rightNormalAction C μ ω B b
      (MulOpposite.op (star (⟨regularGenerator ω h, regularGenerator_mem ω h⟩ :
        twistedGroupAlgebra ω))) = coordinateOperator C μ ω B (1,h) := by
  have ht : opTransposeOnTwisted ω
      (MulOpposite.op (star (⟨regularGenerator ω h, regularGenerator_mem ω h⟩ :
        twistedGroupAlgebra ω))) =
      ⟨regularGenerator (inverseCocycle ω) h, regularGenerator_mem (inverseCocycle ω) h⟩ :=
    Subtype.ext (wotTranspose_star_regularGenerator ω h)
  exact (congrArg (rightAdjointNormalAction C μ ω B b) ht).trans
    (rightAdjointNormalAction_generator C μ ω B b h)

theorem left_rightNormalActions_commute (T : twistedGroupAlgebra μ)
    (S : (twistedGroupAlgebra ω)ᵐᵒᵖ) :
    leftNormalAction C μ ω B b T * rightNormalAction C μ ω B b S =
      rightNormalAction C μ ω B b S * leftNormalAction C μ ω B b T :=
  normalActions_commute C μ ω B b T (opTransposeOnTwisted ω S)

end RightAction

variable {G H V : Type*} [Group G] [Group H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable (C : VirtualGraph G H)
local instance inducedGraphDomainFintype : Fintype (G ⧸ C.domain) :=
  Subgroup.fintypeQuotientOfFiniteIndex
local instance inducedGraphCodomainFintype : Fintype (H ⧸ C.codomain) :=
  Subgroup.fintypeQuotientOfFiniteIndex
variable (μ : ScalarCocycle G) (ω : ScalarCocycle H)
variable (r : CosetSection C.graph)
variable (γ : ProjectiveRepresentation ((prodRatio μ ω).restrict C.graph) V)

theorem induced_graph_normal_actions :
    let B := r.inducedBundle (prodRatio μ ω) γ
    ∃ (L : twistedGroupAlgebra μ →⋆ₐ[ℂ]
          (lp (fun _ : (G × H) ⧸ C.graph => V) 2 →WOT[ℂ]
            lp (fun _ : (G × H) ⧸ C.graph => V) 2))
      (R : (twistedGroupAlgebra ω)ᵐᵒᵖ →⋆ₐ[ℂ]
          (lp (fun _ : (G × H) ⧸ C.graph => V) 2 →WOT[ℂ]
            lp (fun _ : (G × H) ⧸ C.graph => V) 2))
      (UL : PiLp 2 (fun _ : (H ⧸ C.codomain) × Fin (Module.finrank ℂ V) =>
          lp (fun _ : G => ℂ) 2) ≃ₗᵢ[ℂ] lp (fun _ : (G × H) ⧸ C.graph => V) 2)
      (UR : PiLp 2 (fun _ : (G ⧸ C.domain) × Fin (Module.finrank ℂ V) =>
          lp (fun _ : H => ℂ) 2) ≃ₗᵢ[ℂ] lp (fun _ : (G × H) ⧸ C.graph => V) 2),
      Continuous L ∧ Continuous R ∧
      (∀ T S, L T * R S = R S * L T) ∧
      (∀ g, L ⟨regularGenerator μ g, regularGenerator_mem μ g⟩ =
        coordinateOperator C μ ω B (g,1)) ∧
      (∀ h, R (MulOpposite.op (star (⟨regularGenerator ω h, regularGenerator_mem ω h⟩ :
        twistedGroupAlgebra ω))) = coordinateOperator C μ ω B (1,h)) ∧
      (∀ g v, B.action (g,1) (UL v) = UL
        (amplify (scalarRegular μ g).toContinuousLinearEquiv.toContinuousLinearMap v)) ∧
      (∀ h v, B.action (1,h) (UR v) = UR
        (amplify (scalarRegular (inverseCocycle ω) h).toContinuousLinearEquiv.toContinuousLinearMap v)) := by
  let B := r.inducedBundle (prodRatio μ ω) γ
  let b := stdOrthonormalBasis ℂ V
  refine ⟨leftNormalAction C μ ω B b, rightNormalAction C μ ω B b,
    firstFiniteRegularUnitary C μ ω B b, secondFiniteRegularUnitary C μ ω B b,
    leftNormalAction_continuous C μ ω B b, rightNormalAction_continuous C μ ω B b, ?_⟩
  exact ⟨left_rightNormalActions_commute C μ ω B b,
    leftNormalAction_generator C μ ω B b, rightNormalAction_adjoint_generator C μ ω B b,
    firstFiniteRegularUnitary_intertwines C μ ω B b,
    secondFiniteRegularUnitary_intertwines C μ ω B b⟩

end

section
open GermBundles
variable {G : Type*} [Group G]

def standardRightRegular (ω : ScalarCocycle G) (h : G) :
    lp (fun _ : G => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : G => ℂ) 2 :=
  transportLp (Equiv.mulRight h) (fun g => circleUnitary (ω.val g h))

lemma standardRightRegular_apply (ω : ScalarCocycle G) (h : G)
    (x : lp (fun _ : G => ℂ) 2) (g : G) :
    standardRightRegular ω h x (g*h) = (ω.val g h : ℂ) * x g :=
  transportLp_apply (Equiv.mulRight h) (fun g => circleUnitary (ω.val g h)) x g

def oppositeToStandard (ω : ScalarCocycle G) :
    lp (fun _ : G => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : G => ℂ) 2 :=
  transportLp (Equiv.inv G) (fun g => circleUnitary ((ω.val g⁻¹ g)⁻¹))

lemma oppositeToStandard_apply (ω : ScalarCocycle G)
    (x : lp (fun _ : G => ℂ) 2) (g : G) :
    oppositeToStandard ω x g⁻¹ = ((ω.val g⁻¹ g)⁻¹ : Circle) * x g := by
  exact transportLp_apply (Equiv.inv G) (fun g => circleUnitary ((ω.val g⁻¹ g)⁻¹)) x g

lemma rightStandard_phase (ω : ScalarCocycle G) (h g : G) :
    ω.val (h*g)⁻¹ h * (ω.val h g)⁻¹ * (ω.val (h*g)⁻¹ (h*g))⁻¹ =
      (ω.val g⁻¹ g)⁻¹ := by
  have hh := ω.mul_assoc (h*g)⁻¹ h g
  have hg : (h*g)⁻¹ * h = g⁻¹ := by group
  rw [hg] at hh
  have he : ω.val (h*g)⁻¹ h =
      (ω.val h g * ω.val (h*g)⁻¹ (h*g)) * (ω.val g⁻¹ g)⁻¹ :=
    (eq_mul_inv_iff_mul_eq).mpr hh
  rw [he]
  simp [mul_comm, mul_left_comm, mul_assoc]

lemma oppositeToStandard_intertwines (ω : ScalarCocycle G) (h : G)
    (x : lp (fun _ : G => ℂ) 2) :
    oppositeToStandard ω (scalarRegular (inverseCocycle ω) h x) =
      (standardRightRegular ω h).symm (oppositeToStandard ω x) := by
  apply (standardRightRegular ω h).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply lp.ext
  funext k
  obtain ⟨g,rfl⟩ := (Equiv.inv G).surjective k
  change standardRightRegular ω h (oppositeToStandard ω (scalarRegular (inverseCocycle ω) h x)) g⁻¹ =
    oppositeToStandard ω x g⁻¹
  have hi : (h*g)⁻¹ * h = g⁻¹ := by group
  rw [← hi, standardRightRegular_apply, oppositeToStandard_apply, scalarRegular_apply,
    hi, oppositeToStandard_apply]
  change (ω.val (h*g)⁻¹ h : ℂ) *
    (((ω.val (h*g)⁻¹ (h*g))⁻¹ : Circle) * (((ω.val h g)⁻¹ : Circle) * x g)) =
      ((ω.val g⁻¹ g)⁻¹ : Circle) * x g
  have hp := congrArg (fun z : Circle => (z : ℂ)) (rightStandard_phase ω h g)
  simp only [Circle.coe_mul] at hp
  calc
    _ = ((ω.val (h*g)⁻¹ h : ℂ) * ((ω.val h g)⁻¹ : Circle) *
        ((ω.val (h*g)⁻¹ (h*g))⁻¹ : Circle)) * x g := by ring
    _ = _ := congrArg (fun z : ℂ => z * x g) hp

end

open ArithmeticGerms GermBundles
section EntireRegularActions
variable {G H V J : Type*} [Group G] [Group H] [Fintype J]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable (C : VirtualGraph G H)
local instance regularActionDomainFintype : Fintype (G ⧸ C.domain) :=
  Subgroup.fintypeQuotientOfFiniteIndex
local instance regularActionCodomainFintype : Fintype (H ⧸ C.codomain) :=
  Subgroup.fintypeQuotientOfFiniteIndex
variable (μ : ScalarCocycle G) (ω : ScalarCocycle H)
variable (B : ProjectiveBundle (prodRatio μ ω) (fun _ : (G × H) ⧸ C.graph => V))
variable (b : OrthonormalBasis J ℂ V)

lemma leftNormalAction_finite_regular (T : twistedGroupAlgebra μ)
    (v : PiLp 2 (fun _ : (H ⧸ C.codomain) × J => lp (fun _ : G => ℂ) 2)) :
    leftNormalAction C μ ω B b T (firstFiniteRegularUnitary C μ ω B b v) =
      firstFiniteRegularUnitary C μ ω B b (amplify T.val.toCLM v) := by
  change firstFiniteRegularUnitary C μ ω B b
    (amplify T.val.toCLM ((firstFiniteRegularUnitary C μ ω B b).symm
      (firstFiniteRegularUnitary C μ ω B b v))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

lemma rightNormalAction_finite_regular (S : (twistedGroupAlgebra ω)ᵐᵒᵖ)
    (v : PiLp 2 (fun _ : (G ⧸ C.domain) × J => lp (fun _ : H => ℂ) 2)) :
    rightNormalAction C μ ω B b S (secondFiniteRegularUnitary C μ ω B b v) =
      secondFiniteRegularUnitary C μ ω B b (amplify
        (wotTranspose S.unop.val).toCLM v) := by
  change secondFiniteRegularUnitary C μ ω B b
    (amplify (wotTranspose S.unop.val).toCLM ((secondFiniteRegularUnitary C μ ω B b).symm
      (secondFiniteRegularUnitary C μ ω B b v))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

end EntireRegularActions

variable {G H V : Type*} [Group G] [Group H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable (C : VirtualGraph G H)
local instance multiplicityDomainFintype : Fintype (G ⧸ C.domain) :=
  Subgroup.fintypeQuotientOfFiniteIndex
local instance multiplicityCodomainFintype : Fintype (H ⧸ C.codomain) :=
  Subgroup.fintypeQuotientOfFiniteIndex

omit [FiniteDimensional ℂ V] in
lemma graph_regular_multiplicities :
    Fintype.card ((H ⧸ C.codomain) × Fin (Module.finrank ℂ V)) =
      Module.finrank ℂ V * C.codomain.index ∧
    Fintype.card ((G ⧸ C.domain) × Fin (Module.finrank ℂ V)) =
      Module.finrank ℂ V * C.domain.index := by
  simp [Fintype.card_prod, Subgroup.index_eq_card, Nat.card_eq_fintype_card, mul_comm]

end GraphNormality

end

end OAI
