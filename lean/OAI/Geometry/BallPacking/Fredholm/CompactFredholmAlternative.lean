import Mathlib
import OAI.Geometry.BallPacking.Compactness.JetCauchy
import OAI.Geometry.BallPacking.Fredholm.FiniteExtensions

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem compactPerturbation_surjective_of_injective (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hi : Injective (ContinuousLinearMap.id ℝ E+T)) :
    Surjective (ContinuousLinearMap.id ℝ E+T) := by
  obtain he | hr := hT.hasEigenvalue_or_mem_resolventSet (μ := (-1:ℝ)) (by norm_num)
  · exfalso
    apply he
    rw [Module.End.genEigenspace_one]
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply hi
    change x+T x=0+T 0
    have hx' : T x-(-1:ℝ) • x=0 := hx
    simpa only [neg_smul,one_smul,sub_neg_eq_add,add_comm,map_zero,add_zero] using hx'
  · rw [spectrum.mem_resolventSet_iff,←IsUnit.neg_iff,
      ContinuousLinearMap.isUnit_iff_bijective] at hr
    convert hr.2 using 1
    ext x
    simp [add_comm]

 theorem compactPerturbation_injective_iff_surjective (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    Injective (ContinuousLinearMap.id ℝ E+T) ↔ Surjective (ContinuousLinearMap.id ℝ E+T) :=
  ⟨compactPerturbation_surjective_of_injective T hT,
    compactPerturbation_injective_of_surjective T hT⟩

end HigherDimensionalBallPacking.Rigidity

namespace ContinuousLinearMap.FredholmPackage
open scoped _root_.ContinuousLinearMap _root_.ContinuousLinearMap.FredholmPackage
open Set Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {P : E →L[ℝ] F}

 def domCoords (pkg : _root_.ContinuousLinearMap.FredholmPackage P) : E ≃L[ℝ] (pkg.decDom.X₁ × pkg.decDom.X₀) :=
  (Submodule.prodEquivOfIsTopCompl _ _ pkg.decDom.isTopCompl).symm

 def codCoords (pkg : _root_.ContinuousLinearMap.FredholmPackage P) : F ≃L[ℝ] (pkg.decCodom.X₁ × pkg.decCodom.X₀) :=
  (Submodule.prodEquivOfIsTopCompl _ _ pkg.decCodom.isTopCompl).symm

 def finitePerturbation (pkg : _root_.ContinuousLinearMap.FredholmPackage P) (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) : E →L[ℝ] F :=
  pkg.decCodom.X₀.subtypeL.comp (L.comp (pkg.decDom.X₀.projectionOntoL _ pkg.decDom.isTopCompl.symm))

 theorem finitePerturbation_compact (pkg : _root_.ContinuousLinearMap.FredholmPackage P)
    (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) : IsCompactOperator (finitePerturbation pkg L) := by
  let := pkg.decDom.finite_X₀
  have hc : IsCompactOperator (ContinuousLinearMap.id ℝ pkg.decDom.X₀) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).mpr inferInstance
  exact (hc.clm_comp (pkg.decCodom.X₀.subtypeL.comp L)).comp_clm
    (pkg.decDom.X₀.projectionOntoL _ pkg.decDom.isTopCompl.symm)

 theorem finitePerturbation_coords (pkg : _root_.ContinuousLinearMap.FredholmPackage P)
    (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) (x : E) :
    (codCoords pkg) ((P+finitePerturbation pkg L) x) =
      (pkg.equiv ((domCoords pkg) x).1,L ((domCoords pkg) x).2) := by
  apply (codCoords pkg).symm.injective
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [add_apply]
  have he := congrArg (fun A : E →L[ℝ] F => A x) pkg.eq_equiv
  rw [he]
  simp only [finitePerturbation,domCoords,codCoords,ContinuousLinearEquiv.symm_symm,
    Submodule.prodEquivOfIsTopCompl_apply,Submodule.prodEquivOfIsTopCompl_symm_apply,
    ContinuousLinearMap.comp_apply,Submodule.coe_subtypeL,ContinuousLinearEquiv.coe_coe]
  rfl

 theorem finitePerturbation_injective (pkg : _root_.ContinuousLinearMap.FredholmPackage P)
    (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) :
    Injective (P+finitePerturbation pkg L) ↔ Injective L := by
  constructor
  · intro hi x y hxy
    have hh : (P+finitePerturbation pkg L) ((domCoords pkg).symm (0,x)) =
        (P+finitePerturbation pkg L) ((domCoords pkg).symm (0,y)) := by
      apply (codCoords pkg).injective
      rw [finitePerturbation_coords pkg,finitePerturbation_coords pkg,
        ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply,hxy]
    have h := congrArg (domCoords pkg) (hi hh)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,Prod.mk.injEq,true_and] using h
  · intro hi x y hxy
    apply (domCoords pkg).injective
    have hh := congrArg (codCoords pkg) hxy
    rw [finitePerturbation_coords pkg,finitePerturbation_coords pkg] at hh
    exact Prod.ext (pkg.equiv.injective (congrArg Prod.fst hh)) (hi (congrArg Prod.snd hh))

 theorem finitePerturbation_surjective (pkg : _root_.ContinuousLinearMap.FredholmPackage P)
    (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) :
    Surjective (P+finitePerturbation pkg L) ↔ Surjective L := by
  constructor
  · intro hs y
    obtain ⟨x,hx⟩ := hs ((codCoords pkg).symm (0,y))
    refine ⟨((domCoords pkg) x).2,?_⟩
    have hh := congrArg (codCoords pkg) hx
    rw [finitePerturbation_coords pkg,ContinuousLinearEquiv.apply_symm_apply] at hh
    exact congrArg Prod.snd hh
  · intro hs y
    obtain ⟨x,hx⟩ := hs ((codCoords pkg) y).2
    refine ⟨(domCoords pkg).symm (pkg.equiv.symm ((codCoords pkg) y).1,x),?_⟩
    apply (codCoords pkg).injective
    rw [finitePerturbation_coords pkg,ContinuousLinearEquiv.apply_symm_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply,hx,Prod.mk.eta]

end ContinuousLinearMap.FredholmPackage

namespace HigherDimensionalBallPacking.Rigidity
open Function
open Set
open _root_.OAI.ContinuousLinearMap.FredholmPackage
section

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

 theorem finrank_eq_of_map_alternative
    (h : ∀ L : E →L[ℝ] F, Injective L ↔ Surjective L) :
    Module.finrank ℝ E=Module.finrank ℝ F := by
  apply le_antisymm
  · by_contra! hlt
    have hr : Module.rank ℝ F < Module.rank ℝ E := by
      rw [←Module.finrank_eq_rank,←Module.finrank_eq_rank]
      exact_mod_cast hlt
    obtain ⟨g,hg⟩ := Module.Free.exists_linearMap_injective_of_rank_lt hr
    obtain ⟨L,hL⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hg)
    have hLs : Surjective L := by
      intro y
      refine ⟨g y,?_⟩
      exact congrArg (fun A : F →ₗ[ℝ] F => A y) hL
    have hLi : Injective L := (h L.toContinuousLinearMap).mpr hLs
    exact hlt.not_ge (LinearMap.finrank_le_finrank_of_injective hLi)
  · by_contra! hlt
    have hr : Module.rank ℝ E < Module.rank ℝ F := by
      rw [←Module.finrank_eq_rank,←Module.finrank_eq_rank]
      exact_mod_cast hlt
    obtain ⟨L,hLi⟩ := Module.Free.exists_linearMap_injective_of_rank_lt hr
    have hLs : Surjective L := (h L.toContinuousLinearMap).mp hLi
    exact hlt.not_ge (LinearMap.finrank_le_finrank_of_surjective hLs)

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem compactPerturbation_package_finrank (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (pkg : (ContinuousLinearMap.id ℝ E+T).FredholmPackage) :
    Module.finrank ℝ pkg.decDom.X₀=Module.finrank ℝ pkg.decCodom.X₀ := by
  let := pkg.decDom.finite_X₀
  let := pkg.decCodom.finite_X₀
  apply finrank_eq_of_map_alternative
  intro L
  have hc : IsCompactOperator (T+finitePerturbation pkg L) :=
    hT.add (finitePerturbation_compact pkg L)
  have hh := compactPerturbation_injective_iff_surjective (T+finitePerturbation pkg L) hc
  rw [←add_assoc] at hh
  exact (finitePerturbation_injective pkg L).symm.trans (hh.trans (finitePerturbation_surjective pkg L))

 theorem compactPerturbation_index_zero (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    Module.finrank ℝ (ContinuousLinearMap.id ℝ E+T).ker=
      Module.finrank ℝ (E ⧸ (ContinuousLinearMap.id ℝ E+T).range) := by
  obtain ⟨pkg⟩ := (compactPerturbation_fredholm T hT).nonempty_fredholmPackage
  have hd := compactPerturbation_package_finrank T hT pkg
  rw [pkg.ker_eq,pkg.range_eq]
  exact hd.trans (Submodule.quotientEquivOfIsCompl _ _ pkg.decCodom.isTopCompl.isCompl).finrank_eq.symm

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance linCRInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance linCRInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance linCRInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance linCRInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance linCRInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance linCRInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance linCRInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst9 : NormedAddCommGroup (COne ℂ (E →L[ℝ] E)) := inferInstance
local instance linCRInst10 : NormedSpace ℝ (COne ℂ (E →L[ℝ] E)) := inferInstance

abbrev complexI : E →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I

def principalCR (A : HMap ℂ (E →L[ℝ] E)) : COne ℂ E →L[ℝ] HMap ℂ E :=
  jetDirection Complex.I - (holderCoefficientAction A).comp (jetDirection 1)

omit [CompleteSpace E] in
@[simp] lemma principalCR_value [CompleteSpace E]
    (A : HMap ℂ (E →L[ℝ] E)) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (principalCR A u) z = cDeriv u z Complex.I - valueCLM _ A z (cDeriv u z 1) := rfl

variable {K : Set ℂ}
local instance linCRInst11 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance linCRInst12 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance linCRInst13 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance linCRInst14 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance

def markedPrincipal (A : HMap ℂ (E →L[ℝ] E))
    (hA : ∀ z ∉ K, valueCLM _ A z = complexI) :
    markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  (principalCR A).restrict (fun u hu => by
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    have huZ := (mem_supportedHolder (standardJetCR u) K).mp hu.2 z hz
    rw [standardJetCR_value] at huZ
    rw [principalCR_value,hA z hz]
    exact huZ)

@[simp] lemma markedPrincipal_value (A : HMap ℂ (E →L[ℝ] E))
    (hA : ∀ z ∉ K, valueCLM _ A z = complexI)
    (u : markedModel (E := E) K) (z : ℂ) :
    valueCLM _ (markedPrincipal A hA u).val z = cDeriv u.val z Complex.I - valueCLM _ A z (cDeriv u.val z 1) := rfl

def frameCRCoefficient (M : COne ℂ (E →L[ℝ] E)) : HMap ℂ (E →L[ℝ] E) :=
  jetDirection Complex.I M -
    mapCLM ((1:ℝ)/3) ((ContinuousLinearMap.compL ℝ E E E) complexI) (jetDirection 1 M)

omit [CompleteSpace E] in
@[simp] lemma frameCRCoefficient_value [CompleteSpace E]
    (M : COne ℂ (E →L[ℝ] E)) (z : ℂ) (v : E) :
    valueCLM _ (frameCRCoefficient M) z v = cDeriv M z Complex.I v - Complex.I • (cDeriv M z 1 v) := rfl

lemma frameCRCoefficient_zero_outside (hK : IsClosed K) (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E) :
    ∀ z ∉ K, valueCLM _ (frameCRCoefficient M) z = 0 := by
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  rw [frameCRCoefficient_value,coefficientDeriv_zero_outside hK M c hM hz]
  simp only [zero_apply,smul_zero,sub_self]

lemma coefficientAction_standardCR (M : COne ℂ (E →L[ℝ] E)) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (standardJetCR (coefficientAction M u)) z =
      cValue M z (cDeriv u z Complex.I) - Complex.I • cValue M z (cDeriv u z 1) +
      valueCLM _ (frameCRCoefficient M) z (cValue u z) := by
  rw [standardJetCR_value,coefficientAction_deriv M u z,frameCRCoefficient_value M z]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,smul_add]
  abel

lemma frame_principal_pointwise (M : COne ℂ (E →L[ℝ] E)) (A : HMap ℂ (E →L[ℝ] E))
    (u : COne ℂ E) (z : ℂ)
    (hmj : cValue M z (valueCLM _ A z (cDeriv u z 1)) = Complex.I • cValue M z (cDeriv u z 1)) :
    cValue M z (cDeriv u z Complex.I - valueCLM _ A z (cDeriv u z 1)) =
      valueCLM _ (standardJetCR (coefficientAction M u)) z -
        valueCLM _ (frameCRCoefficient M) z (cValue u z) := by
  rw [coefficientAction_standardCR M u z]
  calc
    _ = cValue M z (cDeriv u z Complex.I) - cValue M z (valueCLM _ A z (cDeriv u z 1)) :=
      map_sub (cValue M z) _ _
    _ = cValue M z (cDeriv u z Complex.I) - Complex.I • cValue M z (cDeriv u z 1) :=
      congrArg (fun w : E => cValue M z (cDeriv u z Complex.I) - w) hmj
    _ = _ := (add_sub_cancel_right _ _).symm

lemma frame_conjugates_principal (hK : IsClosed K) (M : COne ℂ (E →L[ℝ] E)) (c : ℝ)
    (hM : ∀ z ∉ K, cValue M z = c • ContinuousLinearMap.id ℝ E)
    (A : HMap ℂ (E →L[ℝ] E)) (hA : ∀ z ∉ K, valueCLM _ A z = complexI)
    (hmj : ∀ z v, cValue M z (valueCLM _ A z v) = Complex.I • (cValue M z v)) :
    (supportedCoefficientAction (jetValueCLM _ M)).comp (markedPrincipal A hA) =
      (markedCR (E := E) (K := K)).comp (markedCoefficientAction hK M c hM) -
      markedZeroOrder (frameCRCoefficient M) (frameCRCoefficient_zero_outside hK M c hM) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply value_ext
  intro z
  change cValue M z (cDeriv u.val z Complex.I - valueCLM _ A z (cDeriv u.val z 1)) =
    valueCLM _ (standardJetCR (coefficientAction M u.val)) z -
      valueCLM _ (frameCRCoefficient M) z (cValue u.val z)
  exact frame_principal_pointwise M A u.val z (hmj z (cDeriv u.val z 1))

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open Set Function

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma fredholm_post_equiv (L : E →L[ℝ] F) (hL : L.IsFredholm) (e : F ≃L[ℝ] G) :
    (e.toContinuousLinearMap.comp L).IsFredholm := by
  obtain ⟨v,hv⟩ := hL.exists_isQuasiInverse
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse
    (v := v.comp e.symm.toContinuousLinearMap)
  exact hv.comp e.toLinearEquiv.isQuasiInverse

lemma fredholm_pre_equiv (L : F →L[ℝ] G) (hL : L.IsFredholm) (e : E ≃L[ℝ] F) :
    (L.comp e.toContinuousLinearMap).IsFredholm := by
  obtain ⟨v,hv⟩ := hL.exists_isQuasiInverse
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse
    (v := e.symm.toContinuousLinearMap.comp v)
  exact e.toLinearEquiv.isQuasiInverse.comp hv

lemma post_equiv_ker (L : E →L[ℝ] F) (e : F ≃L[ℝ] G) :
    (e.toContinuousLinearMap.comp L).ker = L.ker := by
  ext x
  change e (L x) = 0 ↔ L x = 0
  exact e.map_eq_zero_iff

lemma post_equiv_range (L : E →L[ℝ] F) (e : F ≃L[ℝ] G) :
    L.range.map e.toLinearMap = (e.toContinuousLinearMap.comp L).range := by
  exact (LinearMap.range_comp L.toLinearMap e.toLinearMap).symm

lemma post_equiv_finrank_coker (L : E →L[ℝ] F) (e : F ≃L[ℝ] G) :
    Module.finrank ℝ (F ⧸ L.range) =
      Module.finrank ℝ (G ⧸ (e.toContinuousLinearMap.comp L).range) :=
  (Submodule.Quotient.equiv _ _ e.toLinearEquiv (post_equiv_range L e)).finrank_eq

lemma pre_equiv_range (L : F →L[ℝ] G) (e : E ≃L[ℝ] F) :
    (L.comp e.toContinuousLinearMap).range = L.range := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩; exact ⟨e x,rfl⟩
  · rintro ⟨x,rfl⟩; exact ⟨e.symm x,by simp⟩

def preEquivKernel (L : F →L[ℝ] G) (e : E ≃L[ℝ] F) :
    (L.comp e.toContinuousLinearMap).ker ≃ₗ[ℝ] L.ker where
  toFun x := ⟨e x.val,x.property⟩
  invFun x := ⟨e.symm x.val,by
    change L (e (e.symm x.val)) = 0
    rw [e.apply_symm_apply]
    exact x.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact e.map_add x.val y.val
  map_smul' c x := by apply Subtype.ext; exact e.map_smul c x.val

lemma index_zero_post_equiv (L : E →L[ℝ] F)
    (hL : Module.finrank ℝ L.ker = Module.finrank ℝ (F ⧸ L.range)) (e : F ≃L[ℝ] G) :
    Module.finrank ℝ (e.toContinuousLinearMap.comp L).ker =
      Module.finrank ℝ (G ⧸ (e.toContinuousLinearMap.comp L).range) := by
  rw [post_equiv_ker]
  exact hL.trans (post_equiv_finrank_coker L e)

lemma index_zero_pre_equiv (L : F →L[ℝ] G)
    (hL : Module.finrank ℝ L.ker = Module.finrank ℝ (G ⧸ L.range)) (e : E ≃L[ℝ] F) :
    Module.finrank ℝ (L.comp e.toContinuousLinearMap).ker =
      Module.finrank ℝ (G ⧸ (L.comp e.toContinuousLinearMap).range) := by
  rw [pre_equiv_range]
  exact (preEquivKernel L e).finrank_eq.trans hL

lemma equiv_add_compact_fredholm [CompleteSpace E] (e : E ≃L[ℝ] F)
    (C : E →L[ℝ] F) (hC : IsCompactOperator C) :
    (e.toContinuousLinearMap+C).IsFredholm := by
  have hT := hC.clm_comp e.symm.toContinuousLinearMap
  have he : e.toContinuousLinearMap+C = e.toContinuousLinearMap.comp
      (ContinuousLinearMap.id ℝ E+e.symm.toContinuousLinearMap.comp C) := by
    ext x; simp
  rw [he]
  exact fredholm_post_equiv _ (compactPerturbation_fredholm _ hT) e

lemma equiv_add_compact_index_zero [CompleteSpace E] (e : E ≃L[ℝ] F)
    (C : E →L[ℝ] F) (hC : IsCompactOperator C) :
    Module.finrank ℝ (e.toContinuousLinearMap+C).ker =
      Module.finrank ℝ (F ⧸ (e.toContinuousLinearMap+C).range) := by
  have hT := hC.clm_comp e.symm.toContinuousLinearMap
  have he : e.toContinuousLinearMap+C = e.toContinuousLinearMap.comp
      (ContinuousLinearMap.id ℝ E+e.symm.toContinuousLinearMap.comp C) := by
    ext x; simp
  rw [he]
  exact index_zero_post_equiv _ (compactPerturbation_index_zero _ hT) e

lemma conjugated_normal_form (P Z : E →L[ℝ] F) (D : E ≃L[ℝ] F) (R : F ≃L[ℝ] F)
    (h : R.toContinuousLinearMap.comp P = D.toContinuousLinearMap-Z) :
    P = (D.trans R.symm).toContinuousLinearMap - R.symm.toContinuousLinearMap.comp Z := by
  apply ContinuousLinearMap.ext
  intro x
  apply R.injective
  have hx := congrArg (fun L : E →L[ℝ] F => L x) h
  simpa only [ContinuousLinearMap.comp_apply,sub_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply,map_sub,ContinuousLinearEquiv.apply_symm_apply] using hx

lemma framed_compact_perturbation_fredholm [CompleteSpace E]
    (P Z C : E →L[ℝ] F) (D : E ≃L[ℝ] F) (R : F ≃L[ℝ] F)
    (h : R.toContinuousLinearMap.comp P = D.toContinuousLinearMap-Z)
    (hZ : IsCompactOperator Z) (hC : IsCompactOperator C) :
    (P+C).IsFredholm ∧ Module.finrank ℝ (P+C).ker = Module.finrank ℝ (F ⧸ (P+C).range) := by
  have he : P+C = (D.trans R.symm).toContinuousLinearMap +
      (C-R.symm.toContinuousLinearMap.comp Z) := by
    rw [conjugated_normal_form P Z D R h]
    abel
  have hc := hC.sub (hZ.clm_comp R.symm.toContinuousLinearMap)
  rw [he]
  exact ⟨equiv_add_compact_fredholm _ _ hc,equiv_add_compact_index_zero _ _ hc⟩

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma compact_subset_bump_inner {K : Set ℂ} (hK : IsCompact K) :
    ∃ b : ContDiffBump (0:ℂ), K ⊆ Metric.closedBall (0:ℂ) b.rIn := by
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0:ℂ) := ⟨R,R+1,hR,by linarith⟩
  refine ⟨b,?_⟩
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using hKR z hz

lemma markedZeroOrder_isCompact_of_compact [ProperSpace E] {K : Set ℂ} (hK : IsCompact K)
    (C : HMap ℂ (E →L[ℝ] E)) (hC : ∀ z ∉ K, valueCLM _ C z = 0) :
    IsCompactOperator (markedZeroOrder C hC) := by
  obtain ⟨b,hb⟩ := compact_subset_bump_inner hK
  exact markedZeroOrder_isCompact C hC b (fun z hz => hC z (fun hzK => hz (hb hzK)))

variable {n : ℕ} {K : Set ℂ} (hK : IsCompact K) {A : ℂ → End n}
    (hA : ContDiff ℝ ∞ A) (hc : ∀ z, Compatible (A z)) (hstd : ∀ z ∉ K, A z = standardJ n)

local instance mFredInst1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance mFredInst2 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance mFredInst3 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance mFredInst4 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance mFredInst5 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance mFredInst6 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance mFredInst7 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance mFredInst8 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
local instance mFredInst9 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance mFredInst10 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance mFredInst11 : NormedAddCommGroup (HMap ℂ (End n)) := inferInstance
local instance mFredInst12 : NormedSpace ℝ (HMap ℂ (End n)) := inferInstance
local instance mFredInst13 : NormedAddCommGroup (COne ℂ (End n)) := inferInstance
local instance mFredInst14 : NormedSpace ℝ (COne ℂ (End n)) := inferInstance
local instance mFredInst15 : CompleteSpace (markedModel (E := Phase n) K) := inferInstance
local instance mFredInst16 : AddCommGroup (markedModel (E := Phase n) K) := (mFredInst5 (n := n) (K := K)).toAddCommGroup
local instance mFredInst17 : Module ℝ (markedModel (E := Phase n) K) := (mFredInst6 (n := n) (K := K)).toModule
local instance mFredInst18 : AddCommGroup (supportedHolder (E := Phase n) K) := (mFredInst7 (n := n) (K := K)).toAddCommGroup
local instance mFredInst19 : Module ℝ (supportedHolder (E := Phase n) K) := (mFredInst8 (n := n) (K := K)).toModule

include hK hstd in
lemma structureAlong_compactPerturbation : HasCompactSupport (fun z => A z - standardJ n) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hzK
  apply hz
  change A z-standardJ n=0
  rw [hstd z hzK,sub_self]

def smoothAlongJet : COne ℂ (End n) :=
  ofBoundedCThree (boundedCThree_of_compactPerturbation hA (standardJ n)
    (structureAlong_compactPerturbation hK hstd))

@[simp] lemma smoothAlongJet_value (z : ℂ) : cValue (smoothAlongJet (n := n) hK hA hstd) z = A z := rfl

def smoothMarkedPrincipal : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  markedPrincipal (jetValueCLM _ (smoothAlongJet (n := n) hK hA hstd)) (by intro z hz; exact hstd z hz)

@[simp] lemma smoothMarkedPrincipal_value (u : markedModel (E := Phase n) K) (z : ℂ) :
    valueCLM _ (smoothMarkedPrincipal (n := n) hK hA hstd u).val z =
      cDeriv u.val z Complex.I - A z (cDeriv u.val z 1) := rfl

lemma compatible_frame_cr_compact :
    IsCompactOperator (markedZeroOrder (E := Phase n) (frameCRCoefficient (E := Phase n) (compatibleFrameJet (n := n) hK hA hstd))
      (frameCRCoefficient_zero_outside (E := Phase n) hK.isClosed (compatibleFrameJet (n := n) hK hA hstd) 2
        (by intro z hz; rw [compatibleFrameJet_value,hstd z hz,compatibleFrame_standard]))) :=
  markedZeroOrder_isCompact_of_compact (E := Phase n) hK _ _

lemma compatible_frame_cr_identity :
    (compatibleResidualEquiv (n := n) hK hA hc hstd).toContinuousLinearMap.comp
        (smoothMarkedPrincipal (n := n) hK hA hstd) =
      (markedCR (E := Phase n) (K := K)).comp
        (compatibleMarkedEquiv (n := n) hK hA hc hstd).toContinuousLinearMap -
      markedZeroOrder (E := Phase n) (frameCRCoefficient (E := Phase n) (compatibleFrameJet (n := n) hK hA hstd))
        (frameCRCoefficient_zero_outside (E := Phase n) hK.isClosed (compatibleFrameJet (n := n) hK hA hstd) 2
          (by intro z hz; rw [compatibleFrameJet_value,hstd z hz,compatibleFrame_standard])) := by
  apply frame_conjugates_principal (E := Phase n) hK.isClosed (compatibleFrameJet (n := n) hK hA hstd) 2
    (fun z hz => (congrArg compatibleFrame (hstd z hz)).trans compatibleFrame_standard)
    (jetValueCLM _ (smoothAlongJet (n := n) hK hA hstd)) (fun z hz => hstd z hz)
  intro z v
  exact compatibleFrame_intertwine (hc z) v

def compatibleFrameError : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  markedZeroOrder (E := Phase n) (frameCRCoefficient (E := Phase n) (compatibleFrameJet (n := n) hK hA hstd))
    (frameCRCoefficient_zero_outside (E := Phase n) hK.isClosed (compatibleFrameJet (n := n) hK hA hstd) 2
      (by intro z hz; rw [compatibleFrameJet_value,hstd z hz,compatibleFrame_standard]))

lemma compatibleFrameError_compact : IsCompactOperator (compatibleFrameError (n := n) (K := K) (A := A) hK hA hstd) :=
  compatible_frame_cr_compact (n := n) (K := K) (A := A) hK hA hstd

def compatiblePrincipalCoords : markedModel (E := Phase n) K ≃L[ℝ] supportedHolder (E := Phase n) K :=
  (compatibleMarkedEquiv (n := n) hK hA hc hstd).trans (markedCREquiv (E := Phase n) hK)

lemma compatiblePrincipalCoords_toCLM :
    (compatiblePrincipalCoords (n := n) (K := K) (A := A) hK hA hc hstd).toContinuousLinearMap =
      (markedCR (E := Phase n) (K := K)).comp
        (compatibleMarkedEquiv (n := n) hK hA hc hstd).toContinuousLinearMap := rfl

lemma compatible_normal_form :
    (compatibleResidualEquiv (n := n) (K := K) (A := A) hK hA hc hstd).toContinuousLinearMap.comp (smoothMarkedPrincipal (n := n) (K := K) (A := A) hK hA hstd) =
      (compatiblePrincipalCoords (n := n) (K := K) (A := A) hK hA hc hstd).toContinuousLinearMap-compatibleFrameError (n := n) (K := K) (A := A) hK hA hstd := by
  exact compatible_frame_cr_identity (n := n) (K := K) (A := A) hK hA hc hstd

include hc in

lemma smoothMarkedPrincipal_add_compact_fredholm
    (C : markedModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K)
    (hC : IsCompactOperator C) :
    (smoothMarkedPrincipal (n := n) (K := K) (A := A) hK hA hstd+C).IsFredholm ∧
      Module.finrank ℝ (smoothMarkedPrincipal (n := n) (K := K) (A := A) hK hA hstd+C).ker =
      Module.finrank ℝ (supportedHolder (E := Phase n) K ⧸ (smoothMarkedPrincipal (n := n) (K := K) (A := A) hK hA hstd+C).range) := by
  have h := framed_compact_perturbation_fredholm
    (E := markedModel (E := Phase n) K) (F := supportedHolder (E := Phase n) K)
    (smoothMarkedPrincipal (n := n) (K := K) (A := A) hK hA hstd)
    (compatibleFrameError (n := n) (K := K) (A := A) hK hA hstd) C (compatiblePrincipalCoords (n := n) (K := K) (A := A) hK hA hc hstd)
    (compatibleResidualEquiv (n := n) (K := K) (A := A) hK hA hc hstd) (compatible_normal_form (n := n) (K := K) (A := A) hK hA hc hstd)
    (compatibleFrameError_compact (n := n) (K := K) (A := A) hK hA hstd) hC
  exact h

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
