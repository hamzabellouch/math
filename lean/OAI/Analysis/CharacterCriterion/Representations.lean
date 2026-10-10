import OAI.Analysis.CharacterCriterion.States

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder


open scoped InnerProductSpace
namespace KirchbergRordam.GenericRW
namespace Representations
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

def gnsVector (a : A) : f.GNS := (f.toPreGNS a : f.GNS)

@[simp] lemma gnsVector_inner (a b : A) :
    ⟪gnsVector f a, gnsVector f b⟫_ℂ = f (star a * b) := by
  simp [gnsVector, PositiveLinearMap.preGNS_inner_def]

@[simp] lemma gnsVector_apply (a b : A) :
    f.gnsStarAlgHom a (gnsVector f b) = gnsVector f (a * b) := by
  simp [gnsVector, PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.leftMulMapPreGNS]

lemma positive_bound (a : A) : ‖f a‖ ≤ (f 1).re * ‖a‖ := by
  let ξ := gnsVector f 1
  have hi : f a = ⟪ξ, f.gnsStarAlgHom a ξ⟫_ℂ := by
    dsimp [ξ]
    rw [gnsVector_apply, gnsVector_inner]
    simp
  have hn : ‖ξ‖ ^ 2 = (f 1).re := by
    calc
      _ = (⟪ξ, ξ⟫_ℂ).re := (inner_self_eq_norm_sq (𝕜 := ℂ) ξ).symm
      _ = (f 1).re := by dsimp [ξ]; rw [gnsVector_inner]; simp
  calc
    ‖f a‖ = ‖⟪ξ, f.gnsStarAlgHom a ξ⟫_ℂ‖ := congrArg norm hi
    _ ≤ ‖ξ‖ * ‖f.gnsStarAlgHom a ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖a‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left
      ((f.gnsStarAlgHom a).le_opNorm ξ |>.trans <| mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom a) (norm_nonneg ξ)) (norm_nonneg ξ)
    _ = (f 1).re * ‖a‖ := by rw [← hn]; ring

def positiveCLM : A →L[ℂ] ℂ :=
  f.toLinearMap.mkContinuous (f 1).re (positive_bound f)

@[simp] lemma positiveCLM_apply (a : A) : positiveCLM f a = f a := rfl

lemma positiveCLM_norm : ‖positiveCLM f‖ ≤ (f 1).re := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact (Complex.nonneg_iff.mp (f.map_nonneg zero_le_one)).1
  · exact positive_bound f

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

def representationCLM : A →L[ℂ] (H →L[ℂ] H) :=
  π.toAlgHom.toLinearMap.mkContinuous 1 fun a => by
    simpa using NonUnitalStarAlgHom.norm_apply_le π a

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma representationCLM_apply (a : A) : representationCLM π a = π a := rfl

def coefficient (T : H →L[ℂ] H) : A →L[ℂ] ℂ where
  toFun a := ⟪ξ, T (π a ξ)⟫_ℂ
  map_add' a b := by simp
  map_smul' z a := by simp
  cont := (continuous_const.inner <| T.continuous.comp <|
    ((representationCLM π).continuous.clm_apply continuous_const))

@[simp] lemma coefficient_apply (T : H →L[ℂ] H) (a : A) :
    coefficient π ξ T a = ⟪ξ, T (π a ξ)⟫_ℂ := rfl

lemma coefficient_nonneg (T : H →L[ℂ] H) (hT : 0 ≤ T)
    (hc : ∀ a, Commute T (π a)) (a : A) (ha : 0 ≤ a) :
    0 ≤ coefficient π ξ T a := by
  let b := CFC.sqrt a
  have hb : IsSelfAdjoint (π b) := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).map π
  have hab : a = b * b := (CFC.sqrt_mul_sqrt_self a ha).symm
  have ht := ContinuousLinearMap.nonneg_iff_isPositive.mp hT
  have he : coefficient π ξ T a = ⟪π b ξ, T (π b ξ)⟫_ℂ := by
    rw [coefficient_apply, hab, map_mul]
    have hh := congrArg (fun S : H →L[ℂ] H => S (π b ξ)) (hc b).eq
    change ⟪ξ, T (π b (π b ξ))⟫_ℂ = _
    change T (π b (π b ξ)) = π b (T (π b ξ)) at hh
    rw [hh]
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (fun S : H →L[ℂ] H => ⟪S ξ, T (π b ξ)⟫_ℂ) hb.star_eq
  rw [he]
  exact ht.inner_nonneg_right _

lemma coefficient_norm (T : H →L[ℂ] H) (hT : 0 ≤ T)
    (hc : ∀ a, Commute T (π a)) :
    ‖coefficient π ξ T‖ ≤ (⟪ξ, T ξ⟫_ℂ).re := by
  let g : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ (coefficient π ξ T).toLinearMap
    (coefficient_nonneg π ξ T hT hc)
  have he : positiveCLM g = coefficient π ξ T := by ext; rfl
  have hn := positiveCLM_norm g
  rw [he] at hn
  change ‖coefficient π ξ T‖ ≤ (coefficient π ξ T 1).re at hn
  simpa only [coefficient_apply, map_one, one_apply_eq_self] using hn

end Representations
end KirchbergRordam.GenericRW
namespace KirchbergRordam.GenericRW.PureStates
variable {A : Type*} [CStarAlgebra A]

lemma IsPure.split (φ g h : A →L[ℂ] ℂ) (hp : IsPure A φ)
    (hn : ‖g‖ ≤ (g 1).re) (hm : ‖h‖ ≤ (h 1).re)
    (hg : 0 ≤ g 1) (hh : 0 ≤ h 1) (he : g + h = φ) :
    g = (g 1).re • φ := by
  let t := (g 1).re
  let s := (h 1).re
  have hg1 : g 1 = (t : ℂ) := by
    apply Complex.ext <;> simp [t, (Complex.nonneg_iff.mp hg).2.symm]
  have hh1 : h 1 = (s : ℂ) := by
    apply Complex.ext <;> simp [s, (Complex.nonneg_iff.mp hh).2.symm]
  have ht : 0 ≤ t := (Complex.nonneg_iff.mp hg).1
  have hs : 0 ≤ s := (Complex.nonneg_iff.mp hh).1
  have hts : t + s = 1 := by
    have he1 := congrArg (fun f : A →L[ℂ] ℂ => (f 1).re) he
    simpa only [add_apply, Complex.add_re, hp.map_one, Complex.one_re] using he1
  by_cases ht0 : t = 0
  · have hg0 : g = 0 := norm_eq_zero.mp (le_antisymm (hn.trans_eq ht0) (norm_nonneg _))
    change g = t • φ
    rw [ht0, hg0]
    ext a
    simp only [smul_apply, zero_apply]
    exact (zero_smul ℝ (φ a)).symm
  by_cases hs0 : s = 0
  · have hh0 : h = 0 := norm_eq_zero.mp (le_antisymm (hm.trans_eq hs0) (norm_nonneg _))
    have ht1 : t = 1 := by linarith
    change g = t • φ
    simpa [ht1, hh0] using he
  have htn : ‖t⁻¹ • g‖ ≤ 1 := calc
    _ = t⁻¹ * ‖g‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ht)]
    _ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr ht)
    _ = 1 := inv_mul_cancel₀ ht0
  have hsn : ‖s⁻¹ • h‖ ≤ 1 := calc
    _ = s⁻¹ * ‖h‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hs)]
    _ ≤ s⁻¹ * s := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hs)
    _ = 1 := inv_mul_cancel₀ hs0
  have hgn : (t⁻¹ • g) 1 = 1 := by
    simp only [smul_apply, hg1, Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast ht0)
  have hhn : (s⁻¹ • h) 1 = 1 := by
    simp only [smul_apply, hh1, Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast hs0)
  have hf := hp.extreme htn hgn hsn hhn t (lt_of_le_of_ne ht (Ne.symm ht0))
    (by linarith [lt_of_le_of_ne hs (Ne.symm hs0)]) (by
      rw [show 1 - t = s by linarith, smul_smul, smul_smul,
        mul_inv_cancel₀ ht0, mul_inv_cancel₀ hs0, one_smul, one_smul]
      exact he.symm)
  have heq := congrArg (fun f : A →L[ℂ] ℂ => t • f) hf
  simpa only [smul_smul, mul_inv_cancel₀ ht0, one_smul] using heq

end KirchbergRordam.GenericRW.PureStates

namespace KirchbergRordam.GenericRW.Representations
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

lemma coefficient_one : coefficient π ξ 1 = (innerSL ℂ ξ).comp
    ((ContinuousLinearMap.apply ℂ H ξ).comp (representationCLM π)) := by ext; rfl

lemma coefficient_commutant_injective (hd : DenseRange (fun a => π a ξ))
    (T S : H →L[ℂ] H) (hT : ∀ a, Commute T (π a)) (hS : ∀ a, Commute S (π a))
    (he : coefficient π ξ T = coefficient π ξ S) : T = S := by
  have hξ : T ξ = S ξ := by
    apply ext_inner_left ℂ
    intro y
    refine hd.induction_on (p := fun y => ⟪y, T ξ⟫_ℂ = ⟪y, S ξ⟫_ℂ) y
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    have he' := congrArg (fun f : A →L[ℂ] ℂ => f (star a)) he
    have ha (U : H →L[ℂ] H) (hU : ∀ a, Commute U (π a)) :
        coefficient π ξ U (star a) = ⟪π a ξ, U ξ⟫_ℂ := by
      rw [coefficient_apply]
      have hc := congrArg (fun V : H →L[ℂ] H => V ξ) (hU (star a)).eq
      change U (π (star a) ξ) = π (star a) (U ξ) at hc
      rw [hc, map_star]
      exact ContinuousLinearMap.adjoint_inner_right (π a) ξ (U ξ)
    simpa only [ha T hT, ha S hS] using he'
  apply DFunLike.coe_injective
  apply hd.equalizer T.continuous S.continuous
  funext a
  change T (π a ξ) = S (π a ξ)
  have htc := congrArg (fun U : H →L[ℂ] H => U ξ) (hT a).eq
  have hsc := congrArg (fun U : H →L[ℂ] H => U ξ) (hS a).eq
  change T (π a ξ) = π a (T ξ) at htc
  change S (π a ξ) = π a (S ξ) at hsc
  rw [htc, hsc, hξ]

lemma positive_contraction_scalar (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ)
    (hφ : coefficient π ξ 1 = φ) (hd : DenseRange (fun a => π a ξ))
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (hT1 : T ≤ 1) (hc : ∀ a, Commute T (π a)) :
    ∃ t : ℝ, T = t • 1 := by
  let g := coefficient π ξ T
  let h := coefficient π ξ (1 - T)
  have hTc : ∀ a, Commute (1 - T) (π a) := fun a => (Commute.one_left _).sub_left (hc a)
  have hsum : g + h = φ := by
    rw [← hφ]
    ext a
    simp [g, h, coefficient]
  have hgn : ‖g‖ ≤ (g 1).re := by
    simpa only [g, coefficient_apply, map_one, one_apply_eq_self] using coefficient_norm π ξ T hT hc
  have hhn : ‖h‖ ≤ (h 1).re := by
    simpa only [h, coefficient_apply, map_one, one_apply_eq_self] using
      coefficient_norm π ξ (1 - T) (sub_nonneg.mpr hT1) hTc
  have he := hp.split φ g h hgn hhn (coefficient_nonneg π ξ T hT hc 1 zero_le_one)
    (coefficient_nonneg π ξ (1 - T) (sub_nonneg.mpr hT1) hTc 1 zero_le_one) hsum
  refine ⟨(g 1).re, coefficient_commutant_injective π ξ hd T ((g 1).re • 1) hc
    (fun a => (Commute.one_left _).smul_left _) ?_⟩
  change g = coefficient π ξ ((g 1).re • 1)
  calc
    g = (g 1).re • φ := he
    _ = coefficient π ξ ((g 1).re • 1) := by
      conv_lhs => rw [← hφ]
      ext a
      simp [coefficient]

end KirchbergRordam.GenericRW.Representations
namespace KirchbergRordam.GenericRW.Representations
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
variable (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ)
    (hφ : coefficient π ξ 1 = φ) (hd : DenseRange (fun a => π a ξ))

include hp hφ hd

lemma positive_scalar (T : H →L[ℂ] H) (hT : 0 ≤ T) (hc : ∀ a, Commute T (π a)) :
    ∃ t : ℝ, T = t • 1 := by
  by_cases hz : T = 0
  · exact ⟨0, by simp [hz]⟩
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr hz
  have hS : 0 ≤ ‖T‖⁻¹ • T := smul_nonneg (inv_nonneg.mpr hn.le) hT
  have hS1 : ‖T‖⁻¹ • T ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hS).mp <| by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  obtain ⟨t, ht⟩ := positive_contraction_scalar π ξ φ hp hφ hd _ hS hS1
    (fun a => (hc a).smul_left _)
  refine ⟨‖T‖ * t, ?_⟩
  have he := congrArg (fun U : H →L[ℂ] H => ‖T‖ • U) ht
  simpa only [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] using he

lemma selfAdjoint_scalar (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hc : ∀ a, Commute T (π a)) : ∃ t : ℝ, T = t • 1 := by
  have hn := hT.neg.le_algebraMap_norm_self
  rw [norm_neg, Algebra.algebraMap_eq_smul_one] at hn
  have hpT : 0 ≤ T + ‖T‖ • (1 : H →L[ℂ] H) := neg_le_iff_add_nonneg'.mp hn
  obtain ⟨t, ht⟩ := positive_scalar π ξ φ hp hφ hd _ hpT
    (fun a => (hc a).add_left ((Commute.one_left _).smul_left _))
  refine ⟨t - ‖T‖, ?_⟩
  rw [sub_smul]
  exact eq_sub_iff_add_eq.mpr ht


theorem pure_cyclic_scalar_commutant (T : H →L[ℂ] H)
    (hc : ∀ a, Commute T (π a)) : ∃ z : ℂ, T = z • 1 := by
  have hcs (a : A) : Commute (star T) (π a) := by
    exact (show Commute T (star (π a)) by simpa only [map_star] using hc (star a)).star_left
  have hcr (a : A) : Commute (realPart T : H →L[ℂ] H) (π a) := by
    rw [realPart_apply_coe]
    exact ((hc a).add_left (hcs a)).smul_left _
  have hci (a : A) : Commute (imaginaryPart T : H →L[ℂ] H) (π a) := by
    rw [imaginaryPart_apply_coe]
    exact (((hc a).sub_left (hcs a)).smul_left _).smul_left _
  obtain ⟨r, hr⟩ := selfAdjoint_scalar π ξ φ hp hφ hd _ (realPart T).property hcr
  obtain ⟨s, hs⟩ := selfAdjoint_scalar π ξ φ hp hφ hd _ (imaginaryPart T).property hci
  refine ⟨(r : ℂ) + Complex.I * (s : ℂ), ?_⟩
  calc
    T = (realPart T : H →L[ℂ] H) + Complex.I • (imaginaryPart T : H →L[ℂ] H) :=
      (realPart_add_I_smul_imaginaryPart T).symm
    _ = ((r : ℂ) + Complex.I * (s : ℂ)) • 1 := by
      rw [hr, hs, add_smul, mul_smul]
      simp only [Complex.coe_smul]

end KirchbergRordam.GenericRW.Representations
namespace KirchbergRordam.GenericRW
namespace Representations
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma gns_cyclic (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsVector f 1)) := by
  have hd : DenseRange (gnsVector f) := by
    intro x
    apply closure_mono (t := Set.range (gnsVector f)) _ (UniformSpace.Completion.denseRange_coe x)
    rintro _ ⟨a, rfl⟩
    exact ⟨f.ofPreGNS a, by simp [gnsVector]⟩
  simpa only [gnsVector_apply, mul_one] using hd


lemma positive_zero_of_square_zero (f : A →ₚ[ℂ] ℂ) (a : A)
    (hz : f (star a * a) = 0) : f a = 0 := by
  have hvec : gnsVector f a = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    simpa only [gnsVector_inner] using hz
  have hinner := gnsVector_inner f 1 a
  simpa only [hvec, inner_zero_right, star_one, one_mul] using hinner.symm

variable [Nontrivial A]

def stateOfPure (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ φ.toLinearMap (States.eval_nonneg φ hp.norm_le_one hp.map_one)

@[simp] lemma stateOfPure_apply (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) (a : A) :
    stateOfPure φ hp a = φ a := rfl

lemma pure_gns_coefficient (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) :
    coefficient (stateOfPure φ hp).gnsStarAlgHom (gnsVector (stateOfPure φ hp) 1) 1 = φ := by
  ext a
  rw [coefficient_apply, one_apply_eq_self, gnsVector_apply, gnsVector_inner]
  simp

lemma pure_gns_nontrivial (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) :
    Nontrivial (stateOfPure φ hp).GNS := by
  apply nontrivial_of_ne (gnsVector (stateOfPure φ hp) 1) 0
  intro he
  have hh := gnsVector_inner (stateOfPure φ hp) 1 1
  rw [he] at hh
  simp [hp.map_one] at hh

end Representations

universe u

structure IrreducibleRepresentation (A : Type u) [CStarAlgebra A] where
  space : Type u
  [normed : NormedAddCommGroup space]
  [inner : InnerProductSpace ℂ space]
  [complete : CompleteSpace space]
  [nontrivial : Nontrivial space]
  representation : A →⋆ₐ[ℂ] (space →L[ℂ] space)
  scalar_commutant : ∀ T : space →L[ℂ] space,
    (∀ a, Commute T (representation a)) → ∃ z : ℂ, T = z • 1

attribute [instance] IrreducibleRepresentation.normed IrreducibleRepresentation.inner
  IrreducibleRepresentation.complete IrreducibleRepresentation.nontrivial

namespace Representations
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

def pureRepresentation (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) :
    IrreducibleRepresentation A where
  space := (stateOfPure φ hp).GNS
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  nontrivial := pure_gns_nontrivial φ hp
  representation := (stateOfPure φ hp).gnsStarAlgHom
  scalar_commutant := pure_cyclic_scalar_commutant _ _ φ hp (pure_gns_coefficient φ hp)
    (gns_cyclic _)

end Representations


theorem exists_irreducible_representation (A : Type u) [CStarAlgebra A] [Nontrivial A] :
    Nonempty (IrreducibleRepresentation A) := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  obtain ⟨φ, hp⟩ := PureStates.exists_pure A
  exact ⟨Representations.pureRepresentation φ hp⟩

end KirchbergRordam.GenericRW
end

end OAI
