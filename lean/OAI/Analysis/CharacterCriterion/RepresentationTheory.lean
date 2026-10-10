import OAI.Analysis.CharacterCriterion.BalancedLimit

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
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


open NormedSpace
open scoped ComplexOrder
namespace KirchbergRordam
namespace States

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

lemma norm_rotation (a : A) (ha : IsSelfAdjoint a) (t : ℝ) :
    ‖exp (t • (Complex.I • a))‖ = 1 := by
  have he : exp (t • (Complex.I • a)) =
      (selfAdjoint.expUnitary (t • (⟨a, ha⟩ : selfAdjoint A)) : A) := by
    change exp (t • (Complex.I • a)) = exp (Complex.I • t • a)
    rw [smul_comm]
  rw [he, CStarRing.norm_coe_unitary]

lemma eval_selfAdjoint_im_zero (φ : A →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) (h1 : φ 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) : (φ a).im = 0 := by
  let l : A →L[ℝ] ℝ := Complex.reCLM.comp (φ.restrictScalars ℝ)
  have hd : HasDerivAt (fun t : ℝ => l (exp (t • (Complex.I • a))))
      (-(φ a).im) 0 := by
    have hh := l.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_exp_smul_const (Complex.I • a) (0 : ℝ))
    convert hh using 1 <;> first | rfl | simp [l, map_smul, Complex.mul_re]
  have hmax : IsLocalMax (fun t : ℝ => l (exp (t • (Complex.I • a)))) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change (φ (exp (t • (Complex.I • a)))).re ≤ (φ (exp ((0 : ℝ) • (Complex.I • a)))).re
    simp only [zero_smul, exp_zero, h1, Complex.one_re]
    exact (Complex.re_le_norm _).trans <|
      (φ.le_opNorm _).trans <| by rw [norm_rotation a ha t, mul_one]; exact hφ
  exact neg_eq_zero.mp (hmax.hasDerivAt_eq_zero hd)

variable [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]

lemma eval_nonneg (φ : A →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) (h1 : φ 1 = 1)
    (a : A) (ha : 0 ≤ a) : 0 ≤ φ a := by
  have hi := eval_selfAdjoint_im_zero φ hφ h1 a (IsSelfAdjoint.of_nonneg ha)
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, hi.symm⟩
  by_cases hz : a = 0
  · simp [hz]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr hz
  let b := ‖a‖⁻¹ • a
  have hb : 0 ≤ b := smul_nonneg (inv_nonneg.mpr hn.le) ha
  have hbn : ‖b‖ ≤ 1 := by
    dsimp [b]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hb1 : b ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg b hb).mp hbn
  have hn1 : ‖1 - b‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (sub_nonneg.mpr hb1)).mpr (sub_le_self _ hb)
  have hh : (φ (1 - b)).re ≤ 1 :=
    (Complex.re_le_norm _).trans <| (φ.le_opNorm _).trans <|
      (mul_le_mul_of_nonneg_left hn1 (norm_nonneg φ)).trans (by simpa using hφ)
  rw [map_sub, h1, Complex.sub_re, Complex.one_re] at hh
  have hbr : (φ b).re = ‖a‖⁻¹ * (φ a).re := by
    dsimp [b]
    change ((φ.restrictScalars ℝ) (‖a‖⁻¹ • a)).re = _
    rw [map_smul]
    simp
  rw [hbr] at hh
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hn)).mp (by linarith : 0 ≤ ‖a‖⁻¹ * (φ a).re)


theorem exists_state : ∃ φ : A →ₚ[ℂ] ℂ, φ 1 = 1 := by
  obtain ⟨φ, hφ, h1⟩ := exists_dual_vector ℂ (1 : A) (by simp)
  have h1 : φ 1 = 1 := by simpa using h1
  exact ⟨PositiveLinearMap.mk₀ φ.toLinearMap (eval_nonneg φ hφ.le h1), h1⟩

end States
end KirchbergRordam


open scoped ComplexOrder
namespace KirchbergRordam
namespace PureStates
variable (A : Type*) [CStarAlgebra A]

def normStates : Set (WeakDual ℂ A) := {φ | ‖φ.toStrongDual‖ ≤ 1 ∧ φ 1 = 1}

def evaluationReal : WeakDual ℂ A →ₗ[ℝ] (A → ℂ) where
  toFun φ := φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance locallyConvexReal : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
  LocallyConvexSpace.induced (evaluationReal A)

lemma normStates_compact : IsCompact (normStates A) := by
  have h := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).inter_right
    (isClosed_eq (WeakDual.eval_continuous (1 : A)) (continuous_const (y := (1 : ℂ))))
  convert h using 1
  ext φ
  simp [normStates, Metric.mem_closedBall]

variable [Nontrivial A]

lemma normStates_nonempty : (normStates A).Nonempty := by
  obtain ⟨φ, hφ, h1⟩ := exists_dual_vector ℂ (1 : A) (by simp)
  refine ⟨(StrongDual.toWeakDual φ), hφ.le, ?_⟩
  simpa using h1


def IsPure (φ : A →L[ℂ] ℂ) : Prop :=
  (StrongDual.toWeakDual φ) ∈ (normStates A).extremePoints ℝ

theorem exists_pure : ∃ φ : A →L[ℂ] ℂ, IsPure A φ := by
  obtain ⟨φ, hφ⟩ := (normStates_compact A).extremePoints_nonempty (normStates_nonempty A)
  exact ⟨φ.toStrongDual, hφ⟩

variable {A}

omit [Nontrivial A] in
lemma IsPure.norm_le_one {φ : A →L[ℂ] ℂ} (hp : IsPure A φ) : ‖φ‖ ≤ 1 := hp.1.1
omit [Nontrivial A] in
lemma IsPure.map_one {φ : A →L[ℂ] ℂ} (hp : IsPure A φ) : φ 1 = 1 := hp.1.2

omit [Nontrivial A] in
lemma IsPure.extreme {φ ψ χ : A →L[ℂ] ℂ} (hp : IsPure A φ)
    (hψ : ‖ψ‖ ≤ 1) (hψ1 : ψ 1 = 1) (hχ : ‖χ‖ ≤ 1) (hχ1 : χ 1 = 1)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (he : φ = t • ψ + (1 - t) • χ) : ψ = φ := by
  apply StrongDual.toWeakDual.injective
  apply hp.2 (show (StrongDual.toWeakDual ψ) ∈ normStates A from ⟨hψ, hψ1⟩)
    (show (StrongDual.toWeakDual χ) ∈ normStates A from ⟨hχ, hχ1⟩)
  exact ⟨t, 1 - t, ht, sub_pos.mpr ht1, by ring, by
    change t • ψ + (1 - t) • χ = φ
    exact he.symm⟩

end PureStates
end KirchbergRordam

open scoped InnerProductSpace
namespace KirchbergRordam
namespace Representations
variable {A : Type*} [CStarAlgebra A] [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]
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

omit instPartialOrderA instStarOrderedRingA in
@[simp] lemma coefficient_apply.{contextLevel1, contextLevel2}
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {H : Type contextLevel2}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (π : A →⋆ₐ[ℂ] H →L[ℂ] H)
    (ξ : H)
    (T : H →L[ℂ] H) (a : A) :
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
end KirchbergRordam
namespace KirchbergRordam.PureStates
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
    simpa only [_root_.add_apply, Complex.add_re, hp.map_one, Complex.one_re] using he1
  by_cases ht0 : t = 0
  · have hg0 : g = 0 := norm_eq_zero.mp (le_antisymm (hn.trans_eq ht0) (norm_nonneg _))
    change g = t • φ
    rw [ht0, hg0]
    ext a
    simp only [_root_.smul_apply, zero_apply]
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
    simp only [_root_.smul_apply, hg1, Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast ht0)
  have hhn : (s⁻¹ • h) 1 = 1 := by
    simp only [_root_.smul_apply, hh1, Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast hs0)
  have hf := hp.extreme htn hgn hsn hhn t (lt_of_le_of_ne ht (Ne.symm ht0))
    (by linarith [lt_of_le_of_ne hs (Ne.symm hs0)]) (by
      rw [show 1 - t = s by linarith, smul_smul, smul_smul,
        mul_inv_cancel₀ ht0, mul_inv_cancel₀ hs0, one_smul, one_smul]
      exact he.symm)
  have heq := congrArg (fun f : A →L[ℂ] ℂ => t • f) hf
  simpa only [smul_smul, mul_inv_cancel₀ ht0, one_smul] using heq

end KirchbergRordam.PureStates

namespace KirchbergRordam.Representations
variable {A : Type*} [CStarAlgebra A] [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

omit instPartialOrderA instStarOrderedRingA in
lemma coefficient_one.{contextLevel1, contextLevel2}
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {H : Type contextLevel2}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (π : A →⋆ₐ[ℂ] H →L[ℂ] H)
    (ξ : H)
    : coefficient π ξ 1 = (innerSL ℂ ξ).comp
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

end KirchbergRordam.Representations
namespace KirchbergRordam.Representations
variable {A : Type*} [CStarAlgebra A] [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]
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

end KirchbergRordam.Representations
namespace KirchbergRordam
namespace Representations
variable {A : Type*} [CStarAlgebra A] [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]

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
variable {A : Type u} [CStarAlgebra A] [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A] [Nontrivial A]

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

end KirchbergRordam

namespace KirchbergRordam.PureStates
open scoped ComplexOrder
variable (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]
lemma exists_norming_dual (a : A) : ∃ φ : A →L[ℂ] ℂ,
    ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ φ (star a*a)=(‖star a*a‖:ℂ) := by
  let b := star a * a
  have hb : 0 ≤ b := star_mul_self_nonneg a
  let : IsStarNormal b := (IsSelfAdjoint.of_nonneg hb).isStarNormal
  let S := StarAlgebra.elemental ℂ b
  have hs : (‖b‖ : ℂ) ∈ spectrum ℂ b := by
    exact spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg b hb)
  obtain ⟨χ,hχ⟩ := (StarAlgebra.elemental.bijective_characterSpaceToSpectrum b).surjective
    ⟨(‖b‖ : ℂ),hs⟩
  let g : S →ₐ[ℂ] ℂ := WeakDual.CharacterSpace.equivAlgHom χ
  let : StarHomClass (S →ₐ[ℂ] ℂ) S ℂ := AlgHomClass.instStarHomClass
  have hg : ‖g.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul, AlgHom.coe_toContinuousLinearMap] using NonUnitalStarAlgHom.norm_apply_le g x
  obtain ⟨ψ,hψ,hψnorm⟩ := exists_extension_norm_eq S.toSubalgebra.toSubmodule
    g.toContinuousLinearMap
  have hψ1 : ψ 1 = 1 := by
    exact (hψ (1 : S)).trans (map_one g)
  have hψb : ψ b = (‖b‖ : ℂ) := by
    have hh := congrArg Subtype.val hχ
    exact (hψ ⟨b,StarAlgebra.elemental.self_mem ℂ b⟩).trans hh
  exact ⟨ψ,hψnorm.trans_le hg,hψ1,hψb⟩


theorem exists_pure_norming (a : A) : ∃ φ : A →L[ℂ] ℂ,
    IsPure A φ ∧ (φ (star a*a)).re=‖star a*a‖ := by
  let b := star a*a
  let F : Set (WeakDual ℂ A) := {φ | φ ∈ normStates A ∧ (φ b).re=‖b‖}
  have hc : IsCompact F := (normStates_compact A).inter_right
    (isClosed_eq (Complex.continuous_re.comp (WeakDual.eval_continuous b)) continuous_const)
  have hn : F.Nonempty := by
    obtain ⟨φ,hφ,h1,hb⟩ := exists_norming_dual A a
    exact ⟨StrongDual.toWeakDual φ,⟨hφ,h1⟩,by change (φ b).re=‖b‖; rw [hb]; rfl⟩
  obtain ⟨φ,hφ⟩ := hc.extremePoints_nonempty hn
  refine ⟨φ.toStrongDual,⟨hφ.1.1,?_⟩,hφ.1.2⟩
  intro ψ hψ χ hχ he
  obtain ⟨s,t,hs,ht,hst,heq⟩ := he
  have hψb : (ψ b).re ≤ ‖b‖ := (Complex.re_le_norm _).trans <|
    (ψ.toStrongDual.le_opNorm b).trans (by nlinarith [norm_nonneg b,hψ.1])
  have hχb : (χ b).re ≤ ‖b‖ := (Complex.re_le_norm _).trans <|
    (χ.toStrongDual.le_opNorm b).trans (by nlinarith [norm_nonneg b,hχ.1])
  have hv := congrArg (fun f : WeakDual ℂ A => (f b).re) heq
  change ((s • ψ b+t • χ b):ℂ).re=(φ b).re at hv
  simp only [Complex.add_re,Complex.smul_re,smul_eq_mul] at hv
  rw [hφ.1.2] at hv
  have hw : s * ‖b‖ + t * ‖b‖ = ‖b‖ := by rw [← add_mul,hst,one_mul]
  have hψF : ψ ∈ F := ⟨hψ,by
    apply le_antisymm hψb
    by_contra! hlt
    nlinarith [mul_pos hs (sub_pos.mpr hlt), mul_nonneg ht.le (sub_nonneg.mpr hχb)]⟩
  have hχF : χ ∈ F := ⟨hχ,by
    apply le_antisymm hχb
    by_contra! hlt
    nlinarith [mul_pos ht (sub_pos.mpr hlt), mul_nonneg hs.le (sub_nonneg.mpr hψb)]⟩
  exact hφ.2 hψF hχF ⟨s,t,hs,ht,hst,heq⟩
end KirchbergRordam.PureStates

namespace KirchbergRordam

theorem irreducible_separate_zero {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (a : A) (ha : ∀ π : IrreducibleRepresentation A, π.representation a=0) : a=0 := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  obtain ⟨φ,hp,hb⟩ := PureStates.exists_pure_norming A a
  let π := Representations.pureRepresentation φ hp
  have hz : φ (star a*a)=0 := by
    have hh := congrArg (fun f : A →L[ℂ] ℂ => f (star a*a))
      (Representations.pure_gns_coefficient φ hp)
    rw [Representations.coefficient_apply] at hh
    have hs : π.representation (star a*a)=0 := by rw [map_mul,ha π,mul_zero]
    have he := hs
    change (Representations.stateOfPure φ hp).gnsStarAlgHom (star a*a)=0 at he
    rw [he] at hh
    simpa using hh.symm
  rw [hz,Complex.zero_re] at hb
  apply norm_eq_zero.mp
  have hs : ‖star a * a‖ = ‖a‖ * ‖a‖ := CStarRing.norm_star_mul_self
  rw [← hb] at hs
  nlinarith [norm_nonneg a]
end KirchbergRordam
end

end OAI
