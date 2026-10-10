import OAI.Analysis.CharacterCriterion.Fullness

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
namespace KirchbergRordam.GenericRW
namespace DoubleCommutator

lemma derivative_eq_zero_of_concave_bddBelow {f : ℝ → ℝ} {d : ℝ}
    (hc : ConcaveOn ℝ Set.univ f) (hd : HasDerivAt f d 0)
    (M : ℝ) (hM : ∀ t, -M ≤ f t) : d = 0 := by
  have hpos : 0 < M + f 0 + 1 := by linarith [hM 0]
  rcases lt_trichotomy d 0 with hn | he | hp
  · let t := (M + f 0 + 1) / (-d)
    have ht : 0 < t := div_pos hpos (neg_pos.mpr hn)
    have hh := hc.slope_le_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ t) ht hd
    rw [slope_def_field, sub_zero, div_le_iff₀ ht] at hh
    have htd : d * t = -(M + f 0 + 1) := by
      dsimp [t]
      field_simp [ne_of_lt hn]
    have := hM t
    linarith
  · exact he
  · let t := -(M + f 0 + 1) / d
    have ht : t < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hpos) hp
    have hh := hc.le_slope_of_hasDerivAt (Set.mem_univ t) (Set.mem_univ 0) ht hd
    rw [slope_def_field, zero_sub, le_div_iff₀ (neg_pos.mpr ht)] at hh
    have htd : d * t = -(M + f 0 + 1) := by
      dsimp [t]
      field_simp
    have := hM t
    nlinarith

section BanachAlgebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def bracket (X T : A) : A := X * T - T * X

def orbit (X T : A) (t : ℝ) : A := exp (t • X) * T * exp (t • (-X))

lemma derivative_orbit (X T : A) (t : ℝ) :
    HasDerivAt (orbit X T) (orbit X (bracket X T) t) t := by
  have hu := hasDerivAt_exp_smul_const X t
  have hv := hasDerivAt_exp_smul_const' (-X) t
  convert (hu.mul_const T).mul hv using 1
  · rfl
  · dsimp only [orbit, bracket]
    noncomm_ring

end BanachAlgebra

section CStar
variable {A : Type*} [CStarAlgebra A]

lemma bracket_smul_left (z : ℂ) (S T : A) :
    bracket (z • S) T = z • bracket S T := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub]

lemma bracket_smul_right (z : ℂ) (S T : A) :
    bracket S (z • T) = z • bracket S T := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub]

lemma bracket_I_twice (S T : A) :
    bracket (Complex.I • S) (bracket (Complex.I • S) T) =
      -bracket S (bracket S T) := by
  simp only [bracket_smul_left, bracket_smul_right, smul_smul,
    Complex.I_mul_I, neg_one_smul]

lemma star_rotation (S : A) (hS : IsSelfAdjoint S) (t : ℝ) :
    star (exp (t • (Complex.I • S))) = exp (t • (-(Complex.I • S))) := by
  rw [star_exp]
  congr 1
  simp [star_smul, hS.star_eq, smul_neg]

lemma norm_orbit (S T : A) (hS : IsSelfAdjoint S) (t : ℝ) :
    ‖orbit (Complex.I • S) T t‖ = ‖T‖ := by
  have he (t : ℝ) : exp (t • (Complex.I • S)) =
      (selfAdjoint.expUnitary (t • (⟨S, hS⟩ : selfAdjoint A)) : A) := by
    change exp (t • (Complex.I • S)) = exp (Complex.I • t • S)
    rw [smul_comm]
  rw [orbit, ← star_rotation S hS t, he]
  exact (CStarRing.norm_mul_coe_unitary _ (star _)).trans
    (CStarRing.norm_coe_unitary_mul _ _)

lemma selfAdjoint_I_bracket (S T : A) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (Complex.I • bracket S T) := by
  change star (Complex.I • bracket S T) = Complex.I • bracket S T
  simp only [star_smul, bracket, star_sub, star_mul, hS.star_eq, hT.star_eq,
    Complex.star_def, Complex.conj_I, neg_smul, smul_sub]
  abel

end CStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


def quadratic (ξ : H) : (H →L[ℂ] H) →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ H ξ)).restrictScalars ℝ)

omit [CompleteSpace H] in
lemma quadratic_apply (ξ : H) (T : H →L[ℂ] H) :
    quadratic ξ T = (inner ℂ ξ (T ξ)).re := rfl

lemma quadratic_derivative (ξ : H) (X T : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (fun t => quadratic ξ (orbit X T t))
      (quadratic ξ (orbit X (bracket X T) t)) t :=
  (quadratic ξ).hasFDerivAt.comp_hasDerivAt t (derivative_orbit X T t)

lemma quadratic_orbit_lower (ξ : H) (S T : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (t : ℝ) : -(‖quadratic ξ‖ * ‖T‖) ≤ quadratic ξ (orbit (Complex.I • S) T t) := by
  have hn := (quadratic ξ).le_opNorm (orbit (Complex.I • S) T t)
  rw [norm_orbit S T hS t, Real.norm_eq_abs] at hn
  exact (abs_le.mp hn).1

lemma quadratic_orbit_nonneg (ξ : H) (S T : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (hT : T.IsPositive) (t : ℝ) : 0 ≤ quadratic ξ (orbit (Complex.I • S) T t) := by
  have hh := (hT.conj_adjoint (exp (t • (Complex.I • S)))).re_inner_nonneg_right ξ
  simpa only [quadratic_apply, orbit, ← star_rotation S hS t,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, RCLike.re_eq_complex_re] using hh

end DoubleCommutator

open DoubleCommutator


theorem commute_of_positive_double_commutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S T : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hz : (S * (S * T - T * S) - (S * T - T * S) * S).IsPositive) :
    Commute S T := by
  have he (ξ : H) : quadratic ξ (Complex.I • bracket S T) = 0 := by
    let X := Complex.I • S
    let f (t : ℝ) := quadratic ξ (orbit X T t)
    let f' (t : ℝ) := quadratic ξ (orbit X (bracket X T) t)
    let f'' (t : ℝ) := quadratic ξ (orbit X (bracket X (bracket X T)) t)
    have hd (t : ℝ) : HasDerivAt f (f' t) t := quadratic_derivative ξ X T t
    have hd' (t : ℝ) : HasDerivAt f' (f'' t) t :=
      quadratic_derivative ξ X (bracket X T) t
    have hneg (t : ℝ) : f'' t ≤ 0 := by
      dsimp only [f'', X]
      rw [bracket_I_twice]
      simp only [orbit, mul_neg, neg_mul, map_neg, neg_nonpos]
      exact quadratic_orbit_nonneg ξ S (bracket S (bracket S T)) hS hz t
    have hc : ConcaveOn ℝ Set.univ f :=
      concaveOn_of_hasDerivWithinAt2_nonpos (convex_univ)
        (fun t _ => (hd t).continuousAt.continuousWithinAt)
        (fun t _ => (hd t).hasDerivWithinAt)
        (fun t _ => (hd' t).hasDerivWithinAt) (fun t _ => hneg t)
    have := derivative_eq_zero_of_concave_bddBelow hc (hd 0)
      (‖quadratic ξ‖ * ‖T‖) (quadratic_orbit_lower ξ S T hS)
    simpa only [f', X, orbit, zero_smul, exp_zero, one_mul, mul_one,
      bracket_smul_left] using this
  have hQ := selfAdjoint_I_bracket S T hS hT
  have h0 : (Complex.I • bracket S T : H →L[ℂ] H).toLinearMap = 0 := by
    apply (inner_map_self_eq_zero _).mp
    intro ξ
    rw [hQ.isSymmetric ξ ξ, ← hQ.isSymmetric.coe_re_inner_self_apply ξ]
    change (quadratic ξ (Complex.I • bracket S T) : ℂ) = 0
    rw [he, Complex.ofReal_zero]
  have h0' : (Complex.I • bracket S T : H →L[ℂ] H) = 0 := by
    ext ξ
    exact congrArg (fun Q : H →ₗ[ℂ] H => Q ξ) h0
  have : bracket S T = 0 := (smul_eq_zero.mp h0').resolve_left Complex.I_ne_zero
  exact sub_eq_zero.mp this


theorem commute_of_negative_double_commutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S T : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hz : (-(S * (S * T - T * S) - (S * T - T * S) * S)).IsPositive) :
    Commute S T := by
  have h := commute_of_positive_double_commutator S (-T) hS hT.neg (by
    convert hz using 1
    noncomm_ring)
  simpa only [Commute, SemiconjBy, mul_neg, neg_mul, neg_inj] using h

end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.Fullness
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
lemma doubleBracket_selfAdjoint (s t : A) (hs : IsSelfAdjoint s) (ht : IsSelfAdjoint t) :
    IsSelfAdjoint (s * (s * t - t * s) - (s * t - t * s) * s) := by
  change star _ = _
  simp only [star_sub, star_mul, hs.star_eq, ht.star_eq]
  noncomm_ring


theorem full_parts (s t : A) (hs : IsSelfAdjoint s) (ht : IsSelfAdjoint t)
    (h : ∀ π : IrreducibleRepresentation A,
      ¬ Commute (π.representation s) (π.representation t)) :
    let z := s * (s * t - t * s) - (s * t - t * s) * s
    IsFull z⁺ ∧ IsFull z⁻ := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let z := s * (s * t - t * s) - (s * t - t * s) * s
  have hz : IsSelfAdjoint z := doubleBracket_selfAdjoint s t hs ht
  have he (π : IrreducibleRepresentation A) :
      π.representation z = π.representation z⁺ - π.representation z⁻ := by
    rw [← map_sub, CFC.posPart_sub_negPart z hz]
  constructor
  · apply full_of_survives
    intro π hp
    apply h π
    apply commute_of_negative_double_commutator _ _ (hs.map _) (ht.map _)
    apply ContinuousLinearMap.nonneg_iff_isPositive.mp
    have hpos : 0 ≤ π.representation z⁻ := map_nonneg π.representation (CFC.negPart_nonneg z)
    have hm : π.representation z =
        π.representation s * (π.representation s * π.representation t -
          π.representation t * π.representation s) -
        (π.representation s * π.representation t - π.representation t * π.representation s) *
          π.representation s := by simp only [z, map_sub, map_mul]
    rw [← hm, he, hp, zero_sub, neg_neg]
    exact hpos
  · apply full_of_survives
    intro π hn
    apply h π
    apply commute_of_positive_double_commutator _ _ (hs.map _) (ht.map _)
    apply ContinuousLinearMap.nonneg_iff_isPositive.mp
    have hpos : 0 ≤ π.representation z⁺ := map_nonneg π.representation (CFC.posPart_nonneg z)
    have hm : π.representation z =
        π.representation s * (π.representation s * π.representation t -
          π.representation t * π.representation s) -
        (π.representation s * π.representation t - π.representation t * π.representation s) *
          π.representation s := by simp only [z, map_sub, map_mul]
    rw [← hm, he, hn, sub_zero]
    exact hpos

end KirchbergRordam.GenericRW.Fullness
end

end OAI
