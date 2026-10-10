import OAI.AlgebraicGeometry.SurfaceCones.GradedCompletion

namespace OAI


/-! Normality, dimension and completeness of the completed normalized cone. -/
noncomputable section

namespace SectionCompletion

variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

/-- The initial homogeneous polynomial, including zero. -/
noncomputable def initial (f : PowerSeries K) : Polynomial K :=
  Polynomial.monomial f.order.toNat (PowerSeries.constantCoeff f.divXPowOrder)

lemma initial_zero : initial (0 : PowerSeries K) = 0 := by
  simp [initial]

lemma initial_one : initial (1 : PowerSeries K) = 1 := by
  simp [initial, PowerSeries.constantCoeff_divXPowOrder]

lemma initial_mul (f g : PowerSeries K) : initial (f * g) = initial f * initial g := by
  by_cases hf : f = 0
  · simp [hf, initial_zero]
  by_cases hg : g = 0
  · simp [hg, initial_zero]
  simp only [initial, PowerSeries.order_mul, PowerSeries.divXPowOrder_mul, map_mul,
    ENat.toNat_add (PowerSeries.order_eq_top.not.mpr hf) (PowerSeries.order_eq_top.not.mpr hg),
    Polynomial.monomial_mul_monomial]

lemma initial_pow (f : PowerSeries K) (n : ℕ) : initial (f ^ n) = initial f ^ n := by
  induction n with
  | zero => simp [initial_one]
  | succ n ih => rw [pow_succ, initial_mul, ih, pow_succ]

lemma initial_eq (f : PowerSeries K) :
    initial f = Polynomial.monomial f.order.toNat (PowerSeries.coeff f.order.toNat f) := by
  simp [initial, PowerSeries.constantCoeff_divXPowOrder]

lemma initial_ne_zero {f : PowerSeries K} (hf : f ≠ 0) : initial f ≠ 0 := by
  intro h
  apply PowerSeries.coeff_order hf
  have hc := congrArg (fun p : Polynomial K => p.coeff f.order.toNat) h
  simpa [initial_eq] using hc

lemma initial_mem (f : series T) : initial f.val ∈ polynomials T := by
  rw [initial_eq, monomial_mem_polynomials]
  exact f.property _

lemma initial_isAlmostIntegral {f : PowerSeries K}
    (hf : IsAlmostIntegral (series T) f) :
    IsAlmostIntegral (polynomials T) (initial f) := by
  obtain ⟨d, hd, h⟩ := hf
  have hd0 : d.val ≠ 0 := by
    have : d ≠ 0 := by simpa using hd
    exact fun e => this (Subtype.ext e)
  refine ⟨⟨initial d.val, initial_mem T d⟩, ?_, fun n => ?_⟩
  · have hne : (⟨initial d.val, initial_mem T d⟩ : polynomials T) ≠ 0 := by
      intro e
      exact initial_ne_zero hd0 (congrArg Subtype.val e)
    simpa using hne
  · obtain ⟨y, hy⟩ := h n
    refine ⟨⟨initial y.val, initial_mem T y⟩, ?_⟩
    change initial y.val = initial d.val * initial f ^ n
    change y.val = d.val * f ^ n at hy
    rw [hy, initial_mul, initial_pow]

lemma initial_mem_of_isAlmostIntegral [IsNoetherianRing (polynomials T)]
    [IsIntegrallyClosedIn (polynomials T) (Polynomial K)] {f : PowerSeries K}
    (hf : IsAlmostIntegral (series T) f) : initial f ∈ polynomials T := by
  have hi := (initial_isAlmostIntegral T hf).isIntegral
  obtain ⟨y, hy⟩ := (isIntegrallyClosedIn_iff.mp
    (inferInstance : IsIntegrallyClosedIn (polynomials T) (Polynomial K))).2 hi
  exact hy ▸ y.property

/-- Normality is detected one homogeneous initial term at a time. -/
lemma mem_of_isAlmostIntegral [IsNoetherianRing (polynomials T)]
    [IsIntegrallyClosedIn (polynomials T) (Polynomial K)] {f : PowerSeries K}
    (hf : IsAlmostIntegral (series T) f) : f ∈ series T := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let p : PowerSeries K := (PowerSeries.trunc n f : Polynomial K)
    have hp : p ∈ series T := by
      intro m
      change PowerSeries.coeff m ((PowerSeries.trunc n f : Polynomial K) : PowerSeries K) ∈ T m
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with hm
      · exact ih m hm
      · exact (T m).zero_mem
    have hf' : IsAlmostIntegral (series T) (f - p) := by
      apply (completeIntegralClosure (series T) (PowerSeries K)).sub_mem hf
      exact (completeIntegralClosure (series T) (PowerSeries K)).algebraMap_mem ⟨p, hp⟩
    have hc (m : ℕ) : PowerSeries.coeff m (f - p) =
        if m < n then 0 else PowerSeries.coeff m f := by
      dsimp [p]
      rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs <;> simp
    by_cases hn : PowerSeries.coeff n f = 0
    · rw [hn]; exact (T n).zero_mem
    · have ho : (f - p).order = n := by
        apply PowerSeries.order_eq_nat.mpr
        exact ⟨by simpa [hc] using hn, fun i hi => by simp [hc, hi]⟩
      have hm := initial_mem_of_isAlmostIntegral T hf'
      rw [initial_eq, ho, ENat.toNat_natCast, monomial_mem_polynomials] at hm
      simpa [hc] using hm

/-- The coefficient product of a normal Noetherian graded algebra is normal.
The ambient function-field power-series ring is a DVR; denominators transfer
almost integrality to it, where the preceding initial-term induction applies. -/
lemma isIntegrallyClosed_series [IsNoetherianRing (polynomials T)]
    [IsIntegrallyClosedIn (polynomials T) (Polynomial K)] :
    IsIntegrallyClosed (series T) := by
  let S := series T
  let B := PowerSeries K
  let L := FractionRing B
  have hSB : Function.Injective (algebraMap S B) := Subtype.val_injective
  have hSL : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S B L]
    exact (IsFractionRing.injective B L).comp hSB
  let φ : FractionRing S →ₐ[S] L :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId S L) hSL
  apply (isIntegrallyClosed_iff (FractionRing S)).mpr
  intro x hx
  have hix : IsIntegral B (φ x) := (hx.map φ).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hix
  have hay : IsAlmostIntegral S y := by
    obtain ⟨d, hd, h⟩ := hx.isAlmostIntegral
    refine ⟨d, hd, fun n => ?_⟩
    obtain ⟨z, hz⟩ := h n
    refine ⟨z, ?_⟩
    change z.val = d.val * y ^ n
    apply IsFractionRing.injective B L
    calc
      algebraMap B L z.val = φ (algebraMap S (FractionRing S) z) := by
        rw [φ.commutes, IsScalarTower.algebraMap_apply S B L]
        rfl
      _ = φ (d • x ^ n) := congrArg φ hz
      _ = algebraMap B L (d.val * y ^ n) := by
        simp only [Algebra.smul_def, map_mul, map_pow]
        change φ (algebraMap S (FractionRing S) d) * φ x ^ n =
          algebraMap B L d.val * algebraMap B L y ^ n
        rw [φ.commutes, IsScalarTower.algebraMap_apply S B L, hy]
        rfl
  have hym : y ∈ series T := mem_of_isAlmostIntegral T hay
  refine ⟨⟨y, hym⟩, ?_⟩
  apply φ.injective
  change φ (algebraMap S (FractionRing S) ⟨y, hym⟩) = φ x
  rw [φ.commutes, IsScalarTower.algebraMap_apply S B L]
  exact hy
end SectionCompletion

namespace GradedNormalization

open Polynomial
variable {k L : Type} [Field k] [CharZero k] [Field L] [Algebra k L]
variable (B : Subalgebra k L[X])

/-- The normalized cone coefficient completion is Noetherian, normal, local and complete, with the prescribed residue field. -/
lemma normalized_completion_properties [IsAlgClosed k] [Algebra.FiniteType k B]
    [IsFractionRing B (RatFunc L)]
    (hB : ∀ a : k, ∀ p ∈ B, scale a p ∈ B)
    (hzero : ∀ p ∈ B, p.coeff 0 ∈ (⊥ : Subalgebra k L)) :
    let R := SectionCompletion.series (piece B)
    IsNoetherianRing R ∧ IsIntegrallyClosed R ∧
    ∃ (_ : IsLocalRing R),
      IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      Function.Bijective (algebraMap k (IsLocalRing.ResidueField R)) := by
  let T := piece B
  have hz := piece_zero B hzero
  let : Algebra.FiniteType k (SectionCompletion.polynomials T) :=
    polynomialPiece_finiteType B hB
  let : IsNoetherianRing (SectionCompletion.polynomials T) :=
    Algebra.FiniteType.isNoetherianRing k _
  let : IsIntegrallyClosedIn (SectionCompletion.polynomials T) L[X] :=
    polynomialPiece_normalIn B hB
  let : IsLocalRing (SectionCompletion.series T) :=
    SectionCompletion.isLocalRing T (SectionCompletion.zero_piece_closed_inv T hz)
  exact ⟨SectionCompletion.isNoetherianRing_of_finiteType T hz,
    SectionCompletion.isIntegrallyClosed_series T, inferInstance,
    SectionCompletion.adicComplete_of_finiteType T hz,
    SectionCompletion.residue_bijective T hz⟩
end GradedNormalization

namespace ExplicitCone

instance completedRing_isIntegrallyClosed : IsIntegrallyClosed completedRing :=
  (GradedNormalization.normalized_completion_properties polynomialAlgebra
    polynomialAlgebra_scale polynomialAlgebra_constantCoeff).2.1

instance completedRing_isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal completedRing) completedRing := by
  obtain ⟨_, _, h, hc, _⟩ := GradedNormalization.normalized_completion_properties
    polynomialAlgebra polynomialAlgebra_scale polynomialAlgebra_constantCoeff
  exact hc

lemma completedRing_residue_bijective :
    Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField completedRing)) := by
  obtain ⟨_, _, h, _, hr⟩ := GradedNormalization.normalized_completion_properties
    polynomialAlgebra polynomialAlgebra_scale polynomialAlgebra_constantCoeff
  exact hr

end ExplicitCone

namespace SmallCM

lemma mvPolynomial_maximal_height (k : Type) [Field k] (n : ℕ)
    (M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal] : M.height = n := by
  classical
  induction n with
  | zero =>
    let e := (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toRingEquiv
    have h := Ideal.height_le_ringKrullDim_of_ne_top
      (I := M.map e) (Ideal.map_isMaximal_of_equiv e).ne_top
    rw [e.height_map, ringKrullDim_eq_zero_of_field] at h
    exact_mod_cast le_antisymm h (by simp)
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let P : Ideal (Polynomial (MvPolynomial (Fin n) k)) := M.map e
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p : Ideal (MvPolynomial (Fin n) k) := P.under _
    have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver p := ⟨rfl⟩
    have hp := ih p
    have hh := Polynomial.height_eq_height_add_one p P
    rw [hp] at hh
    simpa only [P, e.height_map, Nat.cast_add, Nat.cast_one] using hh

/-- All closed points of an affine integral variety have full height. -/
lemma finiteType_maximal_height (k B : Type) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (M : Ideal B) [M.IsMaximal] :
    (M.height : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨m, f, hf, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  let P := MvPolynomial (Fin m) k
  let : Algebra P B := f.toRingHom.toAlgebra
  let : Module.Finite P B := hfin
  let : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective P B).mpr hf
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hm : (M.under P).IsMaximal := Ideal.IsMaximal.under P M
  have hh := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (M.under P) M
  have hd : ringKrullDim B = m := by
    rw [dimension_eq_of_integral P B]
    simp only [P, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card, Fintype.card_fin, WithBot.coe_natCast, zero_add]
  apply le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top')
  rw [hd]
  have hle : (m : ℕ∞) ≤ M.height := by
    rw [hh, mvPolynomial_maximal_height k m (M.under P)]
    exact le_self_add
  exact_mod_cast hle

lemma completion_at_maximal_dimension (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [I.IsMaximal] [IsNoetherianRing (AdicCompletion I R)] :
    ringKrullDim (AdicCompletion I R) = (I.height : WithBot ℕ∞) := by
  let S := AdicCompletion I R
  let J : Ideal S := I.map (algebraMap R S)
  have hfg := I.fg_of_isNoetherianRing
  have : J.IsMaximal := AdicCompletion.isMaximal_map_of_le I I le_rfl hfg
  have : IsAdicComplete J S := AdicCompletion.isAdicComplete_self I hfg
  have : IsLocalRing S := isLocalRing_of_isAdicComplete_maximal J
  have hJ : J = IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal inferInstance
  have : J.LiesOver I :=
    ⟨Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top' Ideal.le_comap_map⟩
  have hh := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown I J
  rw [show J = I.map (algebraMap R S) from rfl,
    Ideal.map_quotient_self, Ideal.height_bot, add_zero] at hh
  change J.height = I.height at hh
  rw [hJ] at hh
  simpa using
    congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hh
end SmallCM

namespace SectionCompletion

variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

lemma series_dimension [Algebra.FiniteType k (polynomials T)]
    (hzero : T 0 = LinearMap.range (Algebra.linearMap k K)) :
    ringKrullDim (series T) = ringKrullDim (polynomials T) := by
  classical
  have : IsNoetherianRing (polynomials T) := Algebra.FiniteType.isNoetherianRing k _
  have : IsNoetherianRing (series T) := isNoetherianRing_of_finiteType T hzero
  obtain ⟨σ, hσ, v, d, hd, hv, hgen⟩ := finite_positive_presentation T hzero
  let := hσ
  let D : ℕ := Finset.univ.sup d + 1
  have hD : 0 < D := Nat.succ_pos _
  have hc : ∀ n, degreeIdeal T (n * D) ≤ degreeIdeal T 1 ^ n :=
    degreeIdeal_cofinal T v d hd hv hgen D hD
      (fun i => (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))
  let e := completionEquiv T D hD hc
  have : IsNoetherianRing (AdicCompletion (degreeIdeal T 1) (polynomials T)) :=
    isNoetherianRing_of_ringEquiv (series T) e.toRingEquiv
  have : (degreeIdeal T 1).IsMaximal := degreeIdeal_one_isMaximal T hzero
  calc
    ringKrullDim (series T) = ringKrullDim (AdicCompletion (degreeIdeal T 1) (polynomials T)) :=
      e.toRingEquiv.ringKrullDim
    _ = ((degreeIdeal T 1).height : WithBot ℕ∞) :=
      SmallCM.completion_at_maximal_dimension (polynomials T) (degreeIdeal T 1)
    _ = ringKrullDim (polynomials T) :=
      SmallCM.finiteType_maximal_height k (polynomials T) (degreeIdeal T 1)
end SectionCompletion

namespace ExplicitCone

open Algebra Polynomial

lemma polynomialAlgebra_dimension : ringKrullDim polynomialAlgebra = 3 := by
  apply SmallCM.dimension_of_trdeg ℂ polynomialAlgebra 3
  rw [← SmallCM.trdeg_fractionRing ℂ polynomialAlgebra (RatFunc L)]
  exact rationalCone_trdeg

lemma gradedAlgebra_dimension : ringKrullDim (SectionCompletion.polynomials pieces) = 3 := by
  change ringKrullDim (SectionCompletion.polynomials
    (GradedNormalization.piece polynomialAlgebra)) = 3
  rw [GradedNormalization.polynomial_piece_eq polynomialAlgebra polynomialAlgebra_scale]
  let N : Subalgebra polynomialAlgebra L[X] := integralClosure polynomialAlgebra L[X]
  let : CommRing N := Subalgebra.toCommRing (R := polynomialAlgebra) (A := L[X]) N
  let hA : Algebra polynomialAlgebra N := Subalgebra.algebra (R := polynomialAlgebra) N
  let : SMul polynomialAlgebra N := hA.toSMul
  change ringKrullDim N = 3
  have : FaithfulSMul polynomialAlgebra N :=
    (faithfulSMul_iff_algebraMap_injective polynomialAlgebra N).mpr
      (fun _ _ h => Subtype.ext (congrArg (fun x : N => (x : L[X])) h))
  rw [SmallCM.dimension_eq_of_integral polynomialAlgebra N, polynomialAlgebra_dimension]

end ExplicitCone

namespace ExplicitCone

lemma completedRing_dimension : ringKrullDim completedRing = 3 := by
  have : Algebra.FiniteType ℂ (SectionCompletion.polynomials pieces) :=
    GradedNormalization.polynomialPiece_finiteType polynomialAlgebra polynomialAlgebra_scale
  exact (SectionCompletion.series_dimension pieces zero_piece).trans gradedAlgebra_dimension
end ExplicitCone


end

end OAI
