import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveResidueFourier
import Mathlib.Topology.Algebra.Semigroup

namespace OAI

/-! Primitivity detects the kernel of every proper residue reduction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

private lemma finite_monoid_idempotent_power {R : Type*} [Monoid R] [Finite R] (x : R) :
    ∃ n : ℕ, 0 < n ∧ x^n * x^n = x^n := by
  classical
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let S : Set R := {y | ∃ n : ℕ, 0 < n ∧ y = x^n}
  obtain ⟨y,hy,he⟩ := exists_idempotent_in_compact_subsemigroup
    (fun r : R => continuous_of_discreteTopology) S
    ⟨x, 1, by norm_num, by simp⟩ (Set.toFinite S).isCompact (by
      rintro a ⟨m,hm,rfl⟩ b ⟨n,hn,rfl⟩
      exact ⟨m+n, by omega, (pow_add _ _ _).symm⟩)
  obtain ⟨n,hn,rfl⟩ := hy
  exact ⟨n,hn,he⟩

/-- A surjection of finite commutative rings is surjective on units.
The proof lifts an arbitrary element and corrects its zero components using
an idempotent power; no local or unramified hypothesis is imposed. -/
lemma finite_ring_units_surjective {R S : Type*} [CommRing R] [CommRing S] [Finite R]
    (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (Units.map f.toMonoidHom) := by
  intro u
  obtain ⟨x,hx⟩ := hf (u : S)
  obtain ⟨n,hn,he⟩ := finite_monoid_idempotent_power x
  let e := x^n
  have he2 : e*e=e := he
  have hfe : f e = 1 := by
    have hu : IsUnit (f e) := by simpa only [e,map_pow,hx] using u.isUnit.pow n
    exact (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp
      (by simpa only [IsIdempotentElem, map_mul] using congrArg f he2)
  have hp : x*x^(n-1) = e := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  let w := x*e+(1-e)
  let v := x^(n-1)*e+(1-e)
  have hwv : w*v=1 := by
    calc
      _ = (x*x^(n-1))*e^2 + (x+x^(n-1))*(e-e^2) + (1-e)^2 := by
        dsimp only [w,v]
        ring
      _ = 1 := by
        rw [pow_two e,he2,hp,he2,sub_self,mul_zero,add_zero]
        linear_combination he2
  refine ⟨⟨w,v,hwv,by simpa only [mul_comm] using hwv⟩,?_⟩
  apply Units.ext
  change f w = (u:S)
  simp only [w,map_add,map_mul,map_sub,map_one,hfe,hx,mul_one,sub_self,add_zero]

/-- Reduction between actual Eisenstein residue rings. -/
def residueReduction {q d : Eisenstein} (hd : d ∣ q) : Residues q →+* Residues d :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hd)

@[simp] lemma residueReduction_mk {q d : Eisenstein} (hd : d ∣ q) (x : Eisenstein) :
    residueReduction hd (Ideal.Quotient.mk (modulus q) x) =
      Ideal.Quotient.mk (modulus d) x := rfl

lemma residueReduction_units_surjective {q d : Eisenstein} (hq : q ≠ 0) (hd : d ∣ q) :
    Function.Surjective (Units.map (residueReduction hd).toMonoidHom) := by
  let : Finite (Residues q) := finite_residues hq
  exact finite_ring_units_surjective _ (Ideal.Quotient.factor_surjective _)

/-- Triviality on the reduction kernel constructs a genuine lower conductor. -/
lemma residueCharacter_induces_of_kernel {q d : Eisenstein} (hq : q ≠ 0)
    (hd : d ∣ q) (χ : MulChar (Residues q) ℂ)
    (hker : ∀ u : (Residues q)ˣ,
      Units.map (residueReduction hd).toMonoidHom u = 1 → χ u = 1) :
    ∃ ψ : MulChar (Residues d) ℂ, ResidueCharacterInduces q d χ ψ := by
  let f := Units.map (residueReduction hd).toMonoidHom
  have hk : f.ker ≤ χ.toUnitHom.ker := by
    intro u hu
    apply (MonoidHom.mem_ker).mpr
    apply Units.ext
    exact hker u hu
  let E := MonoidHom.liftOfSurjective f (residueReduction_units_surjective hq hd)
    ⟨χ.toUnitHom,hk⟩
  have hE : E.comp f = χ.toUnitHom := MonoidHom.liftOfRightInverse_comp ..
  refine ⟨MulChar.ofUnitHom E,hd,?_⟩
  intro x hx
  let u := (residue_isUnit_of_isCoprime hx).unit
  have hu : (u : Residues q) = Ideal.Quotient.mk (modulus q) x :=
    IsUnit.unit_spec _
  have he := congrArg (fun H => (H u : ℂ)) hE
  change ((E (f u) : ℂˣ) : ℂ) = χ (u : Residues q) at he
  rw [← MulChar.ofUnitHom_coe] at he
  change (MulChar.ofUnitHom E) (residueReduction hd (u : Residues q)) =
    χ (u : Residues q) at he
  rw [hu,residueReduction_mk] at he
  exact he

/-- A primitive character is nontrivial on each proper reduction kernel. -/
theorem primitiveResidue_nontrivial_kernel {q d : Eisenstein} (hq : q ≠ 0)
    (hd : d ∣ q) (hsmall : normNat d < normNat q)
    (χ : MulChar (Residues q) ℂ) (hχ : PrimitiveResidueCharacter q χ) :
    ∃ u : (Residues q)ˣ, Units.map (residueReduction hd).toMonoidHom u = 1 ∧ χ u ≠ 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨ψ,hψ⟩ := residueCharacter_induces_of_kernel hq hd χ h
  exact (not_le_of_gt hsmall) (hχ d ψ hψ)

/-- A nonunit frequency is fixed by a unit on which a primitive character is
nontrivial. The smaller modulus is the quotient by one common prime factor. -/
lemma primitiveResidue_frequency_stabilizer {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : PrimitiveResidueCharacter q χ)
    (a : Residues q) (ha : ¬ IsUnit a) :
    ∃ u : (Residues q)ˣ, a * (u : Residues q) = a ∧ χ u ≠ 1 := by
  classical
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective a
  have hcop : ¬ IsCoprime q r := fun h => ha (residue_isUnit_of_isCoprime h)
  have hrel : ¬ IsRelPrime q r := fun h => hcop h.isCoprime
  rw [UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hq] at hrel
  push Not at hrel
  obtain ⟨p,hpq,hpr,hp⟩ := hrel
  obtain ⟨d,hd⟩ := hpq
  obtain ⟨k,hk⟩ := hpr
  have hd0 : d ≠ 0 := by intro h; simp [h] at hd; exact hq hd
  have hdp : d ∣ q := ⟨p, hd.trans (mul_comm p d)⟩
  have hpN : 1 < normNat p := by
    have hp0 := normNat_ne_zero hp.ne_zero
    have hp1 : normNat p ≠ 1 := by
      intro he
      apply hp.not_isUnit
      apply isUnit_of_norm_eq_one
      rw [← normNat_cast, he, Nat.cast_one]
    omega
  have hsmall : normNat d < normNat q := by
    rw [hd,normNat_mul]
    nlinarith [Nat.pos_of_ne_zero (normNat_ne_zero hd0)]
  obtain ⟨u,hu,hχu⟩ := primitiveResidue_nontrivial_kernel hq hdp hsmall χ hχ
  refine ⟨u,?_,hχu⟩
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : Residues q)
  have hxd : Ideal.Quotient.mk (modulus d) x = 1 := by
    have he := congrArg (fun v : (Residues d)ˣ => (v : Residues d)) hu
    change residueReduction hdp (u : Residues q) = 1 at he
    rw [← hx,residueReduction_mk] at he
    exact he
  have hdx : d ∣ x-1 := by
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change Ideal.Quotient.mk (modulus d) (x-1) = 0
    rw [map_sub,hxd,map_one,sub_self]
  have hdiv : q ∣ r*x-r := by
    obtain ⟨y,hy⟩ := hdx
    refine ⟨k*y,?_⟩
    rw [hd,hk]
    calc
      p*k*x-p*k = p*k*(x-1) := by ring
      _ = p*d*(k*y) := by rw [hy]; ring
  rw [← hx, ← map_mul]
  apply (sub_eq_zero.mp ?_)
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)

/-- The Fourier transform of a primitive residue character vanishes at every
nonunit frequency, including those at ramified factors of the modulus. -/
theorem primitiveResidueFourier_nonunit {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) (a : Residues q) (ha : ¬ IsUnit a) :
    residueCharacterFourier q hq χ a = 0 := by
  obtain ⟨u,hu,hχu⟩ := primitiveResidue_frequency_stabilizer hq χ hχ a ha
  have he := gaussSum_mulShift χ ((residueFourierChar q hq).mulShift a) u
  rw [AddChar.mulShift_mulShift, hu] at he
  exact eq_zero_of_mul_eq_self_left hχu he

/-- The complete Gauss eigenrelation holds with the actual zero extension of
the multiplicative character on nonunits. -/
theorem primitiveResidueFourier_eq {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) (a : Residues q) :
    residueCharacterFourier q hq χ a =
      (star χ) a * gaussSum χ (residueFourierChar q hq) := by
  by_cases ha : IsUnit a
  · obtain ⟨u,rfl⟩ := ha
    exact residueCharacterFourier_unit q hq χ u
  · rw [primitiveResidueFourier_nonunit hq χ hχ a ha, MulChar.map_nonunit _ ha, zero_mul]

/-- Finite Fourier inversion at the unit element. This identity only needs
the additive pairing to be perfect; the ring need not be a field. -/
lemma finite_gauss_fourier_at_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ∑ a : R, gaussSum χ (ψ.mulShift a) * ψ (-a) = Fintype.card R := by
  classical
  simp only [gaussSum, Finset.sum_mul, AddChar.mulShift_apply]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : R, χ x * ∑ a : R, ψ (a*(x-1)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← ψ.map_add_eq_mul]
      congr 2
      ring
    _ = ∑ x : R, χ x * (if x = 1 then (Fintype.card R : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [AddChar.sum_mulShift (x-1) hψ, sub_eq_zero]
      split_ifs <;> simp_all
    _ = Fintype.card R := by simp

/-- Exact square norm of the primitive residue Gauss sum, for arbitrary
nonzero Eisenstein modulus, including prime powers above three. -/
theorem primitiveResidueGauss_mul_conj {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) :
    gaussSum χ (residueFourierChar q hq) *
      star (gaussSum χ (residueFourierChar q hq)) = (normNat q : ℂ) := by
  have hi := finite_gauss_fourier_at_one χ (residueFourierChar q hq)
    (residueFourierChar_isPrimitive q hq)
  change (∑ a : Residues q, residueCharacterFourier q hq χ a *
    residueFourierChar q hq (-a)) = _ at hi
  simp_rw [primitiveResidueFourier_eq hq χ hχ, MulChar.star_apply,
    AddChar.map_neg_eq_conj] at hi
  change (∑ a : Residues q, star (χ a) *
    gaussSum χ (residueFourierChar q hq) * star (residueFourierChar q hq a)) = _ at hi
  have he : (∑ a : Residues q, star (χ a) *
      gaussSum χ (residueFourierChar q hq) * star (residueFourierChar q hq a)) =
      gaussSum χ (residueFourierChar q hq) *
        star (gaussSum χ (residueFourierChar q hq)) := by
    change (∑ a : Residues q, star (χ a) *
      gaussSum χ (residueFourierChar q hq) * star (residueFourierChar q hq a)) =
      gaussSum χ (residueFourierChar q hq) *
        star (∑ a : Residues q, χ a * residueFourierChar q hq a)
    rw [star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [star_mul]
    ring
  rw [he] at hi
  convert hi using 1
  rw [← Nat.card_eq_fintype_card, residues_card hq]

/-- Positive real norm of the primitive Gauss sum. -/
theorem primitiveResidueGauss_norm {q : Eisenstein} (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hχ : PrimitiveResidueCharacter q χ) :
    ‖gaussSum χ (residueFourierChar q hq)‖ = Real.sqrt (normNat q : ℝ) := by
  have hi := congrArg Complex.re (primitiveResidueGauss_mul_conj hq χ hχ)
  have hs : ‖gaussSum χ (residueFourierChar q hq)‖^2 = (normNat q : ℝ) := by
    have hc := Complex.mul_conj' (gaussSum χ (residueFourierChar q hq))
    change gaussSum χ (residueFourierChar q hq) *
      star (gaussSum χ (residueFourierChar q hq)) = _ at hc
    rw [hc] at hi
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.natCast_re] using hi
  rw [← hs, Real.sqrt_sq (_root_.norm_nonneg _)]

end CubicFirstMoment

end

end OAI
