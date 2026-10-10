import Mathlib.RingTheory.MvPolynomial.Ideal
import OAI.AlgebraicGeometry.PlaneCurves.AffineMultiplicity
import OAI.AlgebraicGeometry.PlaneCurves.PolynomialJets

namespace OAI

/-!
# Translation, Taylor coefficients, and ordinary multiplicity
-/

section

/-!
# Cancellation by a function nonzero at a point
-/

namespace Nagata.AffineMultiplicity

variable {R : Type*} [CommRing R]

theorem cancel_nonmember_maximal_power (I : Ideal R) (hI : I.IsMaximal)
    (m : ℕ) (f g : R) (hg : g ∉ I) : g * f ∈ I ^ m ↔ f ∈ I ^ m := by
  by_cases hm : m = 0
  · simp [hm]
  constructor
  · intro hgf
    have hfg : f * g ∈ I ^ m := by simpa only [mul_comm] using hgf
    have hrad : (I ^ m).radical = I := by rw [Ideal.radical_pow I hm, hI.isPrime.radical]
    by_cases h : I ^ m + Ideal.span {g} = ⊤
    · rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.mul_top (Ideal.span {f}), ← h,
        mul_add, Ideal.span_singleton_mul_span_singleton, add_le_iff,
        Ideal.span_singleton_le_iff_mem]
      exact ⟨Ideal.mul_le_right, hfg⟩
    · obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal (I ^ m + Ideal.span {g}) h
      rw [add_le_iff, Ideal.span_singleton_le_iff_mem,
        ← hM.isPrime.radical_le_iff, hrad] at hJM
      exact (hg (hI.eq_of_le hM.ne_top hJM.1 ▸ hJM.2)).elim
  · exact (I ^ m).mul_mem_left g

theorem orderAtLeast_cancel_nonvanishing {σ F : Type*} [Field F]
    (p : σ → F) (m : ℕ) (f g : MvPolynomial σ F)
    (hg : MvPolynomial.eval p g ≠ 0) :
    orderAtLeast p m (g * f) ↔ orderAtLeast p m f := by
  apply cancel_nonmember_maximal_power (pointIdeal p) (pointIdeal_isMaximal p)
  intro h
  exact hg ((pointIdeal_mem_iff p g).mp h)

end Nagata.AffineMultiplicity

end

section

/-! Concrete polynomial coordinate translation and its proved inverse. -/

namespace Nagata.AffineMultiplicity

variable {σ R : Type*} [CommRing R]

noncomputable def translateHom (p : σ → R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (p i))

@[simp] theorem translateHom_C (p : σ → R) (a : R) :
    translateHom p (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [translateHom]

@[simp] theorem translateHom_X (p : σ → R) (i : σ) :
    translateHom p (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C (p i) := by
  simp [translateHom]

theorem translateHom_neg_comp (p : σ → R) :
    (translateHom (-p)).comp (translateHom p) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp
  · intro i; simp [add_assoc]

theorem translateHom_comp_neg (p : σ → R) :
    (translateHom p).comp (translateHom (-p)) = RingHom.id _ := by
  simpa only [neg_neg] using translateHom_neg_comp (-p)

noncomputable def translateEquiv (p : σ → R) : MvPolynomial σ R ≃+* MvPolynomial σ R :=
  { translateHom p with
    invFun := translateHom (-p)
    left_inv := fun f => RingHom.congr_fun (translateHom_neg_comp p) f
    right_inv := fun f => RingHom.congr_fun (translateHom_comp_neg p) f }

@[simp] theorem translateEquiv_apply (p : σ → R) (f : MvPolynomial σ R) :
    translateEquiv p f = translateHom p f := rfl

theorem eval_zero_translate (p : σ → R) (f : MvPolynomial σ R) :
    MvPolynomial.eval (0 : σ → R) (translateHom p f) = MvPolynomial.eval p f := by
  have h : (MvPolynomial.eval (0 : σ → R)).comp (translateHom p) =
      MvPolynomial.eval p := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp
  exact RingHom.congr_fun h f

end Nagata.AffineMultiplicity

end

section

namespace Nagata.AffineMultiplicity

variable {σ R : Type*} [CommRing R]

/-- Actual polynomial evaluation intertwines coordinate translation with
translation of the input point, at every point, not only at the origin. -/
theorem eval_translate (p x : σ → R) (f : MvPolynomial σ R) :
    MvPolynomial.eval x (translateHom p f) = MvPolynomial.eval (x + p) f := by
  have h : (MvPolynomial.eval x).comp (translateHom p) =
      MvPolynomial.eval (x + p) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp
  exact RingHom.congr_fun h f

end Nagata.AffineMultiplicity

end

section

/-!
# Genuine finite Taylor coefficients and ideal-power multiplicity
-/

namespace Nagata.AffineMultiplicity

variable {σ R : Type*} [CommRing R]

theorem pointIdeal_zero_eq_idealOfVars :
    pointIdeal (0 : σ → R) = MvPolynomial.idealOfVars σ R := by
  ext f
  rw [pointIdeal_mem_iff, MvPolynomial.eval_zero]
  have h := MvPolynomial.mem_pow_idealOfVars_iff' 1 f
  have h' : f ∈ MvPolynomial.idealOfVars σ R ↔ f.coeff 0 = 0 := by
    simpa [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] using h
  exact h'.symm

/-- Vanishing order at `p` is exactly vanishing of every coefficient below
total degree `m` after the explicit translation `X ↦ X+p`. -/
theorem orderAtLeast_iff_taylor_coeff (p : σ → R) (m : ℕ) (f : MvPolynomial σ R) :
    orderAtLeast p m f ↔
      ∀ a : σ →₀ ℕ, Finsupp.degree a < m → (translateHom p f).coeff a = 0 := by
  have h := orderAtLeast_equiv_iff p (0 : σ → R) (translateEquiv p)
    (fun g => eval_zero_translate p g) m f
  rw [← h]
  unfold orderAtLeast
  rw [pointIdeal_zero_eq_idealOfVars]
  exact MvPolynomial.mem_pow_idealOfVars_iff' m (translateHom p f)

end Nagata.AffineMultiplicity

end

section

/-!
# Ordinary numerical multiplicity of a nonzero affine polynomial

This is the actual minimum total degree of a nonzero translated coefficient.
The definition is independent of the desired Nagata inequality and is given
only for nonzero polynomials; the zero polynomial is not assigned a finite order.
-/

namespace Nagata.AffineMultiplicity

variable {σ R : Type*} [CommRing R]

theorem translate_ne_zero (p : σ → R) (f : MvPolynomial σ R) (hf : f ≠ 0) :
    translateHom p f ≠ 0 := by
  intro h
  apply hf
  apply (translateEquiv p).injective
  simpa only [translateEquiv_apply, map_zero] using h

theorem translated_support_nonempty (p : σ → R) (f : MvPolynomial σ R) (hf : f ≠ 0) :
    (translateHom p f).support.Nonempty :=
  MvPolynomial.support_nonempty.mpr (translate_ne_zero p f hf)

theorem translated_support_finite (p : σ → R) (f : MvPolynomial σ R) :
    (↑(translateHom p f).support : Set (σ →₀ ℕ)).Finite :=
  Finset.finite_toSet _

/-- The ordinary multiplicity is a finite minimum of genuine Taylor degrees. -/
noncomputable def ordinaryMultiplicity (p : σ → R) (f : MvPolynomial σ R)
    (hf : f ≠ 0) : ℕ :=
  (translateHom p f).support.inf' (translated_support_nonempty p f hf) Finsupp.degree

/-- The minimum is attained by an actual nonzero coefficient. -/
theorem ordinaryMultiplicity_attained (p : σ → R) (f : MvPolynomial σ R)
    (hf : f ≠ 0) :
    ∃ a : σ →₀ ℕ, (translateHom p f).coeff a ≠ 0 ∧
      ordinaryMultiplicity p f hf = Finsupp.degree a := by
  obtain ⟨a, ha, hdegree⟩ := Finset.exists_mem_eq_inf'
    (translated_support_nonempty p f hf) Finsupp.degree
  exact ⟨a, MvPolynomial.mem_support_iff.mp ha, hdegree⟩

/-- The baseline lower-bound predicate agrees with the actual numeric order. -/
theorem orderAtLeast_iff_le_ordinaryMultiplicity
    (p : σ → R) (m : ℕ) (f : MvPolynomial σ R) (hf : f ≠ 0) :
    orderAtLeast p m f ↔ m ≤ ordinaryMultiplicity p f hf := by
  rw [orderAtLeast_iff_taylor_coeff, ordinaryMultiplicity, Finset.le_inf'_iff]
  constructor
  · intro h a ha
    exact Nat.le_of_not_gt (fun hlt => (MvPolynomial.mem_support_iff.mp ha) (h a hlt))
  · intro h a hlt
    by_contra hne
    exact (Nat.not_le_of_gt hlt) (h a (MvPolynomial.mem_support_iff.mpr hne))

theorem orderAtLeast_ordinaryMultiplicity (p : σ → R) (f : MvPolynomial σ R)
    (hf : f ≠ 0) : orderAtLeast p (ordinaryMultiplicity p f hf) f :=
  (orderAtLeast_iff_le_ordinaryMultiplicity p _ f hf).mpr le_rfl

theorem not_orderAtLeast_succ_ordinaryMultiplicity (p : σ → R) (f : MvPolynomial σ R)
    (hf : f ≠ 0) : ¬ orderAtLeast p (ordinaryMultiplicity p f hf + 1) f := by
  rw [orderAtLeast_iff_le_ordinaryMultiplicity]
  exact Nat.not_succ_le_self _

/-- Any actual evaluation-compatible polynomial-ring isomorphism preserves
the finite minimum; its nonzero and coordinate hypotheses are explicit. -/
theorem ordinaryMultiplicity_equiv {τ : Type*}
    (p : σ → R) (q : τ → R)
    (e : MvPolynomial σ R ≃+* MvPolynomial τ R)
    (he : ∀ f, MvPolynomial.eval q (e f) = MvPolynomial.eval p f)
    (f : MvPolynomial σ R) (hf : f ≠ 0) (hef : e f ≠ 0) :
    ordinaryMultiplicity q (e f) hef = ordinaryMultiplicity p f hf := by
  apply Nat.le_antisymm
  · apply (orderAtLeast_iff_le_ordinaryMultiplicity p _ f hf).mp
    apply (orderAtLeast_equiv_iff p q e he _ f).mp
    exact orderAtLeast_ordinaryMultiplicity q (e f) hef
  · apply (orderAtLeast_iff_le_ordinaryMultiplicity q _ (e f) hef).mp
    apply (orderAtLeast_equiv_iff p q e he _ f).mpr
    exact orderAtLeast_ordinaryMultiplicity p f hf

/-- Actual translation preserves numerical multiplicity when its center is
moved to the origin. The coordinate isomorphism is explicitly constructed. -/
theorem ordinaryMultiplicity_translate (p : σ → R) (f : MvPolynomial σ R)
    (hf : f ≠ 0) :
    ordinaryMultiplicity (0 : σ → R) (translateHom p f) (translate_ne_zero p f hf) =
      ordinaryMultiplicity p f hf :=
  ordinaryMultiplicity_equiv p 0 (translateEquiv p) (eval_zero_translate p) f hf
    (translate_ne_zero p f hf)

theorem ordinaryMultiplicity_unit_mul (p : σ → R) (f : MvPolynomial σ R)
    (u : (MvPolynomial σ R)ˣ) (hf : f ≠ 0) (huf : (u : MvPolynomial σ R) * f ≠ 0) :
    ordinaryMultiplicity p ((u : MvPolynomial σ R) * f) huf =
      ordinaryMultiplicity p f hf := by
  apply Nat.le_antisymm
  · apply (orderAtLeast_iff_le_ordinaryMultiplicity p _ f hf).mp
    apply (orderAtLeast_unit_mul_iff p _ u f).mp
    exact orderAtLeast_ordinaryMultiplicity p _ huf
  · apply (orderAtLeast_iff_le_ordinaryMultiplicity p _ _ huf).mp
    apply (orderAtLeast_unit_mul_iff p _ u f).mpr
    exact orderAtLeast_ordinaryMultiplicity p f hf

theorem ordinaryMultiplicity_mul_lower_bound (p : σ → R) (f g : MvPolynomial σ R)
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f * g ≠ 0) :
    ordinaryMultiplicity p f hf + ordinaryMultiplicity p g hg ≤
      ordinaryMultiplicity p (f * g) hfg := by
  apply (orderAtLeast_iff_le_ordinaryMultiplicity p _ _ hfg).mp
  exact orderAtLeast_mul (orderAtLeast_ordinaryMultiplicity p f hf)
    (orderAtLeast_ordinaryMultiplicity p g hg)

theorem ordinaryMultiplicity_pow_lower_bound (p : σ → R) (f : MvPolynomial σ R)
    (N : ℕ) (hf : f ≠ 0) (hN : f ^ N ≠ 0) :
    ordinaryMultiplicity p f hf * N ≤ ordinaryMultiplicity p (f ^ N) hN := by
  apply (orderAtLeast_iff_le_ordinaryMultiplicity p _ _ hN).mp
  exact orderAtLeast_pow (orderAtLeast_ordinaryMultiplicity p f hf) N

section Field

variable {F : Type*} [Field F]

/-- Nonvanishing multipliers are units in the local ring and leave the actual
minimum unchanged, even when they are not units in the polynomial ring. -/
theorem ordinaryMultiplicity_nonvanishing_mul (p : σ → F) (f g : MvPolynomial σ F)
    (hf : f ≠ 0) (hgf : g * f ≠ 0) (hg : MvPolynomial.eval p g ≠ 0) :
    ordinaryMultiplicity p (g * f) hgf = ordinaryMultiplicity p f hf := by
  apply Nat.le_antisymm
  · apply (orderAtLeast_iff_le_ordinaryMultiplicity p _ f hf).mp
    apply (orderAtLeast_cancel_nonvanishing p _ f g hg).mp
    exact orderAtLeast_ordinaryMultiplicity p _ hgf
  · apply (orderAtLeast_iff_le_ordinaryMultiplicity p _ _ hgf).mp
    apply (orderAtLeast_cancel_nonvanishing p _ f g hg).mpr
    exact orderAtLeast_ordinaryMultiplicity p f hf

end Field

end Nagata.AffineMultiplicity

end

section

namespace Nagata.AffineMultiplicity

variable {R : Type*} [CommRing R]

theorem pointIdeal_finTwo_zero :
    pointIdeal (0 : Fin 2 → R) =
      Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) R)) := by
  ext f
  rw [pointIdeal_mem_iff, MvPolynomial.eval_zero]
  change f.coeff 0 = 0 ↔ _
  have h := Nagata.Workers.W30.mem_originIdeal_pow_iff 1 f
  simp only [pow_one] at h
  rw [h]
  constructor
  · intro hf ell b hlt
    have he : ell = 0 := by omega
    have hb : b = 0 := by omega
    subst ell
    subst b
    simpa [Nagata.Workers.W30.exponentPair] using hf
  · intro hf
    simpa [Nagata.Workers.W30.exponentPair] using hf 0 0 (by decide)

/-- Exact ordinary multiplicity criterion for a plane polynomial, including
mixed Taylor coefficients and order zero. -/
theorem orderAtLeast_finTwo_iff_taylor_coeff
    (p : Fin 2 → R) (m : ℕ) (f : MvPolynomial (Fin 2) R) :
    orderAtLeast p m f ↔ ∀ ell b : ℕ, ell + b < m →
      (translateHom p f).coeff (Nagata.Workers.W30.exponentPair ell b) = 0 := by
  have h := orderAtLeast_equiv_iff p (0 : Fin 2 → R) (translateEquiv p)
    (fun g => eval_zero_translate p g) m f
  rw [← h]
  unfold orderAtLeast
  rw [pointIdeal_finTwo_zero]
  exact Nagata.Workers.W30.mem_originIdeal_pow_iff m (translateHom p f)

end Nagata.AffineMultiplicity

end

end OAI
