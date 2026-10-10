import OAI.AlgebraicGeometry.PlaneCurves.Forms
import OAI.AlgebraicGeometry.PlaneCurves.RationalKernels

namespace OAI

/-!
# Associated line bundles of multiplier actions
-/

section

/-!
# Actual associated bundles over a homogeneous plane curve

For a homogeneous equation `G`, the weight-`k` bundle is the quotient of
pairs `(x,w)` with `x ≠ 0` and `G(x)=0` by
`(x,w) ~ (λx, λ^k w)`, `λ ∈ ℂˣ`. Its base is the actual projectivization.
The quotient and its chart maps contain no section-existence, dimension,
normal-bundle, or degeneration assumptions.
-/

noncomputable section

namespace Nagata.W16.AssociatedBundle

open Nagata.ProjectiveGeometry

variable {n : ℕ} (G : NonzeroHomogeneousForm n)

/-- Actual points on the projective zero locus of `G`. -/
abbrev CurvePoint := {p : PlanePoint // MvPolynomial.eval p.rep G.polynomial = 0}

/-- Representatives of the weight-`k` associated bundle. -/
structure BundleVector (k : ℕ) where
  x : Fin 3 → ℂ
  x_ne_zero : x ≠ 0
  on_curve : MvPolynomial.eval x G.polynomial = 0
  w : ℂ

variable {G}

/-- The orbit relation for `(x,w) ↦ (λx,λ^k w)`. -/
def Equivalent {k : ℕ} (a b : BundleVector G k) : Prop :=
  ∃ u : ℂˣ, a.x = (u : ℂ) • b.x ∧ a.w = (u : ℂ) ^ k * b.w

theorem equivalent_refl {k : ℕ} (a : BundleVector G k) : Equivalent a a := by
  exact ⟨1, by simp, by simp⟩

theorem equivalent_symm {k : ℕ} {a b : BundleVector G k}
    (h : Equivalent a b) : Equivalent b a := by
  obtain ⟨u, hx, hw⟩ := h
  refine ⟨u⁻¹, ?_, ?_⟩
  · rw [hx, smul_smul]
    simp
  · rw [hw, ← mul_assoc, ← mul_pow]
    simp

theorem equivalent_trans {k : ℕ} {a b c : BundleVector G k}
    (hab : Equivalent a b) (hbc : Equivalent b c) : Equivalent a c := by
  obtain ⟨u, hux, huw⟩ := hab
  obtain ⟨v, hvx, hvw⟩ := hbc
  refine ⟨u * v, ?_, ?_⟩
  · rw [hux, hvx, smul_smul]
    rfl
  · rw [huw, hvw]
    simp [mul_pow, mul_assoc]

def bundleSetoid (G : NonzeroHomogeneousForm n) (k : ℕ) : Setoid (BundleVector G k) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- The genuine quotient total space of the associated bundle. -/
def TotalSpace (G : NonzeroHomogeneousForm n) (k : ℕ) := Quotient (bundleSetoid G k)

def mk {k : ℕ} (a : BundleVector G k) : TotalSpace G k := Quotient.mk _ a

theorem mk_eq_mk_iff {k : ℕ} (a b : BundleVector G k) : mk a = mk b ↔ Equivalent a b :=
  Quotient.eq

def base {k : ℕ} : TotalSpace G k → PlanePoint :=
  Quotient.lift (fun a => Projectivization.mk ℂ a.x a.x_ne_zero) (by
    intro a b h
    obtain ⟨u, hx, _⟩ := h
    exact (Projectivization.mk_eq_mk_iff ℂ a.x b.x a.x_ne_zero b.x_ne_zero).mpr
      ⟨u, by simpa [Units.smul_def] using hx.symm⟩)

@[simp] theorem base_mk {k : ℕ} (a : BundleVector G k) :
    base (mk a) = Projectivization.mk ℂ a.x a.x_ne_zero := rfl

/-- The quotient base actually lies on the homogeneous curve. -/
theorem base_on_curve {k : ℕ} (t : TotalSpace G k) :
    MvPolynomial.eval (base t).rep G.polynomial = 0 := by
  refine Quotient.inductionOn t ?_
  intro a
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ a.x a.x_ne_zero
  change MvPolynomial.eval (Projectivization.mk ℂ a.x a.x_ne_zero).rep G.polynomial = 0
  rw [← hu]
  change MvPolynomial.eval (fun i => (u : ℂ) * a.x i) G.polynomial = 0
  rw [homogeneous_eval_scale G.homogeneous, a.on_curve, mul_zero]

def curveBase {k : ℕ} (t : TotalSpace G k) : CurvePoint G := ⟨base t, base_on_curve t⟩

theorem equivalent_fiberCoordinate {k : ℕ} {a b : BundleVector G k}
    (h : Equivalent a b) (c : Fin 3) : a.w / (a.x c) ^ k = b.w / (b.x c) ^ k := by
  obtain ⟨u, hx, hw⟩ := h
  rw [hw, hx]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero k u.ne_zero)

/-- Fiber coordinate `w/x_c^k`; used as a trivialization on the chart `x_c ≠ 0`.
The quotient function itself is defined everywhere. -/
def fiberCoordinate {k : ℕ} (c : Fin 3) : TotalSpace G k → ℂ :=
  Quotient.lift (fun a => a.w / (a.x c) ^ k)
    (fun _ _ h => equivalent_fiberCoordinate h c)

@[simp] theorem fiberCoordinate_mk {k : ℕ} (c : Fin 3) (a : BundleVector G k) :
    fiberCoordinate c (mk a) = a.w / (a.x c) ^ k := rfl

theorem base_mk_chart_iff {k : ℕ} (a : BundleVector G k) (c : Fin 3) :
    (base (mk a)).rep c ≠ 0 ↔ a.x c ≠ 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ a.x a.x_ne_zero
  rw [base_mk, ← hu]
  simp [Pi.smul_apply, Units.smul_def, smul_eq_mul, u.ne_zero]

def vectorOfBase {k : ℕ} (p : CurvePoint G) (w : ℂ) : BundleVector G k where
  x := p.val.rep
  x_ne_zero := p.val.rep_nonzero
  on_curve := p.property
  w := w

@[simp] theorem base_vectorOfBase {k : ℕ} (p : CurvePoint G) (w : ℂ) :
    base (mk (vectorOfBase (k := k) p w)) = p.val :=
  Projectivization.mk_rep p.val

@[simp] theorem fiberCoordinate_vectorOfBase {k : ℕ} (c : Fin 3)
    (p : CurvePoint G) (w : ℂ) :
    fiberCoordinate c (mk (vectorOfBase (k := k) p w)) = w / (p.val.rep c) ^ k := rfl

/-- Coordinates on the curve's actual projective affine chart. -/
abbrev CurveChart (G : NonzeroHomogeneousForm n) (c : Fin 3) :=
  {p : CurvePoint G // p.val.rep c ≠ 0}

/-- The part of the associated total space above that affine chart. -/
abbrev BundleChart (G : NonzeroHomogeneousForm n) (k : ℕ) (c : Fin 3) :=
  {t : TotalSpace G k // (base t).rep c ≠ 0}

/-- Reconstruct from a projective base point and a normalized chart fiber. -/
def reconstruct {k : ℕ} (c : Fin 3) (p : CurvePoint G) (z : ℂ) : TotalSpace G k :=
  mk (vectorOfBase p (z * (p.val.rep c) ^ k))

@[simp] theorem base_reconstruct {k : ℕ} (c : Fin 3) (p : CurvePoint G) (z : ℂ) :
    base (reconstruct (k := k) c p z) = p.val :=
  base_vectorOfBase p _

theorem fiberCoordinate_reconstruct {k : ℕ} (c : Fin 3) (p : CurvePoint G)
    (hc : p.val.rep c ≠ 0) (z : ℂ) :
    fiberCoordinate c (reconstruct (k := k) c p z) = z := by
  change (z * (p.val.rep c) ^ k) / (p.val.rep c) ^ k = z
  exact mul_div_cancel_right₀ z (pow_ne_zero k hc)

theorem reconstruct_fiberCoordinate {k : ℕ} (t : TotalSpace G k) (c : Fin 3)
    (hc : (base t).rep c ≠ 0) :
    reconstruct c (curveBase t) (fiberCoordinate c t) = t := by
  revert hc
  refine Quotient.inductionOn t ?_
  intro a hc
  apply (mk_eq_mk_iff _ a).mpr
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ a.x a.x_ne_zero
  refine ⟨u, ?_, ?_⟩
  · change (Projectivization.mk ℂ a.x a.x_ne_zero).rep = (u : ℂ) • a.x
    simpa [Units.smul_def] using hu.symm
  · change (a.w / (a.x c) ^ k) * ((Projectivization.mk ℂ a.x a.x_ne_zero).rep c) ^ k =
      (u : ℂ) ^ k * a.w
    rw [← hu]
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, mul_pow]
    calc
      a.w / (a.x c) ^ k * ((u : ℂ) ^ k * (a.x c) ^ k) =
          (u : ℂ) ^ k * (a.w / (a.x c) ^ k * (a.x c) ^ k) := by ac_rfl
      _ = (u : ℂ) ^ k * a.w := by
        rw [div_mul_cancel₀ _ (pow_ne_zero k ((base_mk_chart_iff a c).mp hc))]

/-- Each actual projective affine chart trivializes the quotient fiber. -/
def chartTrivialization (G : NonzeroHomogeneousForm n) (k : ℕ) (c : Fin 3) :
    BundleChart G k c ≃ CurveChart G c × ℂ where
  toFun t := (⟨curveBase t.val, t.property⟩, fiberCoordinate c t.val)
  invFun pz :=
    ⟨reconstruct c pz.1.val pz.2, by simpa using pz.1.property⟩
  left_inv t := by
    apply Subtype.ext
    exact reconstruct_fiberCoordinate t.val c t.property
  right_inv pz := by
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact base_reconstruct c pz.1.val pz.2
    · exact fiberCoordinate_reconstruct c pz.1.val pz.1.property pz.2

/-- The transition factor between two containing chart fiber coordinates. -/
theorem fiberCoordinate_overlap {k : ℕ} (t : TotalSpace G k) (b c : Fin 3)
    (hb : (base t).rep b ≠ 0) (hc : (base t).rep c ≠ 0) :
    fiberCoordinate c t = ((base t).rep b / (base t).rep c) ^ k * fiberCoordinate b t := by
  have h := congrArg (fiberCoordinate c) (reconstruct_fiberCoordinate t b hb)
  rw [← h]
  change (fiberCoordinate b t * (base t).rep b ^ k) / (base t).rep c ^ k = _
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero k hc)).mpr
  rw [mul_right_comm, div_mul_cancel₀ _ (pow_ne_zero k hc), mul_comm]

open scoped BigOperators

/-- The actual finite polynomial evaluated on homogeneous base and fiber coordinates. -/
def weightedEval (s : Finset ℕ) (T : ℕ → PlanePolynomial) (j : ℕ → ℕ)
    (x : Fin 3 → ℂ) (w : ℂ) : ℂ :=
  ∑ a ∈ s, MvPolynomial.eval x (T a) * w ^ j a

theorem weightedEval_scale (s : Finset ℕ) (T : ℕ → PlanePolynomial) (j : ℕ → ℕ)
    (d k : ℕ) (hdeg : ∀ a ∈ s, (T a).IsHomogeneous (d - k * j a))
    (hkj : ∀ a ∈ s, k * j a ≤ d) (x : Fin 3 → ℂ) (w u : ℂ) :
    weightedEval s T j (u • x) (u ^ k * w) = u ^ d * weightedEval s T j x w := by
  unfold weightedEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  change MvPolynomial.eval (fun i => u * x i) (T a) * (u ^ k * w) ^ j a = _
  rw [homogeneous_eval_scale (hdeg a ha), mul_pow, ← pow_mul]
  calc
    (u ^ (d - k * j a) * MvPolynomial.eval x (T a)) *
        (u ^ (k * j a) * w ^ j a) =
      (u ^ (d - k * j a) * u ^ (k * j a)) *
        (MvPolynomial.eval x (T a) * w ^ j a) := by ac_rfl
    _ = u ^ d * (MvPolynomial.eval x (T a) * w ^ j a) := by
      rw [← pow_add, Nat.sub_add_cancel (hkj a ha)]

def polynomialVector {k : ℕ} (s : Finset ℕ) (T : ℕ → PlanePolynomial)
    (j : ℕ → ℕ) (d : ℕ) (a : BundleVector G k) : BundleVector G d where
  x := a.x
  x_ne_zero := a.x_ne_zero
  on_curve := a.on_curve
  w := weightedEval s T j a.x a.w

/-- Evaluation of a weighted polynomial gives an actual map from the
weight-`k` total space to the weight-`d` total space over the same curve. -/
def polynomialMap {k : ℕ} (s : Finset ℕ) (T : ℕ → PlanePolynomial)
    (j : ℕ → ℕ) (d : ℕ)
    (hdeg : ∀ a ∈ s, (T a).IsHomogeneous (d - k * j a))
    (hkj : ∀ a ∈ s, k * j a ≤ d) : TotalSpace G k → TotalSpace G d :=
  Quotient.lift (fun a => mk (polynomialVector s T j d a)) (by
    intro a b hab
    apply (mk_eq_mk_iff _ _).mpr
    obtain ⟨u, hx, hw⟩ := hab
    refine ⟨u, hx, ?_⟩
    change weightedEval s T j a.x a.w = (u : ℂ) ^ d * weightedEval s T j b.x b.w
    rw [hx, hw]
    exact weightedEval_scale s T j d k hdeg hkj b.x b.w (u : ℂ))

@[simp] theorem polynomialMap_mk {k : ℕ} (s : Finset ℕ) (T : ℕ → PlanePolynomial)
    (j : ℕ → ℕ) (d : ℕ)
    (hdeg : ∀ a ∈ s, (T a).IsHomogeneous (d - k * j a))
    (hkj : ∀ a ∈ s, k * j a ≤ d) (a : BundleVector G k) :
    polynomialMap s T j d hdeg hkj (mk a) = mk (polynomialVector s T j d a) := rfl

theorem polynomialMap_base {k : ℕ} (s : Finset ℕ) (T : ℕ → PlanePolynomial)
    (j : ℕ → ℕ) (d : ℕ)
    (hdeg : ∀ a ∈ s, (T a).IsHomogeneous (d - k * j a))
    (hkj : ∀ a ∈ s, k * j a ≤ d) (t : TotalSpace G k) :
    base (polynomialMap s T j d hdeg hkj t) = base t := by
  refine Quotient.inductionOn t ?_
  intro a
  rfl

/-- A homogeneous polynomial gives a section of the corresponding actual
associated bundle; its local expression is computed from representatives. -/
def homogeneousSection {e : ℕ} (T : PlanePolynomial) (_hT : T.IsHomogeneous e)
    (p : CurvePoint G) : TotalSpace G e :=
  mk (vectorOfBase p (MvPolynomial.eval p.val.rep T))

@[simp] theorem homogeneousSection_base {e : ℕ} (T : PlanePolynomial)
    (hT : T.IsHomogeneous e) (p : CurvePoint G) :
    base (homogeneousSection T hT p) = p.val := base_vectorOfBase p _

theorem homogeneousSection_representative {e k : ℕ} (T : PlanePolynomial)
    (hT : T.IsHomogeneous e) (a : BundleVector G k) :
    homogeneousSection T hT (curveBase (mk a)) =
      mk (BundleVector.mk a.x a.x_ne_zero a.on_curve (MvPolynomial.eval a.x T)) := by
  apply (mk_eq_mk_iff _ _).mpr
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ a.x a.x_ne_zero
  refine ⟨u, ?_, ?_⟩
  · change (Projectivization.mk ℂ a.x a.x_ne_zero).rep = (u : ℂ) • a.x
    simpa [Units.smul_def] using hu.symm
  · change MvPolynomial.eval (Projectivization.mk ℂ a.x a.x_ne_zero).rep T =
      (u : ℂ) ^ e * MvPolynomial.eval a.x T
    rw [← hu]
    exact homogeneous_eval_scale hT a.x (u : ℂ)

/-- The zero fiber is independent of the representative. -/
def IsZeroFiber {k : ℕ} : TotalSpace G k → Prop :=
  Quotient.lift (fun a => a.w = 0) (by
    intro a b h
    apply propext
    obtain ⟨u, _, hw⟩ := h
    rw [hw]
    simp [u.ne_zero])

@[simp] theorem isZeroFiber_mk {k : ℕ} (a : BundleVector G k) :
    IsZeroFiber (mk a) ↔ a.w = 0 := Iff.rfl

/-- Distinct powers cannot cancel a coefficient known to be nonzero at an
actual curve vector. The resulting nonzero value lies in the genuine bundle. -/
theorem polynomialMap_not_identically_zero {k : ℕ} (s : Finset ℕ)
    (T : ℕ → PlanePolynomial) (j : ℕ → ℕ) (d : ℕ)
    (hdeg : ∀ a ∈ s, (T a).IsHomogeneous (d - k * j a))
    (hkj : ∀ a ∈ s, k * j a ≤ d)
    (hinj : Set.InjOn j (↑s : Set ℕ))
    (x : Fin 3 → ℂ) (hx : x ≠ 0) (hGx : MvPolynomial.eval x G.polynomial = 0)
    (hcoeff : ∃ a ∈ s, MvPolynomial.eval x (T a) ≠ 0) :
    ∃ t : TotalSpace G k, ¬ IsZeroFiber (polynomialMap s T j d hdeg hkj t) := by
  classical
  let P : Polynomial ℂ := ∑ a ∈ s, Polynomial.monomial (j a) (MvPolynomial.eval x (T a))
  have hP : P ≠ 0 := Nagata.W18.injective_monomial_sum_ne_zero s j
    (fun a => MvPolynomial.eval x (T a)) hinj hcoeff
  obtain ⟨w, hw⟩ : ∃ w : ℂ, P.eval w ≠ 0 := by
    by_contra h
    apply hP
    apply Polynomial.funext
    intro w
    rw [Polynomial.eval_zero]
    by_contra hw
    exact h ⟨w, hw⟩
  refine ⟨mk (BundleVector.mk x hx hGx w), ?_⟩
  change weightedEval s T j x w ≠ 0
  simpa [P, weightedEval, Polynomial.eval_finsetSum] using hw

end Nagata.W16.AssociatedBundle

end
end

end OAI
