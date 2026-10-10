import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import OAI.AlgebraicGeometry.PlaneCurves.Rows

namespace OAI

/-!
# Exponent evaluation matrices, row spans, and rank
-/

section

namespace Nagata.Workers.W12

variable {R I S : Type*} [CommSemiring R]

/-- Surjectivity of evaluation from a span gives spanning evaluation rows. -/
theorem span_restrictions_eq_top {X : Type*} (g : I → X → R) (point : S → X)
    (hinterp : ∀ target : S → R, ∃ f : X → R,
      f ∈ Submodule.span R (Set.range g) ∧ (fun s => f (point s)) = target) :
    Submodule.span R (Set.range (fun i s => g i (point s))) = ⊤ := by
  let ev : (X → R) →ₗ[R] (S → R) :=
    { toFun := fun f s => f (point s)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply top_unique
  intro target _
  obtain ⟨f, hf, htarget⟩ := hinterp target
  have he := Submodule.apply_mem_span_image_of_mem_span ev hf
  change ev f = target at htarget
  rw [htarget] at he
  simpa [← Set.range_comp, Function.comp_def, ev] using he

end Nagata.Workers.W12

end

section

/-!
# The linear algebra step in Proposition `prop:full-rank`

The hypotheses here assert interpolation, not any geometric conclusion.  The
rows of a rectangular matrix span all functions on its column set precisely in
the form needed to deduce injectivity of its multiplication map.
-/

namespace Nagata.Workers.W12

open Matrix

variable {R I S : Type*} [CommSemiring R] [Fintype S]

/-- A rectangular matrix whose row vectors span the column-coordinate space
has injective multiplication on column vectors.  The row set need not be finite. -/
theorem mulVec_injective_of_span_rows_top (A : Matrix I S R)
    (hspan : Submodule.span R (Set.range A) = ⊤) :
    Function.Injective A.mulVec := by
  classical
  intro v w hvw
  have hdot : ∀ x ∈ Submodule.span R (Set.range A), dotProduct x v = dotProduct x w := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact congrFun hvw i
    | zero => simp
    | add x y hx hy hx' hy' =>
        rw [add_dotProduct, add_dotProduct, hx', hy']
    | smul c x hx hx' =>
        rw [smul_dotProduct, smul_dotProduct, hx']
  funext s
  have hs : Pi.single s (1 : R) ∈ Submodule.span R (Set.range A) := by
    rw [hspan]
    exact Submodule.mem_top
  simpa using hdot (Pi.single s 1) hs

/-- Exact finite-matrix consequence of interpolation in the span of a family
of functions.  This applies to the monomial family of Section 04. -/
theorem evaluation_mulVec_injective {X : Type*} (g : I → X → R) (point : S → X)
    (hinterp : ∀ target : S → R, ∃ f : X → R,
      f ∈ Submodule.span R (Set.range g) ∧ (fun s => f (point s)) = target) :
    Function.Injective (Matrix.mulVec (fun i s => g i (point s))) :=
  mulVec_injective_of_span_rows_top _ (span_restrictions_eq_top g point hinterp)

/-- Set-indexed form, matching a polynomial space given as the span of an
explicit set of monomials. -/
theorem evaluation_mulVec_injective_of_set_interpolation {X : Type*}
    (monomials : Set (X → R)) (point : S → X)
    (hinterp : ∀ target : S → R, ∃ f : X → R,
      f ∈ Submodule.span R monomials ∧ (fun s => f (point s)) = target) :
    Function.Injective
      (Matrix.mulVec (fun (f : monomials) s => (f : X → R) (point s))) := by
  apply evaluation_mulVec_injective (fun f : monomials => (f : X → R)) point
  intro target
  obtain ⟨f, hf, heq⟩ := hinterp target
  refine ⟨f, ?_, heq⟩
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hf

end Nagata.Workers.W12

end

section

namespace Nagata.Workers.W12

open Nagata.W01

/-- A bivariate polynomial in the exact source span evaluates to a function in
that same monomial span. This is a genuine polynomial-to-function bridge. -/
theorem planeEval_mem_monomialSpace {q m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hp : p ∈ polynomialSpace q m) : planeEval p ∈ monomialSpace q m := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, l, hl, rfl⟩ := hp
    have heq : planeEval (MvPolynomial.X 0 ^ b * MvPolynomial.X 1 ^ l) =
        monomial b l := by
      funext z
      simp [planeEval, monomial]
    rw [heq]
    exact monomial_mem hb hl
  | zero =>
    have heq : planeEval (0 : MvPolynomial (Fin 2) ℂ) = 0 := by
      funext z
      simp [planeEval]
    rw [heq]
    exact Submodule.zero_mem _
  | add p p' hp hp' ih ih' =>
    have heq : planeEval (p + p') = planeEval p + planeEval p' := by
      funext z
      simp [planeEval]
    rw [heq]
    exact Submodule.add_mem _ ih ih'
  | smul c p hp ih =>
    have heq : planeEval (c • p) = c • planeEval p := by
      funext z
      simp [planeEval]
    rw [heq]
    exact Submodule.smul_mem _ c ih

end Nagata.Workers.W12

end

section

/-! The actual finite limiting matrix and its column reindexing. The matrix
entries and both finite index sets are the manuscript's literal constructions. -/

noncomputable section
namespace Nagata.Workers.W12
open Nagata.FiniteExponents Nagata.Workers.W30

/-- Literal matrix in `eq:limiting-matrix`: row `(ell,b)`, column `(j,K)`,
entry `K^ell*j^b`.  Both index types are the finite source constructions. -/
def B0 (d : ℤ) (q m : ℕ) (a delta : ℝ) :
    Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ :=
  fun row col => (col.val.2 : ℂ) ^ row.2.val * (col.val.1 : ℂ) ^ row.1.val

@[simp] theorem B0_apply (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (row : JetIndex q m) (col : Column d (m : ℤ) a delta) :
    B0 d q m a delta row col =
      (col.val.2 : ℂ) ^ (jetIndexPair row).1 *
        (col.val.1 : ℂ) ^ (jetIndexPair row).2 := rfl

/-- Under the source's positive degree and nonintegral endpoint conditions,
the actual matrix has a column. This is proved from the integer interval itself. -/
theorem B0_column_nonempty (d : ℤ) (m : ℕ) (a delta : ℝ)
    (hd : 3 * (m : ℤ) < d)
    (hU : firstLower d (m : ℤ) 0 a delta ∉ Set.range (Int.cast : ℤ → ℝ)) :
    Nonempty (Column d (m : ℤ) a delta) := by
  obtain ⟨p, hp⟩ := exponentSet_nonempty (Int.natCast_nonneg m) hd hU
  exact ⟨⟨p, hp⟩⟩

/-- Inclusion of a genuine exponent column into the coordinatewise complex image. -/
def columnToComplex (d m : ℤ) (a delta : ℝ) (col : Column d m a delta) :
    Nagata.W29.complexSet (exponentSet d m a delta) := by
  classical
  exact ⟨Nagata.W29.complexPoint col.val,
    Finset.mem_image.mpr ⟨col.val, col.property, rfl⟩⟩

/-- Standard complex inclusion gives a bijection, not a quotient losing columns. -/
theorem columnToComplex_bijective (d m : ℤ) (a delta : ℝ) :
    Function.Bijective (columnToComplex d m a delta) := by
  classical
  constructor
  · intro c c' h
    apply Subtype.ext
    apply Nagata.W29.complexPoint_injective
    exact congrArg Subtype.val h
  · intro z
    obtain ⟨p, hp, hz⟩ := Finset.mem_image.mp z.property
    exact ⟨⟨p, hp⟩, Subtype.ext hz⟩

/-- Explicit equivalence between the genuine integer columns and interpolation's
complex finite set. Its map is the ordinary ℤ²→ℂ² inclusion. -/
def columnComplexEquiv (d m : ℤ) (a delta : ℝ) :
    Column d m a delta ≃ Nagata.W29.complexSet (exponentSet d m a delta) :=
  Equiv.ofBijective (columnToComplex d m a delta)
    (columnToComplex_bijective d m a delta)

@[simp] theorem columnComplexEquiv_val (d m : ℤ) (a delta : ℝ)
    (col : Column d m a delta) :
    (columnComplexEquiv d m a delta col).val = Nagata.W29.complexPoint col.val := rfl

end Nagata.Workers.W12

end
end

section

/-! Exact finite coefficient equations for the manuscript matrix. -/

namespace Nagata.Workers.W12

open scoped BigOperators
open Nagata.FiniteExponents Nagata.Workers.W30

/-- Actual matrix multiplication is the coefficient-weighted monomial sum. -/
theorem B0_mulVec_apply (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (v : Column d (m : ℤ) a delta → ℂ) (row : JetIndex q m) :
    (B0 d q m a delta).mulVec v row =
      ∑ col : Column d (m : ℤ) a delta,
        v col * ((col.val.2 : ℂ) ^ row.2.val * (col.val.1 : ℂ) ^ row.1.val) := by
  simp only [Matrix.mulVec, dotProduct, B0]
  apply Finset.sum_congr rfl
  intro col _
  exact mul_comm _ _

/-- Vanishing of the actual matrix map is exactly the entire finite family of
coefficient equations, with no rows or degree-zero columns dropped. -/
theorem B0_mulVec_eq_zero_iff (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (v : Column d (m : ℤ) a delta → ℂ) :
    (B0 d q m a delta).mulVec v = 0 ↔
      ∀ row : JetIndex q m,
        (∑ col : Column d (m : ℤ) a delta,
          v col * ((col.val.2 : ℂ) ^ row.2.val * (col.val.1 : ℂ) ^ row.1.val)) = 0 := by
  constructor
  · intro h row
    simpa only [B0_mulVec_apply, Pi.zero_apply] using congrFun h row
  · intro h
    funext row
    simpa only [B0_mulVec_apply, Pi.zero_apply] using h row

end Nagata.Workers.W12

end

section

/-! The two ordered limiting arguments are combined at one common positive
parameter. No continuity or selection of the kernel vectors is assumed. -/

open Filter Topology
namespace Nagata.Workers.W12
open Nagata.Workers.W30 Nagata.FiniteExponents

/-- Two eventual properties near zero from the right hold simultaneously at
some positive parameter below any prescribed positive bound. -/
theorem exists_common_small_parameter (P Q : ℝ → Prop)
    (hP : ∀ᶠ τ in 𝓝[>] (0 : ℝ), P τ)
    (hQ : ∀ᶠ τ in 𝓝[>] (0 : ℝ), Q τ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ τ : ℝ, 0 < τ ∧ τ < epsilon ∧ P τ ∧ Q τ := by
  have hpos : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ := self_mem_nhdsWithin
  have hsmall : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ < epsilon :=
    mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds hepsilon)
  obtain ⟨τ, ⟨hp, hq⟩, hpos, hsmall⟩ :=
    ((hP.and hQ).and (hpos.and hsmall)).exists
  exact ⟨τ, hpos, hsmall, hp, hq⟩

/-- A genuine coefficient vector cannot be both nonzero in the kernel and
subject to injectivity at the same sufficiently small positive parameter. -/
theorem coefficient_kernel_contradiction
    (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (B : ℝ → Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ)
    (hinjective : ∀ᶠ τ in 𝓝[>] (0 : ℝ), Function.Injective (B τ).mulVec)
    (hkernel : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∃ v : Column d (m : ℤ) a delta → ℂ,
        v ≠ 0 ∧ (B τ).mulVec v = 0) : False := by
  obtain ⟨τ, _, _, hinj, v, hv, hzero⟩ :=
    exists_common_small_parameter _ _ hinjective hkernel (show (0 : ℝ) < 1 from zero_lt_one)
  exact hv (hinj (by simpa only [Matrix.mulVec_zero] using hzero))

end Nagata.Workers.W12

end

section

/-! Exact row identification and interpolation-to-rank implication for the finite
exponent matrix. Polynomial interpolation on the column set implies injectivity
of the matrix action. -/

noncomputable section
namespace Nagata.Workers.W12
open Nagata.W01 Nagata.FiniteExponents Nagata.Workers.W30

/-- The finite jet row labels enumerate exactly the monomials of `P_{q,m}`. -/
theorem jet_monomial_range (q m : ℕ) :
    Set.range (fun row : JetIndex q m => monomial row.1.val row.2.val) =
      {f | ∃ b < m, ∃ l < q * (m - b), f = monomial b l} := by
  ext f
  constructor
  · rintro ⟨⟨⟨b, hb⟩, ⟨l, hl⟩⟩, rfl⟩
    exact ⟨b, hb, l, hl, rfl⟩
  · rintro ⟨b, hb, l, hl, rfl⟩
    exact ⟨⟨⟨b, hb⟩, ⟨l, hl⟩⟩, rfl⟩

/-- Entrywise identification with evaluation rows, including the source order
`K^ell*j^b` rather than the polynomial-function convention `j^b*K^ell`. -/
theorem B0_eq_evaluationMatrix (d : ℤ) (q m : ℕ) (a delta : ℝ) :
    B0 d q m a delta =
      (fun row col => monomial row.1.val row.2.val
        (Nagata.W29.complexPoint col.val)) := by
  funext row col
  simp only [B0, monomial, Nagata.W29.complexPoint, mul_comm]

/-- Interpolation on the exponent column set implies injectivity of the matrix action. -/
theorem B0_mulVec_injective_of_interpolation (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (hinterp : ∀ v : Nagata.W29.complexSet (exponentSet d (m : ℤ) a delta) → ℂ,
      ∃ p ∈ polynomialSpace q m,
        ∀ z : Nagata.W29.complexSet (exponentSet d (m : ℤ) a delta),
          planeEval p z.val = v z) :
    Function.Injective (B0 d q m a delta).mulVec := by
  rw [B0_eq_evaluationMatrix]
  apply evaluation_mulVec_injective
    (fun row : JetIndex q m => monomial row.1.val row.2.val)
    (fun col : Column d (m : ℤ) a delta => Nagata.W29.complexPoint col.val)
  intro target
  let e := columnComplexEquiv d (m : ℤ) a delta
  obtain ⟨p, hp, hvalues⟩ := hinterp (fun z => target (e.symm z))
  refine ⟨planeEval p, ?_, ?_⟩
  · rw [jet_monomial_range]
    exact planeEval_mem_monomialSpace hp
  · funext col
    have h := hvalues (e col)
    simpa only [e, columnComplexEquiv_val, Equiv.symm_apply_apply] using h

end Nagata.Workers.W12

end
end

section

/-!
# Full column rank of the manuscript's finite exponent matrix
-/

noncomputable section

namespace Nagata.Workers.W12

open Nagata.W01 Nagata.FiniteExponents Nagata.Workers.W30

/-- Full column rank of the actual finite exponent matrix, assuming only the
numeric parameter hypotheses used in the manuscript's polygon and integer count.
There is no interpolation, rank, span, geometric, or arbitrary-set hypothesis. -/
theorem B0_mulVec_injective (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m) :
    Function.Injective (B0 d q m a delta).mulVec := by
  apply B0_mulVec_injective_of_interpolation
  exact Nagata.W29.finite_exponent_interpolation
    d q m rho a delta lam ha hm hrho hdelta hlam hlam1 hratio hslack hcoef hmargin

end Nagata.Workers.W12

end
end

end OAI
