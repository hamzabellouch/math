import OAI.AlgebraicGeometry.PlaneCurves.LineBases

namespace OAI

/-!
# Polynomial motion of tuples, exceptional parameters, and gradients
-/

section

/-! One finite exceptional parameter set for a finite family of polynomial
nonvanishing conditions. The exceptional set explicitly excludes parameter zero
when every condition is nonzero there. -/
noncomputable section
namespace Nagata.Workers.W14

/-- Finitely many polynomial conditions, valid at zero, remain valid outside
one finite union of their actual root sets. -/
theorem finite_polynomial_exceptions {K ι : Type*} [Field K] [Fintype ι]
    (P : ι → Polynomial K) (hP : ∀ i, (P i).eval 0 ≠ 0) :
    ∃ E : Finset K, 0 ∉ E ∧ ∀ s ∉ E, ∀ i, (P i).eval s ≠ 0 := by
  classical
  have hne : ∀ i, P i ≠ 0 := by
    intro i hi
    exact hP i (by simp [hi])
  let E : Finset K := Finset.univ.biUnion (fun i => (P i).roots.toFinset)
  have hmem : ∀ s, s ∈ E ↔ ∃ i, (P i).eval s = 0 := by
    intro s
    constructor
    · intro hs
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hs
      exact ⟨i, (Polynomial.mem_roots (hne i)).mp (Multiset.mem_toFinset.mp hi)⟩
    · rintro ⟨i, hi⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hne i)).mpr hi)⟩
  refine ⟨E, ?_, ?_⟩
  · intro hz
    obtain ⟨i, hi⟩ := (hmem 0).1 hz
    exact hP i hi
  · intro s hs i hi
    exact hs ((hmem s).2 ⟨i, hi⟩)

/-- Arbitrary further finite exclusions can be included without losing
existence of a good parameter over an infinite field. -/
theorem exists_parameter_for_finite_polynomials {K ι : Type*}
    [Field K] [Infinite K] [Fintype ι]
    (P : ι → Polynomial K) (hP : ∀ i, (P i).eval 0 ≠ 0) (F : Finset K) :
    ∃ s : K, s ∉ F ∧ ∀ i, (P i).eval s ≠ 0 := by
  classical
  obtain ⟨E, _, hE⟩ := finite_polynomial_exceptions P hP
  obtain ⟨s, hs⟩ := (E ∪ F).finite_toSet.exists_notMem
  have hsE : s ∉ E := fun he => hs (Finset.mem_union_left F he)
  have hsF : s ∉ F := fun hf => hs (Finset.mem_union_right E hf)
  exact ⟨s, hsF, hE s hsE⟩

end Nagata.Workers.W14

end
end

section

/-! Polynomial-coordinate nonvanishing and minor separation outside one finite
parameter set. The projective interpretation is proved separately. -/
noncomputable section
namespace Nagata.Workers.W14

/-- Evaluate a polynomial homogeneous-coordinate motion at a parameter. -/
def evaluateMotion {K : Type*} [Field K] {r n : ℕ}
    (P : Fin r → Fin n → Polynomial K) (s : K) (i : Fin r) : Fin n → K :=
  fun c => (P i c).eval s

/-- A tuple of polynomial vectors with nonzero coordinates and pair-separating
minors at zero preserves both properties off one finite root set. -/
theorem polynomial_motion_separated_cofinite {K : Type*} [Field K] {r n : ℕ}
    (P : Fin r → Fin n → Polynomial K)
    (hzero : ∀ i, evaluateMotion P 0 i ≠ 0)
    (hsep : ∀ i j, i ≠ j → ∃ a b,
      evaluateMotion P 0 i a * evaluateMotion P 0 j b -
        evaluateMotion P 0 i b * evaluateMotion P 0 j a ≠ 0) :
    ∃ E : Finset K, 0 ∉ E ∧
      (∀ s ∉ E, ∀ i, evaluateMotion P s i ≠ 0) ∧
      ∀ s ∉ E, ∀ i j, i ≠ j → ∃ a b,
        evaluateMotion P s i a * evaluateMotion P s j b -
          evaluateMotion P s i b * evaluateMotion P s j a ≠ 0 := by
  classical
  have hcoord : ∀ i, ∃ c, evaluateMotion P 0 i c ≠ 0 := by
    intro i
    by_contra hn
    apply hzero i
    funext c
    exact Classical.not_not.mp (fun hc => hn ⟨c, hc⟩)
  choose c hc using hcoord
  let Pairs := {z : Fin r × Fin r // z.1 ≠ z.2}
  have hpairs : ∀ z : Pairs, ∃ a b,
      evaluateMotion P 0 z.val.1 a * evaluateMotion P 0 z.val.2 b -
        evaluateMotion P 0 z.val.1 b * evaluateMotion P 0 z.val.2 a ≠ 0 :=
    fun z => hsep z.val.1 z.val.2 z.property
  choose a b hab using hpairs
  let tests : Fin r ⊕ Pairs → Polynomial K := Sum.elim
    (fun i => P i (c i))
    (fun z => P z.val.1 (a z) * P z.val.2 (b z) -
      P z.val.1 (b z) * P z.val.2 (a z))
  have htests : ∀ z, (tests z).eval 0 ≠ 0 := by
    intro z
    cases z with
    | inl i => exact hc i
    | inr z => simpa [tests, evaluateMotion] using hab z
  obtain ⟨E, hE0, hE⟩ := finite_polynomial_exceptions tests htests
  refine ⟨E, hE0, ?_, ?_⟩
  · intro s hs i hz
    apply hE s hs (Sum.inl i)
    exact congrFun hz (c i)
  · intro s hs i j hne
    let z : Pairs := ⟨(i, j), hne⟩
    refine ⟨a z, b z, ?_⟩
    simpa [tests, evaluateMotion, z] using hE s hs (Sum.inr z)

end Nagata.Workers.W14

end
end

section

/-!
# Cofinite validity of actual moving projective configurations

For the affine-linear motions in manuscript §1, Proposition
`prop:normal-polynomial`, distinctness at parameter zero supplies nonzero
coordinate and minor polynomials. Their roots form one finite exception set.
All projective points below are Mathlib's actual projectivization quotient.
-/
noncomputable section
namespace Nagata.Workers.W14

/-- Polynomial representative motions whose classes are distinct at zero
remain nonzero and pairwise projectively distinct outside one finite set.
The same finite set controls every representative and every pair simultaneously. -/
theorem polynomial_projective_motion_cofinite {K : Type*} [Field K] {r n : ℕ}
    (P : Fin r → Fin n → Polynomial K)
    (hzero : ∀ i, evaluateMotion P 0 i ≠ 0)
    (hinj : Function.Injective
      (fun i => Projectivization.mk K (evaluateMotion P 0 i) (hzero i))) :
    ∃ E : Finset K, 0 ∉ E ∧
      ∃ hvalid : ∀ s ∉ E, ∀ i, evaluateMotion P s i ≠ 0,
        ∀ s (hs : s ∉ E), Function.Injective
          (fun i => Projectivization.mk K (evaluateMotion P s i) (hvalid s hs i)) := by
  have hsep : ∀ i j, i ≠ j → ∃ a b,
      evaluateMotion P 0 i a * evaluateMotion P 0 j b -
        evaluateMotion P 0 i b * evaluateMotion P 0 j a ≠ 0 := by
    intro i j hne
    exact exists_minor_ne_zero_of_projective_ne _ _ (hzero i) (hzero j)
      (fun he => hne (hinj he))
  obtain ⟨E, hE0, hvalid, hseparated⟩ :=
    polynomial_motion_separated_cofinite P hzero hsep
  refine ⟨E, hE0, hvalid, ?_⟩
  intro s hs i j hij
  by_contra hne
  obtain ⟨a, b, hm⟩ := hseparated s hs i j hne
  exact projective_ne_of_minor_ne_zero (evaluateMotion P s i)
    (evaluateMotion P s j) (hvalid s hs i) (hvalid s hs j) a b hm hij

/-- The affine-linear homogeneous-coordinate motion `a + s V`. -/
def linearMotion {K : Type*} [Field K] {r n : ℕ}
    (a V : Fin r → Fin n → K) : Fin r → Fin n → Polynomial K :=
  fun i c => Polynomial.C (a i c) + Polynomial.X * Polynomial.C (V i c)

@[simp] theorem evaluate_linearMotion {K : Type*} [Field K] {r n : ℕ}
    (a V : Fin r → Fin n → K) (s : K) (i : Fin r) :
    evaluateMotion (linearMotion a V) s i = a i + s • V i := by
  funext c
  simp only [evaluateMotion, linearMotion, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The manuscript's actual affine-linear motions satisfy the cofinite tuple
condition, for arbitrary velocity vectors. -/
theorem linear_projective_motion_cofinite {r : ℕ}
    (a V : Fin r → Fin 3 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hinj : Function.Injective (fun i => Projectivization.mk ℂ (a i) (ha i))) :
    ∃ E : Finset ℂ, 0 ∉ E ∧
      ∃ hvalid : ∀ s ∉ E, ∀ i, a i + s • V i ≠ 0,
        ∀ s (hs : s ∉ E), Function.Injective
          (fun i => Projectivization.mk ℂ (a i + s • V i) (hvalid s hs i)) := by
  have hzero : ∀ i, evaluateMotion (linearMotion a V) 0 i ≠ 0 := by
    simpa using ha
  have hi : Function.Injective
      (fun i => Projectivization.mk ℂ (evaluateMotion (linearMotion a V) 0 i) (hzero i)) := by
    simpa using hinj
  simpa using polynomial_projective_motion_cofinite (linearMotion a V) hzero hi

/-- Starting directly from an actual distinct projective tuple, Mathlib's
nonzero representatives give affine-linear homogeneous-coordinate motions with
one finite exceptional parameter set. -/
theorem projective_tuple_linear_motion_cofinite {r : ℕ}
    (p : Fin r → Projectivization ℂ (Fin 3 → ℂ)) (hp : Function.Injective p)
    (V : Fin r → Fin 3 → ℂ) :
    ∃ E : Finset ℂ, 0 ∉ E ∧
      ∃ hvalid : ∀ s ∉ E, ∀ i, (p i).rep + s • V i ≠ 0,
        ∀ s (hs : s ∉ E), Function.Injective
          (fun i => Projectivization.mk ℂ ((p i).rep + s • V i) (hvalid s hs i)) := by
  apply linear_projective_motion_cofinite (fun i => (p i).rep) V
    (fun i => (p i).rep_nonzero)
  simpa only [Projectivization.mk_rep] using hp

end Nagata.Workers.W14

end
end

section

/-! The polynomial chain rule under actual polynomial coordinate substitution. -/
noncomputable section
namespace Nagata.Workers.W14
open scoped BigOperators

 theorem pderiv_polynomial_substitution {K : Type*} [Field K]
    (f : Fin 3 → MvPolynomial (Fin 2) K) (Q : MvPolynomial (Fin 3) K) (j : Fin 2) :
    MvPolynomial.pderiv j (MvPolynomial.eval₂ MvPolynomial.C f Q) =
      ∑ i : Fin 3, MvPolynomial.eval₂ MvPolynomial.C f (MvPolynomial.pderiv i Q) *
        MvPolynomial.pderiv j (f i) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
    simp only [MvPolynomial.eval₂_add, map_add, hP,hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P k hP =>
    fin_cases k <;> simp_all [Pi.single_apply,
      Fin.sum_univ_succ] <;> ring

 theorem eval_pderiv_substitution_eq_zero_of_singular {K : Type*} [Field K]
    (f : Fin 3 → MvPolynomial (Fin 2) K) (Q : MvPolynomial (Fin 3) K)
    (v : Fin 2 → K) (j : Fin 2)
    (hsing : ∀ i, MvPolynomial.eval (fun k => MvPolynomial.eval v (f k))
      (MvPolynomial.pderiv i Q) = 0) :
    MvPolynomial.eval v (MvPolynomial.pderiv j
      (MvPolynomial.eval₂ MvPolynomial.C f Q)) = 0 := by
  rw [pderiv_polynomial_substitution,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul]
  have hi : MvPolynomial.eval v (MvPolynomial.eval₂ MvPolynomial.C f
      (MvPolynomial.pderiv i Q)) = 0 := by
    change MvPolynomial.eval v ((MvPolynomial.eval₂Hom MvPolynomial.C f) _) = 0
    rw [MvPolynomial.map_eval₂Hom]
    have hC : (MvPolynomial.eval v).comp MvPolynomial.C = RingHom.id K := by
      ext c
      simp
    rw [hC]
    exact hsing i
  rw [hi,zero_mul]

end Nagata.Workers.W14

end
end

section

/-! Polynomial motions in genuine projective charts and compatibility of
ordinary projective-chart multiplicity with the finite matrix's chart equations. -/
noncomputable section
namespace Nagata.Workers.W14
open Nagata.ProjectiveGeometry

/-- Polynomial homogeneous representatives with fixed distinguished coordinate
one in a separately chosen affine chart at every marked point. -/
def chartPolynomialRepresentatives {r : ℕ} (c : Fin r → Fin 3)
    (p : Fin r × Fin 2 → Polynomial ℂ) : Fin r → Fin 3 → Polynomial ℂ :=
  fun i => (c i).insertNth 1 (fun j => p (i, j))

/-- Parameter evaluation commutes with the genuine chart embedding. -/
theorem evaluate_chartPolynomialRepresentatives {r : ℕ} (c : Fin r → Fin 3)
    (p : Fin r × Fin 2 → Polynomial ℂ) (s : ℂ) (i : Fin r) :
    evaluateMotion (chartPolynomialRepresentatives c p) s i =
      chartVector₂ (c i) (fun j => (p (i, j)).eval s) := by
  funext j
  by_cases hj : j = c i
  · subst j
    simp [evaluateMotion, chartPolynomialRepresentatives, chartVector₂]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [evaluateMotion, chartPolynomialRepresentatives, chartVector₂]

/-- Validity of distinct polynomial affine-chart configurations outside one
finite exceptional parameter set, with no restriction on the polynomial degrees. -/
theorem chart_polynomial_motion_cofinite {r : ℕ} (c : Fin r → Fin 3)
    (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval 0))) :
    ∃ E : Finset ℂ, 0 ∉ E ∧ ∀ s ∉ E, Function.Injective
      (configurationChartEmbedding c (fun ij => (p ij).eval s)) := by
  let P := chartPolynomialRepresentatives c p
  have hzero : ∀ i, evaluateMotion P 0 i ≠ 0 := by
    intro i
    rw [evaluate_chartPolynomialRepresentatives]
    exact chartVector₂_ne_zero _ _
  have hinj : Function.Injective
      (fun i => Projectivization.mk ℂ (evaluateMotion P 0 i) (hzero i)) := by
    unfold configurationChartEmbedding chartPoint₂ at hbase
    simpa only [P, evaluate_chartPolynomialRepresentatives] using hbase
  obtain ⟨E, hE0, hvalid, hdistinct⟩ := polynomial_projective_motion_cofinite P hzero hinj
  refine ⟨E, hE0, ?_⟩
  intro s hs
  unfold configurationChartEmbedding chartPoint₂
  simpa only [P, evaluate_chartPolynomialRepresentatives] using hdistinct s hs

/-- A projective multiplicity lower bound gives exactly the direct chart order
used by the global homogeneous coefficient matrix, at a normalized chart point. -/
theorem order_directChart_of_multiplicity {F : MvPolynomial (Fin 3) ℂ}
    (c : Fin 3) (z : Fin 2 → ℂ) (m : ℕ)
    (h : multiplicityAtLeast F (chartPoint₂ c z) m) :
    Nagata.AffineMultiplicity.orderAtLeast z m (Nagata.W27.directChartHom c F) := by
  have hchart := h c (chartPoint₂_coordinate_ne_zero c z)
  have htwo := (orderAtLeast_chartDehomogenize₂_iff c (chartPoint₂ c z) F m).2 hchart
  rw [chartCoordinates₂_chartPoint₂, chartDehomogenize₂_eq_eval₂_insertNth] at htwo
  exact htwo

end Nagata.Workers.W14

end
end

section

/-! Actual gradients transported into a line restriction by the proved
polynomial coordinate automorphism. -/
noncomputable section
namespace Nagata.Workers.W14
open Module
open scoped BigOperators

 theorem coordinateLineRestriction_basisChange (b : Basis (Fin 3) ℂ (Fin 3 → ℂ))
    (Q : MvPolynomial (Fin 3) ℂ) :
    coordinateLineRestriction (Nagata.W01.basisPolynomialChange b Q) =
      MvPolynomial.eval₂ MvPolynomial.C
        (fun i => MvPolynomial.C (b 0 i) * MvPolynomial.X 0 +
          MvPolynomial.C (b 1 i) * MvPolynomial.X 1) Q := by
  have h : coordinateLineRestriction.comp (Nagata.W01.basisPolynomialChange b).toRingHom =
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i => MvPolynomial.C (b 0 i) * MvPolynomial.X 0 +
          MvPolynomial.C (b 1 i) * MvPolynomial.X 1) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coordinateLineRestriction, Nagata.W01.basisPolynomialChange_eq_eval₂]
    · intro i
      simp [Nagata.W01.basisPolynomialChange_X, coordinateLineRestriction,
        Fin.sum_univ_succ]
  exact RingHom.congr_fun h Q

 theorem basis_line_partial_zero_of_singular (b : Basis (Fin 3) ℂ (Fin 3 → ℂ))
    (Q : MvPolynomial (Fin 3) ℂ)
    (hsing : ∀ i, MvPolynomial.eval (b 0) (MvPolynomial.pderiv i Q) = 0) :
    MvPolynomial.eval ![1,0] (MvPolynomial.pderiv 1
      (coordinateLineRestriction (Nagata.W01.basisPolynomialChange b Q))) = 0 := by
  rw [coordinateLineRestriction_basisChange]
  apply eval_pderiv_substitution_eq_zero_of_singular
  intro i
  simpa using hsing i

end Nagata.Workers.W14

end
end

end OAI
