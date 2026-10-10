import OAI.AlgebraicGeometry.PlaneCurves.AnalyticFactorization
import OAI.AlgebraicGeometry.PlaneCurves.CubicGeometry

namespace OAI

/-!
# Polynomial relation ideals, generators, and prime relations
-/

section

/-! The actual ideal of polynomial relations among three complex cover functions.
Membership means vanishing at every nonzero complex argument. No image geometry,
homogeneity, holomorphicity, or primeness is built into the definition. -/
noncomputable section
namespace Nagata.Workers.W25

/-- Every relation is tested by evaluation at every point of the punctured plane. -/
def polynomialRelationIdeal (s : Fin 3 → ℂ → ℂ) :
    Ideal (MvPolynomial (Fin 3) ℂ) :=
  ⨅ z : {z : ℂ // z ≠ 0}, RingHom.ker (MvPolynomial.eval (fun i => s i z.val))

@[simp] theorem mem_polynomialRelationIdeal (s : Fin 3 → ℂ → ℂ)
    (P : MvPolynomial (Fin 3) ℂ) :
    P ∈ polynomialRelationIdeal s ↔
      ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval (fun i => s i z) P = 0 := by
  simp only [polynomialRelationIdeal, Ideal.mem_iInf, RingHom.mem_ker]
  exact ⟨fun h z hz => h ⟨z, hz⟩, fun h z => h z.val z.property⟩

/-- The constant one never vanishes, since the punctured plane contains one. -/
theorem one_not_mem_polynomialRelationIdeal (s : Fin 3 → ℂ → ℂ) :
    (1 : MvPolynomial (Fin 3) ℂ) ∉ polynomialRelationIdeal s := by
  intro h
  have hz := (mem_polynomialRelationIdeal s 1).mp h 1 one_ne_zero
  simp at hz

/-- Properness is unconditional and does not assume an algebraic image theorem. -/
theorem polynomialRelationIdeal_ne_top (s : Fin 3 → ℂ → ℂ) :
    polynomialRelationIdeal s ≠ ⊤ := by
  intro h
  exact one_not_mem_polynomialRelationIdeal s (h ▸ trivial)

/-- Relation-ideal containment is exactly vanishing of each chosen generator. -/
theorem span_le_polynomialRelationIdeal (s : Fin 3 → ℂ → ℂ)
    (E : Set (MvPolynomial (Fin 3) ℂ)) :
    Ideal.span E ≤ polynomialRelationIdeal s ↔
      ∀ P ∈ E, ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval (fun i => s i z) P = 0 := by
  rw [Ideal.span_le]
  constructor
  · intro h P hP
    exact (mem_polynomialRelationIdeal s P).mp (h hP)
  · intro h P hP
    exact (mem_polynomialRelationIdeal s P).mpr (h P hP)

end Nagata.Workers.W25

end
end

section

namespace Nagata.Workers.W25

theorem relation_generator_dvd_iff (s : Fin 3 → ℂ → ℂ)
    (G : MvPolynomial (Fin 3) ℂ)
    (hI : polynomialRelationIdeal s = Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ)))
    (P : MvPolynomial (Fin 3) ℂ) :
    G ∣ P ↔ ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval (fun i => s i z) P = 0 := by
  rw [← mem_polynomialRelationIdeal s P, hI, Ideal.mem_span_singleton]

theorem exists_eval_ne_zero_of_not_dvd_relation_generator (s : Fin 3 → ℂ → ℂ)
    (G : MvPolynomial (Fin 3) ℂ)
    (hI : polynomialRelationIdeal s = Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ)))
    (P : MvPolynomial (Fin 3) ℂ) (hP : ¬ G ∣ P) :
    ∃ z : ℂ, z ≠ 0 ∧ MvPolynomial.eval (fun i => s i z) P ≠ 0 := by
  classical
  by_contra h
  apply hP
  apply (relation_generator_dvd_iff s G hI P).mpr
  intro z hz
  by_contra he
  exact h ⟨z, hz, he⟩

end Nagata.Workers.W25

end

section

/-! Genuine analytic primeness and cubic containment for the actual cover map. -/
namespace Nagata.Workers.W25

/-- The identity principle on the connected punctured plane makes its polynomial
relation ideal prime. Holomorphicity is an explicit, ordinary function hypothesis. -/
theorem polynomialRelationIdeal_isPrime (s : Fin 3 → ℂ → ℂ)
    (hs : ∀ i, DifferentiableOn ℂ (s i) {z : ℂ | z ≠ 0}) :
    (polynomialRelationIdeal s).IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨polynomialRelationIdeal_ne_top s, ?_⟩
  intro P Q hPQ
  simpa only [mem_polynomialRelationIdeal] using
    Nagata.W19.polynomial_eval_punctured_mul_zero s hs P Q
      ((mem_polynomialRelationIdeal s (P * Q)).mp hPQ)

/-- Specialization to actual degree-three automorphic sections, with their
holomorphicity derived from membership in the concrete section space. -/
theorem cubicSectionRelationIdeal_isPrime {τ γ : ℂ}
    (b : Fin 3 → Nagata.W08.automorphicSections τ 3 γ) :
    (polynomialRelationIdeal (fun i => (b i).val)).IsPrime :=
  polynomialRelationIdeal_isPrime _
    (fun i z hz => ((b i).property.2.1 z hz).differentiableWithinAt)

/-- The actual cubic relation belongs to the relation ideal. Only the stated
finite-dimensional degree-nine section input is used here. -/
theorem exists_cubic_mem_relationIdeal {τ γ : ℂ}
    (b : Fin 3 → Nagata.W08.automorphicSections τ 3 γ)
    [Module.Finite ℂ (Nagata.W08.automorphicSections τ 9 (γ ^ 3))]
    (hdim : Module.finrank ℂ (Nagata.W08.automorphicSections τ 9 (γ ^ 3)) ≤ 9) :
    ∃ P : MvPolynomial (Fin 3) ℂ, P ≠ 0 ∧ P.IsHomogeneous 3 ∧
      P ∈ polynomialRelationIdeal (fun i => (b i).val) := by
  obtain ⟨P, hP, hhom, heval⟩ :=
    Nagata.W21.exists_cubicEquation_of_degreeNine_dimension b hdim
  refine ⟨P, hP, hhom, (mem_polynomialRelationIdeal _ P).mpr ?_⟩
  intro z _
  exact heval z

end Nagata.Workers.W25

end

section

/-! Actual distinct basis sections satisfy no nontrivial linear equation on C*.
The zero extension at the omitted point allows ordinary basis linear independence
to apply to the pointwise relation. -/
namespace Nagata.Workers.W25

theorem basis_pair_linear_relation_trivial {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (Nagata.W08.automorphicSections τ 3 γ))
    (i j : Fin 3) (hij : i ≠ j) (a c : ℂ)
    (hrel : MvPolynomial.C a * MvPolynomial.X i + MvPolynomial.C c * MvPolynomial.X j ∈
      polynomialRelationIdeal (fun k => (b k).val)) : a = 0 ∧ c = 0 := by
  have hsec : a • b i + c • b j = 0 := by
    apply Subtype.ext
    funext z
    by_cases hz : z = 0
    · subst z
      change a * (b i).val 0 + c * (b j).val 0 = 0
      rw [(b i).property.1, (b j).property.1, mul_zero, mul_zero, add_zero]
    · have heval := (mem_polynomialRelationIdeal _ _).mp hrel z hz
      change a * (b i).val z + c * (b j).val z = 0
      simpa only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] using heval
  constructor
  · have h := congrArg (fun f => b.repr f i) hsec
    simpa [hij, Ne.symm hij] using h
  · have h := congrArg (fun f => b.repr f j) hsec
    simpa [hij, Ne.symm hij] using h

end Nagata.Workers.W25

end

end OAI
