import OAI.Analysis.KadisonSimilarity.FreeProduct.ReducedWordAutomorphisms

namespace OAI

/-! Ordinary algebraic generation implies density of centered reduced words.
This is an algebraic centering argument, independent of freeness. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

theorem alternatingProduct_cons {n : ℕ} (a c : Fin (n + 1) → P) :
    alternatingProduct a c = a 0 * c 0 *
      alternatingProduct (fun i => a i.succ) (fun i => c i.succ) := by
  simp only [alternatingProduct, List.ofFn_succ, List.prod_cons]

open scoped Pointwise
open TracialCornerGeometry

namespace CenteredWordSpan

variable (τ : P →ₗ[ℂ] ℂ) (A D : StarSubalgebra ℂ P)

def words : Set P := {x | ∃ (n : ℕ) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D),
    (∀ i, τ (a i : P) = 0) ∧ (∀ i, τ (c i : P) = 0) ∧
      x = (d : P) * alternatingProduct (fun i => (a i : P))
        (fun i => (c i : P)) * (b : P)}

def span : Submodule ℂ P := Submodule.span ℂ (words τ A D)

theorem word_mem (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, τ (a i : P) = 0) (hc : ∀ i, τ (c i : P) = 0) :
    (d : P) * alternatingProduct (fun i => (a i : P))
      (fun i => (c i : P)) * (b : P) ∈ span τ A D :=
  Submodule.subset_span ⟨n, d, b, a, c, ha, hc, rfl⟩

theorem base_mem (b : A) : (b : P) ∈ span τ A D := by
  simpa only [alternatingProduct_zero, OneMemClass.coe_one, one_mul, mul_one] using
    word_mem τ A D 0 1 b Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

theorem one_mem : (1 : P) ∈ span τ A D := base_mem τ A D 1

theorem other_mul_word (x : D) (n : ℕ) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, τ (a i : P) = 0) (hc : ∀ i, τ (c i : P) = 0) :
    (x : P) * ((d : P) * alternatingProduct (fun i => (a i : P))
      (fun i => (c i : P)) * (b : P)) ∈ span τ A D := by
  simpa only [MulMemClass.coe_mul, mul_assoc] using word_mem τ A D n (x * d) b a c ha hc

/-- Centering the first two letters reduces all remaining products to a
shorter word. -/
theorem base_mul_word (hτ : τ 1 = 1) (n : ℕ) (x : A) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, τ (a i : P) = 0) (hc : ∀ i, τ (c i : P) = 0) :
    (x : P) * ((d : P) * alternatingProduct (fun i => (a i : P))
      (fun i => (c i : P)) * (b : P)) ∈ span τ A D := by
  induction n generalizing x d b with
  | zero =>
    let x₀ : A := ⟨traceCentered τ (x : P), traceCentered_mem τ A x.property⟩
    let d₀ : D := ⟨traceCentered τ (d : P), traceCentered_mem τ D d.property⟩
    have hxd : (x₀ : P) * (d₀ : P) * (b : P) ∈ span τ A D := by
      simpa only [alternatingProduct_cons, alternatingProduct_zero, OneMemClass.coe_one,
        one_mul, mul_one, Fin.cons_zero] using
        word_mem τ A D 1 1 b (Fin.cons x₀ Fin.elim0) (Fin.cons d₀ Fin.elim0)
          (by intro i; fin_cases i; exact traceCentered_trace τ hτ x)
          (by intro i; fin_cases i; exact traceCentered_trace τ hτ d)
    have hdb : (d₀ : P) * (b : P) ∈ span τ A D := by
      simpa only [alternatingProduct_zero, mul_one] using
        word_mem τ A D 0 d₀ b Fin.elim0 Fin.elim0
          (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    have hxb := base_mem τ A D (x * b)
    have heq : (x : P) * (d : P) * (b : P) =
        (x₀ : P) * (d₀ : P) * (b : P) +
        τ (x : P) • ((d₀ : P) * (b : P)) + τ (d : P) • ((x : P) * (b : P)) := by
      dsimp only [x₀, d₀]
      simp only [traceCentered, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one]
      module
    simpa only [alternatingProduct_zero, mul_one, ← mul_assoc, heq,
      MulMemClass.coe_mul] using
      (span τ A D).add_mem ((span τ A D).add_mem hxd ((span τ A D).smul_mem _ hdb))
        ((span τ A D).smul_mem _ hxb)
  | succ n ih =>
    let x₀ : A := ⟨traceCentered τ (x : P), traceCentered_mem τ A x.property⟩
    let d₀ : D := ⟨traceCentered τ (d : P), traceCentered_mem τ D d.property⟩
    let w := alternatingProduct (fun i => (a i : P)) (fun i => (c i : P)) * (b : P)
    have hxd : (x₀ : P) * (d₀ : P) * w ∈ span τ A D := by
      simpa only [alternatingProduct_cons, OneMemClass.coe_one, one_mul, Fin.cons_zero,
        Fin.cons_succ, w, mul_assoc] using
        word_mem τ A D (n + 2) 1 b (Fin.cons x₀ a) (Fin.cons d₀ c)
          (by intro i; refine Fin.cases ?_ (fun j => ha j) i
              exact traceCentered_trace τ hτ x)
          (by intro i; refine Fin.cases ?_ (fun j => hc j) i
              exact traceCentered_trace τ hτ d)
    have hdw : (d₀ : P) * w ∈ span τ A D := by
      simpa only [w, mul_assoc] using word_mem τ A D (n + 1) d₀ b a c ha hc
    have hxw : (x : P) * w ∈ span τ A D := by
      have h := ih (x * a 0) (c 0) b (fun i => a i.succ) (fun i => c i.succ)
        (fun i => ha i.succ) (fun i => hc i.succ)
      simpa only [w, alternatingProduct_cons, MulMemClass.coe_mul, mul_assoc] using h
    have heq : (x : P) * (d : P) * w = (x₀ : P) * (d₀ : P) * w +
        τ (x : P) • ((d₀ : P) * w) + τ (d : P) • ((x : P) * w) := by
      dsimp only [x₀, d₀]
      simp only [traceCentered, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one]
      module
    have hres : (x : P) * (d : P) * w ∈ span τ A D := by
      rw [heq]
      exact (span τ A D).add_mem
        ((span τ A D).add_mem hxd ((span τ A D).smul_mem _ hdw))
          ((span τ A D).smul_mem _ hxw)
    simpa only [w, mul_assoc] using hres

/-- Left multiplication by either generating algebra preserves the full span. -/
theorem factor_mul (hτ : τ 1 = 1) {x y : P}
    (hx : x ∈ (A : Set P) ∪ (D : Set P)) (hy : y ∈ span τ A D) :
    x * y ∈ span τ A D := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, d, b, a, c, ha, hc, rfl⟩ := hy
    rcases hx with hx | hx
    · exact base_mul_word τ A D hτ n ⟨x, hx⟩ d b a c ha hc
    · exact other_mul_word τ A D ⟨x, hx⟩ n d b a c ha hc
  | zero => simpa only [mul_zero] using (span τ A D).zero_mem
  | add a b _ _ ha hb => simpa only [mul_add] using (span τ A D).add_mem ha hb
  | smul r a _ ha => simpa only [mul_smul_comm] using (span τ A D).smul_mem r ha

/-- The elements preserving a given word span form an ordinary subalgebra. -/
def preservingAlgebra : Subalgebra ℂ P where
  carrier := {x | ∀ y ∈ span τ A D, x * y ∈ span τ A D}
  zero_mem' := by intro y _; simpa only [zero_mul] using (span τ A D).zero_mem
  one_mem' := by intro y hy; simpa only [one_mul] using hy
  add_mem' := by
    intro a b ha hb y hy
    simpa only [add_mul] using (span τ A D).add_mem (ha y hy) (hb y hy)
  mul_mem' := by intro a b ha hb y hy; simpa only [mul_assoc] using ha _ (hb y hy)
  algebraMap_mem' r := by
    intro y hy
    simpa only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] using
      (span τ A D).smul_mem r hy

/-- Centered normal forms span the ordinary star algebra generated by the factors. -/
theorem generated_mem (hτ : τ 1 = 1) {x : P} (hx : x ∈ factorAlgebra A D) :
    x ∈ span τ A D := by
  have hstable : (factorAlgebra A D).toSubalgebra ≤ preservingAlgebra τ A D := by
    rw [factorAlgebra, StarAlgebra.adjoin_toSubalgebra]
    simp only [Set.union_star, StarMemClass.star_coe_eq, Set.union_self]
    exact Algebra.adjoin_le (fun a ha y hy => factor_mul τ A D hτ ha hy)
  simpa only [mul_one] using hstable hx 1 (one_mem τ A D)

end CenteredWordSpan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

theorem vector_mem_reducedWordSpan {x : P}
    (hx : x ∈ CenteredWordSpan.span G.trace A D) :
    G.vector x ∈ Submodule.span ℂ (reducedWordVectors G A D) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, d, b, a, c, ha, hc, rfl⟩ := hx
    exact Submodule.subset_span ⟨n, d, b, a, c, ha, hc, rfl⟩
  | zero => simpa only [map_zero] using (Submodule.span ℂ (reducedWordVectors G A D)).zero_mem
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul r a _ ha => simpa only [map_smul] using Submodule.smul_mem _ r ha

/-- No additional density assumption on centered normal forms is needed once
the two ordinary factor algebras generate the tracial Hilbert space. -/
theorem reducedWordGenerated_of_factorsTraciallyGenerate (hτ : G.trace 1 = 1)
    (hgen : G.FactorsTraciallyGenerate A D) : ReducedWordGenerated G A D := by
  apply top_unique
  intro x _
  exact hgen.induction_on x (Submodule.isClosed_topologicalClosure _) (fun a =>
    Submodule.le_topologicalClosure _ (G.vector_mem_reducedWordSpan A D
      (CenteredWordSpan.generated_mem G.trace A D hτ a.property)))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
