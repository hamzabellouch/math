import OAI.Analysis.FreeGroupFactor.NCPolynomial

namespace OAI

noncomputable section

universe uA uB uG uι

open Set Metric
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
namespace TraceCocycle

abbrev CF (G : Type uG) := G →₀ ℂ

def shift {G : Type uG} [Group G] (g : G) : CF G ≃+ CF G :=
  Finsupp.domCongr (MulAut.conj g).toEquiv

@[simp] theorem shift_apply {G : Type uG} [Group G] (g : G) (p : CF G) (b : G) :
    shift g p b = p (g⁻¹ * b * g) := rfl

@[simp] theorem shift_one {G : Type uG} [Group G] (p : CF G) : shift (1 : G) p = p := by
  ext b
  simp

@[simp] theorem shift_mul {G : Type uG} [Group G] (g b : G) (p : CF G) :
    shift (g * b) p = shift g (shift b p) := by
  ext c
  simp [mul_assoc]

def action (G : Type uG) [Group G] : G →* MulAut (Multiplicative (CF G)) where
  toFun g := AddEquiv.toMultiplicative (shift g)
  map_one' := by
    apply MulEquiv.ext
    intro p
    exact shift_one p.toAdd
  map_mul' g b := by
    apply MulEquiv.ext
    intro p
    exact shift_mul g b p.toAdd

def graph {ι : Type uι} (h : ι → CF (FreeGroup ι)) :
    FreeGroup ι →* (Multiplicative (CF (FreeGroup ι)) ⋊[action (FreeGroup ι)] FreeGroup ι) :=
  FreeGroup.lift (fun i => ⟨Multiplicative.ofAdd (h i), FreeGroup.of i⟩)

@[simp] theorem graph_right {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) :
    (graph h g).right = g := by
  have hr : SemidirectProduct.rightHom.comp (graph h) = MonoidHom.id _ := by
    ext i
    simp [graph]
  exact DFunLike.congr_fun hr g

def cocycle {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) : CF (FreeGroup ι) :=
  (graph h g).left.toAdd

@[simp] theorem cocycle_of {ι : Type uι} (h : ι → CF (FreeGroup ι)) (i : ι) :
    cocycle h (FreeGroup.of i) = h i := by
  simp [cocycle, graph]

@[simp] theorem cocycle_one {ι : Type uι} (h : ι → CF (FreeGroup ι)) : cocycle h 1 = 0 := by
  simp [cocycle]

theorem cocycle_mul {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g b : FreeGroup ι) :
    cocycle h (g * b) = cocycle h g + shift g (cocycle h b) := by
  unfold cocycle
  rw [map_mul, SemidirectProduct.mul_left, graph_right]
  rfl

theorem cocycle_inv {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) :
    cocycle h g⁻¹ = -shift g⁻¹ (cocycle h g) := by
  have he := cocycle_mul h g⁻¹ g
  simp only [inv_mul_cancel, cocycle_one] at he
  exact eq_neg_of_add_eq_zero_left he.symm

def traceDerivative {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) : ℂ :=
  cocycle h g g⁻¹

theorem traceDerivative_conjugate {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (a g : FreeGroup ι) :
    traceDerivative h (a * g * a⁻¹) = traceDerivative h g := by
  simp only [traceDerivative, cocycle_mul, cocycle_inv, shift_apply,
    Finsupp.add_apply, Finsupp.neg_apply, mul_inv_rev, inv_inv]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  ring

def CyclicConjugate {G : Type uG} [Group G] (c b : G) : Prop :=
  ∃ (a : G) (k : ℤ), b = a * c ^ k * a⁻¹

theorem CyclicConjugate.conj {G : Type uG} [Group G] {c b : G}
    (hb : CyclicConjugate c b) (g : G) : CyclicConjugate c (g * b * g⁻¹) := by
  obtain ⟨a, k, rfl⟩ := hb
  exact ⟨g * a, k, by simp [mul_assoc]⟩

theorem CyclicConjugate.inv {G : Type uG} [Group G] {c b : G}
    (hb : CyclicConjugate c b) : CyclicConjugate c b⁻¹ := by
  obtain ⟨a, k, rfl⟩ := hb
  exact ⟨a, -k, by simp [mul_assoc]⟩

def SupportedOn {G : Type uG} (P : G → Prop) (p : CF G) : Prop :=
  ∀ b, ¬P b → p b = 0

@[simp] theorem supported_zero {G : Type uG} (P : G → Prop) : SupportedOn P (0 : CF G) := by
  intro b hb
  rfl

theorem supported_add {G : Type uG} {P : G → Prop} {p q : CF G}
    (hp : SupportedOn P p) (hq : SupportedOn P q) : SupportedOn P (p + q) := by
  intro b hb
  simp [hp b hb, hq b hb]

theorem supported_neg {G : Type uG} {P : G → Prop} {p : CF G}
    (hp : SupportedOn P p) : SupportedOn P (-p) := by
  intro b hb
  simp [hp b hb]

theorem supported_shift {G : Type uG} [Group G] {c : G} {p : CF G}
    (hp : SupportedOn (CyclicConjugate c) p) (g : G) :
    SupportedOn (CyclicConjugate c) (shift g p) := by
  intro b hb
  apply hp
  intro h
  have := h.conj g
  apply hb
  simpa [mul_assoc] using this

end TraceCocycle
end FreeGroupFactorMain

namespace FreeGroupFactorMain.TraceCocycle

 theorem cocycle_supported {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : FreeGroup ι)
    (hh : ∀ i, SupportedOn (CyclicConjugate c) (h i)) (g : FreeGroup ι) :
    SupportedOn (CyclicConjugate c) (cocycle h g) := by
  induction g using FreeGroup.induction_on with
  | one => simp
  | of i => simpa using hh i
  | inv_of g hg => rw [cocycle_inv]; exact supported_neg (supported_shift hg _)
  | mul g b hg hb => rw [cocycle_mul]; exact supported_add hg (supported_shift hb _)

 theorem cocycle_pow_zero {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : FreeGroup ι)
    (hc : cocycle h c = 0) (k : ℕ) : cocycle h (c ^ k) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, cocycle_mul, ih, hc]

 theorem cocycle_zpow_zero {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : FreeGroup ι)
    (hc : cocycle h c = 0) (k : ℤ) : cocycle h (c ^ k) = 0 := by
  cases k with
  | ofNat k => simpa using cocycle_pow_zero h c hc k
  | negSucc k => simp [zpow_negSucc, cocycle_inv, cocycle_pow_zero h c hc]

 theorem universalGroupTraceIdentity {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : ι)
    (hh : ∀ i, SupportedOn (CyclicConjugate (FreeGroup.of c)) (h i))
    (hc : h c = 0) (g : FreeGroup ι) : traceDerivative h g = 0 := by
  classical
  by_cases hg : CyclicConjugate (FreeGroup.of c) g
  · obtain ⟨a, k, rfl⟩ := hg
    rw [traceDerivative_conjugate, traceDerivative,
      cocycle_zpow_zero h _ (by simpa using hc)]
    rfl
  · apply cocycle_supported h (FreeGroup.of c) hh g
    intro hginv
    exact hg (by simpa using hginv.inv)

def rightShift {G : Type uG} [Group G] (g : G) : CF G ≃ₗ[ℂ] CF G :=
  Finsupp.domLCongr (Equiv.mulRight g)

@[simp] theorem rightShift_apply {G : Type uG} [Group G] (g : G) (p : CF G) (b : G) :
    rightShift g p b = p (b * g⁻¹) := rfl

def polynomialDerivative {ι : Type uι} (h : ι → CF (FreeGroup ι)) :
    CF (FreeGroup ι) →ₗ[ℂ] CF (FreeGroup ι) :=
  Finsupp.linearCombination ℂ (fun g => rightShift g (cocycle h g))

@[simp] theorem polynomialDerivative_single {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (g : FreeGroup ι) (a : ℂ) :
    polynomialDerivative h (Finsupp.single g a) = a • rightShift g (cocycle h g) := by
  simp [polynomialDerivative]

 theorem polynomialDerivative_trace_zero {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : ι)
    (hh : ∀ i, SupportedOn (CyclicConjugate (FreeGroup.of c)) (h i))
    (hc : h c = 0) (p : CF (FreeGroup ι)) : (polynomialDerivative h p) 1 = 0 := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single g a =>
    simp only [polynomialDerivative_single, Finsupp.smul_apply, smul_eq_mul,
      rightShift_apply, one_mul]
    change a * traceDerivative h g = 0
    rw [universalGroupTraceIdentity h c hh hc, mul_zero]

 theorem iteratedDerivative_trace_zero {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : ι)
    (hh : ∀ i, SupportedOn (CyclicConjugate (FreeGroup.of c)) (h i))
    (hc : h c = 0) (p : CF (FreeGroup ι)) (r : ℕ) :
    ((polynomialDerivative h)^[r + 1] p) 1 = 0 := by
  rw [Function.iterate_succ_apply']
  exact polynomialDerivative_trace_zero h c hh hc _

def algebraDerivative {ι : Type uι} (h : ι → CF (FreeGroup ι)) :
    MonoidAlgebra ℂ (FreeGroup ι) →ₗ[ℂ] MonoidAlgebra ℂ (FreeGroup ι) :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
    polynomialDerivative h ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem algebraDerivative_coeff {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    (algebraDerivative h p).coeff = polynomialDerivative h p.coeff := rfl

@[simp] theorem algebraDerivative_of_coeff {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (g : FreeGroup ι) (b : FreeGroup ι) :
    (algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g)).coeff b =
      cocycle h g (b * g⁻¹) := by
  simp [MonoidAlgebra.of_apply]

theorem algebraDerivative_mul_of {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (g b : FreeGroup ι) :
    algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g *
      MonoidAlgebra.of ℂ (FreeGroup ι) b) =
      algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g) *
        MonoidAlgebra.of ℂ (FreeGroup ι) b +
      MonoidAlgebra.of ℂ (FreeGroup ι) g *
        algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) b) := by
  rw [← map_mul]
  ext x
  simp [MonoidAlgebra.of_apply, cocycle_mul, mul_assoc]

theorem algebraDerivative_mul {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (p q : MonoidAlgebra ℂ (FreeGroup ι)) :
    algebraDerivative h (p * q) = algebraDerivative h p * q + p * algebraDerivative h q := by
  induction p using MonoidAlgebra.induction_on with
  | of g =>
    induction q using MonoidAlgebra.induction_on with
    | of b => exact algebraDerivative_mul_of h g b
    | add q₁ q₂ ih₁ ih₂ => simp only [mul_add, map_add, ih₁, ih₂]; abel
    | smul r q ih => simp only [mul_smul_comm, map_smul, ih, smul_add]
  | add p₁ p₂ ih₁ ih₂ => simp only [add_mul, map_add, ih₁, ih₂]; abel
  | smul r p ih => simp only [smul_mul_assoc, map_smul, ih, smul_add]

def laurent {G : Type uG} [Group G] (c : G) (l : ℤ →₀ ℂ) : CF G :=
  Finsupp.linearCombination ℂ (fun k => Finsupp.single (c ^ k) 1) l

theorem supported_smul {G : Type uG} {P : G → Prop} {p : CF G}
    (hp : SupportedOn P p) (a : ℂ) : SupportedOn P (a • p) := by
  intro b hb
  simp [hp b hb]

theorem laurent_supported {G : Type uG} [Group G] (c : G) (l : ℤ →₀ ℂ) :
    SupportedOn (CyclicConjugate c) (laurent c l) := by
  classical
  induction l using Finsupp.induction_linear with
  | zero => simp [laurent]
  | add p q hp hq => simpa only [laurent, map_add] using supported_add hp hq
  | single k a =>
    simp only [laurent, Finsupp.linearCombination_single]
    apply supported_smul
    intro b hb
    apply Finsupp.single_eq_of_ne
    intro heq
    apply hb
    exact ⟨1, k, by simpa using heq⟩

def fieldCoefficients {ι : Type uι} (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) :
    Option ι → CF (FreeGroup (Option ι))
  | none => 0
  | some i => (h i).sum fun g a => ((a : ℂ) * Complex.I) •
      shift (FreeGroup.map Option.some g) (laurent (FreeGroup.of none) l)

theorem fieldCoefficients_supported {ι : Type uι} (h : ι → FreeGroup ι →₀ ℝ)
    (l : ℤ →₀ ℂ) (i : Option ι) :
    SupportedOn (CyclicConjugate (FreeGroup.of none)) (fieldCoefficients h l i) := by
  classical
  cases i with
  | none => exact supported_zero _
  | some i =>
    intro b hb
    simp only [fieldCoefficients, Finsupp.sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro g hg
    exact supported_smul (supported_shift (laurent_supported _ _) _) _ b hb

theorem sourceLaurentTraceIdentity {ι : Type uι} (h : ι → FreeGroup ι →₀ ℝ)
    (l : ℤ →₀ ℂ) (p : MonoidAlgebra ℂ (FreeGroup (Option ι))) (r : ℕ) :
    ((algebraDerivative (fieldCoefficients h l))^[r + 1] p).coeff 1 = 0 := by
  rw [Function.iterate_succ_apply', algebraDerivative_coeff]
  exact polynomialDerivative_trace_zero _ none (fieldCoefficients_supported h l) rfl _

end FreeGroupFactorMain.TraceCocycle

namespace FreeGroupFactorMain
namespace AlgebraPolynomial
open NCPolynomial

def signed {ι : Type uι} (ib : ι × Bool) : FreeGroup ι :=
  if ib.2 then FreeGroup.of ib.1 else (FreeGroup.of ib.1)⁻¹

def wordExpr {ι : Type uι} : List (ι × Bool) → Expr (ι × Bool)
  | [] => .scalar 1
  | a :: w => .mul (.gen a) (wordExpr w)

theorem eval_wordExpr {ι : Type uι} {A : Type uA} [Semiring A] [Algebra ℂ A]
    (ρ : FreeGroup ι →* A) (w : List (ι × Bool)) :
    eval (fun ib => ρ (signed ib)) (wordExpr w) = ρ (FreeGroup.mk w) := by
  induction w with
  | nil => simp [wordExpr, eval, ← FreeGroup.one_eq_mk]
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    change ρ (signed (i, b)) * eval (fun ib => ρ (signed ib)) (wordExpr w) = _
    rw [ih, ← map_mul]
    cases b <;> rfl

def groupExpr {ι : Type uι} [DecidableEq ι] (g : FreeGroup ι) : Expr (ι × Bool) :=
  wordExpr g.toWord

theorem eval_groupExpr {ι : Type uι} {A : Type uA} [DecidableEq ι] [Semiring A] [Algebra ℂ A]
    (ρ : FreeGroup ι →* A) (g : FreeGroup ι) :
    eval (fun ib => ρ (signed ib)) (groupExpr g) = ρ g := by
  rw [groupExpr, eval_wordExpr, FreeGroup.mk_toWord]

def sumExpr {ι : Type uι} : List (Expr ι) → Expr ι
  | [] => .scalar 0
  | p :: ps => .add p (sumExpr ps)

theorem eval_sumExpr {ι : Type uι} {A : Type uA} [Semiring A] [Algebra ℂ A]
    (X : ι → A) (ps : List (Expr ι)) :
    eval X (sumExpr ps) = (ps.map (eval X)).sum := by
  induction ps with
  | nil => simp [sumExpr, eval]
  | cons p ps ih => simp [sumExpr, eval, ih]

def encode {ι : Type uι} [DecidableEq ι] (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    Expr (ι × Bool) :=
  sumExpr (p.coeff.support.toList.map fun g => .mul (.scalar (p.coeff g)) (groupExpr g))

theorem eval_encode {ι : Type uι} [DecidableEq ι] (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib)) (encode p) = p := by
  classical
  rw [encode, eval_sumExpr, List.map_map]
  simp only [Function.comp_def, eval]
  simp_rw [eval_groupExpr]
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_map_toList]
  simpa only [Finsupp.sum] using (MonoidAlgebra.sum_coeff_single p)

def encodedField {ι : Type uι} [DecidableEq ι]
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (ib : ι × Bool) : Expr (ι × Bool) :=
  encode (TraceCocycle.algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib)))

theorem algebraDerivative_one {ι : Type uι} (h : ι → TraceCocycle.CF (FreeGroup ι)) :
    TraceCocycle.algebraDerivative h 1 = 0 := by
  have he := TraceCocycle.algebraDerivative_mul h 1 1
  simp only [one_mul, mul_one] at he
  exact (add_eq_left.mp he.symm)

theorem eval_delta_encoded {ι : Type uι} [DecidableEq ι]
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (p : Expr (ι × Bool)) :
    eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib))
      (delta (encodedField h) p) =
    TraceCocycle.algebraDerivative h
      (eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib)) p) := by
  induction p with
  | scalar c =>
    simp only [delta, eval, Algebra.algebraMap_eq_smul_one, map_smul,
      algebraDerivative_one, smul_zero, zero_smul]
  | gen ib => exact eval_encode _
  | add p q hp hq => simp only [delta, eval, hp, hq, map_add]
  | mul p q hp hq => simp only [delta, eval, hp, hq, TraceCocycle.algebraDerivative_mul]

theorem map_eval {ι : Type uι} {A : Type uA} {B : Type uB} [Semiring A] [Semiring B]
    [Algebra ℂ A] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) (X : ι → A) (p : Expr ι) :
    φ (eval X p) = eval (fun i => φ (X i)) p := by
  induction p with
  | scalar c => exact φ.commutes c
  | gen i => rfl
  | add p q hp hq => simp only [eval, map_add, hp, hq]
  | mul p q hp hq => simp only [eval, map_mul, hp, hq]

theorem encoded_initial_trace {ι : Type uι} [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (p : Expr ((Option ι) × Bool)) :
    (eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup (Option ι)) (signed ib))
      (delta (encodedField (TraceCocycle.fieldCoefficients h l)) p)).coeff 1 = 0 := by
  rw [eval_delta_encoded]
  exact TraceCocycle.sourceLaurentTraceIdentity h l _ 0

end AlgebraPolynomial
end FreeGroupFactorMain

end

end OAI
