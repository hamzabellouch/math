import OAI.Analysis.FreeGroupFactor.Operators
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open scoped ENNReal Pointwise
local instance groupAlgebraDecEq (G : Type*) : DecidableEq G := Classical.decEq _
abbrev Ell2 (G : Type*) := FreeGroupFactorMain.GroupHilbert G
abbrev Operator (G : Type*) := FreeGroupFactorMain.GroupOperator G
/-- Reindex a square-summable vector by a permutation. -/
abbrev reindexVector {G : Type*} (e : G ≃ G) (f : Ell2 G) : Ell2 G :=
  FreeGroupFactorMain.hilbertReindex e f

@[simp] theorem reindexVector_apply {G : Type*} (e : G ≃ G) (f : Ell2 G) (g : G) :
    reindexVector e f g = f (e.symm g) := rfl

theorem reindexVector_norm {G : Type*} (e : G ≃ G) (f : Ell2 G) :
    ‖reindexVector e f‖ = ‖f‖ := by
  exact (FreeGroupFactorMain.hilbertReindex e).norm_map f

/-- The bounded unitary implementation of a permutation on ell2. -/
abbrev reindex {G : Type*} (e : G ≃ G) : Ell2 G ≃ₗᵢ[ℂ] Ell2 G :=
  FreeGroupFactorMain.hilbertReindex e

/-- The left regular operator, constructed on every square-summable vector. -/
abbrev leftRegular {G : Type*} [Group G] (g : G) : Ell2 G →L[ℂ] Ell2 G :=
  FreeGroupFactorMain.leftRegular g

@[simp] theorem leftRegular_apply {G : Type*} [Group G] (g b : G) (f : Ell2 G) :
    leftRegular g f b = f (g⁻¹ * b) := rfl

@[simp] theorem leftRegular_one {G : Type*} [Group G] : leftRegular (1 : G) = 1 := by
  ext f b
  simp

@[simp] theorem leftRegular_mul {G : Type*} [Group G] (g h : G) :
    leftRegular (g * h) = leftRegular g * leftRegular h := by
  ext f b
  simp

theorem leftRegular_norm_vector {G : Type*} [Group G] (g : G) (f : Ell2 G) :
    ‖leftRegular g f‖ = ‖f‖ := reindexVector_norm (Equiv.mulLeft g) f

variable (G : Type*) [Group G]

abbrev regularOperators : Set (Operator G) := FreeGroupFactorMain.leftTranslations G
abbrev groupAlgebra : StarSubalgebra ℂ (Operator G) :=
  FreeGroupFactorMain.groupVonNeumann G

def delta : Ell2 G := by
  classical
  exact lp.single 2 (1 : G) 1
def trace (T : groupAlgebra G) : ℂ := inner ℂ (delta G) ((T : Operator G) (delta G))

@[simp] theorem leftRegular_trace (g : G) :
    inner ℂ (delta G) (leftRegular g (delta G)) = if g = 1 then 1 else 0 := by
  classical
  rw [delta, lp.inner_single_left]
  simp [lp.single_apply, Pi.single_apply]

variable {G}
@[simp] theorem leftRegular_star {G : Type*} [Group G] (g : G) :
    star (leftRegular g) = leftRegular g⁻¹ := by
  change star ((reindex (Equiv.mulLeft g)) : Ell2 G →L[ℂ] Ell2 G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext f b
  change f (g * b) = f ((g⁻¹)⁻¹ * b)
  simp

/-- Right translations, needed to prove that the identity vector is separating. -/
def rightRegular {G : Type*} [Group G] (g : G) : Ell2 G →L[ℂ] Ell2 G :=
  (reindex (Equiv.mulRight g)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rightRegular_apply {G : Type*} [Group G] (g b : G) (f : Ell2 G) :
    rightRegular g f b = f (b * g⁻¹) := rfl

theorem left_right_commute {G : Type*} [Group G] (g h : G) :
    leftRegular g * rightRegular h = rightRegular h * leftRegular g := by
  ext f b
  simp [mul_assoc]

theorem regularOperators_star (G : Type*) [Group G] :
    star (regularOperators G) = regularOperators G := by
  rw [regularOperators, FreeGroupFactorMain.leftTranslations_eq_range]
  ext T
  simp only [Set.mem_star, Set.mem_range]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, by simpa only [leftRegular_star, star_star] using congrArg star hg⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, (leftRegular_star g).symm⟩

/-- Exact equality with the manuscript's plain double commutant of lambda(G). -/
theorem groupAlgebra_carrier (G : Type*) [Group G] :
    (groupAlgebra G : Set (Operator G)) =
      Set.centralizer (Set.centralizer (regularOperators G)) := by
  rw [groupAlgebra, FreeGroupFactorMain.groupVonNeumann,
    StarSubalgebra.coe_centralizer_centralizer,
    regularOperators_star, Set.union_self]

/-- The target algebra actually satisfies mathlib's concrete von Neumann algebra definition. -/
abbrev concreteGroupAlgebra (G : Type*) [Group G] : VonNeumannAlgebra (Ell2 G) :=
  FreeGroupFactorMain.groupVonNeumannBundled G

theorem rightRegular_mem_commutant (G : Type*) [Group G] (g : G) :
    rightRegular g ∈ StarSubalgebra.centralizer ℂ (regularOperators G) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  rw [regularOperators, FreeGroupFactorMain.leftTranslations_eq_range] at hT
  obtain ⟨h, rfl⟩ := hT
  exact ⟨left_right_commute h g, by rw [leftRegular_star]; exact left_right_commute h⁻¹ g⟩

theorem algebra_right_commute (G : Type*) [Group G] (T : groupAlgebra G)
    (g : G) :
    (T : Operator G) * rightRegular g =
      rightRegular g * (T : Operator G) := by
  have ht := T.property
  change (T : Operator G) ∈ StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (regularOperators G) : Set (Operator G)) at ht
  rw [StarSubalgebra.mem_centralizer_iff] at ht
  exact (ht (rightRegular g) (rightRegular_mem_commutant G g)).1.symm

theorem rightRegular_delta (G : Type*) [Group G] (g : G) :
    rightRegular g (delta G) = lp.single 2 g (1 : ℂ) := by
  classical
  ext b
  simp [delta, lp.single_apply, Pi.single_apply, mul_inv_eq_one]

/-- Fourier coefficients at the identity separate all elements of the group algebra,
by commuting with right translations and using the density of finitely supported vectors. -/
theorem delta_separating (G : Type*) [Group G] (T : groupAlgebra G)
    (hT : (T : Operator G) (delta G) = 0) : T = 0 := by
  classical
  apply Subtype.ext
  change (T : Operator G) = 0
  apply lp.ext_continuousLinearMap (by simp)
  intro g
  apply ContinuousLinearMap.ext
  intro c
  change (T : Operator G) (lp.single 2 g c) = 0
  have hs : lp.single 2 g c = c • rightRegular g (delta G) := by
    rw [rightRegular_delta, ← lp.single_smul]
    simp
  have hz : (T : Operator G) (rightRegular g (delta G)) = 0 := by
    change ((T : Operator G) * rightRegular g) (delta G) = 0
    rw [algebra_right_commute]
    change rightRegular g ((T : Operator G) (delta G)) = 0
    rw [hT, map_zero]
  rw [hs, map_smul, hz, smul_zero]

/-- The canonical vector functional evaluated on a positive square. -/
theorem trace_star_mul_self (G : Type*) [Group G] (T : groupAlgebra G) :
    trace G (star T * T) =
      inner ℂ ((T : Operator G) (delta G))
        ((T : Operator G) (delta G)) := by
  exact ContinuousLinearMap.adjoint_inner_right (T : Operator G)
    (delta G) ((T : Operator G) (delta G))

/-- Faithfulness of the canonical vector trace. -/
theorem trace_faithful (G : Type*) [Group G] (T : groupAlgebra G) :
    trace G (star T * T) = 0 ↔ T = 0 := by
  rw [trace_star_mul_self, inner_self_eq_zero]
  constructor
  · exact delta_separating G T
  · intro h
    subst T
    simp

end

section
local instance traceDecEq (G : Type*) : DecidableEq G := Classical.decEq _
open scoped ComplexConjugate
variable {G : Type*} [Group G]

@[simp] theorem delta_inner (ξ : Ell2 G) : inner ℂ (delta G) ξ = ξ 1 := by
  classical
  simp [delta, lp.inner_single_left]

theorem algebra_apply_single (T : groupAlgebra G) (g b : G) :
    (T : Operator G) (lp.single 2 g (1 : ℂ)) b =
      (T : Operator G) (delta G) (b * g⁻¹) := by
  rw [← rightRegular_delta G g]
  have h := congrArg (fun S : Operator G => S (delta G) b) (algebra_right_commute G T g)
  exact h

theorem adjoint_coefficient (T : groupAlgebra G) (g : G) :
    star (((star T : groupAlgebra G) : Operator G) (delta G) g) =
      (T : Operator G) (delta G) g⁻¹ := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_left (T : Operator G)
    (lp.single 2 g (1 : ℂ)) (delta G)
  simpa [lp.inner_single_right, delta_inner, algebra_apply_single,
    RCLike.inner_apply, ContinuousLinearMap.star_eq_adjoint] using h

theorem trace_mul_formula (S T : groupAlgebra G) :
    trace G (S * T) = ∑' g : G,
      (S : Operator G) (delta G) g⁻¹ * (T : Operator G) (delta G) g := by
  change inner ℂ (delta G) ((S : Operator G) ((T : Operator G) (delta G))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum]
  apply tsum_congr
  intro g
  rw [RCLike.inner_apply]
  change _ * star (((star S : groupAlgebra G) : Operator G) (delta G) g) = _
  rw [adjoint_coefficient, mul_comm]

/-- Cyclicity for all bounded operators in the actual double commutant. -/
theorem trace_mul_comm (S T : groupAlgebra G) : trace G (S * T) = trace G (T * S) := by
  rw [trace_mul_formula, trace_mul_formula]
  rw [← (Equiv.inv G).tsum_eq (fun g : G =>
    (T : Operator G) (delta G) g⁻¹ * (S : Operator G) (delta G) g)]
  apply tsum_congr
  intro g
  simp [mul_comm]

@[simp] theorem trace_one : trace G (1 : groupAlgebra G) = 1 := by
  classical
  simp [trace, delta]

@[simp] theorem trace_add (S T : groupAlgebra G) : trace G (S + T) = trace G S + trace G T := by
  exact inner_add_right _ _ _

@[simp] theorem trace_smul (c : ℂ) (T : groupAlgebra G) : trace G (c • T) = c * trace G T := by
  exact inner_smul_right _ _ _

def traceLinear : groupAlgebra G →ₗ[ℂ] ℂ where
  toFun := trace G
  map_add' := trace_add
  map_smul' := trace_smul

/-- The canonical trace two-norm is the norm of the identity-vector image. -/
def traceNorm (T : groupAlgebra G) : ℝ := ‖(T : Operator G) (delta G)‖

theorem traceNorm_sq (T : groupAlgebra G) :
    traceNorm T ^ 2 = (trace G (star T * T)).re := by
  rw [trace_star_mul_self]
  simp [traceNorm, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

end

section
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete finite tracial von Neumann algebra in a faithful vector-trace
representation. These are operator-algebra data, without approximation assumptions. -/
structure TracialRepresentation (M : VonNeumannAlgebra H) where
  vector : H
  norm_vector : ‖vector‖ = 1
  cyclic : ∀ S T : M.toStarSubalgebra,
    inner ℂ vector ((S : H →L[ℂ] H) ((T : H →L[ℂ] H) vector)) =
    inner ℂ vector ((T : H →L[ℂ] H) ((S : H →L[ℂ] H) vector))
  separating : ∀ T : M.toStarSubalgebra, (T : H →L[ℂ] H) vector = 0 → T = 0

namespace TracialRepresentation
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
abbrev Algebra := M.toStarSubalgebra

def trace (T : Algebra (M := M)) : ℂ := inner ℂ τ.vector ((T : H →L[ℂ] H) τ.vector)
def norm₂ (T : Algebra (M := M)) : ℝ := ‖(T : H →L[ℂ] H) τ.vector‖

@[simp] theorem trace_one : τ.trace 1 = 1 := by
  simp [trace, inner_self_eq_norm_sq_to_K, τ.norm_vector]

theorem trace_mul_comm (S T : Algebra (M := M)) : τ.trace (S*T) = τ.trace (T*S) :=
  τ.cyclic S T

theorem trace_star_mul (T : Algebra (M := M)) :
    τ.trace (star T*T) = (τ.norm₂ T : ℂ)^2 := by
  unfold trace norm₂
  change inner ℂ τ.vector ((star (T : H →L[ℂ] H)) ((T : H →L[ℂ] H) τ.vector)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem norm₂_star (T : Algebra (M := M)) : τ.norm₂ (star T) = τ.norm₂ T := by
  have h := τ.trace_mul_comm (star T) T
  have h2 := τ.trace_star_mul (star T)
  simp only [star_star] at h2
  rw [τ.trace_star_mul, h2] at h
  have hr := congrArg Complex.re h
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at hr
  have hn : 0 ≤ τ.norm₂ T := norm_nonneg _
  have hs : 0 ≤ τ.norm₂ (star T) := norm_nonneg _
  nlinarith

@[simp] theorem norm₂_zero : τ.norm₂ 0 = 0 := by simp [norm₂]
@[simp] theorem norm₂_sub (S T : Algebra (M := M)) :
    τ.norm₂ (S-T) = ‖(S : H →L[ℂ] H) τ.vector - (T : H →L[ℂ] H) τ.vector‖ := rfl

theorem norm₂_add_le (S T : Algebra (M := M)) : τ.norm₂ (S+T) ≤ τ.norm₂ S+τ.norm₂ T :=
  norm_add_le _ _

theorem norm₂_smul (c : ℂ) (T : Algebra (M := M)) : τ.norm₂ (c • T) = ‖c‖*τ.norm₂ T :=
  norm_smul _ _

theorem norm₂_mul_le (S T : Algebra (M := M)) : τ.norm₂ (S*T) ≤ ‖S‖ * τ.norm₂ T :=
  (S : H →L[ℂ] H).le_opNorm ((T : H →L[ℂ] H) τ.vector)

theorem norm₂_mul_le_right (S T : Algebra (M := M)) : τ.norm₂ (S*T) ≤ τ.norm₂ S * ‖T‖ := by
  rw [← τ.norm₂_star (S*T), star_mul]
  have h := τ.norm₂_mul_le (star T) (star S)
  simpa [τ.norm₂_star, mul_comm, ContinuousLinearMap.star_eq_adjoint] using h

theorem norm₂_le_norm (T : Algebra (M := M)) : τ.norm₂ T ≤ ‖T‖ := by
  have h := (T : H →L[ℂ] H).le_opNorm τ.vector
  simpa [norm₂, τ.norm_vector] using h

theorem norm_trace_le_norm₂ (T : Algebra (M := M)) : ‖τ.trace T‖ ≤ τ.norm₂ T := by
  simpa [trace, norm₂, τ.norm_vector] using norm_inner_le_norm τ.vector ((T : H →L[ℂ] H) τ.vector)

theorem norm₂_eq_zero_iff (T : Algebra (M := M)) : τ.norm₂ T = 0 ↔ T = 0 := by
  constructor
  · intro h
    exact τ.separating T (norm_eq_zero.mp h)
  · rintro rfl
    exact τ.norm₂_zero

end TracialRepresentation

local instance finiteTraceDecEq (G : Type*) : DecidableEq G := Classical.decEq _
/-- The actual group algebra supplies the concrete tracial data; no group
approximation, ICC, factor, or countability premise occurs. -/
def groupTracialRepresentation (G : Type*) [Group G] :
    TracialRepresentation (concreteGroupAlgebra G) where
  vector := delta G
  norm_vector := by simp [delta, lp.norm_single]
  cyclic := trace_mul_comm
  separating := delta_separating G

end

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual ultraweak topology, generated by absolutely summable vector
functionals. No continuity of a chosen trace is built into this definition. -/
@[instance_reducible] def ultraweakTopology : TopologicalSpace (H →L[ℂ] H) :=
  ⨅ (ξ : ℕ → H) (η : ℕ → H) (_ : Summable (fun n => ‖ξ n‖ * ‖η n‖)),
    TopologicalSpace.induced (fun T : H →L[ℂ] H => ∑' n, inner ℂ (ξ n) (T (η n)))
      inferInstance

variable {H}
omit [CompleteSpace H] in
theorem vectorFunctional_ultraweak_continuous (ξ η : H) :
    @Continuous _ _ (ultraweakTopology H) inferInstance
      (fun T : H →L[ℂ] H => inner ℂ ξ (T η)) := by
  let x : ℕ → H := fun n => if n = 0 then ξ else 0
  let y : ℕ → H := fun n => if n = 0 then η else 0
  have hs : Summable (fun n => ‖x n‖ * ‖y n‖) := by
    exact (hasSum_ite_eq (0 : ℕ) (‖ξ‖ * ‖η‖)).summable.congr (by intro n; by_cases h : n = 0 <;> simp [x,y,h])
  have hc : @Continuous _ _ (ultraweakTopology H) inferInstance
      (fun T : H →L[ℂ] H => ∑' n, inner ℂ (x n) (T (y n))) :=
    continuous_iInf_dom (i := x) (continuous_iInf_dom (i := y)
      (continuous_iInf_dom (i := hs) continuous_induced_dom))
  have he (T : H →L[ℂ] H) :
      (fun n => inner ℂ (x n) (T (y n))) =
        (fun n => if n = 0 then inner ℂ ξ (T η) else 0) := by
    funext n
    by_cases h : n = 0 <;> simp [x,y,h]
  have hf : (fun T : H →L[ℂ] H => ∑' n, inner ℂ (x n) (T (y n))) =
      (fun T => inner ℂ ξ (T η)) := by
    funext T
    rw [he]
    exact tsum_ite_eq 0 _
  rw [hf] at hc
  exact hc

@[instance_reducible] def algebraUltraweakTopology (M : VonNeumannAlgebra H) :
    TopologicalSpace M.toStarSubalgebra :=
  TopologicalSpace.induced (fun T : M.toStarSubalgebra => (T : H →L[ℂ] H)) (ultraweakTopology H)

/-- Vector traces are normal, expressed as continuity for the actual ultraweak topology. -/
theorem TracialRepresentation.trace_normal {M : VonNeumannAlgebra H}
    (τ : TracialRepresentation M) :
    @Continuous _ _ (algebraUltraweakTopology M) inferInstance τ.trace :=
  @Continuous.comp _ _ _ (algebraUltraweakTopology M) (ultraweakTopology H) _
    _ _ (vectorFunctional_ultraweak_continuous τ.vector τ.vector) continuous_induced_dom

end UltrapowerBridge

end

end OAI
