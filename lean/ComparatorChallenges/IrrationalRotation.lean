import Mathlib

namespace OAI

section
noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

abbrev Circle := AddCircle (1 : ℝ)

def circleMeasure : Measure Circle := volume

def negLogCost (t : ℝ) : ℝ≥0∞ :=
  if t = 0 then ∞ else ENNReal.ofReal (-Real.log |t|)

def HasNegInfiniteLogIntegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) : Prop :=
  (∫⁻ x, negLogCost (f x) ∂μ) = ∞

def scalarWeightDeterminant {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) : ℝ≥0∞ :=
  EReal.exp (-((∫⁻ x, negLogCost (f x) ∂μ) : EReal))

def NormQuasinilpotent {A : Type*} [NormedRing A] (T : A) : Prop :=
  Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)

def IsContinuousCircleWeight (f : Circle → ℝ) : Prop :=
  Continuous f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
    (∀ x, f x = 0 ↔ x = 0) ∧ HasNegInfiniteLogIntegral circleMeasure f

end Invariant233

end
end

section
noncomputable section
open scoped ENNReal
namespace Invariant233.WeightedShift

abbrev Hilbert := lp (fun _ : ℤ => ℂ) 2
abbrev Weight := lp (fun _ : ℤ => ℂ) ∞

def reindex (e : Equiv.Perm ℤ) : Hilbert ≃ₗᵢ[ℂ] Hilbert where
  toFun ξ := ⟨fun k => ξ (e k), memℓp_gen <|
    (e.summable_iff).2 ((lp.memℓp ξ).summable (by norm_num))⟩
  invFun ξ := ⟨fun k => ξ (e.symm k), memℓp_gen <|
    (e.symm.summable_iff).2 ((lp.memℓp ξ).summable (by norm_num))⟩
  left_inv ξ := by ext k; simp
  right_inv ξ := by ext k; simp
  map_add' ξ η := by ext k; rfl
  map_smul' c ξ := by ext k; rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun k => ‖ξ k‖ ^ (2 : ENNReal).toReal)

def shift (m : ℤ) : Hilbert ≃ₗᵢ[ℂ] Hilbert := reindex (Equiv.addRight (-m))

def diagonal (w : Weight) : Hilbert →L[ℂ] Hilbert :=
  lp.mapCLM 2 (fun k => w k • ContinuousLinearMap.id ℂ ℂ) (norm_nonneg w)
    (fun k => by
      let : T0Space ℂ := @MetricSpace.instT0Space ℂ Complex.instNormedAddCommGroup.toMetricSpace
      simpa [norm_smul] using lp.norm_apply_le_norm (by simp) w k)

def diagonalAlgHom : Weight →ₐ[ℂ] (Hilbert →L[ℂ] Hilbert) where
  toFun := diagonal
  map_one' := by
    ext ξ k
    change (1 : ℂ) * ξ k = ξ k
    exact one_mul _
  map_mul' w v := by
    ext ξ k
    change (w k * v k) * ξ k = w k * (v k * ξ k)
    exact mul_assoc _ _ _
  map_zero' := by
    ext ξ k
    change (0 : ℂ) * ξ k = 0
    exact zero_mul _
  map_add' w v := by
    ext ξ k
    change (w k + v k) * ξ k = w k * ξ k + v k * ξ k
    exact add_mul _ _ _
  commutes' c := by
    ext ξ k
    change c * ξ k = c * ξ k
    rfl

def translate (w : Weight) (m : ℤ) : Weight :=
  ⟨fun k => w (k + m), memℓp_infty <| by
    refine ⟨‖w‖, ?_⟩
    rintro r ⟨k, rfl⟩
    exact lp.norm_apply_le_norm (by simp) w (k + m)⟩

def operator (w : Weight) : Hilbert →L[ℂ] Hilbert :=
  (shift 1).toLinearIsometry.toContinuousLinearMap.comp (diagonal w)

def orbitProduct (w : Weight) (n : ℕ) : Weight :=
  ⟨fun k => ∏ j ∈ Finset.range n, w (k + j), memℓp_infty <| by
    refine ⟨‖w‖ ^ n, ?_⟩
    rintro r ⟨k, rfl⟩
    calc
      ‖∏ j ∈ Finset.range n, w (k + j)‖ ≤
          ∏ j ∈ Finset.range n, ‖w (k + j)‖ := le_of_eq (norm_prod _ _)
      _ ≤ ∏ _j ∈ Finset.range n, ‖w‖ := by
        apply Finset.prod_le_prod₀
        · intro j hj; exact norm_nonneg _
        · intro j hj; exact lp.norm_apply_le_norm (by simp) w _
      _ = ‖w‖ ^ n := by simp⟩

def tailWeight (m : ℤ) : Weight :=
  ⟨fun k => if m ≤ k then 1 else 0, memℓp_infty <| by
    refine ⟨1, ?_⟩
    rintro r ⟨k, rfl⟩
    by_cases h : m ≤ k <;> simp [h]⟩

def tailProjection (m : ℤ) : Hilbert →L[ℂ] Hilbert := diagonal (tailWeight m)

end Invariant233.WeightedShift

end
end

section
open scoped Pointwise

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local instance instStarModuleGenerated : StarModule ℂ (H →L[ℂ] H) :=
  ContinuousLinearMap.instStarModuleId

noncomputable def vonNeumannGenerated (s : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra :=
    StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) :
        Set (H →L[ℂ] H))) = _
    rw [StarSubalgebra.coe_centralizer_centralizer]
    rw [Set.centralizer_centralizer_centralizer]
    exact (StarSubalgebra.coe_centralizer_centralizer ℂ s).symm

end Invariant233

end

section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal lp Topology

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem diagonal_value (w : Weight) (v : Hilbert) (i : ℤ) :
    diagonal w v i = w i * v i := rfl

theorem diagonal_bound (w : Weight) (C : ℝ) (hw : ‖w‖ ≤ C) (v : Hilbert) :
    ‖diagonal w v‖ ≤ C * ‖v‖ := by
  apply (diagonal w).le_of_opNorm_le
  exact (lp.norm_mapCLM_le 2 _ (norm_nonneg w) _).trans hw

theorem diagonal_aestronglyMeasurable (a : X → Weight) (C : ℝ) (_hC : 0 ≤ C)
    (_ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)
    {f : X → Hilbert} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => diagonal (a x) (f x)) μ := by
  classical
  let : Nonempty (Finset ℤ) := ⟨∅⟩
  let F : Finset ℤ → X → Hilbert :=
    fun s => ∑ i ∈ s, fun x => lp.single 2 i (a x i * f x i)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ℤ))
    (f := F)
  · intro s
    apply Finset.aestronglyMeasurable_sum
    intro i hi
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 i).continuous.comp_aestronglyMeasurable
      ((hm i).mul ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 i).continuous.comp_aestronglyMeasurable hf))
  · apply Filter.Eventually.of_forall
    intro x
    simpa only [F, Finset.sum_apply, diagonal_value, HasSum, SummationFilter.unconditional] using
      lp.hasSum_single (by norm_num) (diagonal (a x) (f x))

def fieldDiagonalVec (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)
    (f : Lp (Hilbert) 2 μ) : Lp (Hilbert) 2 μ :=
  ((Lp.memLp f).of_le_mul
    (diagonal_aestronglyMeasurable a C hC ha hm (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => diagonal_bound (a x) C (ha x) (f x))).toLp _

theorem fieldDiagonalVec_ae (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)
    (f : Lp (Hilbert) 2 μ) :
    fieldDiagonalVec a C hC ha hm f =ᵐ[μ]
      fun x => diagonal (a x) (f x) :=
  MemLp.coeFn_toLp _

def fieldDiagonalLinear (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ) :
    Lp (Hilbert) 2 μ →ₗ[ℂ] Lp (Hilbert) 2 μ where
  toFun := fieldDiagonalVec a C hC ha hm
  map_add' f g := by
    apply Lp.ext
    filter_upwards [fieldDiagonalVec_ae a C hC ha hm (f + g),
      fieldDiagonalVec_ae a C hC ha hm f, fieldDiagonalVec_ae a C hC ha hm g,
      Lp.coeFn_add f g, Lp.coeFn_add
        (fieldDiagonalVec a C hC ha hm f) (fieldDiagonalVec a C hC ha hm g)]
      with x hfg hf hg hsum hout
    simp only [Pi.add_apply] at hsum hout
    rw [hfg, hout, hf, hg, hsum, map_add]
  map_smul' c f := by
    change fieldDiagonalVec a C hC ha hm (c • f) = c • fieldDiagonalVec a C hC ha hm f
    apply Lp.ext
    filter_upwards [fieldDiagonalVec_ae a C hC ha hm (c • f),
      fieldDiagonalVec_ae a C hC ha hm f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (fieldDiagonalVec a C hC ha hm f)] with x hcf hf hsmul hout
    simp only [Pi.smul_apply] at hsmul hout
    rw [hcf, hout, hf, hsmul, map_smul]

def fieldDiagonal (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ) :
    Lp (Hilbert) 2 μ →L[ℂ] Lp (Hilbert) 2 μ :=
  (fieldDiagonalLinear a C hC ha hm).mkContinuous C (by
    intro f
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    change ∀ᵐ x ∂μ, ‖fieldDiagonalVec a C hC ha hm f x‖ ≤ C * ‖f x‖
    filter_upwards [fieldDiagonalVec_ae a C hC ha hm f] with x hx
    rw [hx]
    exact diagonal_bound (a x) C (ha x) (f x))

end Invariant233.WeightedShift

end
end

section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.Rotation

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

instance circleMeasure_probability : IsProbabilityMeasure circleMeasure := by
  constructor
  change volume (Set.univ : Set Circle) = 1
  exact UnitAddCircle.measure_univ

abbrev Fiber := WeightedShift.Hilbert
abbrev Hilbert := MeasureTheory.Lp Fiber 2 circleMeasure

def action (θ : ℝ) (k : ℤ) (x : Circle) : Circle :=
  x + k • (θ : Circle)

def U : Hilbert →L[ℂ] Hilbert :=
  (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 circleMeasure

def orbitWeight (θ : ℝ) (a : C(Circle, ℂ)) (x : Circle) : WeightedShift.Weight :=
  ⟨fun k => a (action θ k x), memℓp_infty <| by
    refine ⟨‖a‖, ?_⟩
    rintro r ⟨k, rfl⟩
    exact a.norm_coe_le_norm _⟩

def character : C(Circle, ℂ) := fourier 1

def representation (θ : ℝ) (a : C(Circle, ℂ)) : Hilbert →L[ℂ] Hilbert :=
  WeightedShift.fieldDiagonal (orbitWeight θ a) ‖a‖ (norm_nonneg a)
    (fun x => lp.norm_le_of_forall_le (norm_nonneg a) (fun k => a.norm_coe_le_norm _))
    (fun k => by
      let : T0Space ℝ := @MetricSpace.instT0Space ℝ Real.metricSpace
      let : T0Space ℂ := @MetricSpace.instT0Space ℂ Complex.instNormedAddCommGroup.toMetricSpace
      change AEStronglyMeasurable (fun x : Circle => a (x + k • (θ : Circle))) circleMeasure
      exact (a.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)

def V (θ : ℝ) : Hilbert →L[ℂ] Hilbert := representation θ character

def algebra (θ : ℝ) : VonNeumannAlgebra Hilbert :=
  vonNeumannGenerated ({U, V θ} : Set (Hilbert →L[ℂ] Hilbert))

def weighted (θ : ℝ) (a : C(Circle, ℂ)) : Hilbert →L[ℂ] Hilbert :=
  U * representation θ a

def complexWeight (f : C(Circle, ℝ)) : C(Circle, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

def weightedReal (θ : ℝ) (f : C(Circle, ℝ)) : Hilbert →L[ℂ] Hilbert :=
  weighted θ (complexWeight f)

def vacuum : Hilbert := Lp.const 2 circleMeasure (lp.single 2 (0 : ℤ) (1 : ℂ))

def vacuumFunctional (T : Hilbert →L[ℂ] Hilbert) : ℂ := inner ℂ vacuum (T vacuum)

end Invariant233.Rotation

end
end

section
noncomputable section
namespace Invariant233

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def HasOnlyTrivialInvariantProjections (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) : Prop :=
  ∀ p : H →L[ℂ] H, p ∈ M → IsStarProjection p →
    (1 - p) * T * p = 0 → p = 0 ∨ p = 1

def IsProjectionAtom (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) : Prop :=
  p ∈ M ∧ IsStarProjection p ∧ p ≠ 0 ∧
    ∀ q : H →L[ℂ] H, q ∈ M → IsStarProjection q → q * p = q →
      q = 0 ∨ q = p

def IsAtomicVonNeumannAlgebra (M : VonNeumannAlgebra H) : Prop :=
  ∀ p : H →L[ℂ] H, p ∈ M → IsStarProjection p → p ≠ 0 →
    ∃ q : H →L[ℂ] H, IsProjectionAtom M q ∧ q * p = q

def IsAbelianVonNeumannAlgebra (M : VonNeumannAlgebra H) : Prop :=
  ∀ A B : H →L[ℂ] H, A ∈ M → B ∈ M → Commute A B

def IsDiffuseVonNeumannAlgebra (M : VonNeumannAlgebra H) : Prop :=
  ∀ p : H →L[ℂ] H, ¬ IsProjectionAtom M p

def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  Nontrivial H ∧ ∀ A : H →L[ℂ] H, A ∈ M →
    (∀ B : H →L[ℂ] H, B ∈ M → Commute A B) →
      ∃ c : ℂ, A = c • (1 : H →L[ℂ] H)

def vectorTrace (ξ : H) (A : H →L[ℂ] H) : ℂ :=
  @inner ℂ H InnerProductSpace.toInner ξ (A ξ)

def IsFaithfulTracialVector (M : VonNeumannAlgebra H) (ξ : H) : Prop :=
  ‖ξ‖ = 1 ∧
    (∀ A B : H →L[ℂ] H, A ∈ M → B ∈ M →
      vectorTrace ξ (A * B) = vectorTrace ξ (B * A)) ∧
    (∀ A : H →L[ℂ] H, A ∈ M → A.IsPositive →
      vectorTrace ξ A = 0 → A = 0)

def IsTypeII1FactorWithVector (M : VonNeumannAlgebra H) (ξ : H) : Prop :=
  IsFactor M ∧ IsDiffuseVonNeumannAlgebra M ∧ IsFaithfulTracialVector M ξ

local instance instNormedAlgebraPredual : NormedAlgebra ℂ (H →L[ℂ] H) :=
  ContinuousLinearMap.toNormedAlgebra

def HasSeparablePredual (M : VonNeumannAlgebra H) : Prop :=
  ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X)
    (_ : CompleteSpace X) (_ : TopologicalSpace.SeparableSpace X),
    Nonempty (StrongDual ℂ X ≃ₗᵢ[ℂ] M.toStarSubalgebra)

end Invariant233

end
end

section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Invariant233

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

structure TracialState (A : Type*) [CStarAlgebra A] where
  toContinuousLinearMap : A →L[ℂ] ℂ
  map_one : toContinuousLinearMap 1 = 1
  map_star : ∀ a, toContinuousLinearMap (star a) = star (toContinuousLinearMap a)
  positive : ∀ a, 0 ≤ (toContinuousLinearMap (star a * a)).re
  tracial : ∀ a b, toContinuousLinearMap (a * b) = toContinuousLinearMap (b * a)

namespace TracialState

variable {A : Type*} [CStarAlgebra A]

instance : CoeFun (TracialState A) (fun _ => A → ℂ) :=
  ⟨fun τ => τ.toContinuousLinearMap⟩

end TracialState

def fugledeKadisonDeterminant {A : Type*} [CStarAlgebra A]
    (τ : TracialState A) (a : A) : ℝ≥0∞ :=
  ⨅ ε : {r : ℝ // 0 < r},
    ENNReal.ofReal (Real.exp ((τ (CFC.log (star a * a + (ε.val : ℝ) • (1 : A)))).re / 2))

def logarithmicPotentialDeterminant (μ : Measure ℂ) (z : ℂ) : ℝ≥0∞ :=
  ⨅ ε : {r : ℝ // 0 < r},
    ENNReal.ofReal (Real.exp ((∫ w, Real.log (‖w - z‖ ^ 2 + ε.val) ∂μ) / 2))

def IsBrownMeasure {A : Type*} [CStarAlgebra A]
    (τ : TracialState A) (a : A) (μ : Measure ℂ) : Prop :=
  IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
    ∀ z : ℂ, fugledeKadisonDeterminant τ (a - algebraMap ℂ A z) =
      logarithmicPotentialDeterminant μ z

end Invariant233

end
end

section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def vectorFugledeKadisonDeterminant (ξ : H) (T : H →L[ℂ] H) : ℝ≥0∞ :=
  ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
    (Real.exp ((vectorTrace ξ (CFC.log (star T * T + ε.val • (1 : H →L[ℂ] H)))).re / 2))

def IsVectorBrownMeasure (ξ : H) (T : H →L[ℂ] H) (μ : Measure ℂ) : Prop :=
  IsProbabilityMeasure μ ∧ IsCompact μ.support ∧ ∀ z : ℂ,
    vectorFugledeKadisonDeterminant ξ (T - z • (1 : H →L[ℂ] H)) =
      logarithmicPotentialDeterminant μ z

def operatorModulus (T : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (star T * T)

def HasCountablyAtomicSpectralType (B : H →L[ℂ] H) : Prop :=
  ∃ S : Set ℂ, S.Countable ∧
    (⨆ z : S, Module.End.eigenspace B.toLinearMap z.val).topologicalClosure = ⊤

def polarConjugate (U B : H →L[ℂ] H) (n : ℤ) : H →L[ℂ] H :=
  if 0 ≤ n then U ^ n.toNat * B * star U ^ n.toNat
  else star U ^ (-n).toNat * B * U ^ (-n).toNat

def finitePolarAlgebra (U B : H →L[ℂ] H) (F : Finset ℤ) : VonNeumannAlgebra H :=
  vonNeumannGenerated {A | ∃ n ∈ F, A = polarConjugate U B n}

def fullPolarAlgebra (U B : H →L[ℂ] H) : VonNeumannAlgebra H :=
  vonNeumannGenerated (Set.range (polarConjugate U B))

def ProductPolarStructure (U T : H →L[ℂ] H) : Prop :=
  star U * U = 1 ∧ U * star U = 1 ∧ T = U * operatorModulus T ∧
    Function.Injective (operatorModulus T) ∧ HasCountablyAtomicSpectralType (operatorModulus T) ∧
    (∀ F : Finset ℤ,
      IsAbelianVonNeumannAlgebra (finitePolarAlgebra U (operatorModulus T) F) ∧
      IsAtomicVonNeumannAlgebra (finitePolarAlgebra U (operatorModulus T) F)) ∧
    IsAbelianVonNeumannAlgebra (fullPolarAlgebra U (operatorModulus T)) ∧
    IsDiffuseVonNeumannAlgebra (fullPolarAlgebra U (operatorModulus T))

end Invariant233

end
end

section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def circleRepresentative (x : Circle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 x).val

instance circleMeasure_probability : IsProbabilityMeasure circleMeasure := by
  constructor
  simp [circleMeasure, Circle, AddCircle.measure_univ]

namespace ProductModel

abbrev Base := ℕ → Circle

def baseMeasure : Measure Base := Measure.infinitePi (fun _ : ℕ => circleMeasure)

instance baseMeasure_probability : IsProbabilityMeasure baseMeasure := by
  unfold baseMeasure
  infer_instance

def Ordered (x y : Base) : Prop :=
  ∀ i, circleRepresentative (x i) ≤ circleRepresentative (y i)

def rotation (θ : ℕ → ℝ) (x : Base) : Base :=
  fun i => x i + (θ i : Circle)

def rotationIterate (θ : ℕ → ℝ) (k : ℤ) (x : Base) : Base :=
  fun i => x i + ((k : ℝ) * θ i : ℝ)

def logarithmicCost (θ c : ℕ → ℝ) (x : Base) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (c i * (⌊circleRepresentative (x i) + θ i⌋ : ℤ))

def weight (θ c : ℕ → ℝ) (x : Base) : ℝ :=
  (EReal.exp (-(logarithmicCost θ c x : EReal))).toReal

def JointlyRationallyIndependent (θ : ℕ → ℝ) : Prop :=
  LinearIndependent ℚ (fun i : Option ℕ => i.elim 1 θ)

def AdmissibleAnglesAndCosts (θ c : ℕ → ℝ) : Prop :=
  (∀ i, 0 < θ i ∧ θ i < 1 ∧ 0 < c i) ∧
    Summable θ ∧ JointlyRationallyIndependent θ

abbrev Fiber := @lp ℤ (fun _ => ℂ) (fun _ => Complex.instNormedAddCommGroup) 2
abbrev Hilbert :=
  @MeasureTheory.Lp Base Fiber MeasurableSpace.pi
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) fact_one_le_two_ennreal)
    2 baseMeasure

end ProductModel
end Invariant233

end
end

section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233.ProductModel

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

theorem measurable_rep : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (T := (1 : ℝ)) 0).measurable

theorem measurable_iterate (θ : ℕ → ℝ) (k : ℤ) :
    Measurable (rotationIterate θ k) := by
  let : T0Space ℝ := @MetricSpace.instT0Space ℝ Real.metricSpace
  let : BorelSpace Circle := QuotientAddGroup.borelSpace
  let : ContinuousAdd Circle :=
    (QuotientAddGroup.instIsTopologicalAddGroup (AddSubgroup.zmultiples (1 : ℝ))).toContinuousAdd
  let : MeasurableAdd Circle := ContinuousAdd.measurableAdd
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply i).add_const _

theorem measurable_cost (θ c : ℕ → ℝ) : Measurable (logarithmicCost θ c) := by
  apply Measurable.tsum
  intro i
  have hm : Measurable (fun x : Base => circleRepresentative (x i) + θ i) :=
    (measurable_rep.comp (measurable_pi_apply i)).add_const (θ i)
  have hc : Measurable (fun x : Base => (⌊circleRepresentative (x i) + θ i⌋ : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hm.floor
  exact (measurable_const.mul hc).ennreal_ofReal

theorem weight_measurable (θ c : ℕ → ℝ) : Measurable (weight θ c) := by
  exact (measurable_cost θ c).coe_ereal_ennreal.neg.ereal_exp.ennreal_toReal

theorem weight_nonneg (θ c : ℕ → ℝ) (x : Base) : 0 ≤ weight θ c x :=
  ENNReal.toReal_nonneg

theorem weight_le_one (θ c : ℕ → ℝ) (x : Base) : weight θ c x ≤ 1 := by
  have h : EReal.exp (-(logarithmicCost θ c x : EReal)) ≤ 1 := by
    rw [← EReal.exp_zero]
    apply EReal.exp_le_exp_iff.mpr
    exact EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg (logarithmicCost θ c x))
  exact (ENNReal.toReal_mono (by simp) h).trans (by simp)

def shiftOperator : Hilbert →L[ℂ] Hilbert :=
  (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 baseMeasure

def multiplierField (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ)
    (hb : ∀ x, ‖g x‖ ≤ C) (x : Base) : WeightedShift.Weight :=
  ⟨fun k => g (rotationIterate θ k x), memℓp_infty <| by
    refine ⟨C, ?_⟩
    rintro r ⟨k, rfl⟩
    exact hb _⟩

def multiplier (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) : Hilbert →L[ℂ] Hilbert :=
  WeightedShift.fieldDiagonal (multiplierField θ g C hb) C hC
    (fun _x => lp.norm_le_of_forall_le hC (fun _k => hb _))
    (fun k => (hg.comp (measurable_iterate θ k)).aestronglyMeasurable)

def multiplierGenerators (θ : ℕ → ℝ) : Set (Hilbert →L[ℂ] Hilbert) :=
  {A | ∃ (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g)
    (hb : ∀ x, ‖g x‖ ≤ C), A = multiplier θ g C hC hg hb}

def factor (θ : ℕ → ℝ) : VonNeumannAlgebra Hilbert :=
  vonNeumannGenerated ({shiftOperator} ∪ multiplierGenerators θ)

def traceVector : Hilbert := Lp.const 2 baseMeasure (lp.single 2 0 (1 : ℂ))

theorem measurable_complexWeight (θ c : ℕ → ℝ) :
    Measurable (fun x => (weight θ c x : ℂ)) :=
  (weight_measurable θ c).complex_ofReal

theorem norm_complexWeight_le_one (θ c : ℕ → ℝ) (x : Base) :
    ‖(weight θ c x : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg θ c x)]
    using weight_le_one θ c x

local instance instNormedAddCommGroupProductWeightedOperator : NormedAddCommGroup Hilbert :=
  @MeasureTheory.Lp.instNormedAddCommGroup Base Fiber MeasurableSpace.pi 2 baseMeasure
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) fact_one_le_two_ennreal)
    fact_one_le_two_ennreal

local instance instInnerProductSpaceProductWeightedOperator :
    @InnerProductSpace ℂ Hilbert Complex.instRCLike
      instNormedAddCommGroupProductWeightedOperator.toSeminormedAddCommGroup :=
  @MeasureTheory.L2.innerProductSpace Base Fiber ℂ Complex.instRCLike MeasurableSpace.pi
    baseMeasure
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) fact_one_le_two_ennreal)
    (@lp.instInnerProductSpace ℤ ℂ Complex.instRCLike (fun _ => ℂ)
      (fun _ => Complex.instNormedAddCommGroup)
      (fun _ => @RCLike.innerProductSpace ℂ Complex.instRCLike))

local instance instTopologicalSpaceProductWeightedOperator : TopologicalSpace Hilbert :=
  instNormedAddCommGroupProductWeightedOperator.toUniformSpace.toTopologicalSpace

local instance instAddCommMonoidProductWeightedOperator : AddCommMonoid Hilbert :=
  instNormedAddCommGroupProductWeightedOperator.toAddCommGroup.toAddCommMonoid

local instance instModuleProductWeightedOperator : Module ℂ Hilbert :=
  instInnerProductSpaceProductWeightedOperator.toNormedSpace.toModule

local notation "weightedOperatorSemiring" =>
  Complex.instNormedField.toField.toCommRing.toRing.toSemiring

local notation "weightedOperatorScalarIdentity" =>
  @RingHom.id ℂ (@Semiring.toNonAssocSemiring ℂ weightedOperatorSemiring)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def weightedOperator (θ c : ℕ → ℝ) :
    @ContinuousLinearMap ℂ ℂ weightedOperatorSemiring weightedOperatorSemiring
      weightedOperatorScalarIdentity
      Hilbert instTopologicalSpaceProductWeightedOperator instAddCommMonoidProductWeightedOperator
      Hilbert instTopologicalSpaceProductWeightedOperator instAddCommMonoidProductWeightedOperator
      instModuleProductWeightedOperator instModuleProductWeightedOperator :=
  let compose := fun (Scalar : Type) [Semiring Scalar] (Space : Type)
      [TopologicalSpace Space] [AddCommMonoid Space] [Module Scalar Space]
      (left right : Space →L[Scalar] Space) => left ∘L right
  @compose ℂ weightedOperatorSemiring Hilbert instTopologicalSpaceProductWeightedOperator
    instAddCommMonoidProductWeightedOperator instModuleProductWeightedOperator
    shiftOperator (multiplier θ (fun x => (weight θ c x : ℂ)) 1 zero_le_one
      (measurable_complexWeight θ c) (norm_complexWeight_le_one θ c))

end Invariant233.ProductModel

end
end

section
noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

abbrev EndpointPair := Base × Base

def selectedEndpoint (I : Finset ℕ) (x z : Base) : Base :=
  fun i => if i ∈ I then z i else x i

def triangularEvent (I : Finset ℕ) : Set EndpointPair :=
  {xz | ∀ i ∈ I, circleRepresentative (xz.1 i) < circleRepresentative (xz.2 i)}

def triangularLaw (I : Finset ℕ) : Measure EndpointPair :=
  Measure.map (fun xz : EndpointPair => (xz.1, selectedEndpoint I xz.1 xz.2))
    ((baseMeasure.prod baseMeasure).restrict (triangularEvent I))

def triangularFirstDensity (I : Finset ℕ) (x : Base) : ℝ :=
  ∏ i ∈ I, (1 - circleRepresentative (x i))

def triangularSecondDensity (I : Finset ℕ) (y : Base) : ℝ :=
  ∏ i ∈ I, circleRepresentative (y i)

def TriangularLawProperties (I : Finset ℕ) : Prop :=
  IsFiniteMeasure (triangularLaw I) ∧
  triangularLaw I Set.univ = (1 / 2 : ℝ≥0∞) ^ I.card ∧
  (triangularLaw I).map Prod.fst =
    baseMeasure.withDensity (fun x => ENNReal.ofReal (triangularFirstDensity I x)) ∧
  (triangularLaw I).map Prod.snd =
    baseMeasure.withDensity (fun y => ENNReal.ofReal (triangularSecondDensity I y)) ∧
  (∀ᵐ xy ∂triangularLaw I, Ordered xy.1 xy.2) ∧
  (∀ x, 0 ≤ triangularFirstDensity I x ∧ triangularFirstDensity I x ≤ 1) ∧
  (∀ y, 0 ≤ triangularSecondDensity I y ∧ triangularSecondDensity I y ≤ 1)

def WeaklyConverges (η : ℕ → Measure EndpointPair) (ν : Measure EndpointPair) : Prop :=
  ∀ φ : C(EndpointPair, ℝ),
    Tendsto (fun l => ∫ xy, φ xy ∂η l) atTop (𝓝 (∫ xy, φ xy ∂ν))

def SupportedOnPositiveOrderedOrbitPairs (θ : ℕ → ℝ) (η : Measure EndpointPair) : Prop :=
  ∃ N : Finset ℕ, (∀ n ∈ N, 0 < n) ∧
    ∀ᵐ xy ∂η, Ordered xy.1 xy.2 ∧
      ∃ n ∈ N, xy.2 = rotationIterate θ (n : ℤ) xy.1

def HasUniformL2Marginals (η : ℕ → Measure EndpointPair) : Prop :=
  ∃ H : ℝ, 0 ≤ H ∧ ∀ l, ∃ f g : Lp ℝ 2 baseMeasure,
    (∀ᵐ x ∂baseMeasure, 0 ≤ f x) ∧ (∀ᵐ y ∂baseMeasure, 0 ≤ g y) ∧
    (η l).map Prod.fst = baseMeasure.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    (η l).map Prod.snd = baseMeasure.withDensity (fun y => ENNReal.ofReal (g y)) ∧
    ‖f‖ ≤ H ∧ ‖g‖ ≤ H

def OrderedOrbitSampling (θ : ℕ → ℝ) (I : Finset ℕ) : Prop :=
  ∃ η : ℕ → Measure EndpointPair,
    (∀ l, IsFiniteMeasure (η l)) ∧
    (∀ l, SupportedOnPositiveOrderedOrbitPairs θ (η l)) ∧
    HasUniformL2Marginals η ∧ WeaklyConverges η (triangularLaw I)

def HasAllFiniteCoordinateSampling (θ : ℕ → ℝ) : Prop :=
  ∀ I : Finset ℕ, OrderedOrbitSampling θ I

end Invariant233.ProductModel

end
end

section
noncomputable section
open MeasureTheory
namespace Invariant233.ProductModel

def IsCovariantFieldRepresentation (θ : ℕ → ℝ) (A : Hilbert →L[ℂ] Hilbert)
    (F : Base → Fiber →L[ℂ] Fiber) (B : ℝ) : Prop :=
  0 ≤ B ∧ (∀ x, ‖F x‖ ≤ B) ∧
    (∀ v : Fiber, StronglyMeasurable (fun x => F x v)) ∧
    (∀ f : Hilbert, A f =ᵐ[baseMeasure] fun x => F x (f x)) ∧
    (∀ᵐ x ∂baseMeasure,
      F (rotation θ x) =
        (WeightedShift.shift (-1)).toLinearIsometry.toContinuousLinearMap * F x *
          (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap)

def centralDiagonalIntegral (F : Base → Fiber →L[ℂ] Fiber) : ℂ :=
  ∫ x, inner ℂ (lp.single 2 0 (1 : ℂ) : Fiber)
    (F x (lp.single 2 0 (1 : ℂ) : Fiber)) ∂baseMeasure

end Invariant233.ProductModel

end
end

namespace Invariant233

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def Rotation.IsContinuousCounterexample (θ : ℝ) (f : C(Circle, ℝ)) : Prop :=
  IsContinuousCircleWeight f ∧
    let operator : Rotation.Hilbert →L[ℂ] Rotation.Hilbert := Rotation.weightedReal θ f
    let factor : VonNeumannAlgebra Rotation.Hilbert := Rotation.algebra θ
    operator ∈ factor ∧
    HasOnlyTrivialInvariantProjections (H := Rotation.Hilbert) factor operator ∧
    operator ≠ 0 ∧
    NormQuasinilpotent (A := Rotation.Hilbert →L[ℂ] Rotation.Hilbert) operator ∧
    vectorFugledeKadisonDeterminant (H := Rotation.Hilbert) Rotation.vacuum operator = 0

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

local instance ProductModel.instFactOneLeTwoCounterexample :
    Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

abbrev ProductModel.CounterexampleFiber : Type :=
  @lp ℤ (fun _ => ℂ) (fun _ => Complex.instNormedAddCommGroup) 2

abbrev ProductModel.CounterexampleHilbert : Type :=
  @MeasureTheory.Lp ProductModel.Base ProductModel.CounterexampleFiber MeasurableSpace.pi
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) ProductModel.instFactOneLeTwoCounterexample)
    2 ProductModel.baseMeasure

instance ProductModel.instCompleteSpaceHilbertCounterexample :
    CompleteSpace ProductModel.CounterexampleHilbert := inferInstance

def ProductOperatorProperties {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (factor : VonNeumannAlgebra H)
    (traceVector : H) (shift operator : H →L[ℂ] H) : Prop :=
  IsTypeII1FactorWithVector factor traceVector ∧
    HasSeparablePredual factor ∧
    operator ∈ factor ∧ operator ≠ 0 ∧
    NormQuasinilpotent operator ∧
    vectorFugledeKadisonDeterminant traceVector operator = 0 ∧
    spectrum ℂ operator = {0} ∧
    IsVectorBrownMeasure traceVector operator (MeasureTheory.Measure.dirac 0) ∧
    HasOnlyTrivialInvariantProjections factor operator ∧
    ProductPolarStructure shift operator

@[instance_reducible]
noncomputable def ProductModel.counterexampleHilbertNormedAddCommGroup :
    NormedAddCommGroup ProductModel.CounterexampleHilbert :=
  @MeasureTheory.Lp.instNormedAddCommGroup ProductModel.Base ProductModel.CounterexampleFiber
    MeasurableSpace.pi 2 ProductModel.baseMeasure
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) ProductModel.instFactOneLeTwoCounterexample)
    ProductModel.instFactOneLeTwoCounterexample

@[instance_reducible]
noncomputable def ProductModel.counterexampleHilbertInnerProductSpace :
    @InnerProductSpace ℂ ProductModel.CounterexampleHilbert Complex.instRCLike
      ProductModel.counterexampleHilbertNormedAddCommGroup.toSeminormedAddCommGroup :=
  @MeasureTheory.L2.innerProductSpace ProductModel.Base ProductModel.CounterexampleFiber ℂ
    Complex.instRCLike MeasurableSpace.pi ProductModel.baseMeasure
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) ProductModel.instFactOneLeTwoCounterexample)
    (@lp.instInnerProductSpace ℤ ℂ Complex.instRCLike (fun _ => ℂ)
      (fun _ => Complex.instNormedAddCommGroup)
      (fun _ => @RCLike.innerProductSpace ℂ Complex.instRCLike))

def ProductModel.HasCounterexampleOperator (θ c : ℕ → ℝ) : Prop :=
  @ProductOperatorProperties ProductModel.CounterexampleHilbert
    ProductModel.counterexampleHilbertNormedAddCommGroup
    ProductModel.counterexampleHilbertInnerProductSpace
    ProductModel.instCompleteSpaceHilbertCounterexample (ProductModel.factor θ)
    ProductModel.traceVector ProductModel.shiftOperator (ProductModel.weightedOperator θ c)

def ProductModel.IsCounterexampleRealization (θ c : ℕ → ℝ) : Prop :=
  ProductModel.AdmissibleAnglesAndCosts θ c ∧
    ProductModel.HasAllFiniteCoordinateSampling θ ∧
    Filter.Eventually (fun x : ProductModel.Base => 0 < ProductModel.weight θ c x)
      (@MeasureTheory.ae ProductModel.Base
        (@MeasureTheory.Measure ProductModel.Base MeasurableSpace.pi)
        MeasureTheory.Measure.instFunLike MeasureTheory.Measure.instOuterMeasureClass
        ProductModel.baseMeasure) ∧
    @HasNegInfiniteLogIntegral ProductModel.Base MeasurableSpace.pi
      ProductModel.baseMeasure (ProductModel.weight θ c) ∧
    ProductModel.HasCounterexampleOperator θ c

end Invariant233

namespace Invariant233.Results

theorem prescribed_irrational_counterexample (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hθ : Irrational θ) :
    ∃ f : C(Circle, ℝ), Rotation.IsContinuousCounterexample θ f := by
  sorry

theorem product_realization :
    ∃ θ c : ℕ → ℝ, ProductModel.IsCounterexampleRealization θ c := by
  sorry

end Invariant233.Results

end OAI
