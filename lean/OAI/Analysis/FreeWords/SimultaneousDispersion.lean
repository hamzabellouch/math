import Mathlib
import OAI.Analysis.FreeWords.TraceTransfer
import OAI.Analysis.FreeWords.TupleHull

namespace OAI

noncomputable section

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) {ι : Type*} [Fintype ι]

end

end KKFactorSupport

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) {ι : Type*} [Fintype ι]

theorem tupleVector_norm_sq (x : ι → ConcreteAlgebra M) :
    ‖tupleVector τ x‖^2 = ∑ i, (traceNorm τ (x i))^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i hi
  change ‖gnsVector (tracePositive τ) (x i)‖^2 = _
  rw [@norm_sq_eq_re_inner ℂ,gnsVector_inner]
  have he := congrArg Complex.re (traceNorm_sq τ (x i))
  exact he.symm

omit [Fintype ι] in
theorem tupleVector_add (x y : ι → ConcreteAlgebra M) :
    tupleVector τ (fun i => x i + y i) = tupleVector τ x + tupleVector τ y := by
  ext i
  exact map_add (gnsVector (tracePositive τ)) (x i) (y i)

omit [Fintype ι] in
@[simp] theorem tupleVector_zero : tupleVector τ (fun _ : ι => 0) = 0 := by
  ext i
  exact map_zero (gnsVector (tracePositive τ))

theorem exists_simultaneous_dispersion (hM : KKFreeLiftFrontier.IsFactor M)
    (x : ι → ConcreteAlgebra M) (hx : ∀ i, τ.map (x i) = 0) :
    ∃ u : unitary (ConcreteAlgebra M),
      ∑ i, (traceNorm τ (x i + algebraConj u (x i)))^2 ≤
        3 * ∑ i, (traceNorm τ (x i))^2 := by
  let : InnerProductSpace ℝ (TupleSpace τ (ι := ι)) :=
    InnerProductSpace.rclikeToReal ℂ (TupleSpace τ (ι := ι))
  let v := tupleVector τ x
  have hz : (0 : TupleSpace τ (ι := ι)) ∈ tupleHull τ x := by
    simpa only [hx,zero_smul,tupleVector_zero] using tuple_trace_in_hull τ hM x
  have hout : ∃ u : unitary (ConcreteAlgebra M), ‖v + tupleConj τ u v‖^2 ≤ 3 * ‖v‖^2 := by
    by_cases hv : v = 0
    · exact ⟨1,by simp [hv]⟩
    · have hc : 0 < ‖v‖^2/2 := by positivity
      let c := ‖v‖^2/2
      let φ : TupleSpace τ (ι := ι) →L[ℝ] ℝ := innerSL ℝ v
      have hex : ∃ u : unitary (ConcreteAlgebra M), φ (tupleConj τ u v) ≤ c := by
        by_contra hh
        push Not at hh
        have ho : tupleOrbit τ x ⊆ φ ⁻¹' Set.Ici c := by
          rintro _ ⟨u,rfl⟩
          change c ≤ φ (tupleVector τ (fun i => algebraConj u (x i)))
          rw [← tupleConj_vector]
          exact (hh u).le
        have hcv : Convex ℝ (φ ⁻¹' Set.Ici c) :=
          (convex_Ici c).linear_preimage φ.toLinearMap
        have hall : tupleHull τ x ⊆ φ ⁻¹' Set.Ici c :=
          closure_minimal (convexHull_min ho hcv) (isClosed_Ici.preimage φ.continuous)
        have hh0 := hall hz
        change c ≤ φ 0 at hh0
        rw [map_zero] at hh0
        exact (not_le_of_gt hc) hh0
      obtain ⟨u,hu⟩ := hex
      refine ⟨u,?_⟩
      simp only [norm_add_sq_real,tupleConj_norm]
      change ⟪v,tupleConj τ u v⟫_ℝ ≤ ‖v‖^2/2 at hu
      linarith only [hu]
  obtain ⟨u,hu⟩ := hout
  refine ⟨u,?_⟩
  simpa only [v,tupleConj_vector,← tupleVector_add,tupleVector_norm_sq] using hu

end

end KKFactorSupport
end

end OAI
