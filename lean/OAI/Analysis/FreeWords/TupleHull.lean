import Mathlib
import OAI.Analysis.FreeWords.FactorStructure

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

abbrev TupleSpace := PiLp 2 (fun _ : ι => (tracePositive τ).GNS)

def tupleVector (x : ι → ConcreteAlgebra M) : TupleSpace τ (ι := ι) :=
  WithLp.toLp 2 (fun i => gnsVector (tracePositive τ) (x i))

def tupleConj (u : unitary (ConcreteAlgebra M)) : TupleSpace τ (ι := ι) →L[ℂ] TupleSpace τ (ι := ι) :=
  (PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (gnsConj (tracePositive τ) (tracePositive_tracial τ) u).comp (PiLp.proj 2 _ i)))

def tupleOrbit (x : ι → ConcreteAlgebra M) : Set (TupleSpace τ (ι := ι)) :=
  Set.range (fun u : unitary (ConcreteAlgebra M) => tupleVector τ (fun i => algebraConj u (x i)))

def tupleHull (x : ι → ConcreteAlgebra M) : Set (TupleSpace τ (ι := ι)) :=
  closure (convexHull ℝ (tupleOrbit τ x))

omit [Fintype ι] in
@[simp] theorem tupleConj_apply (u : unitary (ConcreteAlgebra M))
    (v : TupleSpace τ (ι := ι)) (i : ι) :
    tupleConj τ u v i = gnsConj (tracePositive τ) (tracePositive_tracial τ) u (v i) := rfl

omit [Fintype ι] in
@[simp] theorem tupleConj_vector (u : unitary (ConcreteAlgebra M)) (x : ι → ConcreteAlgebra M) :
    tupleConj τ u (tupleVector τ x) = tupleVector τ (fun i => algebraConj u (x i)) := by
  ext i
  exact gnsConj_vector _ _ _ _

theorem tupleConj_norm (u : unitary (ConcreteAlgebra M)) (v : TupleSpace τ (ι := ι)) :
    ‖tupleConj τ u v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2, tupleConj_apply, gnsConj_norm]

theorem mapsTo_hull_codomain {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : F →L[ℝ] G) {S : Set F} {T : Set G}
    (hf : Set.MapsTo f S T) :
    Set.MapsTo f (closure (convexHull ℝ S)) (closure (convexHull ℝ T)) := by
  apply Set.MapsTo.closure _ f.continuous
  intro x hx
  have hh : f x ∈ f '' convexHull ℝ S := ⟨x,hx,rfl⟩
  rw [show f '' convexHull ℝ S = convexHull ℝ (f '' S) from
    f.toLinearMap.image_convexHull S] at hh
  exact convexHull_mono hf.image_subset hh

theorem tupleHull_component (x : ι → ConcreteAlgebra M)
    (v : TupleSpace τ (ι := ι)) (hv : v ∈ tupleHull τ x) (i : ι) :
    v i ∈ conjugacyHull τ (x i) := by
  let f : TupleSpace τ (ι := ι) →L[ℝ] (tracePositive τ).GNS :=
    (PiLp.proj 2 (fun _ : ι => (tracePositive τ).GNS) i :
      TupleSpace τ (ι := ι) →L[ℂ] (tracePositive τ).GNS).restrictScalars ℝ
  have hm : Set.MapsTo f (tupleOrbit τ x) (conjugacyOrbit τ (x i)) := by
    rintro _ ⟨u,rfl⟩
    exact ⟨u,rfl⟩
  exact mapsTo_hull_codomain f hm hv

theorem tupleConj_hull (x : ι → ConcreteAlgebra M) (u : unitary (ConcreteAlgebra M)) :
    Set.MapsTo (tupleConj τ u) (tupleHull τ x) (tupleHull τ x) := by
  change Set.MapsTo (tupleConj τ u) (closure (convexHull ℝ (tupleOrbit τ x)))
    (closure (convexHull ℝ (tupleOrbit τ x)))
  apply mapsTo_hull ((tupleConj τ u).restrictScalars ℝ) (S := tupleOrbit τ x)
  rintro _ ⟨w,rfl⟩
  refine ⟨u*w,?_⟩
  change tupleVector τ (fun i => algebraConj (u*w) (x i)) =
    tupleConj τ u (tupleVector τ (fun i => algebraConj w (x i)))
  rw [tupleConj_vector]
  congr 1
  funext i
  simp only [algebraConj_apply,Submonoid.coe_mul,star_mul,mul_assoc]

theorem tuple_trace_in_hull (hM : KKFreeLiftFrontier.IsFactor M) (x : ι → ConcreteAlgebra M) :
    tupleVector τ (fun i => τ.map (x i) • 1) ∈ tupleHull τ x := by
  let : InnerProductSpace ℝ (TupleSpace τ (ι := ι)) :=
    InnerProductSpace.rclikeToReal ℂ (TupleSpace τ (ι := ι))
  have hc : Convex ℝ (tupleHull τ x) := (convex_convexHull ℝ _).closure
  have hn : (tupleHull τ x).Nonempty := by
    refine ⟨tupleVector τ x,subset_closure (subset_convexHull ℝ _ ?_)⟩
    refine ⟨1,?_⟩
    ext i
    change gnsVector (tracePositive τ) (algebraConj 1 (x i)) = gnsVector (tracePositive τ) (x i)
    simp only [algebraConj_apply,OneMemClass.coe_one,star_one,one_mul,mul_one]
  obtain ⟨v,hv,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hn isClosed_closure.isComplete hc 0
  have hf (u : unitary (ConcreteAlgebra M)) : tupleConj τ u v = v := by
    exact (norm_minimizer_unique hc hv (tupleConj_hull τ x u hv) hmin
      (tupleConj_norm τ u v)).symm
  have he : tupleVector τ (fun i => τ.map (x i) • 1) = v := by
    ext i
    have hi := tupleHull_component τ x v hv i
    obtain ⟨a,ha,hav⟩ := conjugacyHull_bounded τ (x i) hi
    have hcentral : ∀ b, Commute a b := by
      apply commute_all_of_unitary
      intro u
      have he : algebraConj u a = a := by
        apply gnsVector_injective τ
        rw [← gnsConj_vector,hav]
        exact congrArg (fun z : TupleSpace τ (ι := ι) => z i) (hf u)
      have he' := congrArg (fun z => z * (u : ConcreteAlgebra M)) he
      simp only [algebraConj_apply,mul_assoc,Unitary.coe_star_mul_self,mul_one] at he'
      exact he'.symm
    obtain ⟨c,hcc⟩ := hM a hcentral
    have ht := conjugacyHull_trace τ (x i) (v i) hi
    rw [← hav,gnsVector_inner,star_one,one_mul] at ht
    change τ.map a = τ.map (x i) at ht
    rw [hcc,map_smul,τ.normalized,smul_eq_mul,mul_one] at ht
    change gnsVector (tracePositive τ) (τ.map (x i) • 1) = v i
    rw [← ht,← hcc]
    exact hav
  exact he ▸ hv

end

end KKFactorSupport
end

end OAI
