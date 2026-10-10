import OAI.Probability.FreeIsing.Estimates.InfinitePiPair

namespace OAI

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace Problem367

variable {I : Type*} {A B : I → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

def dependentPiPairEquiv : (∀ i, A i × B i) ≃ᵐ ((∀ i, A i) × (∀ i, B i)) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun x : ∀ i, A i × B i =>
      (fun i => (x i).1, fun i => (x i).2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : (∀ i, A i) × (∀ i, B i) =>
      fun i => (p.1 i, p.2 i))
    fun_prop

theorem measurePreserving_dependentPiPairEquiv [Fintype I]
    (μ : ∀ i, Measure (A i)) (ν : ∀ i, Measure (B i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (dependentPiPairEquiv (A := A) (B := B))
      (Measure.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := dependentPiPairEquiv.measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
        (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn)) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi fun i =>
          (μ i).toFiniteSpanningSetsIn).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi fun i =>
          (ν i).toFiniteSpanningSetsIn).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      have heq : dependentPiPairEquiv ⁻¹' (univ.pi s ×ˢ univ.pi t) =
          univ.pi (fun i => s i ×ˢ t i) := by
        ext x
        simp [dependentPiPairEquiv, mem_pi, forall_and]
      rw [heq]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

theorem infinitePi_map_pair_dependent_arrays
    (μ : ∀ i, Measure (A i)) (ν : ∀ i, Measure (B i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i)) =
      Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  apply (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro s
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      s.restrict ∘ (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i)) =
      (fun p : (∀ i : s, A i) × (∀ i : s, B i) => fun i => (p.1 i, p.2 i)) ∘
        Prod.map s.restrict s.restrict := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  exact (measurePreserving_dependentPiPairEquiv
    (fun i : s => μ i) (fun i : s => ν i)).symm.map_eq

theorem infinitePi_map_split_dependent_pairs
    (μ : ∀ i, Measure (A i)) (ν : ∀ i, Measure (B i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i => (μ i).prod (ν i))).map
      (fun x : ∀ i, A i × B i => (fun i => (x i).1, fun i => (x i).2)) =
      (Measure.infinitePi μ).prod (Measure.infinitePi ν) := by
  rw [← infinitePi_map_pair_dependent_arrays μ ν,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      (fun x : ∀ i, A i × B i => (fun i => (x i).1, fun i => (x i).2)) ∘
        (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i)) = id := rfl
  rw [hcomp, Measure.map_id]

end Problem367

end

end OAI
