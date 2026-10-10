import Mathlib.Probability.Independence.Basic

namespace OAI

/-!
# Independence from one-coordinate splittings

If each real coordinate is independent of all the remaining coordinates
together, finite intersections factor. Hence the joint law is the product
of the coordinate laws. This is used for the abelian row conditionals.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace DukePrimeDegree

theorem iIndepFun_of_independent_remaining
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ι → Ω → ℝ)
    (h : ∀ i, IndepFun (f i) (fun x (j : {j : ι // j ≠ i}) => f j.val x) μ) :
    iIndepFun f μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro sets hsets
      simp
  | @insert i S hi ih =>
      intro sets hsets
      let T : Set ({j : ι // j ≠ i} → ℝ) :=
        ⋂ j : S, (fun z => z ⟨j.val, fun he => hi (he ▸ j.prop)⟩) ⁻¹' sets j.val
      have hT : MeasurableSet T := by
        apply MeasurableSet.iInter
        intro j
        exact (measurable_pi_apply _) (hsets j.val (Finset.mem_insert_of_mem j.prop))
      have hpre : (fun x (j : {j : ι // j ≠ i}) => f j.val x) ⁻¹' T =
          ⋂ j ∈ S, f j ⁻¹' sets j := by
        ext x
        simp only [T, mem_preimage, mem_iInter, Subtype.forall]
      have H := (h i).measure_inter_preimage_eq_mul (sets i) T
        (hsets i (Finset.mem_insert_self _ _)) hT
      rw [hpre] at H
      rw [Finset.set_biInter_insert, Finset.prod_insert hi, H,
        ih (fun j hj => hsets j (Finset.mem_insert_of_mem hj))]

theorem joint_law_eq_pi_of_independent_remaining
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ι → Ω → ℝ)
    (hf : ∀ i, Measurable (f i))
    (h : ∀ i, IndepFun (f i) (fun x (j : {j : ι // j ≠ i}) => f j.val x) μ) :
    μ.map (fun x i => f i x) = Measure.pi (fun i => μ.map (f i)) :=
  (iIndepFun_of_independent_remaining μ f h).map_fun_eq_pi_map
    (fun i => (hf i).aemeasurable)

end DukePrimeDegree

end

end OAI
