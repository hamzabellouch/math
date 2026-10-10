import OAI.Combinatorics.BooleanFunctions.FiniteMoments

namespace OAI

open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace SquareRootDegree
namespace FiniteCLT
attribute [local instance] Classical.propDecidable

variable {α : Type*} [MeasurableSpace α]

/-- The normalized sum uses an actual finite product space at every index. -/
def normalizedSum (T : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i, T (x i)

theorem measurable_normalizedSum (T : α → ℝ) (hT : Measurable T) (n : ℕ) :
    Measurable (normalizedSum T n) := by
  unfold normalizedSum
  fun_prop

theorem finite_product_clt (μ : Measure α) [IsProbabilityMeasure μ]
    (T : α → ℝ) (hT : Measurable T)
    (h0 : ∫ x, T x ∂μ = 0) (h1 : ∫ x, (T x)^2 ∂μ = 1) :
    TendstoInDistribution (normalizedSum T) atTop (fun x : ℝ => x)
      (fun n => Measure.pi (fun _ : Fin n => μ)) (gaussianReal 0 1) := by
  obtain ⟨Ω, mΩ, P, X, hmX, hlX, hiX, hP⟩ := exists_iid ℕ μ
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure P := hP
  have hi : iIndepFun (fun i ω => T (X i ω)) P := hiX.comp (fun _ => T) (fun _ => hT)
  have hl (i : ℕ) : HasLaw (fun ω => T (X i ω)) (μ.map T) P :=
    (show HasLaw T (μ.map T) μ from ⟨hT.aemeasurable, rfl⟩).fun_comp (hlX i)
  have hid (i : ℕ) : IdentDistrib (fun ω => T (X i ω)) (fun ω => T (X 0 ω)) P P :=
    (hl i).identDistrib (hl 0)
  have hz : ∫ ω, T (X 0 ω) ∂P = 0 :=
    ((hlX 0).integral_comp hT.aestronglyMeasurable).trans h0
  have ho : ∫ ω, (T (X 0 ω)) ^ 2 ∂P = 1 :=
    ((hlX 0).integral_comp (hT.pow_const 2).aestronglyMeasurable).trans h1
  have hc := tendstoInDistribution_inv_sqrt_mul_sum
    (P' := gaussianReal 0 1) (Y := fun x : ℝ => x) HasLaw.id hz ho hi hid
  refine ⟨fun n => (measurable_normalizedSum T hT n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  have hdist (n : ℕ) :
      IdentDistrib (normalizedSum T n)
        (fun ω => (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, T (X k ω))
        (Measure.pi (fun _ : Fin n => μ)) P := by
    have hfin : HasLaw (fun ω (i : Fin n) => X i ω) (Measure.pi (fun _ : Fin n => μ)) P :=
      (hiX.precomp Fin.val_injective).hasLaw_pi (fun i => hlX i)
    have hn := (show HasLaw (normalizedSum T n)
        ((Measure.pi (fun _ : Fin n => μ)).map (normalizedSum T n))
        (Measure.pi (fun _ : Fin n => μ)) from
      ⟨(measurable_normalizedSum T hT n).aemeasurable, rfl⟩).fun_comp hfin
    have he : (fun ω => normalizedSum T n (fun i : Fin n => X i ω)) =
        (fun ω => (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, T (X k ω)) := by
      funext ω
      unfold normalizedSum
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun k => T (X k ω)) n
    rw [he] at hn
    exact (show HasLaw (normalizedSum T n) _ (Measure.pi (fun _ : Fin n => μ))
      from ⟨(measurable_normalizedSum T hT n).aemeasurable, rfl⟩).identDistrib hn
  apply hc.tendsto.congr
  intro n
  exact Subtype.ext (hdist n).map_eq.symm

end FiniteCLT
end SquareRootDegree

namespace SquareRootDegree
namespace UniformFinite
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {α ι : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

def uniformMeasure (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] : Measure α :=
  (PMF.uniformOfFintype α).toMeasure

instance uniformMeasure_probability : IsProbabilityMeasure (uniformMeasure α) := by
  unfold uniformMeasure; infer_instance

theorem uniform_singleton (a : α) : uniformMeasure α {a} = (Fintype.card α : ENNReal)⁻¹ := by
  rw [uniformMeasure,PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),PMF.uniformOfFintype_apply]

theorem integral_uniform (f : α → ℝ) : (∫ x, f x ∂uniformMeasure α) = average f := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Measure.real,uniform_singleton,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  exact (Finset.mul_sum ..).symm

theorem uniform_pi [Fintype ι] [DecidableEq ι] :
    Measure.pi (fun _ : ι => uniformMeasure α) = uniformMeasure (ι → α) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton,uniform_singleton]
  simp only [uniform_singleton,Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,ENNReal.inv_pow]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem average_pi_eval_any {κ : Type*} [Fintype κ] [DecidableEq κ]
    (j : κ) (f : α → ℝ) : average (fun x : κ → α => f (x j)) = average f := by
  convert average_pi_eval j f using 1
  congr 1
  exact Subsingleton.elim _ _

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem centered_sq_any {κ : Type*} [Fintype κ] [DecidableEq κ] (T : α → ℝ)
    (h0 : average T = 0) :
    average (fun x : κ → α => (∑ i, T (x i))^2) = ∑ _ : κ, average (fun a => (T a)^2) := by
  have h := FiniteMoments.normalized_product_centered_sq
    (fun (_ : κ) (_ : α) => (1:ℝ)) (fun _ => average_const 1)
    (fun _ => T) (by simpa using fun (_ : κ) => h0)
  simp only [Finset.prod_const_one,one_mul] at h
  convert h using 1
  congr 1
  exact Subsingleton.elim _ _

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem average_normalizedSum (T : α → ℝ) (h0 : average T = 0) (n : ℕ) :
    average (FiniteCLT.normalizedSum T n) = 0 := by
  unfold FiniteCLT.normalizedSum
  rw [average_const_mul,average_sum]
  simp only [average_pi_eval_any,h0,Finset.sum_const_zero,mul_zero]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem average_normalizedSum_sq (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) {n : ℕ} (hn : 0 < n) :
    average (fun x => (FiniteCLT.normalizedSum T n x)^2) = 1 := by
  have h := centered_sq_any (κ := Fin n) T h0
  simp only [h1,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
  simp only [FiniteCLT.normalizedSum,mul_pow,average_const_mul,h,inv_pow]
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  exact inv_mul_cancel₀ (show (n:ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

theorem uniform_clt (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    TendstoInDistribution (FiniteCLT.normalizedSum T) atTop (fun x : ℝ => x)
      (fun n => uniformMeasure (Fin n → α)) (gaussianReal 0 1) := by
  have hm : Measurable T := measurable_of_finite T
  have hz : (∫ x, T x ∂uniformMeasure α) = 0 := (integral_uniform T).trans h0
  have hv : (∫ x, (T x)^2 ∂uniformMeasure α) = 1 := (integral_uniform _).trans h1
  have hc := FiniteCLT.finite_product_clt (uniformMeasure α) T hm hz hv
  simpa only [uniform_pi] using hc

end UniformFinite
end SquareRootDegree

end

end OAI
