import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Jacobian

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X]
variable {k : ℕ} (C : IntegerChart X k)
lemma jacobian_permute (π : Fin k → X → ℝ) (σ : Equiv.Perm (Fin k)) (z : Euc k) :
    C.jacobian (π ∘ σ) z = (Equiv.Perm.sign σ : ℤ) * C.jacobian π z := by
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j =>
    fderivWithin ℝ (C.scalar (π i)) C.domain z (EuclideanSpace.single j 1)
  change (M.submatrix σ id).det = (Equiv.Perm.sign σ : ℤ) * M.det
  exact Matrix.det_permute σ M

lemma action_permute {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    C.action b (π ∘ σ) = (Equiv.Perm.sign σ : ℤ) * C.action b π := by
  have hσ : Admissible b (π ∘ σ) := ⟨h.1, fun i => h.2 (σ i)⟩
  simp only [action, ite_eq_left h, ite_eq_left hσ, C.jacobian_permute]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

end IntegerChart

namespace Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma IntegerRectifiable.apply_update_mul {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b f g : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (hg : BoundedLip g) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (i : Fin k) :
    T b (Function.update π i (fun x => f x * g x)) =
      T (fun x => b x * f x) (Function.update π i g) +
      T (fun x => b x * g x) (Function.update π i f) := by
  obtain ⟨C, _, hC, hsum, hrepr⟩ := hT
  have hup {a : X → ℝ} (ha : BoundedLip a) :
      ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i a) j) := by
    intro j
    by_cases hji : j = i
    · simpa [hji] using ha.1
    · simpa [hji] using hπ j
  rw [hrepr, hrepr, hrepr, ← Summable.tsum_add
    (summable_actions_of_summable_masses hC hsum ⟨BoundedLip.mul hb hf, hup hg⟩)
    (summable_actions_of_summable_masses hC hsum ⟨BoundedLip.mul hb hg, hup hf⟩)]
  apply tsum_congr
  intro j
  exact (C j).action_update_mul hb hf hg π hπ i

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma admissible_vecCons {k : ℕ} {b f : X → ℝ} {π : Fin k → X → ℝ}
    (hb : BoundedLip b) (hf : ∃ K : ℝ≥0, LipschitzWith K f)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Admissible b (Matrix.vecCons f π) := by
  refine ⟨hb, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hf
  · exact hπ j

lemma update_vecCons_zero {α : Type*} {k : ℕ} (f g : α) (π : Fin k → α) :
    Function.update (Matrix.vecCons f π) 0 g = Matrix.vecCons g π := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

lemma IntegerRectifiable.product_rule {k : ℕ} {T : Functional X (k + 1)}
    (hT : IntegerRectifiable T) {b f : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    T b (Matrix.vecCons f π) + T f (Matrix.vecCons b π) =
      boundarySucc T (fun x => b x * f x) π := by
  have h := IntegerRectifiable.apply_update_mul hT (BoundedLip.const 1) hb hf (Matrix.vecCons b π)
    (admissible_vecCons (BoundedLip.const 1) hb.1 hπ).2 0
  simp only [update_vecCons_zero, one_mul] at h
  have hadm : Admissible (fun x => b x * f x) π := ⟨BoundedLip.mul hb hf, hπ⟩
  exact h.symm.trans (by rw [boundarySucc, ite_eq_left hadm])

lemma IntegerRectifiable.cycle_product_rule {k : ℕ} {T : Functional X (k + 1)}
    (hT : IntegerRectifiable T) (hz : IsCycle T) {b f : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    T b (Matrix.vecCons f π) = -T f (Matrix.vecCons b π) := by
  have h := IntegerRectifiable.product_rule hT hb hf π hπ
  have hz' : boundarySucc T = fun _ _ => 0 := hz
  rw [hz'] at h
  exact eq_neg_of_add_eq_zero_left h

omit [BorelSpace X] [CompactSpace X] in
lemma IntegerRectifiable.apply_permute {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    T b (π ∘ σ) = (Equiv.Perm.sign σ : ℤ) * T b π := by
  obtain ⟨C, _, _, _, hrepr⟩ := hT
  rw [hrepr, hrepr, ← tsum_mul_left]
  exact tsum_congr fun j => (C j).action_permute h σ

omit [BorelSpace X] [CompactSpace X] in
lemma IntegerRectifiable.abs_apply_permute {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    |T b (π ∘ σ)| = |T b π| := by
  rw [IntegerRectifiable.apply_permute hT h σ, abs_mul, abs_unit_intCast, one_mul]

lemma IntegerRectifiable.head_bound {k : ℕ} {T : Functional X (k + 1)}
    (hT : IntegerRectifiable T) (hcur : IsMetricCurrent T)
    (hbd : IsMetricCurrent (boundarySucc T))
    {b f : X → ℝ} {Kb : ℝ≥0} (hb : LipschitzWith Kb b) (hf : BoundedLip f)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ i, LipschitzWith (K i) (π i))
    (B F : ℝ≥0) (hB : ∀ x, |b x| ≤ B) (hF : ∀ x, |f x| ≤ F) :
    |T b (Matrix.vecCons f π)| ≤
      (∏ i, (K i : ℝ)) * ((B : ℝ) * mass (boundarySucc T) + (Kb : ℝ) * mass T) * F := by
  have hb' : BoundedLip b := ⟨⟨Kb, hb⟩, B, hB⟩
  have hπ' : ∀ i, ∃ L : ℝ≥0, LipschitzWith L (π i) := fun i => ⟨K i, hπ i⟩
  have hprod := IntegerRectifiable.product_rule hT hb' hf π hπ'
  have heq : T b (Matrix.vecCons f π) =
      boundarySucc T (fun x => b x * f x) π - T f (Matrix.vecCons b π) := by
    linarith
  have hbf (x : X) : |b x * f x| ≤ (B : ℝ) * F := by
    rw [abs_mul]
    exact mul_le_mul (hB x) (hF x) (abs_nonneg _) B.coe_nonneg
  have h1 := hbd.mass_bound_uniform (BoundedLip.mul hb' hf) K hπ hbf
  have hK : ∀ i, LipschitzWith (Matrix.vecCons Kb K i) (Matrix.vecCons b π i) := by
    intro i
    exact Fin.cases hb (fun j => hπ j) i
  have h2 := hcur.mass_bound_uniform hf (Matrix.vecCons Kb K) hK hF
  have hmult : (∏ i, ((Matrix.vecCons Kb K i : ℝ≥0) : ℝ)) =
      (Kb : ℝ) * ∏ i, (K i : ℝ) := by rw [Fin.prod_univ_succ]; rfl
  rw [hmult] at h2
  rw [heq]
  calc |boundarySucc T (fun x => b x * f x) π - T f (Matrix.vecCons b π)| ≤
      |boundarySucc T (fun x => b x * f x) π| + |T f (Matrix.vecCons b π)| := abs_sub _ _
    _ ≤ ((∏ i, (K i : ℝ)) * ((B : ℝ) * F)) * mass (boundarySucc T) +
        (((Kb : ℝ) * ∏ i, (K i : ℝ)) * F) * mass T := add_le_add h1 h2
    _ = _ := by ring

end Foundations
end CAT0Fillings

end

end OAI
