import Mathlib

namespace OAI

/-! Products. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment

variable {α β : Type*}

lemma ennreal_tsum_fin_product (n : ℕ) (f : Fin n → α → ℝ≥0∞) :
    (∑' v : Fin n → α, ∏ j, f j (v j)) = ∏ j, ∑' a, f j a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) ↦ α)).tsum_eq]
    change (∑' z : α × (Fin n → α), ∏ j, f j (Fin.cons (α := fun _ : Fin (n+1) ↦ α) z.1 z.2 j)) = _
    simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod' (f := fun z : α × (Fin n → α) ↦ f 0 z.1*∏ j, f j.succ (z.2 j))]
    simp_rw [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right]

def productPMF {n : ℕ} (p : Fin n → PMF α) : PMF (Fin n → α) :=
  ⟨fun v ↦ ∏ j, p j (v j), ENNReal.summable.hasSum_iff.2 (by
    rw [ennreal_tsum_fin_product]
    simp only [PMF.tsum_coe, Finset.prod_const_one])⟩

@[simp] lemma productPMF_apply {n : ℕ} (p : Fin n → PMF α) (v : Fin n → α) :
    productPMF p v = ∏ j, p j (v j) := rfl

lemma productPMF_pure {n : ℕ} (v : Fin n → α) :
    productPMF (fun j ↦ PMF.pure (v j)) = PMF.pure v := by
  classical
  apply PMF.ext
  intro w
  by_cases h : w = v
  · subst w; simp
  · have hn : ∃ j, w j ≠ v j := by simpa only [funext_iff, not_forall] using h
    obtain ⟨j,hj⟩ := hn
    simp only [productPMF_apply, PMF.pure_apply, ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

lemma productPMF_bind {n : ℕ} (p : Fin n → PMF α) (K : Fin n → α → PMF β) :
    (productPMF p).bind (fun v ↦ productPMF (fun j ↦ K j (v j))) =
      productPMF (fun j ↦ (p j).bind (K j)) := by
  apply PMF.ext
  intro w
  simp only [PMF.bind_apply, productPMF_apply, ← Finset.prod_mul_distrib]
  exact ennreal_tsum_fin_product n (fun j a ↦ p j a*K j a (w j))

lemma productPMF_map {n : ℕ} (p : Fin n → PMF α) (T : Fin n → α → β) :
    (productPMF p).map (fun v j ↦ T j (v j)) = productPMF (fun j ↦ (p j).map (T j)) := by
  change (productPMF p).bind (fun v ↦ PMF.pure (fun j ↦ T j (v j))) = _
  simp_rw [← productPMF_pure]
  exact productPMF_bind p (fun j a ↦ PMF.pure (T j a))

lemma productPMF_measure [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {n : ℕ} (p : Fin n → PMF α) :
    (productPMF p).toMeasure = Measure.pi (fun j ↦ (p j).toMeasure) := by
  have h : productPMF p = (Measure.pi (fun j ↦ (p j).toMeasure)).toPMF := by
    apply PMF.ext
    intro v
    simp [productPMF_apply, Measure.toPMF_apply, Measure.pi_singleton, PMF.toMeasure_apply_singleton]
  rw [h, Measure.toPMF_toMeasure]

lemma productPMF_cons {n : ℕ} (p : Fin (n+1) → PMF α) :
    productPMF p = (p 0).bind (fun a ↦ (productPMF (fun j ↦ p j.succ)).map (Fin.cons a)) := by
  classical
  apply PMF.ext
  intro v
  rw [PMF.bind_apply, tsum_eq_single (v 0)]
  · rw [PMF.map_apply, tsum_eq_single (Fin.tail v)]
    · simp [productPMF_apply, Fin.prod_univ_succ, Fin.tail]
    · intro w hw
      have hn : v ≠ Fin.cons (v 0) w := by
        intro he
        have := congrArg Fin.tail he
        simp only [Fin.tail_cons] at this
        exact hw this.symm
      simp [hn]
  · intro a ha
    have he : (productPMF (fun j ↦ p j.succ)).map (Fin.cons a) v = 0 := by
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro w
      have hn : v ≠ Fin.cons a w := by
        intro h
        exact ha (congrFun h 0).symm
      simp [hn]
    rw [he, mul_zero]

end ThreeState.TreeClauses.Experiment

end

end OAI
