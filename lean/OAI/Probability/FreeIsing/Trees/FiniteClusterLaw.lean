import OAI.Probability.FreeIsing.Estimates.FiniteMarginals
import OAI.Probability.FreeIsing.Trees.WeightEncoding

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.FiniteCluster

attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V]

def Compatible (A : Finset (V × V)) (eta : V → IsingSpin) : Prop :=
  ∀ e ∈ A, eta e.1 = eta e.2

def bondWeight (theta : ℝ) (E A : Finset (V × V)) : ℝ :=
  theta ^ A.card * (1 - theta) ^ (E \ A).card

def colorWeight (E A : Finset (V × V)) (eta : V → IsingSpin) : ℝ :=
  if Compatible A eta then (1 / 2 : ℝ) ^ ((E \ A).card + 1) else 0

lemma bondWeight_nonneg {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (E A : Finset (V × V)) : 0 ≤ bondWeight theta E A := by
  unfold bondWeight
  positivity

lemma colorWeight_nonneg (E A : Finset (V × V)) (eta : V → IsingSpin) :
    0 ≤ colorWeight E A eta := by
  unfold colorWeight
  split_ifs <;> positivity

lemma bondWeight_sum (theta : ℝ) (E : Finset (V × V)) :
    (∑ A ∈ E.powerset, bondWeight theta E A) = 1 := by
  simpa only [bondWeight, Finset.prod_const, add_sub_cancel, Finset.prod_const_one, one_pow] using
    (Finset.prod_add (fun _ : V × V => theta) (fun _ => 1 - theta) E).symm

private lemma weighted_color_eq (theta : ℝ) (E A : Finset (V × V))
    (eta : V → IsingSpin) :
    bondWeight theta E A * colorWeight E A eta =
      (1 / 2 : ℝ) * (∏ e ∈ A, theta * (if eta e.1 = eta e.2 then 1 else 0)) *
        ∏ _e ∈ E \ A, (1 - theta) / 2 := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_boole,
    Finset.prod_const]
  unfold bondWeight colorWeight Compatible
  split_ifs <;> simp_all only [mul_one, mul_zero, zero_mul]
  rw [pow_succ', div_pow, div_pow, one_pow]
  ring

theorem marginal_eq_edge_product (theta : ℝ) (E : Finset (V × V))
    (eta : V → IsingSpin) :
    (∑ A ∈ E.powerset, bondWeight theta E A * colorWeight E A eta) =
      (1 / 2 : ℝ) * ∏ e ∈ E,
        (1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2 := by
  simp_rw [weighted_color_eq, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.prod_add]
  apply Finset.prod_congr rfl
  intro e _
  split_ifs <;> ring

theorem colorWeight_eq_vertices_sub_edges {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {A : Finset (TreeVertex d × TreeVertex d)} (hA : A ⊆ inducedEdges D)
    (eta : TreeVertex d → IsingSpin) :
    colorWeight (inducedEdges D) A eta =
      if Compatible A eta then (1 / 2 : ℝ) ^ (D.card - A.card) else 0 := by
  have hc := hD.inducedEdges_card_add_one
  have hle := Finset.card_le_card hA
  have hdiff := Finset.card_sdiff_of_subset hA
  have hexp : ((inducedEdges D) \ A).card + 1 = D.card - A.card := by omega
  unfold colorWeight
  rw [Finset.card_sdiff_of_subset hA]
  congr 2
  omega

theorem marginal_eq_freeCylinderWeight {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    ENNReal.ofReal (∑ A ∈ (inducedEdges D).powerset,
      bondWeight theta (inducedEdges D) A * colorWeight (inducedEdges D) A eta) =
      freeCylinderWeight theta D eta := by
  rw [marginal_eq_edge_product]
  rfl

theorem colorWeight_eq_edge_product (E A : Finset (V × V)) (hA : A ⊆ E)
    (eta : V → IsingSpin) :
    colorWeight E A eta = (1 / 2 : ℝ) * ∏ e ∈ E,
      if e ∈ A then (if eta e.1 = eta e.2 then 1 else 0) else 1 / 2 := by
  let f : V × V → ℝ := fun e =>
    if e ∈ A then (if eta e.1 = eta e.2 then 1 else 0) else 1 / 2
  have hopen : (∏ e ∈ A, f e) = if Compatible A eta then 1 else 0 := by
    calc
      _ = ∏ e ∈ A, (if eta e.1 = eta e.2 then (1 : ℝ) else 0) := by
        apply Finset.prod_congr rfl
        intro e he
        simp only [f, he, ite_true]
      _ = _ := by rw [Finset.prod_boole]; unfold Compatible; split_ifs <;> rfl
  have hclosed : (∏ e ∈ E \ A, f e) = (1 / 2 : ℝ) ^ (E \ A).card := by
    calc
      _ = ∏ _e ∈ E \ A, (1 / 2 : ℝ) := by
        apply Finset.prod_congr rfl
        intro e he
        simp only [f, (Finset.mem_sdiff.mp he).2, ite_false]
      _ = _ := Finset.prod_const _
  change colorWeight E A eta = (1 / 2 : ℝ) * ∏ e ∈ E, f e
  rw [← Finset.prod_sdiff hA, hclosed, hopen]
  unfold colorWeight
  split_ifs <;> simp [pow_succ', mul_comm]

theorem colorWeight_sum {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) {A : Finset (TreeVertex d × TreeVertex d)}
    (hA : A ⊆ inducedEdges D) :
    (∑ eta : D → IsingSpin,
      colorWeight (inducedEdges D) A (extendFiniteSpin D eta)) = 1 := by
  obtain ⟨r, hr, hmin⟩ := D.exists_min_image (fun v => v.1.length) hD.1
  let q : D → IsingSpin → ℝ := fun v s =>
    if (v : TreeVertex d) = r then 1 / 2 else
      if (parentVertex (v : TreeVertex d), (v : TreeVertex d)) ∈ A then (if s = IsingSpin.pos then 1 else 0) else 1 / 2
  have hq : ∀ v : D, (∑ s : IsingSpin, q v s) = 1 := by
    intro v
    have hu : (Finset.univ : Finset IsingSpin) = {.neg, .pos} := by
      ext s
      cases s <;> simp
    rw [hu, Finset.sum_insert (by decide), Finset.sum_singleton]
    by_cases hv : (v : TreeVertex d) = r
    · norm_num [q, hv]
    · by_cases he : (parentVertex v, (v : TreeVertex d)) ∈ A <;> norm_num [q, hv, he]
  have hterm (eta : D → IsingSpin) :
      colorWeight (inducedEdges D) A (extendFiniteSpin D eta) =
        ∏ v : D, q v (connectedSpinEncode hD r hr hmin eta v) := by
    rw [colorWeight_eq_edge_product _ _ hA]
    have heq := hD.prod_inducedEdges_eq_parent_prod r hr hmin
      (fun u v => if (u, v) ∈ A then
        (if extendFiniteSpin D eta u = extendFiniteSpin D eta v then (1 : ℝ) else 0)
        else 1 / 2)
    simp only [Prod.mk.eta] at heq
    rw [heq]
    let f : TreeVertex d → ℝ := fun v =>
      if v = r then 1 / 2 else
        if (parentVertex v, v) ∈ A then
          (if extendFiniteSpin D eta (parentVertex v) = extendFiniteSpin D eta v then 1 else 0)
        else 1 / 2
    calc
      _ = f r * ∏ v ∈ D.erase r, f v := by
        simp only [f, ite_eq_left rfl]
        congr 1
        apply Finset.prod_congr rfl
        intro v hv
        simp only [(Finset.mem_erase.mp hv).1, ite_false]
      _ = ∏ v ∈ D, f v := Finset.mul_prod_erase D f hr
      _ = ∏ v : D, f v := (Finset.prod_coe_sort D f).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro v _
        by_cases hv : (v : TreeVertex d) = r
        · simp [f, q, hv]
        · rw [connectedSpinEncode_apply_ne_root hD r hr hmin eta v hv]
          have hp := extendFiniteSpin_apply D eta
            ⟨parentVertex v, hD.parent_mem_of_ne_min hr hmin v.2 hv⟩
          simp only [f, q, hv, ite_false, extendFiniteSpin_apply,
            spinAgreementCode_eq_pos_iff, hp]
  calc
    _ = ∑ eta : D → IsingSpin,
        ∏ v : D, q v (connectedSpinEquiv hD r hr hmin eta v) := by
      apply Finset.sum_congr rfl
      intro eta _
      exact hterm eta
    _ = ∑ xi : D → IsingSpin, ∏ v : D, q v (xi v) :=
      (connectedSpinEquiv hD r hr hmin).sum_comp (fun xi => ∏ v : D, q v (xi v))
    _ = ∏ v : D, ∑ s : IsingSpin, q v s := (Fintype.prod_sum q).symm
    _ = 1 := by simp only [hq, Finset.prod_const_one]

end Problem367.FiniteCluster

end

end OAI
