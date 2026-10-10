import OAI.Analysis.OInfinity.CocycleCentrality

namespace OAI

/-! # Weighted finite Rohlin sums

Orthogonal projection domains give a square-sum norm bound. Hence N
coefficient errors of size L/N contribute at most L/√N, even before
commutation with the projections is imposed. The shift and unitarity
errors are tracked separately.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

lemma weightedProjection_norm_le_one (e : E) (he : star e = e) (hee : e * e = e) :
    ‖e‖ ≤ 1 := by
  have h := CStarRing.norm_star_mul_self (x := e)
  rw [he, hee] at h
  nlinarith [norm_nonneg e]

lemma orthogonalWeighted_square (e x : I → E)
    (he : ∀ i, star (e i) = e i) (hee : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) :
    (∑ i, x i * e i) * star (∑ i, x i * e i) =
      ∑ i, x i * e i * star (x i) := by
  have hterm (i j : I) : (x i * e i) * star (x j * e j) =
      if i = j then x i * e i * star (x i) else 0 := by
    rw [star_mul, he]
    calc
      _ = x i * (e i * e j) * star (x j) := by noncomm_ring
      _ = _ := by
        split_ifs with hij
        · subst j
          rw [hee]
        · rw [horth i j hij, mul_zero, zero_mul]
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum, hterm, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma orthogonalWeighted_norm_sq_le (e x : I → E)
    (he : ∀ i, star (e i) = e i) (hee : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) :
    ‖∑ i, x i * e i‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
  calc
    _ = ‖(∑ i, x i * e i) * star (∑ i, x i * e i)‖ := by
      rw [CStarRing.norm_self_mul_star, pow_two]
    _ = ‖∑ i, x i * e i * star (x i)‖ := by rw [orthogonalWeighted_square e x he hee horth]
    _ ≤ ∑ i, ‖x i * e i * star (x i)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ‖x i‖ * ‖e i‖ * ‖x i‖ := by
          simpa only [norm_star] using
            (norm_mul_le (x i * e i) (star (x i))).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ ‖x i‖ * 1 * ‖x i‖ := by
          gcongr
          exact weightedProjection_norm_le_one (e i) (he i) (hee i)
        _ = ‖x i‖ ^ 2 := by ring

lemma orthogonalWeighted_norm_le (e x : I → E)
    (he : ∀ i, star (e i) = e i) (hee : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hx : ∀ i, ‖x i‖ ≤ δ) :
    ‖∑ i, x i * e i‖ ≤ Real.sqrt (Fintype.card I) * δ := by
  have h := orthogonalWeighted_norm_sq_le e x he hee horth
  have hb : (∑ i, ‖x i‖ ^ 2) ≤ (Fintype.card I : ℝ) * δ ^ 2 := by
    calc
      _ ≤ ∑ _ : I, δ ^ 2 := Finset.sum_le_sum fun i _ => by
        nlinarith [norm_nonneg (x i), hx i]
      _ = _ := by simp
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card I by positivity)
  have hn := Real.sqrt_nonneg (Fintype.card I : ℝ)
  have hp : 0 ≤ Real.sqrt (Fintype.card I : ℝ) * δ := mul_nonneg hn hδ
  nlinarith [norm_nonneg (∑ i, x i * e i)]

def finiteRohlinSum (v : I → unitary E) (e : I → E) : E := ∑ i, (v i : E) * e i

omit [DecidableEq I] in
lemma finiteRohlinSum_defect_identity (φ : E →⋆ₙₐ[ℂ] E) (w : unitary E)
    (σ : Equiv.Perm I) (v : I → unitary E) (e : I → E) :
    (w : E) * φ (finiteRohlinSum v e) - finiteRohlinSum v e =
      (∑ i, ((w : E) * φ (v i) - (v (σ i) : E)) * e (σ i)) +
        ∑ i, ((w : E) * φ (v i)) * (φ (e i) - e (σ i)) := by
  have hreindex : (∑ i, (v (σ i) : E) * e (σ i)) = finiteRohlinSum v e := by
    apply Fintype.sum_equiv σ
    intro i
    rfl
  symm
  rw [← Finset.sum_add_distrib]
  calc
    _ = (∑ i, (w : E) * φ ((v i : E) * e i)) -
        ∑ i, (v (σ i) : E) * e (σ i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul]
      noncomm_ring
    _ = _ := by rw [hreindex, ← Finset.mul_sum, ← map_sum]; rfl

lemma finiteRohlinSum_defect_le [Nontrivial E] (φ : E →⋆ₙₐ[ℂ] E) (w : unitary E)
    (σ : Equiv.Perm I) (v : I → unitary E) (e : I → E)
    (he : ∀ i, star (e i) = e i) (hee : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (δ η : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ i, ‖(w : E) * φ (v i) - (v (σ i) : E)‖ ≤ δ)
    (hshift : ∀ i, ‖φ (e i) - e (σ i)‖ ≤ η) :
    ‖(w : E) * φ (finiteRohlinSum v e) - finiteRohlinSum v e‖ ≤
      Real.sqrt (Fintype.card I) * δ + (Fintype.card I : ℝ) * η := by
  rw [finiteRohlinSum_defect_identity φ w σ v e]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact orthogonalWeighted_norm_le (fun i => e (σ i))
      (fun i => (w : E) * φ (v i) - (v (σ i) : E)) (fun i => he (σ i))
      (fun i => hee (σ i)) (fun i j hij => horth (σ i) (σ j) (σ.injective.ne hij)) δ hδ hv
  · calc
      _ ≤ ∑ i, ‖((w : E) * φ (v i)) * (φ (e i) - e (σ i))‖ := norm_sum_le _ _
      _ ≤ ∑ _ : I, η := by
        apply Finset.sum_le_sum
        intro i hi
        rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
        calc
          _ ≤ ‖φ (v i)‖ * ‖φ (e i) - e (σ i)‖ := norm_mul_le _ _
          _ ≤ 1 * η := by
            apply mul_le_mul
            · exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans (CStarRing.norm_coe_unitary (v i)).le
            · exact hshift i
            · exact norm_nonneg _
            · norm_num
          _ = η := one_mul η
      _ = _ := by simp

/-- One of the two unitary defects only needs the diagonal commutators. -/
lemma finiteRohlinSum_coisometry_defect_le (v : I → unitary E) (e : I → E)
    (he : ∀ i, star (e i) = e i) (hee : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : (∑ i, e i) = 1) (δ : ℝ)
    (hc : ∀ i, ‖(v i : E) * e i - e i * (v i : E)‖ ≤ δ) :
    ‖finiteRohlinSum v e * star (finiteRohlinSum v e) - 1‖ ≤ (Fintype.card I : ℝ) * δ := by
  change ‖(∑ i, (v i : E) * e i) * star (∑ i, (v i : E) * e i) - 1‖ ≤ _
  rw [orthogonalWeighted_square e (fun i => (v i : E)) he hee horth, ← hsum,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(v i : E) * e i * star (v i : E) - e i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : I, δ := by
      apply Finset.sum_le_sum
      intro i hi
      have hid : (v i : E) * e i * star (v i : E) - e i =
          ((v i : E) * e i - e i * (v i : E)) * star (v i : E) := by
        rw [sub_mul, mul_assoc (e i), (v i).property.2, mul_one]
      rw [hid]
      change ‖((v i : E) * e i - e i * (v i : E)) * (star (v i) : unitary E)‖ ≤ δ
      rw [CStarRing.norm_mul_coe_unitary]
      exact hc i
    _ = _ := by simp

end WeakPureInfiniteness

end

end OAI
