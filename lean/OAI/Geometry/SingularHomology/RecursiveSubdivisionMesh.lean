import OAI.Geometry.SingularHomology.SimplexSubdivisionMesh

namespace OAI

noncomputable section

open Set Metric

namespace Problem340.SimplexSubdivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def BarycentricCell : (n : ℕ) → (Fin (n + 1) → E) → (Fin (n + 1) → E) → Prop
  | 0, v, w => w = v
  | n + 1, v, w => ∃ i : Fin (n + 2), ∃ u : Fin (n + 1) → E,
      BarycentricCell n (v ∘ i.succAbove) u ∧
        w = Fin.cons (faceCenter v Finset.univ) u

lemma meshRatio_monotone_step (n : ℕ) :
    (n : ℝ) / (n + 1) ≤ (n + 1) / (n + 2) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem BarycentricCell.carrier_and_mesh {n : ℕ} {v w : Fin (n + 1) → E}
    (h : BarycentricCell n v w) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ i j, dist (v i) (v j) ≤ D) :
    Set.range w ⊆ convexHull ℝ (Set.range v) ∧
      ∀ i j, dist (w i) (w j) ≤ ((n : ℝ) / (n + 1)) * D := by
  induction n with
  | zero =>
      change w = v at h
      subst w
      refine ⟨subset_convexHull ℝ _, ?_⟩
      intro i j
      have hij : i = j := Fin.ext (by omega)
      simp [hij]
  | succ n ih =>
      obtain ⟨i, u, hu, rfl⟩ := h
      obtain ⟨hcarrier, hmesh⟩ := ih hu (fun j k => hD _ _)
      have hface : Set.range (v ∘ i.succAbove) ⊆ Set.range v := by
        rintro _ ⟨j, rfl⟩
        exact ⟨i.succAbove j, rfl⟩
      have hchild : Set.range u ⊆ convexHull ℝ (Set.range v) :=
        hcarrier.trans (convexHull_mono hface)
      have hcenter : faceCenter v Finset.univ ∈ convexHull ℝ (Set.range v) := by
        simpa only [Finset.coe_univ, Set.image_univ] using
          faceCenter_mem_convexHull v (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + 2))).Nonempty)
      have hrad (j : Fin (n + 1)) :
          dist (faceCenter v Finset.univ) (u j) ≤
            (((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1)) * D := by
        apply dist_faceCenter_of_mem_convexHull_le_mesh v Finset.univ_nonempty
          (n + 1) (by simp) D hD0 (fun a _ b _ => hD a b)
        simpa only [Finset.coe_univ, Set.image_univ] using hchild (Set.mem_range_self j)
      refine ⟨?_, ?_⟩
      · rintro _ ⟨j, rfl⟩
        refine Fin.cases ?_ (fun k => ?_) j
        · exact hcenter
        · exact hchild (Set.mem_range_self k)
      · intro j k
        refine Fin.cases ?_ (fun j => ?_) j
        · refine Fin.cases ?_ (fun k => ?_) k
          · simp only [Fin.cons_zero, dist_self]
            positivity
          · simpa only [Fin.cons_zero, Fin.cons_succ] using hrad k
        · refine Fin.cases ?_ (fun k => ?_) k
          · simpa only [Fin.cons_zero, Fin.cons_succ, dist_comm] using hrad j
          · simp only [Fin.cons_succ]
            apply (hmesh j k).trans
            apply mul_le_mul_of_nonneg_right _ hD0
            simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
              meshRatio_monotone_step n

theorem BarycentricCell.carrier {n : ℕ} {v w : Fin (n + 1) → E}
    (h : BarycentricCell n v w) : Set.range w ⊆ convexHull ℝ (Set.range v) := by
  exact (h.carrier_and_mesh (Metric.diam (Set.range v)) Metric.diam_nonneg
    (fun i j => Metric.dist_le_diam_of_mem (Set.finite_range v).isBounded
      (Set.mem_range_self i) (Set.mem_range_self j))).1

theorem BarycentricCell.diam_le {n : ℕ} {v w : Fin (n + 1) → E}
    (h : BarycentricCell n v w) :
    Metric.diam (convexHull ℝ (Set.range w)) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (convexHull ℝ (Set.range v)) := by
  rw [convexHull_diam, convexHull_diam]
  have hmesh := (h.carrier_and_mesh (Metric.diam (Set.range v)) Metric.diam_nonneg
    (fun i j => Metric.dist_le_diam_of_mem (Set.finite_range v).isBounded
      (Set.mem_range_self i) (Set.mem_range_self j))).2
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact hmesh i j

end Problem340.SimplexSubdivision

end

end OAI
