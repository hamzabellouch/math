import Mathlib

namespace OAI

noncomputable section

open Set Metric

namespace Problem340.SimplexSubdivision

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def faceCenter (v : ι → E) (s : Finset ι) : E :=
  s.centerMass (fun _ => (1 : ℝ)) v

lemma faceCenter_eq (v : ι → E) (s : Finset ι) :
    faceCenter v s = (s.card : ℝ)⁻¹ • ∑ i ∈ s, v i := by
  simp [faceCenter, Finset.centerMass]

lemma card_smul_faceCenter (v : ι → E) {s : Finset ι} (hs : s.Nonempty) :
    (s.card : ℝ) • faceCenter v s = ∑ i ∈ s, v i := by
  rw [faceCenter_eq, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast hs.card_ne_zero

lemma sum_sub_faceCenter (v : ι → E) {s : Finset ι} (hs : s.Nonempty) :
    ∑ i ∈ s, (v i - faceCenter v s) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, card_smul_faceCenter v hs, sub_self]

lemma faceCenter_mem_convexHull (v : ι → E) {s : Finset ι} (hs : s.Nonempty) :
    faceCenter v s ∈ convexHull ℝ (v '' (s : Set ι)) := by
  apply s.centerMass_mem_convexHull (fun _ _ => zero_le_one)
  · simpa using (show (0 : ℝ) < s.card by exact_mod_cast hs.card_pos)
  · intro i hi
    exact ⟨i, hi, rfl⟩

lemma dist_faceCenter_le (v : ι → E) {s : Finset ι} (hs : s.Nonempty)
    (x : E) (D : ℝ) (h : ∀ i ∈ s, dist (v i) x ≤ D) :
    dist (faceCenter v s) x ≤ D := by
  apply (convex_closedBall x D).centerMass_mem (fun _ _ => zero_le_one)
  · simpa using (show (0 : ℝ) < s.card by exact_mod_cast hs.card_pos)
  · exact h

lemma card_smul_faceCenter_sub [DecidableEq ι] (v : ι → E)
    {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t) :
    (t.card : ℝ) • (faceCenter v t - faceCenter v s) =
      ∑ i ∈ t \ s, (v i - faceCenter v s) := by
  have ht : t.Nonempty := hs.mono hst
  calc
    (t.card : ℝ) • (faceCenter v t - faceCenter v s) =
        ∑ i ∈ t, (v i - faceCenter v s) := by
      rw [smul_sub, card_smul_faceCenter v ht, Finset.sum_sub_distrib,
        Finset.sum_const, Nat.cast_smul_eq_nsmul]
    _ = ∑ i ∈ t \ s, (v i - faceCenter v s) := by
      rw [← Finset.sum_sdiff hst, sum_sub_faceCenter v hs, add_zero]

lemma dist_faceCenter_nested_le [DecidableEq ι] (v : ι → E)
    {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t) (D : ℝ)
    (hD : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D) :
    dist (faceCenter v s) (faceCenter v t) ≤
      ((t.card - s.card : ℕ) : ℝ) / (t.card : ℝ) * D := by
  have ht : t.Nonempty := hs.mono hst
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have hbound : (t.card : ℝ) * dist (faceCenter v t) (faceCenter v s) ≤
      ((t \ s).card : ℝ) * D := by
    calc
      (t.card : ℝ) * dist (faceCenter v t) (faceCenter v s) =
          ‖(t.card : ℝ) • (faceCenter v t - faceCenter v s)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htpos.le, dist_eq_norm]
      _ = ‖∑ i ∈ t \ s, (v i - faceCenter v s)‖ :=
        congrArg norm (card_smul_faceCenter_sub v hs hst)
      _ ≤ ∑ i ∈ t \ s, ‖v i - faceCenter v s‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ t \ s, D := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← dist_eq_norm, dist_comm]
        exact dist_faceCenter_le v hs (v i) D
          (fun j hj => hD j (hst hj) i (Finset.mem_sdiff.mp hi).1)
      _ = ((t \ s).card : ℝ) * D := by simp
  calc
    dist (faceCenter v s) (faceCenter v t) =
        dist (faceCenter v t) (faceCenter v s) := dist_comm _ _
    _ ≤ ((t \ s).card : ℝ) * D / (t.card : ℝ) :=
      (le_div_iff₀ htpos).2 (by simpa only [mul_comm] using hbound)
    _ = ((t.card - s.card : ℕ) : ℝ) / (t.card : ℝ) * D := by
      rw [Finset.card_sdiff_of_subset hst]
      ring

lemma dist_faceCenter_nested_le_mesh [DecidableEq ι] (v : ι → E)
    {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t)
    (n : ℕ) (hcard : t.card ≤ n + 1) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D) :
    dist (faceCenter v s) (faceCenter v t) ≤
      ((n : ℝ) / (n + 1)) * D := by
  apply (dist_faceCenter_nested_le v hs hst D hD).trans
  apply mul_le_mul_of_nonneg_right _ hD0
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast (hs.mono hst).card_pos
  have hsone : (1 : ℝ) ≤ s.card := by exact_mod_cast hs.card_pos
  have htcard : (t.card : ℝ) ≤ n + 1 := by exact_mod_cast hcard
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [Nat.cast_sub (Finset.card_le_card hst)]
  apply (div_le_div_iff₀ htpos hn).2
  nlinarith

lemma diam_faceCenter_chain_le [DecidableEq ι] {κ : Type*} (v : ι → E)
    (t : Finset ι) (faces : κ → Finset ι)
    (hne : ∀ k, (faces k).Nonempty) (hsub : ∀ k, faces k ⊆ t)
    (hchain : ∀ k l, faces k ⊆ faces l ∨ faces l ⊆ faces k)
    (n : ℕ) (hcard : t.card ≤ n + 1) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D) :
    Metric.diam (convexHull ℝ (Set.range (fun k => faceCenter v (faces k)))) ≤
      ((n : ℝ) / (n + 1)) * D := by
  rw [convexHull_diam]
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  rcases hchain k l with hkl | hlk
  · exact dist_faceCenter_nested_le_mesh v (hne k) hkl n
      ((Finset.card_le_card (hsub l)).trans hcard) D hD0
      (fun i hi j hj => hD i (hsub l hi) j (hsub l hj))
  · rw [dist_comm]
    exact dist_faceCenter_nested_le_mesh v (hne l) hlk n
      ((Finset.card_le_card (hsub k)).trans hcard) D hD0
      (fun i hi j hj => hD i (hsub k hi) j (hsub k hj))

lemma dist_faceCenter_of_mem_convexHull_le_mesh [DecidableEq ι] (v : ι → E)
    {t : Finset ι} (_ht : t.Nonempty) (n : ℕ) (hcard : t.card ≤ n + 1)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D)
    {x : E} (hx : x ∈ convexHull ℝ (v '' (t : Set ι))) :
    dist (faceCenter v t) x ≤ ((n : ℝ) / (n + 1)) * D := by
  obtain ⟨y, ⟨i, hi, rfl⟩, hy⟩ := convexHull_exists_dist_ge hx (faceCenter v t)
  rw [dist_comm] at hy
  apply hy.trans
  have hsingle : faceCenter v {i} = v i := by
    simp [faceCenter, Finset.centerMass]
  rw [← hsingle]
  exact dist_faceCenter_nested_le_mesh v (Finset.singleton_nonempty i)
    (Finset.singleton_subset_iff.mpr hi) n hcard D hD0 hD

lemma diam_convexHull_insert_faceCenter_le_mesh [DecidableEq ι] (v : ι → E)
    {t : Finset ι} (ht : t.Nonempty) (n : ℕ) (hcard : t.card ≤ n + 1)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D)
    (W : Set E) (hW : W ⊆ convexHull ℝ (v '' (t : Set ι)))
    (hsmall : ∀ x ∈ W, ∀ y ∈ W, dist x y ≤ ((n : ℝ) / (n + 1)) * D) :
    Metric.diam (convexHull ℝ (insert (faceCenter v t) W)) ≤
      ((n : ℝ) / (n + 1)) * D := by
  rw [convexHull_diam]
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · simp only [dist_self]
    positivity
  · exact dist_faceCenter_of_mem_convexHull_le_mesh v ht n hcard D hD0 hD (hW hy)
  · rw [dist_comm]
    exact dist_faceCenter_of_mem_convexHull_le_mesh v ht n hcard D hD0 hD (hW hx)
  · exact hsmall x hx y hy

end Problem340.SimplexSubdivision

end

end OAI
