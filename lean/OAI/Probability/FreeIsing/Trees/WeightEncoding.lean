import OAI.Probability.FreeIsing.Trees.Cardinality
import OAI.Probability.FreeIsing.Trees.SpinEncoding

namespace OAI

noncomputable section

namespace Problem367

lemma ConnectedFinset.prod_inducedEdges_eq_parent_prod {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    {M : Type*} [CommMonoid M] (f : TreeVertex d → TreeVertex d → M) :
    (∏ e ∈ inducedEdges D, f e.1 e.2) =
      ∏ v ∈ D.erase r, f (parentVertex v) v := by
  classical
  rw [← hD.inducedEdges_image_snd hr hmin]
  rw [Finset.prod_image (inducedEdges_snd_injOn D)]
  apply Finset.prod_congr rfl
  intro e he
  have he' := (Finset.mem_filter.mp he).2
  rw [treeAdj_parent_of_length_lt he'.1 he'.2]

lemma ConnectedFinset.freeCylinderWeight_eq_parent_prod {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    (theta : ℝ) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      ENNReal.ofReal ((1 / 2 : ℝ) * ∏ v ∈ D.erase r,
        (1 + (if eta (parentVertex v) = eta v then theta else -theta)) / 2) := by
  unfold freeCylinderWeight
  rw [hD.prod_inducedEdges_eq_parent_prod r hr hmin
    (fun u v => (1 + (if eta u = eta v then theta else -theta)) / 2)]

def treeNoiseMass {d : ℕ} (theta : ℝ) (r v : TreeVertex d) (s : IsingSpin) : ℝ :=
  if v = r then 1 / 2 else (1 + (if s = .pos then theta else -theta)) / 2

lemma treeNoiseMass_sum {d : ℕ} (theta : ℝ) (r v : TreeVertex d) :
    (∑ s : IsingSpin, treeNoiseMass theta r v s) = 1 := by
  classical
  have hspin : (Finset.univ : Finset IsingSpin) = {.neg, .pos} := by
    ext s
    cases s <;> simp
  rw [hspin]
  by_cases hv : v = r
  · simp [treeNoiseMass, hv]
  · simp [treeNoiseMass, hv]
    ring

lemma treeNoiseMass_nonneg {d : ℕ} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (r v : TreeVertex d) (s : IsingSpin) : 0 ≤ treeNoiseMass theta r v s := by
  classical
  by_cases hv : v = r
  · norm_num [treeNoiseMass, hv]
  · cases s <;> simp [treeNoiseMass, hv] <;> linarith

lemma treeNoiseMass_le_one {d : ℕ} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (r v : TreeVertex d) (s : IsingSpin) : treeNoiseMass theta r v s ≤ 1 := by
  classical
  by_cases hv : v = r
  · norm_num [treeNoiseMass, hv]
  · cases s <;> simp [treeNoiseMass, hv] <;> linarith

lemma treeNoiseMass_prod_sum {d : ℕ} (theta : ℝ) (r : TreeVertex d)
    (D : Finset (TreeVertex d)) :
    (∑ ξ : D → IsingSpin, ∏ v : D, treeNoiseMass theta r v (ξ v)) = 1 := by
  classical
  rw [← Fintype.prod_sum]
  simp [treeNoiseMass_sum]

lemma ConnectedFinset.freeCylinderWeight_eq_noise_prod {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (r : TreeVertex d) (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    (theta : ℝ) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      ENNReal.ofReal (∏ v : D,
        treeNoiseMass theta r v
          (connectedSpinEncode hD r hr hmin (fun w : D => eta w) v)) := by
  classical
  rw [hD.freeCylinderWeight_eq_parent_prod r hr hmin]
  congr 1
  let f : TreeVertex d → ℝ := fun v =>
    if v = r then 1 / 2 else
      (1 + (if eta (parentVertex v) = eta v then theta else -theta)) / 2
  calc
    (1 / 2 : ℝ) * ∏ v ∈ D.erase r,
        (1 + (if eta (parentVertex v) = eta v then theta else -theta)) / 2
        = f r * ∏ v ∈ D.erase r, f v := by
      have hfr : f r = 1 / 2 := by simp [f]
      rw [hfr]
      congr 1
      apply Finset.prod_congr rfl
      intro v hv
      simp [f, (Finset.mem_erase.mp hv).1]
    _ = ∏ v ∈ D, f v := Finset.mul_prod_erase D f hr
    _ = ∏ v : D, f v := (Finset.prod_coe_sort D f).symm
    _ = ∏ v : D, treeNoiseMass theta r v
          (connectedSpinEncode hD r hr hmin (fun w : D => eta w) v) := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases hvr : (v : TreeVertex d) = r
      · simp [f, treeNoiseMass, hvr]
      · rw [connectedSpinEncode_apply_ne_root hD r hr hmin _ v hvr]
        simp [f, treeNoiseMass, hvr]

end Problem367

end

end OAI
