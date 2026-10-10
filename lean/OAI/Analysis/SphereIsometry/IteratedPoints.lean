import OAI.Analysis.SphereIsometry.SubdivisionData
import OAI.Analysis.SphereIsometry.BarycentricPoints

namespace OAI

/-!
# Actual geometric points of iterated subdivision

Initial vertices are coordinate unit vectors. Every later vertex is the finite
barycenter of the nonempty old face that it represents. Simplex membership,
exact carriers, and the geometric mesh bound follow from this recursive formula.
-/

noncomputable section

namespace Tingley

/-- The actual geometric realization of every recursively constructed vertex. -/
def iterDataPoint (I : Type) [Fintype I] [DecidableEq I] :
    (k : ℕ) → (iterData I k).Vertex → I → ℝ
  | 0, v => Pi.single v 1
  | k + 1, v => finiteBarycenter (iterDataPoint I k) v.val

@[simp] theorem iterDataPoint_zero (I : Type) [Fintype I] [DecidableEq I] (v : I) :
    iterDataPoint I 0 v = Pi.single v 1 := rfl

@[simp] theorem iterDataPoint_succ (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (v : (iterData I (k + 1)).Vertex) :
    iterDataPoint I (k + 1) v = finiteBarycenter (iterDataPoint I k) v.val := rfl

/-- The recursion produces simplex vectors at every level. -/
theorem iterDataPoint_mem_stdSimplex (I : Type) [Fintype I] [DecidableEq I] :
    ∀ (k : ℕ) (v : (iterData I k).Vertex),
      iterDataPoint I k v ∈ probabilitySimplexSet I := by
  intro k
  induction k with
  | zero =>
      intro v
      exact single_mem_probabilitySimplexSet v
  | succ k ih =>
      intro v
      exact finiteBarycenter_mem_stdSimplex (iterDataPoint I k) v.property.2
        (fun u _ => ih u)

/-- The recursively defined combinatorial carrier is exactly the set of
strict-positive coordinates of the actual recursive point. -/
theorem positiveCarrier_iterDataPoint (I : Type) [Fintype I] [DecidableEq I] :
    ∀ (k : ℕ) (v : (iterData I k).Vertex),
      positiveCarrier (iterDataPoint I k v) = (iterData I k).carrier v := by
  intro k
  induction k with
  | zero =>
      intro v
      change positiveCarrier (Pi.single v (1 : ℝ)) = {v}
      ext i
      by_cases hi : v = i
      · subst i
        simp [positiveCarrier]
      · simp [positiveCarrier, Pi.single_apply, Ne.symm hi]
  | succ k ih =>
      intro v
      change positiveCarrier (finiteBarycenter (iterDataPoint I k) v.val) =
        v.val.biUnion (fun u => (iterData I k).carrier u)
      rw [positiveCarrier_finiteBarycenter (iterDataPoint I k) v.property.2
        (fun u _ i => (iterDataPoint_mem_stdSimplex I k u).1 i)]
      ext i
      simp only [Finset.mem_biUnion, ih]

/-- The coordinate form used by the simplex fixed-point argument. -/
abbrev iterPoint (m k : ℕ) : IterVertex m k → Fin (m + 1) → ℝ :=
  iterDataPoint (Fin (m + 1)) k

@[simp] theorem iterPoint_zero (m : ℕ) (v : Fin (m + 1)) :
    iterPoint m 0 v = Pi.single v 1 := rfl

@[simp] theorem iterPoint_succ (m k : ℕ) (v : IterVertex m (k + 1)) :
    iterPoint m (k + 1) v = finiteBarycenter (iterPoint m k) v.val := rfl

theorem iterPoint_mem_stdSimplex (m k : ℕ) (v : IterVertex m k) :
    iterPoint m k v ∈ probabilitySimplexSet (Fin (m + 1)) :=
  iterDataPoint_mem_stdSimplex (Fin (m + 1)) k v

theorem positiveCarrier_iterPoint (m k : ℕ) (v : IterVertex m k) :
    positiveCarrier (iterPoint m k v) = iterCarrier m k v :=
  positiveCarrier_iterDataPoint (Fin (m + 1)) k v

/-- Exact boundary compatibility of the coordinate labelling rule. -/
theorem iterPoint_pos_iff (m k : ℕ) (v : IterVertex m k) (i : Fin (m + 1)) :
    0 < iterPoint m k v i ↔ i ∈ iterCarrier m k v := by
  rw [← mem_positiveCarrier, positiveCarrier_iterPoint]

/-- Any two probability vectors have distance at most one in the ambient sup norm. -/
theorem norm_sub_le_one_of_mem_stdSimplex {I : Type*} [Fintype I]
    {x y : I → ℝ} (hx : x ∈ probabilitySimplexSet I) (hy : y ∈ probabilitySimplexSet I) :
    ‖x - y‖ ≤ 1 := by
  rw [← dist_eq_norm]
  apply (dist_pi_le_iff zero_le_one).mpr
  intro i
  have hxi := mem_Icc_of_mem_probabilitySimplexSet hx i
  have hyi := mem_Icc_of_mem_probabilitySimplexSet hy i
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]

/-- The mesh of each actual level-k face is bounded by the kth power of the
barycentric contraction factor. No face coverage assertion is assumed. -/
theorem iterPoint_mesh (m : ℕ) :
    ∀ (k : ℕ) (s : Finset (IterVertex m k)), s ∈ iterComplex m k →
      ∀ u ∈ s, ∀ v ∈ s,
        ‖iterPoint m k u - iterPoint m k v‖ ≤
          ((m : ℝ) / (m + 1 : ℝ)) ^ k := by
  intro k
  induction k with
  | zero =>
      intro s _ u _ v _
      simpa only [pow_zero] using norm_sub_le_one_of_mem_stdSimplex
        (iterPoint_mem_stdSimplex m 0 u) (iterPoint_mem_stdSimplex m 0 v)
  | succ k ih =>
      intro s hs u hu v hv
      have hchain : (iterData (Fin (m + 1)) k).complex.chain s :=
        FiniteComplex.mem_sd_iff.mp hs
      have hD : 0 ≤ ((m : ℝ) / (m + 1 : ℝ)) ^ k :=
        pow_nonneg (div_nonneg (Nat.cast_nonneg m)
          (add_nonneg (Nat.cast_nonneg m) zero_le_one)) k
      rcases hchain u hu v hv with huv | hvu
      · have h := norm_finiteBarycenter_sub_le_mesh (p := iterPoint m k) m hD
          u.property.2 huv (iter_card_le (m := m) (k := k) v.property.1)
          (ih v.val v.property.1)
        simpa only [iterPoint_succ, pow_succ'] using h
      · have h := norm_finiteBarycenter_sub_le_mesh (p := iterPoint m k) m hD
          v.property.2 hvu (iter_card_le (m := m) (k := k) u.property.1)
          (ih u.val u.property.1)
        calc
          ‖iterPoint m (k + 1) u - iterPoint m (k + 1) v‖ =
              ‖iterPoint m (k + 1) v - iterPoint m (k + 1) u‖ := norm_sub_rev _ _
          _ ≤ ((m : ℝ) / (m + 1 : ℝ)) ^ (k + 1) := by
            simpa only [iterPoint_succ, pow_succ'] using h

end Tingley

end

end OAI
