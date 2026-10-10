import OAI.Analysis.OInfinity.BinaryFragmentation

namespace OAI

/-! # The actual row cocycle and its finite splitting defect

The product cocycle `V_n = W φ(W) ... φ^[n-1](W)` is not a finite
permutation. Its splitting defect is: `V_n φ(V_n*) = ψ^[n](W*) W`,
where `ψ = Ad(W) φ`. For commuting binary Cuntz rows the right side is
the adjoint of the joint-word cycle already constructed.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

section Group

variable {G : Type*} [Group G]

def finiteGroupCocycle (φ : G →* G) (u : G) : ℕ → G
  | 0 => 1
  | n + 1 => u * φ (finiteGroupCocycle φ u n)

lemma finiteGroupCocycle_splitting_defect (φ ψ : G →* G) (u : G)
    (hψ : ∀ x, ψ x = u * φ x * u⁻¹) (n : ℕ) :
    finiteGroupCocycle φ u n * φ ((finiteGroupCocycle φ u n)⁻¹) =
      (ψ^[n]) (u⁻¹) * u := by
  induction n with
  | zero => simp [finiteGroupCocycle]
  | succ n ih =>
      change (u * φ (finiteGroupCocycle φ u n)) *
        φ ((u * φ (finiteGroupCocycle φ u n))⁻¹) = _
      calc
        _ = u * φ (finiteGroupCocycle φ u n *
            φ ((finiteGroupCocycle φ u n)⁻¹)) * φ (u⁻¹) := by
          simp only [map_mul, map_inv, mul_inv_rev]
          group
        _ = u * (φ ((ψ^[n]) (u⁻¹)) * φ u) * φ (u⁻¹) := by rw [ih, map_mul]
        _ = ψ ((ψ^[n]) (u⁻¹)) * u := by
          rw [hψ]
          simp only [map_inv]
          group
        _ = _ := by rw [Function.iterate_succ_apply']

end Group

variable {E : Type*} [CStarAlgebra E]

def binarySplitHom (a b : E) (ha : star a * a = 1) (hb : star b * b = 1)
    (hab : star a * b = 0) : unitary E →* unitary E where
  toFun u := binaryCornerUnitary a ha u * binaryCornerUnitary b hb u
  map_one' := by rw [binaryCornerUnitary_one, binaryCornerUnitary_one, one_mul]
  map_mul' u v := by
    change binaryCornerUnitary a ha (u * v) * binaryCornerUnitary b hb (u * v) = _
    rw [binaryCornerUnitary_mul, binaryCornerUnitary_mul]
    calc
      _ = binaryCornerUnitary a ha u *
          (binaryCornerUnitary a ha v * binaryCornerUnitary b hb u) *
          binaryCornerUnitary b hb v := by simp only [mul_assoc]
      _ = binaryCornerUnitary a ha u *
          (binaryCornerUnitary b hb u * binaryCornerUnitary a ha v) *
          binaryCornerUnitary b hb v := by
        rw [(binaryCornerUnitary_commute a b ha hb hab v u).eq]
      _ = _ := by simp only [mul_assoc]

lemma binarySplitHom_coe (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (u : unitary E) :
    (binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
      (by simpa using hs 1 1) (by simpa using hs 0 1) u : E) = finiteRowShift s u := by
  change cornerCompression (s 0) u * cornerCompression (s 1) u = _
  have hsum' : s 0 * star (s 0) + s 1 * star (s 1) = 1 := by
    simpa only [Fin.sum_univ_two] using hsum
  rw [cornerCompression_pair_product _ _ _ _ (by simpa using hs 0 1)]
  simp only [finiteRowShift, Fin.sum_univ_two]
  rw [← hsum']
  noncomm_ring

def binaryRowUnitary (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1) : unitary E :=
  ⟨finiteRowCocycle s t,
    finiteRowCocycle_gram 1 s t (by simp) (by simp) hs ht hsum htsum⟩

lemma finiteRowCocycle_conjugate_shift (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (x : E) :
    finiteRowCocycle s t * finiteRowShift s x * star (finiteRowCocycle s t) =
      finiteRowShift t x := by
  simp only [finiteRowShift, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have he : star (s i) * star (finiteRowCocycle s t) = star (t i) := by
    simpa only [star_mul] using congrArg star
      (finiteRowCocycle_mul_row 1 s t (by simp) (by simp) hs ht i)
  calc
    _ = (finiteRowCocycle s t * s i) * x *
        (star (s i) * star (finiteRowCocycle s t)) := by noncomm_ring
    _ = _ := by rw [finiteRowCocycle_mul_row 1 s t (by simp) (by simp) hs ht, he]

lemma binarySplitHom_conjugacy (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1) (x : unitary E) :
    binarySplitHom (t 0) (t 1) (by simpa using ht 0 0)
        (by simpa using ht 1 1) (by simpa using ht 0 1) x =
      binaryRowUnitary s t hs ht hsum htsum *
        binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
          (by simpa using hs 1 1) (by simpa using hs 0 1) x *
        (binaryRowUnitary s t hs ht hsum htsum)⁻¹ := by
  apply Subtype.ext
  rw [binarySplitHom_coe t ht htsum]
  change finiteRowShift t x = finiteRowCocycle s t *
    (binarySplitHom (s 0) (s 1) _ _ _ x : E) * star (finiteRowCocycle s t)
  rw [binarySplitHom_coe s hs hsum]
  exact (finiteRowCocycle_conjugate_shift s t hs ht x).symm

lemma binarySplitHom_iterate_coe (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (x : unitary E) (n : ℕ) :
    (((binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
      (by simpa using hs 1 1) (by simpa using hs 0 1))^[n]) x : E) =
        finiteRowShiftIterate s n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', binarySplitHom_coe s hs hsum, finiteRowShiftIterate, ih]

lemma finiteRowShift_star (s : Fin 2 → E) (x : E) :
    star (finiteRowShift s x) = finiteRowShift s (star x) := by
  simp only [finiteRowShift, star_sum, star_mul, star_star, mul_assoc]

lemma finiteRowShiftIterate_star (s : Fin 2 → E) (n : ℕ) (x : E) :
    star (finiteRowShiftIterate s n x) = finiteRowShiftIterate s n (star x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [finiteRowShiftIterate, finiteRowShift_star, ih]; rfl

def binaryRowCocycleUnitary (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1) (n : ℕ) : unitary E :=
  finiteGroupCocycle (binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
    (by simpa using hs 1 1) (by simpa using hs 0 1))
    (binaryRowUnitary s t hs ht hsum htsum) n

/-- The splitting defect of the actual product cocycle, not the product
itself, is the adjoint joint-word permutation. -/
lemma binaryRowCocycleUnitary_defect (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1) (n : ℕ) :
    ((binaryRowCocycleUnitary s t hs ht hsum htsum n : E) *
      star (binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
        (by simpa using hs 1 1) (by simpa using hs 0 1)
        (binaryRowCocycleUnitary s t hs ht hsum htsum n) : E)) =
      star (finiteJointCycleCoboundary t s n) := by
  let α := binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
    (by simpa using hs 1 1) (by simpa using hs 0 1)
  let β := binarySplitHom (t 0) (t 1) (by simpa using ht 0 0)
    (by simpa using ht 1 1) (by simpa using ht 0 1)
  let w := binaryRowUnitary s t hs ht hsum htsum
  have h := finiteGroupCocycle_splitting_defect α β w
    (binarySplitHom_conjugacy s t hs ht hsum htsum) n
  rw [map_inv] at h
  have he := congrArg (fun v : unitary E => (v : E)) h
  change (↑(finiteGroupCocycle α w n) : E) * star (↑(α (finiteGroupCocycle α w n)) : E) =
    ((β^[n]) (w⁻¹) : E) * (w : E) at he
  rw [binarySplitHom_iterate_coe t ht htsum] at he
  change (binaryRowCocycleUnitary s t hs ht hsum htsum n : E) *
    star (α (binaryRowCocycleUnitary s t hs ht hsum htsum n) : E) =
      finiteRowShiftIterate t n (star (finiteRowCocycle s t)) * finiteRowCocycle s t at he
  simpa only [finiteJointCycleCoboundary, star_mul, finiteRowShiftIterate_star,
    star_star, finiteRowCocycle_star] using he

/-- Uniform paths for the genuine binary product cocycles. The bound is
independent of the number of factors. These are coisometric rows in the
ambient unit; applying this in a proper corner requires corner transport. -/
lemma exists_uniform_binaryRowCocycle_path [Nontrivial E] (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hc : ∀ i j, Commute (s i) (t j)) (n : ℕ) :
    ∃ p : Path (binaryRowCocycleUnitary s t hs ht hsum htsum n) 1,
      ∀ a b, ‖(p a : E) - p b‖ ≤ (192 * Real.pi) * |(a : ℝ) - b| := by
  let v := binaryRowCocycleUnitary s t hs ht hsum htsum n
  let α := binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
    (by simpa using hs 1 1) (by simpa using hs 0 1)
  obtain ⟨c, hcoe, p, hp⟩ := exists_controlled_jointCycleCoboundary_path
    1 t s (by simp) (by simp) ht hs htsum hsum (fun i j => (hc j i).symm) n
  simp only [sub_self, add_zero] at hcoe
  have hd : v * star (α v) = star c := by
    apply Subtype.ext
    change (v : E) * star (α v : E) = star (c : E)
    rw [hcoe]
    exact binaryRowCocycleUnitary_defect s t hs ht hsum htsum n
  let q : Path (1 : unitary E) (v * star (α v)) :=
    (p.map (continuous_star : Continuous (star : unitary E → unitary E))).cast (by simp) hd
  have hq : ∀ a b, ‖(q a : E) - q b‖ ≤ (4 * Real.pi) * |(a : ℝ) - b| := by
    intro a b
    change ‖star (p a : E) - star (p b : E)‖ ≤ _
    rw [← star_sub, norm_star]
    exact hp a b
  obtain ⟨r, hr⟩ := exists_binaryFragmentation_of_defect_path (s 0) (s 1)
    (by simpa using hs 0 0) (by simpa using hs 1 1) (by simpa using hs 0 1)
    v (4 * Real.pi) (by positivity) q hq
  refine ⟨r, ?_⟩
  intro a b
  simpa only [show 32 * (4 * Real.pi + 2 * Real.pi) = 192 * Real.pi by ring] using hr a b

end WeakPureInfiniteness

end

end OAI
