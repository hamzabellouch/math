import OAI.Analysis.OInfinity.IncompleteTails

namespace OAI

/-! # Uniform paths for the actual incomplete binary cocycle

Binary fragmentation needs two orthogonal isometries, not a coisometric row.
For the complemented binary corner map, the splitting defect of an iterated
cocycle has a path controlled by the original one-step unitary. Thus the
bound is independent of the number of cocycle factors. The binary family
need not generate a dense subalgebra of O∞.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma incompleteUnitaryShift_sub_norm_le (φ : E →⋆ₙₐ[ℂ] E) (u v : unitary E) :
    ‖(incompleteUnitaryShift φ u : E) - incompleteUnitaryShift φ v‖ ≤ ‖(u : E) - v‖ := by
  have he : (incompleteUnitaryShift φ u : E) - incompleteUnitaryShift φ v =
      φ ((u : E) - v) := by
    simp only [incompleteUnitaryShift_coe, bergCornerLift, map_sub]
    abel
  rw [he]
  exact NonUnitalStarAlgHom.norm_apply_le φ _

lemma incompleteUnitaryShift_binary (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (u : unitary E) :
    incompleteUnitaryShift (finiteCuntzDiagonalHom s hs) u =
      binaryCornerUnitary (s 0) (by simpa using hs 0 0) u *
        binaryCornerUnitary (s 1) (by simpa using hs 1 1) u := by
  apply Subtype.ext
  change bergCornerLift (finiteCuntzDiagonalHom s hs) u =
    cornerCompression (s 0) u * cornerCompression (s 1) u
  rw [cornerCompression_pair_product (s 0) (s 1) u u (by simpa using hs 0 1)]
  change 1 - (∑ i : Fin 2, s i * 1 * star (s i)) +
      (∑ i : Fin 2, s i * (u : E) * star (s i)) = _
  simp only [Fin.sum_univ_two, mul_one]
  noncomm_ring

def conjugateUnitaryShift (α : unitary E →* unitary E) (u : unitary E) :
    unitary E →* unitary E where
  toFun x := u * α x * u⁻¹
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]; group

lemma conjugateUnitaryShift_continuous (α : unitary E →* unitary E)
    (hα : Continuous α) (u : unitary E) : Continuous (conjugateUnitaryShift α u) := by
  change Continuous (fun x => u * α x * u⁻¹)
  exact (continuous_const.mul hα).mul continuous_const

lemma conjugateUnitaryShift_sub_norm_le (α : unitary E →* unitary E)
    (hα : ∀ x y, ‖(α x : E) - α y‖ ≤ ‖(x : E) - y‖) (u x y : unitary E) :
    ‖(conjugateUnitaryShift α u x : E) - conjugateUnitaryShift α u y‖ ≤ ‖(x : E) - y‖ := by
  change ‖((u : E) * (α x : E)) * (u⁻¹ : unitary E) -
    ((u : E) * (α y : E)) * (u⁻¹ : unitary E)‖ ≤ _
  rw [← sub_mul, CStarRing.norm_mul_coe_unitary, ← mul_sub,
    CStarRing.norm_coe_unitary_mul]
  exact hα x y

lemma unitaryShift_iterate_sub_norm_le (α : unitary E →* unitary E)
    (hα : ∀ x y, ‖(α x : E) - α y‖ ≤ ‖(x : E) - y‖) (n : ℕ) (x y : unitary E) :
    ‖(α^[n] x : E) - α^[n] y‖ ≤ ‖(x : E) - y‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (hα _ _).trans ih

/-- A fixed path for `u` controls the splitting defects of all its product
cocycles. The two factors move simultaneously, so their speed is at most `2L`. -/
lemma exists_controlled_cocycle_splitting_path (α : unitary E →* unitary E)
    (hαcont : Continuous α)
    (hα : ∀ x y, ‖(α x : E) - α y‖ ≤ ‖(x : E) - y‖)
    (u : unitary E) (L : ℝ) (p : Path (1 : unitary E) u)
    (hp : ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b|) (n : ℕ) :
    ∃ q : Path (1 : unitary E)
        (finiteGroupCocycle (G := unitary E) α u n *
          star (α (finiteGroupCocycle (G := unitary E) α u n))),
      ∀ a b, ‖(q a : E) - q b‖ ≤ (2 * L) * |(a : ℝ) - b| := by
  let β := conjugateUnitaryShift α u
  have hβcont : Continuous β := conjugateUnitaryShift_continuous α hαcont u
  have hβ : ∀ x y, ‖(β x : E) - β y‖ ≤ ‖(x : E) - y‖ :=
    conjugateUnitaryShift_sub_norm_le α hα u
  have he := finiteGroupCocycle_splitting_defect α β u (fun _ => rfl) n
  have he' : (β^[n]) (star u) * u =
      finiteGroupCocycle (G := unitary E) α u n *
        star (α (finiteGroupCocycle (G := unitary E) α u n)) := by
    simpa only [map_inv, Unitary.star_eq_inv] using he.symm
  let q₀ : Path (1 : unitary E) ((β^[n]) (star u)) :=
    { toFun := fun t => (β^[n]) (star (p t))
      continuous_toFun := (hβcont.iterate n).comp (continuous_star.comp p.continuous)
      source' := by rw [p.source, star_one, Function.iterate_fixed (map_one β)]
      target' := by rw [p.target] }
  have hq₀ : ∀ a b, ‖(q₀ a : E) - q₀ b‖ ≤ L * |(a : ℝ) - b| := by
    intro a b
    exact (unitaryShift_iterate_sub_norm_le β hβ n _ _).trans (by
      change ‖star (p a : E) - star (p b : E)‖ ≤ _
      rw [← star_sub, norm_star]
      exact hp a b)
  let q := (q₀.mul p).cast (one_mul _).symm he'.symm
  refine ⟨q, ?_⟩
  intro a b
  change ‖((q₀.mul p) a : E) - (q₀.mul p) b‖ ≤ _
  simpa only [show L + L = 2 * L by ring] using
    unitaryPath_mul_sub_norm_le q₀ p L L hq₀ hp a b

/-- Uniform contraction of the genuine complemented binary cocycle. In
particular, no norm bound on the terminal projection enters this theorem. -/
lemma exists_uniform_incompleteBinaryCocycle_path (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (u : unitary E) (L : ℝ) (hL : 0 ≤ L) (p : Path (1 : unitary E) u)
    (hp : ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b|) (n : ℕ) :
    ∃ q : Path (finiteGroupCocycle (G := unitary E)
        (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u n) 1,
      ∀ a b, ‖(q a : E) - q b‖ ≤ (32 * (2 * L + 2 * Real.pi)) * |(a : ℝ) - b| := by
  let α := incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)
  let v := finiteGroupCocycle (G := unitary E) α u n
  obtain ⟨q, hq⟩ := exists_controlled_cocycle_splitting_path α
    (incompleteUnitaryShift_continuous _) (incompleteUnitaryShift_sub_norm_le _) u L p hp n
  have hend : v * star (binaryCornerUnitary (s 0) (by simpa using hs 0 0) v *
      binaryCornerUnitary (s 1) (by simpa using hs 1 1) v) = v * star (α v) := by
    rw [show α v = _ from incompleteUnitaryShift_binary s hs v]
  let q' := q.cast rfl hend
  apply exists_binaryFragmentation_of_defect_path (s 0) (s 1)
    (by simpa using hs 0 0) (by simpa using hs 1 1) (by simpa using hs 0 1)
    v (2 * L) (by positivity) q'
  intro a b
  change ‖(q a : E) - q b‖ ≤ _
  exact hq a b

/-- The explicit two-swap completion has a path of speed at most `4π`.
The bound does not depend on the rank of its initial projection. -/
lemma exists_controlled_unitary_extension [Nontrivial E] (v r : E)
    (hv : v * star v * v = v) (hr : star r * r = 1)
    (hpr : (star v * v) * r = 0) (hqr : (v * star v) * r = 0) :
    ∃ u : unitary E, (u : E) * (star v * v) = v ∧
      ∃ p : Path (1 : unitary E) u,
        ∀ a b, ‖(p a : E) - p b‖ ≤ (4 * Real.pi) * |(a : ℝ) - b| := by
  obtain ⟨u, _, hueq, hup⟩ := exists_explicit_connected_unitary_extension v r hv hr hpr hqr
  have hpp : (star v * v) * (star v * v) = star v * v := by
    calc
      _ = star v * (v * star v * v) := by noncomm_ring
      _ = _ := by rw [hv]
  have hpstar : star (star v * v) = star v * v := by simp only [star_mul, star_star]
  let a : unitary E := ⟨partialIsometrySwap (r * (star v * v)),
    partialIsometrySwap_isometry_projection_mem r (star v * v) hr hpstar hpp hpr⟩
  let b : unitary E := u * star a
  have hform : (u : E) = partialIsometrySwap (v * star r) * (a : E) := hueq
  have hbcoe : (b : E) = partialIsometrySwap (v * star r) := by
    change (u : E) * star (a : E) = _
    rw [hform, mul_assoc, a.property.2, mul_one]
  have hastar : star (a : E) = (a : E) := partialIsometrySwap_star _
  have hbstar : star (b : E) = (b : E) := by rw [hbcoe, partialIsometrySwap_star]
  obtain ⟨pa, hpa⟩ := exists_controlled_selfadjoint_unitary_path a hastar
  obtain ⟨pb, hpb⟩ := exists_controlled_selfadjoint_unitary_path b hbstar
  have hba : b * a = u := by
    dsimp only [b]
    simp only [mul_assoc, Unitary.star_mul_self, mul_one]
  let p := (pb.mul pa).cast (one_mul _).symm hba.symm
  refine ⟨u, hup, p, ?_⟩
  intro x y
  change ‖((pb.mul pa) x : E) - (pb.mul pa) y‖ ≤ _
  simpa only [show 2 * Real.pi + 2 * Real.pi = 4 * Real.pi by ring] using
    unitaryPath_mul_sub_norm_le pb pa (2 * Real.pi) (2 * Real.pi) hpb hpa x y

section ControlledTransfer
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A supplied common unused isometry gives an actual one-step transfer with
a path bound independent of the number of tested row entries. -/
lemma exists_controlled_row_transfer [Nontrivial E] (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (r : E) (hr : star r * r = 1)
    (hsr : ∀ i, star (s i) * r = 0) (htr : ∀ i, star (t i) * r = 0) :
    ∃ u : unitary E, (∀ i, (u : E) * s i = t i) ∧
      ∃ p : Path (1 : unitary E) u,
        ∀ a b, ‖(p a : E) - p b‖ ≤ (4 * Real.pi) * |(a : ℝ) - b| := by
  let v := finiteCuntzTransfer s t 1
  have hp : star v * v = finiteCuntzDiagonalHom s hs 1 := by
    change star v * v = ∑ i, s i * 1 * star (s i)
    simpa only [v, star_one, one_mul] using finiteCuntzTransfer_star_mul s t ht 1
  have hq : v * star v = finiteCuntzDiagonalHom t ht 1 := by
    dsimp only [v]
    rw [finiteCuntzTransfer_star, star_one]
    change finiteCuntzTransfer s t 1 * finiteCuntzTransfer t s 1 =
      ∑ i, t i * 1 * star (t i)
    simpa only [finiteCuntzTransfer_star, star_one, one_mul] using
      finiteCuntzTransfer_star_mul t s hs 1
  have hvp : v * (star v * v) = v := by
    rw [hp]
    change finiteCuntzTransfer s t 1 * (∑ i, s i * 1 * star (s i)) = v
    simp only [mul_one, Finset.mul_sum, ← mul_assoc, finiteCuntzTransfer_mul s t hs]
    simp only [v, finiteCuntzTransfer, mul_one]
  have hv : v * star v * v = v := by simpa only [mul_assoc] using hvp
  have hpr : (star v * v) * r = 0 := by
    rw [hp]
    change (∑ i, s i * 1 * star (s i)) * r = 0
    simp only [Finset.sum_mul, mul_assoc, hsr, mul_zero, Finset.sum_const_zero]
  have hqr : (v * star v) * r = 0 := by
    rw [hq]
    change (∑ i, t i * 1 * star (t i)) * r = 0
    simp only [Finset.sum_mul, mul_assoc, htr, mul_zero, Finset.sum_const_zero]
  obtain ⟨u, hup, p, hpath⟩ := exists_controlled_unitary_extension v r hv hr hpr hqr
  refine ⟨u, ?_, p, hpath⟩
  intro i
  have hpi : (star v * v) * s i = s i := by
    rw [hp]
    exact (finiteCuntzTransfer_mul s s hs 1 i).trans (mul_one (s i))
  calc
    (u : E) * s i = (u : E) * ((star v * v) * s i) := by rw [hpi]
    _ = v * s i := by rw [← mul_assoc, hup]
    _ = t i := by simpa only [mul_one] using finiteCuntzTransfer_mul s t hs 1 i

end ControlledTransfer

/-- All canonical finite rows have a controlled one-step completion. The
unused product generator supplies the common isometry explicitly. -/
lemma exists_controlled_canonical_transfer [Nontrivial E] (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : ∀ i j, Commute (star (t i)) (s j)) (N : ℕ) :
    ∃ u : unitary E, (∀ i < N, (u : E) * s i = t i) ∧
      ∃ p : Path (1 : unitary E) u,
        ∀ a b, ‖(p a : E) - p b‖ ≤ (4 * Real.pi) * |(a : ℝ) - b| := by
  let r := s N * t N
  have hr : star r * r = 1 := by
    dsimp only [r]
    rw [star_mul]
    calc
      _ = star (t N) * (star (s N) * s N) * t N := by noncomm_ring
      _ = 1 := by rw [hs, ite_eq_left rfl, mul_one, ht, ite_eq_left rfl]
  have hsr (i : Fin N) : star (s i) * r = 0 := by
    dsimp only [r]
    rw [← mul_assoc, hs, ite_eq_right (Nat.ne_of_lt i.isLt), zero_mul]
  have htr (i : Fin N) : star (t i) * r = 0 := by
    dsimp only [r]
    rw [← mul_assoc, (hc i N).eq, mul_assoc, ht,
      ite_eq_right (Nat.ne_of_lt i.isLt), mul_zero]
  obtain ⟨u, hu, p, hp⟩ := exists_controlled_row_transfer
    (fun i : Fin N => s i) (fun i : Fin N => t i)
    (fun i j => by simpa only [Fin.ext_iff] using hs i j)
    (fun i j => by simpa only [Fin.ext_iff] using ht i j) r hr hsr htr
  exact ⟨u, fun i hi => hu ⟨i, hi⟩, p, hp⟩

/-- Canonical binary cocycles have a uniform `320π` path bound. -/
lemma exists_uniform_canonicalBinaryCocycle_paths [Nontrivial E] (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : ∀ i j, Commute (star (t i)) (s j)) :
    ∃ u : unitary E, (∀ i < 2, (u : E) * s i = t i) ∧
      ∀ n, ∃ p : Path (canonicalIncompleteCocycle s hs 2 u n) 1,
        ∀ a b, ‖(p a : E) - p b‖ ≤ (320 * Real.pi) * |(a : ℝ) - b| := by
  obtain ⟨u, hu, p, hp⟩ := exists_controlled_canonical_transfer s t hs ht hc 2
  refine ⟨u, hu, ?_⟩
  intro n
  obtain ⟨q, hq⟩ := exists_uniform_incompleteBinaryCocycle_path
    (fun i : Fin 2 => s i) (fun i j => by simpa only [Fin.ext_iff] using hs i j)
    u (4 * Real.pi) (by positivity) p hp n
  refine ⟨q, ?_⟩
  intro a b
  change ‖(q a : E) - q b‖ ≤ _
  simpa only [show 32 * (2 * (4 * Real.pi) + 2 * Real.pi) = 320 * Real.pi by ring] using hq a b

end WeakPureInfiniteness

end

end OAI
