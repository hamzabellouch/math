import OAI.Analysis.OInfinity.ProperBufferAbsorption
import OAI.Analysis.OInfinity.FiniteRowCompletion

namespace OAI

/-! # Absorption with a canonical vacuum spare

A second unused source isometry is orthogonal to every word in the finite
Fock sum. It therefore completes that sum to a connected ambient unitary
without requiring the target corner to commute with the source row. The
commutation requirements on the tested target entries remain explicit.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

/-- The second source spare replaces source-corner commutation in the
connected Fock completion. Only the selected target entries must commute
with the fixed binary coefficients. -/
lemma BufferAbsorptionCorner.exists_vacuum_absorption_on [Nontrivial E]
    (D : BufferAbsorptionCorner E) (s t : I → E) (r z : E) (P : I → Prop)
    (hrr : star r * r = 1) (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hzz : star z * z = 1) (hqz : D.q * z = 0)
    (hzr : star z * r = 0) (hzs : ∀ i, star z * s i = 0)
    (htq : ∀ i, t i * D.q = t i) (ht : ∑ i, t i * star (t i) = D.q)
    (htt : ∀ i j, star (t i) * t j = if i = j then D.q else 0)
    (hat : ∀ i, P i → Commute (star D.a) (t i))
    (hbt : ∀ i, P i → Commute (star D.b) (t i))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W : unitary E, Joined D.anchor W ∧
      ∀ i, P i → ‖(W : E) * s i - (t i + D.w * s i * star D.w) * (W : E)‖ < ε := by
  let δ := ε / 6
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / δ ^ 2)
  have hsmall : 2 / ((m : ℝ) + 1) < δ ^ 2 := by
    have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
    have hm' : 2 < (m : ℝ) * δ ^ 2 := (div_lt_iff₀ hδsq).mp hm
    apply (div_lt_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mpr
    nlinarith
  let v := finiteRowIsometry s t r D.q m
  have hvg : star v * v = D.q := finiteRowIsometry_gram s t r D.q
    D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq hrr hr hs htq ht m
  have hvq : v * D.q = v := relativeIsometry_mul_support v D.q hvg
    D.projection.isSelfAdjoint.star_eq D.projection.isIdempotentElem.eq
  have hvz : star v * z = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star
      (finiteRowIsometry_unused s t r D.q z hzr hzs m)
  obtain ⟨u, hu, _, huv⟩ := exists_explicit_connected_unitary_extension v z
    (by rw [mul_assoc, hvg, hvq]) hzz (by rw [hvg]; exact hqz)
    (by rw [mul_assoc, hvz, mul_zero])
  have huq : (u : E) * D.q = v := by simpa only [hvg] using huv
  have hvn : ‖v‖ ≤ 1 := finiteRowIsometry_norm_le s t r D.q
    D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq hrr hr hs htq ht m
  refine ⟨D.absorption u, D.absorption_joined_anchor u hu, ?_⟩
  intro i hi
  have hf : ‖s i * v - v * t i‖ < δ := by
    have h := finiteRowIsometry_forward_norm_sq s t r D.q
      D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq
      hrr hr hs htq ht htt m i
    change ‖s i * v - v * t i‖ ^ 2 ≤ _ at h
    nlinarith [norm_nonneg (s i * v - v * t i)]
  have hb : ‖star v * s i - t i * star v‖ < δ := by
    have h := finiteRowIsometry_backward_norm_sq s t r D.q
      D.projection.isIdempotentElem.eq D.projection.isSelfAdjoint.star_eq
      hrr hr hs htq ht htt m i
    have he : star v * s i - t i * star v =
        star (star (s i) * v - v * star (t i)) := by
      simp only [star_sub, star_mul, star_star]
    rw [he, norm_star]
    have hone : ((m : ℝ) + 1)⁻¹ ≤ 2 / ((m : ℝ) + 1) := by
      rw [← one_div]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    change ‖star (s i) * v - v * star (t i)‖ ^ 2 ≤ _ at h
    nlinarith [norm_nonneg (star (s i) * v - v * star (t i))]
  calc
    _ ≤ 2 * ‖s i * v - v * t i‖ + 3 * ‖star v * s i - t i * star v‖ :=
      D.absorption_error_bound u v (s i) (t i) huq (htq i) (hat i hi) (hbt i hi) hvn
    _ < ε := by dsimp only [δ] at hf hb; linarith


/-- Canonical source rows supply both required spare isometries. The
only geometric condition on the target corner is its annihilation of the
second unused generator, as provided by the canonical vacuum split. -/
lemma BufferAbsorptionCorner.exists_canonical_vacuum_absorption [Nontrivial E]
    (D : BufferAbsorptionCorner E) (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (t : Fin n → E)
    (hqz : D.q * s (n + 1) = 0)
    (htq : ∀ i, t i * D.q = t i) (ht : ∑ i, t i * star (t i) = D.q)
    (htt : ∀ i j, star (t i) * t j = if i = j then D.q else 0)
    (hat : ∀ i, Commute (star D.a) (t i))
    (hbt : ∀ i, Commute (star D.b) (t i))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W : unitary E, Joined D.anchor W ∧
      ∀ i : Fin n,
        ‖(W : E) * s i - (t i + D.w * s i * star D.w) * (W : E)‖ < ε := by
  have hsource (i j : Fin n) : star (s i) * s j = if i = j then 1 else 0 := by
    simpa only [Fin.ext_iff] using hs i j
  have hroot (i : Fin n) : star (s n) * s i = 0 := by
    rw [hs, ite_eq_right (by omega)]
  have hspare (i : Fin n) : star (s (n + 1)) * s i = 0 := by
    rw [hs, ite_eq_right (by omega)]
  obtain ⟨W, hW, hWi⟩ := D.exists_vacuum_absorption_on (fun i : Fin n => s i) t
    (s n) (s (n + 1)) (fun _ => True)
    (by simpa only [ite_true] using hs n n) hroot hsource
    (by simpa only [ite_true] using hs (n + 1) (n + 1)) hqz
    (by rw [hs, ite_eq_right (by omega)]) hspare htq ht htt
    (fun i _ => hat i) (fun i _ => hbt i) ε hε
  exact ⟨W, hW, fun i => hWi i True.intro⟩


end WeakPureInfiniteness

end

end OAI
