import OAI.GroupTheory.PolycyclicRecognition.Algebra.RayMixedWidths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConjugationBounds
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledWordSums
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryLimits

namespace OAI

/-!+# Negative-height templates for the actual ray ideal

The halfspace construction is applied to the actual Cartan weights on
canonical height. Every word in the finite mixed-word spanning pool then
has positive width. Consequently a fixed ideal displacement shrinks in
every maximizing full word box, even after a polynomial loss.+-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter Set
open scoped BigOperators Topology

theorem isMixedWord_mono {I : Type*} {p q : I → Prop}
    (hpq : ∀ i, p i → q i) (w : FreeMagma I) (hw : IsMixedWord p w) :
    IsMixedWord q w := by
  induction w using FreeMagma.rec with
  | of i => exact hpq i hw
  | mul u v hu hv =>
    rcases hw with hw | hw
    · exact Or.inl (hu hw)
    · exact Or.inr (hv hw)

namespace CartanWordModel

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The switch template stays in a fixed strictly negative halfspace and
gives positive width to every word in the actual ray-ideal spanning pool. -/
theorem exists_negative_ray_ideal_template
    (α : W →L[ℝ] ℝ) (v₀ : W) (hα : α v₀ < 0) :
    let αH := α.toLinearMap.comp
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))
    ∃ E : Set W, IsCompact E ∧ Convex ℝ E ∧ v₀ ∈ E ∧
      (∀ v ∈ E, α v ≤ α v₀) ∧
      ∀ w : M.coneMixedWords (positiveWeightRay αH),
        0 < M.boxCost T hunimod eW E w.val := by
  let αH := α.toLinearMap.comp
    (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))
  let β : Fin M.letterCount → W →L[ℝ] ℝ := fun i =>
    ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
  have hβval (i : Fin M.letterCount) (h : H) :
      β i (eW (heightProjection T.character (h : L))) = M.weight i h := by
    change cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (h : L)))) = _
    rw [eW.symm_apply_apply, cartanHeightWeight_projection]
  have hβ (i : Fin M.letterCount) : β i ≠ 0 := by
    intro hz
    apply M.weight_nonzero i
    funext h
    have he := congrArg (fun f : W →L[ℝ] ℝ =>
      f (eW (heightProjection T.character (h : L)))) hz
    change β i (eW (heightProjection T.character (h : L))) = 0 at he
    change M.weight i h = 0
    rwa [hβval] at he
  have hout (i : Fin M.letterCount)
      (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∉ positiveWeightRay αH) :
      (β i).toLinearMap ∉ positiveWeightRay α.toLinearMap := by
    rintro ⟨c, hc, he⟩
    apply hi
    refine ⟨c, hc, ?_⟩
    apply LinearMap.ext
    intro h
    have hh := DFunLike.congr_fun he (eW (heightProjection T.character (h : L)))
    change M.weight i h = c * α (eW (heightProjection T.character (h : L)))
    simpa only [ContinuousLinearMap.coe_coe, hβval, LinearMap.smul_apply,
      smul_eq_mul] using hh
  obtain ⟨E, hE, hconv, hv₀, hheight, hpos⟩ :=
    exists_negative_halfspace_positive_mixed_widths α β v₀ hα hβ M.wordDegreeBound
  refine ⟨E, hE, hconv, hv₀, hheight, ?_⟩
  intro w
  exact hpos w.val (isMixedWord_mono hout _ w.property) (M.word_degrees_le w.val).2

omit [FiniteDimensional ℝ W] in
/-- A fixed element of the actual ideal becomes arbitrarily small in
the full maximizing boxes, including after any fixed polynomial loss. -/
theorem fixed_ideal_polynomial_box_norm_tendsto_zero
    (C : Set (H →ₗ[ℝ] ℝ)) (E : Set W)
    (hpos : ∀ w : M.coneMixedWords C, 0 < M.boxCost T hunimod eW E w.val)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β : ℕ → M.Bases)
    (hβ : ∀ n, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) (β n).val)
    (x : M.coneWordIdeal C) (A : ℝ) (hA : 0 ≤ A) (p : ℕ) :
    Tendsto (fun n : ℕ => A * (1 + (n : ℝ)) ^ p *
      ‖(M.boxBasis T hunimod eW E (β n) n).equivFun (x : cartanRootIdeal H)‖)
      atTop (𝓝 0) := by
  obtain ⟨b, w, hw⟩ := M.exists_cone_mixed_word_basis C
  obtain ⟨K, hK, hword⟩ := exists_uniform_rescaled_word_bound M.letter M.wordList b₀
  let cost := M.boxCost T hunimod eW E
  let f : ℕ → ℝ := fun n => ∑ j,
    (|b.repr x j| * K * A) * (1 + (n : ℝ)) ^ p * Real.exp (-cost (w j).val * n)
  have hf : Tendsto f atTop (𝓝 0) := by
    have hj (j) : Tendsto (fun n : ℕ =>
        (|b.repr x j| * K * A) * (1 + (n : ℝ)) ^ p * Real.exp (-cost (w j).val * n))
        atTop (𝓝 0) :=
      (summable_polynomial_exp_decay (|b.repr x j| * K * A) p (hpos (w j))).tendsto_atTop_zero
    simpa only [f, Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hj j)
  apply squeeze_zero (fun n => by positivity) _ hf
  intro n
  let bn := M.boxBasis T hunimod eW E (β n) n
  have hnorm (j) : ‖bn.equivFun (evalBracketWord M.letter (w j).val)‖ ≤
      K * Real.exp (-cost (w j).val * n) := by
    have hh := hword cost (β n) (hβ n) n (Nat.cast_nonneg n) (w j).val
    have he : evalBracketWord M.letter (w j).val =
        Real.exp (-cost (w j).val * n) •
          (Real.exp ((n : ℝ) * cost (w j).val) • evalBracketWord M.letter (w j).val) := by
      rw [smul_smul, ← Real.exp_add]
      have hz : -cost (w j).val * (n : ℝ) + n * cost (w j).val = 0 := by ring
      rw [hz, Real.exp_zero, one_smul]
    rw [he, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hx : (x : cartanRootIdeal H) = ∑ j, b.repr x j • evalBracketWord M.letter (w j).val := by
    have hh := congrArg (M.coneWordIdeal C).incl (b.sum_repr x)
    simp only [map_sum, map_smul, ← hw] at hh
    exact hh.symm
  have hh : ‖bn.equivFun (x : cartanRootIdeal H)‖ ≤
      ∑ j, |b.repr x j| * (K * Real.exp (-cost (w j).val * n)) := by
    rw [hx, map_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hnorm j) (abs_nonneg _)
  apply (mul_le_mul_of_nonneg_left hh (mul_nonneg hA (pow_nonneg (by positivity) _))).trans_eq
  simp only [Finset.mul_sum, f]
  apply Finset.sum_congr rfl
  intro j _
  ring

end CartanWordModel
end PolycyclicRecognition

end

end OAI
