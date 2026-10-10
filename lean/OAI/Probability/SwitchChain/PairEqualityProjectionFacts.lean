import OAI.Probability.SwitchChain.PairEqualityProjection
import OAI.Probability.SwitchChain.PairEqualityErrorLine

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem expectation_centered (i j k l : Fin n) :
    expectation n d {i,j} (centered i j k l) = 0 := by
  rw [centered, fluctuation_eq_sub, map_sub, expectation_idempotent, sub_self]

theorem expectation_eq_zero_of_mem_equalitySpace (i j k l : Fin n)
    (f : StateSpace n d) (hf : f ∈ equalitySpace i j k l) :
    expectation n d {i,j} f = 0 := by
  ext G
  obtain ⟨c, hc⟩ := hf G
  by_cases ha : active i j k l G
  · have hs : (∑ H ∈ fiberStates {i,j} G, f H) =
        c * ∑ H ∈ fiberStates {i,j} G, centered i j k l H := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro H hH
      simpa only [ite_eq_left ha] using hc H ((mem_fiberStates {i,j} G H).mp hH)
    rw [expectation_eq_average, hs]
    have hz := congrArg (fun v : StateSpace n d => v G)
      (expectation_centered (d := d) i j k l)
    change expectation n d {i,j} (centered i j k l) G = 0 at hz
    rw [expectation_eq_average] at hz
    change (c * ∑ H ∈ fiberStates {i,j} G, centered i j k l H) / _ = 0
    rw [mul_div_assoc, hz, mul_zero]
  · rw [expectation_eq_average]
    have hz : (∑ H ∈ fiberStates {i,j} G, f H) = 0 := by
      apply Finset.sum_eq_zero
      intro H hH
      simpa only [ite_eq_right ha, mul_zero] using hc H ((mem_fiberStates {i,j} G H).mp hH)
    simp only [hz, zero_div, PiLp.zero_apply]

theorem equalitySpace_le_orthogonal (i j k l : Fin n) :
    equalitySpace (d := d) i j k l ≤ (fiberSpace n d {i,j})ᗮ := by
  intro f hf
  exact (Submodule.starProjection_apply_eq_zero_iff (fiberSpace n d {i,j})).mp
    (expectation_eq_zero_of_mem_equalitySpace i j k l f hf)

theorem projection_isSymmetric (i j k l : Fin n) :
    (projection (d := d) i j k l).toLinearMap.IsSymmetric :=
  (equalitySpace i j k l).starProjection_isSymmetric

@[simp] theorem projection_idempotent (i j k l : Fin n) (f : StateSpace n d) :
    projection i j k l (projection i j k l f) = projection i j k l f :=
  (projection_eq_self_iff i j k l _).mpr
    ((equalitySpace i j k l).starProjection_apply_mem f)

theorem projection_eq_zero_of_mem_fiberSpace (i j k l : Fin n)
    (f : StateSpace n d) (hf : f ∈ fiberSpace n d {i,j}) :
    projection i j k l f = 0 := by
  apply (Submodule.starProjection_apply_eq_zero_iff (equalitySpace i j k l)).mpr
  apply (Submodule.mem_orthogonal _ _).mpr
  intro g hg
  exact (Submodule.mem_orthogonal' _ _).mp
    (equalitySpace_le_orthogonal i j k l hg) f hf

@[simp] theorem projection_constant (i j k l : Fin n) (c : ℝ) :
    projection (d := d) i j k l (WithLp.toLp 2 (fun _ => c)) = 0 :=
  projection_eq_zero_of_mem_fiberSpace i j k l _ (constant_mem _ c)

@[simp] theorem projection_expectation (i j k l : Fin n) (f : StateSpace n d) :
    projection i j k l (expectation n d {i,j} f) = 0 :=
  projection_eq_zero_of_mem_fiberSpace i j k l _ (expectation_mem _ f)

@[simp] theorem expectation_projection (i j k l : Fin n) (f : StateSpace n d) :
    expectation n d {i,j} (projection i j k l f) = 0 :=
  expectation_eq_zero_of_mem_equalitySpace i j k l _
    ((equalitySpace i j k l).starProjection_apply_mem f)

@[simp] theorem projection_fluctuation (i j k l : Fin n) (f : StateSpace n d) :
    projection i j k l (fluctuation n d {i,j} f) = projection i j k l f := by
  rw [fluctuation_eq_sub, map_sub, projection_expectation, sub_zero]

@[simp] theorem fluctuation_projection (i j k l : Fin n) (f : StateSpace n d) :
    fluctuation n d {i,j} (projection i j k l f) = projection i j k l f := by
  rw [fluctuation_eq_sub, expectation_projection, sub_zero]

theorem gated_rowExtreme_fluctuation_mem (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) :
    fluctuation n d {i,j} (WithLp.toLp 2 (fun H : GraphState n d =>
      PairEqualityErrorLine.rowExtreme H.val i j k l)) ∈ equalitySpace i j k l := by
  intro G
  refine ⟨1, fun H h => ?_⟩
  rw [PairEqualityErrorLine.fluctuation_rowExtreme i j k l hij hk hl H]
  have ha := active_sameFiber i j k l hij h
  by_cases activeG : active i j k l G
  · have activeH := ha.mp activeG
    simp only [active] at activeH
    simp only [ite_eq_left activeH, ite_eq_left activeG, one_mul]
    rfl
  · have inactiveH := mt ha.mpr activeG
    simp only [active] at inactiveH
    simp only [ite_eq_right inactiveH, ite_eq_right activeG, mul_zero]

theorem projection_fixes_gated_rowExtreme_fluctuation (i j k l : Fin n)
    (hij : i ≠ j) (hk : Outside i j k) (hl : Outside i j l) :
    projection (d := d) i j k l (fluctuation n d {i,j}
      (WithLp.toLp 2 (fun H : GraphState n d => PairEqualityErrorLine.rowExtreme H.val i j k l))) =
    fluctuation n d {i,j}
      (WithLp.toLp 2 (fun H : GraphState n d => PairEqualityErrorLine.rowExtreme H.val i j k l)) :=
  (projection_eq_self_iff i j k l _).mpr
    (gated_rowExtreme_fluctuation_mem i j k l hij hk hl)

theorem gated_affine_rowExtreme_fluctuation_mem (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l)
    (w : GraphState n d → ℝ)
    (hw : ∀ G H, SameFiber {i,j} G.val H.val → w G = w H)
    (s r : ℝ) :
    fluctuation n d {i,j} (WithLp.toLp 2 (fun H : GraphState n d =>
      w H * (s * PairEqualityErrorLine.rowExtreme H.val i j k l + r))) ∈
      equalitySpace i j k l := by
  intro G
  refine ⟨w G * s, fun H h => ?_⟩
  rw [PairEqualityErrorLine.fluctuation_cell_affine_rowExtreme i j k l hij hk hl w hw s r H]
  have ha := active_sameFiber i j k l hij h
  rw [← hw G H h]
  by_cases activeG : active i j k l G
  · have activeH := ha.mp activeG
    simp only [active] at activeH
    simp only [ite_eq_left activeH, ite_eq_left activeG]
    rfl
  · have inactiveH := mt ha.mpr activeG
    simp only [active] at inactiveH
    simp only [ite_eq_right inactiveH, ite_eq_right activeG, mul_zero]

theorem multiply_mem_equalitySpace (i j k l : Fin n) (w f : StateSpace n d)
    (hw : w ∈ fiberSpace n d {i,j}) (hf : f ∈ equalitySpace i j k l) :
    multiply w f ∈ equalitySpace i j k l := by
  intro G
  obtain ⟨c, hc⟩ := hf G
  refine ⟨w G * c, fun H h => ?_⟩
  change w H * f H = _
  rw [hw H G h.symm, hc H h, mul_assoc]

theorem multiply_inner (w f g : StateSpace n d) :
    ⟪multiply w f, g⟫ = ⟪f, multiply w g⟫ := by
  rw [state_inner, state_inner]
  apply Finset.sum_congr rfl
  intro G hG
  change (w G * f G) * g G = f G * (w G * g G)
  ring

theorem multiply_mem_equalitySpace_orthogonal (i j k l : Fin n)
    (w f : StateSpace n d) (hw : w ∈ fiberSpace n d {i,j})
    (hf : f ∈ (equalitySpace i j k l)ᗮ) :
    multiply w f ∈ (equalitySpace i j k l)ᗮ := by
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro g hg
  rw [multiply_inner]
  exact (Submodule.mem_orthogonal' _ _).mp hf (multiply w g)
    (multiply_mem_equalitySpace i j k l w g hw hg)

theorem projection_multiply (i j k l : Fin n) (w f : StateSpace n d)
    (hw : w ∈ fiberSpace n d {i,j}) :
    projection i j k l (multiply w f) = multiply w (projection i j k l f) := by
  have hp : projection i j k l f ∈ equalitySpace i j k l :=
    (equalitySpace i j k l).starProjection_apply_mem f
  have hr : f - projection i j k l f ∈ (equalitySpace i j k l)ᗮ := by
    apply (Submodule.starProjection_apply_eq_zero_iff (equalitySpace i j k l)).mp
    change projection i j k l (f - projection i j k l f) = 0
    rw [map_sub, projection_idempotent, sub_self]
  have hz := (Submodule.starProjection_apply_eq_zero_iff (equalitySpace i j k l)).mpr
    (multiply_mem_equalitySpace_orthogonal i j k l w _ hw hr)
  have heq : multiply w (f - projection i j k l f) =
      multiply w f - multiply w (projection i j k l f) := by
    ext G
    change w G * (f G - projection i j k l f G) =
      w G * f G - w G * projection i j k l f G
    ring
  change projection i j k l (multiply w (f - projection i j k l f)) = 0 at hz
  rw [heq, map_sub, (projection_eq_self_iff i j k l _).mpr
    (multiply_mem_equalitySpace i j k l w _ hw hp)] at hz
  exact sub_eq_zero.mp hz

theorem projection_restrict_fiberUnion (i j k l : Fin n)
    (C : GraphState n d → Prop)
    (hC : ∀ G H, SameFiber {i,j} G.val H.val → (C G ↔ C H))
    (f : StateSpace n d) :
    projection i j k l (WithLp.toLp 2 (fun G : GraphState n d => if C G then f G else 0)) =
      WithLp.toLp 2 (fun G : GraphState n d => if C G then projection i j k l f G else 0) := by
  let w : StateSpace n d := WithLp.toLp 2 (fun G => if C G then 1 else 0)
  have hw : w ∈ fiberSpace n d {i,j} := by
    intro G H h
    simp only [w, hC G H h]
  have h := projection_multiply i j k l w f hw
  simpa only [multiply, w, ite_mul, one_mul, zero_mul] using h

end Problem315.PairEquality

end

end OAI
