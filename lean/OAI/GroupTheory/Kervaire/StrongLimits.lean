import OAI.GroupTheory.Kervaire.ComponentFibers

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace KervaireStrong
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {ι : Type*} {l : Filter ι}
abbrev Operator (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] := H →L[ℂ] H

def StrongTendsto (T : ι → Operator H) (l : Filter ι) (S : Operator H) : Prop :=
  ∀ ξ, Tendsto (fun i => T i ξ) l (𝓝 (S ξ))

/-- Joint continuity of evaluation for strong convergence on an operator-norm
bounded family. -/
theorem StrongTendsto.apply_variable {T : ι → Operator H} {S : Operator H}
    (h : StrongTendsto T l S) {C : ℝ} (_hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C)
    {x : ι → H} {ξ : H} (hx : Tendsto x l (𝓝 ξ)) :
    Tendsto (fun i => T i (x i)) l (𝓝 (S ξ)) := by
  have hzero : Tendsto (fun i => T i (x i - ξ)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun i => (T i).le_of_opNorm_le (hb i) _)
    have hx' : Tendsto (fun i => ‖x i - ξ‖) l (𝓝 0) := by
      simpa using (hx.sub (tendsto_const_nhds (x := ξ))).norm
    simpa using hx'.const_mul C
  have hs := hzero.add (h ξ)
  simpa only [map_sub, sub_add_cancel, zero_add] using hs

theorem StrongTendsto.mul {T T' : ι → Operator H} {S S' : Operator H}
    (h : StrongTendsto T l S) (h' : StrongTendsto T' l S')
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C) :
    StrongTendsto (fun i => T i * T' i) l (S * S') := by
  intro ξ
  exact h.apply_variable hC hb (h' ξ)

theorem StrongTendsto.pow {T : ι → Operator H} {S : Operator H}
    (h : StrongTendsto T l S) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C)
    (n : ℕ) : StrongTendsto (fun i => T i ^ n) l (S ^ n) := by
  induction n with
  | zero => intro ξ; simp only [pow_zero]; exact tendsto_const_nhds
  | succ n ih => simpa only [pow_succ'] using h.mul ih hC hb

/-- Exponentiation is strongly continuous on uniformly bounded families. -/
theorem StrongTendsto.exp [CompleteSpace H] {T : ι → Operator H} {S : Operator H}
    (h : StrongTendsto T l S) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C) :
    StrongTendsto (fun i => NormedSpace.exp (T i)) l (NormedSpace.exp S) := by
  intro ξ
  let a : ℕ → ℝ := fun n => (n.factorial : ℝ)⁻¹
  have hs (R : Operator H) : HasSum (fun n => a n • ((R ^ n) ξ))
      (NormedSpace.exp R ξ) := by
    simpa [a] using
      ((ContinuousLinearMap.apply ℂ H ξ).restrictScalars ℝ).hasSum
        (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) R)
  have ht := tendsto_tsum_of_dominated_convergence
    ((NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) C).mul_right ‖ξ‖)
    (fun n => (h.pow hC hb n ξ).const_smul (a n)) ?_
  · simpa only [(hs _).tsum_eq] using ht
  · filter_upwards [] with i n
    calc
      ‖a n • ((T i ^ n) ξ)‖ = ‖a n‖ * ‖(T i ^ n) ξ‖ := norm_smul _ _
      _ ≤ ‖a n‖ * (C ^ n * ‖ξ‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', mul_apply_eq_comp]
          exact ((T i).le_of_opNorm_le (hb i) _).trans
            ((mul_le_mul_of_nonneg_left ih hC).trans_eq (by rw [pow_succ']; ring))
      _ = ‖(n.factorial : ℝ)⁻¹ • C ^ n‖ * ‖ξ‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hC n)]
        exact (mul_assoc _ _ _).symm

/-- A strong limit preserves commutation with any fixed bounded operator. -/
theorem StrongTendsto.commute {T : ι → Operator H} {S R : Operator H} [l.NeBot]
    (h : StrongTendsto T l S) (hc : ∀ i, Commute (T i) R) : Commute S R := by
  apply ContinuousLinearMap.ext
  intro ξ
  exact tendsto_nhds_unique (h (R ξ))
    ((R.continuous.tendsto (S ξ)).comp (h ξ) |>.congr fun i =>
      congrArg (fun L : Operator H => L ξ) (hc i).eq.symm)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
open scoped ComplexOrder

/-- The positive cone is strongly closed, even on an uncountable Hilbert space. -/
theorem StrongTendsto.nonneg {T : ι → Operator K} {S : Operator K} [l.NeBot]
    (h : StrongTendsto T l S) (hp : ∀ i, 0 ≤ T i) : 0 ≤ S := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply (ContinuousLinearMap.isPositive_iff_complex S).mpr
  intro ξ
  have ht := Filter.Tendsto.inner (𝕜 := ℂ) (h ξ) (tendsto_const_nhds (x := ξ))
  have hi (i) := Complex.nonneg_iff.mp
    ((ContinuousLinearMap.nonneg_iff_isPositive.mp (hp i)).inner_nonneg_left ξ)
  have hre : 0 ≤ (inner ℂ (S ξ) ξ).re :=
    ge_of_tendsto ((Complex.continuous_re.tendsto _).comp ht) (Eventually.of_forall fun i => (hi i).1)
  have him : (inner ℂ (S ξ) ξ).im = 0 :=
    tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp ht)
      (tendsto_const_nhds.congr fun i => (hi i).2)
  exact ⟨Complex.ext rfl (by simpa using him.symm), hre⟩

end KervaireStrong

end

end OAI
