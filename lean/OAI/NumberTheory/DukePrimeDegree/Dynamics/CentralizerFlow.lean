import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootCentralizer

namespace OAI

/-!
# Small centralizer factors in late diagonal returns

The root-pair centralizer supplies a scalar double block and a complementary
matrix. A fixed neighborhood controls that complementary matrix; late
neutral diagonal times separate its spectrum and keep the scalar away
from the rational units.
-/

noncomputable section
open Set Filter Matrix
open scoped Classical Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def complementaryMatrix {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (g : G n) : Matrix (Fin m) (Fin m) ℝ :=
  fun r s => g.val (e.symm (Sum.inr r)) (e.symm (Sum.inr s))

lemma rootPairCentralizer_block_explicit {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (hij : e.symm (Sum.inl 0) ≠ e.symm (Sum.inl 1))
    (g : G n) (hg : g ∈ rootPairCentralizer hij) :
    Matrix.reindex e e g.val = Matrix.fromBlocks
      (Matrix.diagonal (fun _ : Fin 2 => g.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0))))
      0 0 (complementaryMatrix e g) := by
  obtain ⟨c, B, h⟩ := rootPairCentralizer_block e hij g hg
  have hc := congrArg (fun M => M (Sum.inl 0) (Sum.inl 0)) h
  change g.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) = c at hc
  have hB : complementaryMatrix e g = B := by
    ext r s
    exact congrArg (fun M => M (Sum.inr r) (Sum.inr s)) h
  rwa [← hc, ← hB] at h

lemma diagonal_mem_rootPairCentralizer {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell i = ell j) (t : ℝ) :
    diagonalOneParameter ell hell t ∈ rootPairCentralizer hij := by
  apply (mem_rootPairCentralizer hij _).mpr
  constructor
  · apply (commutes_root_one_iff hij _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      simp [diagonalOneParameter, Matrix.diagonal, hr]
    · intro s hs
      simp [diagonalOneParameter, Matrix.diagonal, Ne.symm hs]
    · simp [diagonalOneParameter, hneut]
  · apply (commutes_root_one_iff hij.symm _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      simp [diagonalOneParameter, Matrix.diagonal, hr]
    · intro s hs
      simp [diagonalOneParameter, Matrix.diagonal, Ne.symm hs]
    · simp [diagonalOneParameter, hneut]

lemma complementaryMatrix_diagonal_mul {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (t : ℝ) (g : G n) :
    complementaryMatrix e (diagonalOneParameter ell hell t * g) =
      Matrix.diagonal (fun r => Real.exp (ell (e.symm (Sum.inr r)) * t)) *
        complementaryMatrix e g := by
  ext r s
  change (Matrix.diagonal (fun i => Real.exp (ell i * t)) * g.val)
    (e.symm (Sum.inr r)) (e.symm (Sum.inr s)) = _
  simp only [Matrix.diagonal_mul, complementaryMatrix]

lemma continuous_complementaryMatrix {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m) :
    Continuous (complementaryMatrix e) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)

lemma complementaryMatrix_one {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m) :
    complementaryMatrix e 1 = 1 := by
  ext r s
  simp [complementaryMatrix, Matrix.one_apply, e.symm.injective.eq_iff]

lemma eventually_separated_scaled_weights {m : ℕ} (w : Fin m → ℝ)
    (hw : Function.Injective w) :
    ∀ᶠ k : ℕ in atTop, ∀ r s : Fin m, r ≠ s →
      1 < |w r * (k : ℝ) - w s * (k : ℝ)| := by
  apply Filter.eventually_all.mpr
  intro r
  apply Filter.eventually_all.mpr
  intro s
  by_cases hrs : r = s
  · exact Filter.Eventually.of_forall fun _ h => (h hrs).elim
  · have hp : 0 < |w r - w s| := abs_pos.mpr (sub_ne_zero.mpr (hw.ne hrs))
    have ht : Tendsto (fun k : ℕ => |w r - w s| * (k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hp
    filter_upwards [ht.eventually (eventually_gt_atTop (1 : ℝ))] with k hk _
    have habs : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
    simpa only [← sub_mul, abs_mul, habs] using hk

lemma eventually_scalar_between_zero_one {a : ℝ} (ha : a < 0) :
    ∀ᶠ k : ℕ in atTop, ∀ c : ℝ, 0 < c → c < Real.exp 1 →
      0 < Real.exp (a * (k : ℝ)) * c ∧ Real.exp (a * (k : ℝ)) * c < 1 := by
  have ht : Tendsto (fun k : ℕ => a * (k : ℝ)) atTop atBot :=
    tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg ha
  filter_upwards [ht.eventually (eventually_lt_atBot (-1 : ℝ))] with k hk c hc hc'
  refine ⟨mul_pos (Real.exp_pos _) hc, ?_⟩
  calc
    Real.exp (a * (k : ℝ)) * c < Real.exp (a * (k : ℝ)) * Real.exp 1 :=
      mul_lt_mul_of_pos_left hc' (Real.exp_pos _)
    _ = Real.exp (a * (k : ℝ) + 1) := (Real.exp_add _ _).symm
    _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)

/-- A fixed identity neighborhood simultaneously controls the scalar and
complementary blocks of every centralizer factor. -/
lemma eventually_small_centralizer_blocks {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (hij : e.symm (Sum.inl 0) ≠ e.symm (Sum.inl 1)) :
    ∀ᶠ g : rootPairCentralizer hij in 𝓝 1,
      0 < g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) ∧
      g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) < Real.exp 1 ∧
      ∀ r, ∑ s, ‖(complementaryMatrix e g.val - 1) r s‖ < spectralRelativeRadius := by
  have hc : Continuous (fun g : rootPairCentralizer hij =>
      g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0))) := by fun_prop
  have hscalar : Tendsto (fun g : rootPairCentralizer hij =>
      g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0))) (𝓝 1) (𝓝 1) := by
    convert hc.tendsto (1 : rootPairCentralizer hij) using 1; simp
  have hpos := hscalar.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hupper := hscalar.eventually (gt_mem_nhds
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)))
  have hcB : Continuous (fun g : rootPairCentralizer hij => complementaryMatrix e g.val) := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro s
    change Continuous (fun g : rootPairCentralizer hij =>
      g.val.val (e.symm (Sum.inr r)) (e.symm (Sum.inr s)))
    fun_prop
  have ht : Tendsto (fun g : rootPairCentralizer hij => complementaryMatrix e g.val)
      (𝓝 1) (𝓝 1) := by
    have h := hcB.tendsto (1 : rootPairCentralizer hij)
    change Tendsto _ _ (𝓝 (complementaryMatrix e (1 : G n))) at h
    rwa [complementaryMatrix_one] at h
  exact hpos.and (hupper.and (ht.eventually eventually_spectral_row_bound))

end DukePrimeDegree

end

end OAI
