import Mathlib

namespace OAI




noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials
section LinearCost
variable {H M : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- Linear Hilbert-plus-path cost, with the Hilbert residual eliminated.
    This is exactly inf_{x=h+B μ} (‖h‖+‖μ‖), not the quadratic cost. -/
def linearCost (B : M →L[ℝ] H) (x : H) : ℝ :=
  ⨅ μ : M, ‖x - B μ‖ + ‖μ‖

lemma linearCost_bddBelow (B : M →L[ℝ] H) (x : H) :
    BddBelow (range fun μ : M => ‖x - B μ‖ + ‖μ‖) :=
  ⟨0, by rintro _ ⟨μ, rfl⟩; positivity⟩

lemma linearCost_nonneg (B : M →L[ℝ] H) (x : H) : 0 ≤ linearCost B x := by
  exact le_ciInf fun μ => add_nonneg (norm_nonneg _) (norm_nonneg _)

lemma linearCost_le (B : M →L[ℝ] H) (x : H) (μ : M) :
    linearCost B x ≤ ‖x - B μ‖ + ‖μ‖ :=
  ciInf_le (linearCost_bddBelow B x) μ

lemma linearCost_le_norm (B : M →L[ℝ] H) (x : H) :
    linearCost B x ≤ ‖x‖ := by
  simpa using linearCost_le B x 0

@[simp] lemma linearCost_zero (B : M →L[ℝ] H) : linearCost B 0 = 0 := by
  exact le_antisymm (by simpa using linearCost_le_norm B 0) (linearCost_nonneg B 0)

lemma linearCost_synthesis_le (B : M →L[ℝ] H) (μ : M) :
    linearCost B (B μ) ≤ ‖μ‖ := by
  simpa using linearCost_le B (B μ) μ

/-- The lower comparison does not assume an attained decomposition. -/
lemma norm_le_mul_linearCost (B : M →L[ℝ] H) {K : ℝ} (hK : 1 ≤ K)
    (hB : ∀ μ : M, ‖B μ‖ ≤ K * ‖μ‖) (x : H) :
    ‖x‖ ≤ K * linearCost B x := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rw [mul_comm K (linearCost B x)]
  apply (div_le_iff₀ hK0).mp
  apply le_ciInf
  intro μ
  apply (div_le_iff₀ hK0).mpr
  calc
    ‖x‖ = ‖(x - B μ) + B μ‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - B μ‖ + ‖B μ‖ := norm_add_le _ _
    _ ≤ K * ‖x - B μ‖ + K * ‖μ‖ :=
      add_le_add (le_mul_of_one_le_left (norm_nonneg _) hK) (hB μ)
    _ = (‖x - B μ‖ + ‖μ‖) * K := by ring

lemma linearCost_add_le (B : M →L[ℝ] H) (x y : H) :
    linearCost B (x + y) ≤ linearCost B x + linearCost B y := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  obtain ⟨μ, hμ⟩ := (ciInf_lt_iff (linearCost_bddBelow B x)).mp
    (show linearCost B x < r - linearCost B y by linarith)
  obtain ⟨ν, hν⟩ := (ciInf_lt_iff (linearCost_bddBelow B y)).mp
    (show linearCost B y < r - (‖x - B μ‖ + ‖μ‖) by linarith)
  calc
    linearCost B (x + y) ≤ ‖x + y - B (μ + ν)‖ + ‖μ + ν‖ := linearCost_le _ _ _
    _ = ‖(x - B μ) + (y - B ν)‖ + ‖μ + ν‖ := by rw [map_add]; congr 2; abel
    _ ≤ (‖x - B μ‖ + ‖y - B ν‖) + (‖μ‖ + ‖ν‖) :=
      add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ ≤ r := by linarith

lemma linearCost_smul_le (B : M →L[ℝ] H) (a : ℝ) (x : H) :
    linearCost B (a • x) ≤ ‖a‖ * linearCost B x := by
  change linearCost B (a • x) ≤ ‖a‖ * (⨅ μ : M, ‖x - B μ‖ + ‖μ‖)
  rw [Real.mul_iInf_of_nonneg (norm_nonneg a)]
  apply le_ciInf
  intro μ
  calc
    linearCost B (a • x) ≤ ‖a • x - B (a • μ)‖ + ‖a • μ‖ := linearCost_le _ _ _
    _ = ‖a‖ * (‖x - B μ‖ + ‖μ‖) := by rw [map_smul, ← smul_sub, norm_smul, norm_smul]; ring

/-- Seminorm supplied to Hahn--Banach in exact linear-cost duality. -/
def linearCostSeminorm (B : M →L[ℝ] H) : Seminorm ℝ H :=
  Seminorm.ofSMulLE (linearCost B) (linearCost_zero B)
    (linearCost_add_le B) (linearCost_smul_le B)

/-- Hahn--Banach for a seminorm, with the norming functional retained as an
    algebraic map so that the original Hilbert topology is not changed. -/
lemma exists_linear_norming {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) :
    ∃ φ : E →ₗ[ℝ] ℝ, φ x = p x ∧ ∀ z : E, |φ z| ≤ p z := by
  let : SeminormedAddCommGroup E := p.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : NormedSpace ℝ E :=
    { norm_smul_le := fun a z => (map_smul_eq_mul p a z).le }
  obtain ⟨φ, hφ, hx⟩ := exists_dual_vector'' ℝ x
  refine ⟨φ.toLinearMap, hx, fun z => ?_⟩
  change ‖φ z‖ ≤ ‖z‖
  calc
    ‖φ z‖ ≤ ‖φ‖ * ‖z‖ := φ.le_opNorm z
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hφ (norm_nonneg z)
    _ = ‖z‖ := one_mul _

lemma linearCost_exists_norming (B : M →L[ℝ] H) (x : H) :
    ∃ φ : H →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ φ x = linearCost B x ∧
      ∀ z : H, |φ z| ≤ linearCost B z := by
  obtain ⟨ψ, hx, hψ⟩ := exists_linear_norming (linearCostSeminorm B) x
  have hb : ∀ z : H, ‖ψ z‖ ≤ 1 * ‖z‖ := fun z => by
    simpa using (hψ z).trans (linearCost_le_norm B z)
  let φ : H →L[ℝ] ℝ := ψ.mkContinuous 1 hb
  exact ⟨φ, φ.opNorm_le_bound (by norm_num) hb, hx, hψ⟩

end LinearCost
section HilbertCost
variable {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- The easy direction of linear-cost duality, with absolute convergence
    abstracted into the bounded synthesis operator B. -/
lemma inner_le_linearCost (B : M →L[ℝ] H)
    {f : H} (hf : ‖f‖ ≤ 1) (hpath : ∀ μ : M, |inner ℝ f (B μ)| ≤ ‖μ‖)
    (x : H) : inner ℝ f x ≤ linearCost B x := by
  apply le_ciInf
  intro μ
  calc
    inner ℝ f x = inner ℝ f (x - B μ) + inner ℝ f (B μ) := by
      rw [← inner_add_right, sub_add_cancel]
    _ ≤ ‖f‖ * ‖x - B μ‖ + ‖μ‖ :=
      add_le_add (real_inner_le_norm _ _) ((le_abs_self _).trans (hpath μ))
    _ ≤ ‖x - B μ‖ + ‖μ‖ := by
      exact add_le_add (by simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg (x - B μ))) le_rfl

/-- Exact infimal linear-cost duality. For root-path synthesis on ℓ₁(T_n), this gives the root-potential norming-set identity without assuming a minimizer. -/


theorem linearCost_exact_duality [CompleteSpace H]
    (B : M →L[ℝ] H) (x : H) :
    linearCost B x = sSup {r : ℝ | ∃ f : H, ‖f‖ ≤ 1 ∧
      (∀ μ : M, |inner ℝ f (B μ)| ≤ ‖μ‖) ∧ r = inner ℝ f x} := by
  let S : Set ℝ := {r | ∃ f : H, ‖f‖ ≤ 1 ∧
      (∀ μ : M, |inner ℝ f (B μ)| ≤ ‖μ‖) ∧ r = inner ℝ f x}
  have hb : BddAbove S := ⟨linearCost B x, by
    rintro r ⟨f, hf, hp, rfl⟩
    exact inner_le_linearCost B hf hp x⟩
  have h0 : (0 : ℝ) ∈ S := by
    refine ⟨0, by simp, ?_, by simp⟩
    intro μ
    simp
  obtain ⟨φ, hφ, hx, hφcost⟩ := linearCost_exists_norming B x
  let f : H := (InnerProductSpace.toDual ℝ H).symm φ
  have hf : ‖f‖ ≤ 1 := by simpa [f] using hφ
  have hfx : inner ℝ f x = linearCost B x := by
    exact InnerProductSpace.toDual_symm_apply.trans hx
  have hp : ∀ μ : M, |inner ℝ f (B μ)| ≤ ‖μ‖ := by
    intro μ
    rw [show inner ℝ f (B μ) = φ (B μ) from InnerProductSpace.toDual_symm_apply]
    exact (hφcost _).trans (linearCost_synthesis_le B μ)
  exact le_antisymm (le_csSup hb ⟨f, hf, hp, hfx.symm⟩)
    (csSup_le ⟨0, h0⟩ fun r ⟨g, hg, hgpath, hr⟩ => hr ▸ inner_le_linearCost B hg hgpath x)

end HilbertCost
section Synthesis
variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [completeE : CompleteSpace E]

abbrev L1Mass (I : Type*) := lp (fun _ : I => ℝ) 1

lemma l1_hasSum_norm (μ : L1Mass I) : HasSum (fun i => ‖μ i‖) ‖μ‖ := by
  simpa using lp.hasSum_norm (p := 1) (by norm_num) μ

lemma atom_summable_norm {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (b : I → E) {K : ℝ} (hb : ∀ i, ‖b i‖ ≤ K)
    (μ : L1Mass I) : Summable (fun i => ‖μ i • b i‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => show ‖μ i • b i‖ ≤ K * ‖μ i‖ from ?_)
    ((l1_hasSum_norm μ).summable.mul_left K)
  rw [norm_smul, mul_comm K]
  exact mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)

lemma atom_summable (b : I → E) {K : ℝ} (hb : ∀ i, ‖b i‖ ≤ K)
    (μ : L1Mass I) : Summable (fun i => μ i • b i) := by
  exact (atom_summable_norm b hb μ).of_norm

lemma atom_tsum_norm_le (b : I → E) {K : ℝ} (hb : ∀ i, ‖b i‖ ≤ K)
    (μ : L1Mass I) : ‖∑' i, μ i • b i‖ ≤ K * ‖μ‖ := by
  calc
    ‖∑' i, μ i • b i‖ ≤ ∑' i, ‖μ i • b i‖ := norm_tsum_le_tsum_norm (atom_summable_norm b hb μ)
    _ ≤ ∑' i, K * ‖μ i‖ := Summable.tsum_le_tsum (fun i => by
        rw [norm_smul, mul_comm K]
        exact mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _))
      (atom_summable_norm b hb μ) ((l1_hasSum_norm μ).summable.mul_left K)
    _ = K * ‖μ‖ := by rw [tsum_mul_left, (l1_hasSum_norm μ).tsum_eq]

/-- Absolutely convergent signed synthesis from ℓ₁. -/
def atomSynthesis (b : I → E) {K : ℝ} (hb : ∀ i, ‖b i‖ ≤ K) : L1Mass I →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun μ => ∑' i, μ i • b i
      map_add' := fun μ ν => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact Summable.tsum_add (atom_summable b hb μ) (atom_summable b hb ν)
      map_smul' := fun a μ => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
        exact (atom_summable b hb μ).tsum_const_smul a }
    K (atom_tsum_norm_le b hb)

@[simp] lemma atomSynthesis_apply (b : I → E) {K : ℝ} (hb : ∀ i, ‖b i‖ ≤ K)
    (μ : L1Mass I) : atomSynthesis b hb μ = ∑' i, μ i • b i := rfl

@[simp] lemma atomSynthesis_single [DecidableEq I] (b : I → E) {K : ℝ} (hb : ∀ i, ‖b i‖ ≤ K)
    (i : I) (a : ℝ) : atomSynthesis b hb (lp.single 1 i a) = a • b i := by
  classical
  rw [atomSynthesis_apply, tsum_eq_single i]
  · simp
  · intro j hj
    simp only [lp.single_apply, Pi.single_eq_of_ne hj, zero_smul]
end Synthesis

section AtomDuality
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma atom_pairing_bound (b : I → E) {K : ℝ} (hb : ∀ i, ‖b i‖ ≤ K)
    {f : E} (hf : ∀ i, |inner ℝ f (b i)| ≤ 1) (μ : L1Mass I) :
    |inner ℝ f (atomSynthesis b hb μ)| ≤ ‖μ‖ := by
  have heq : inner ℝ f (atomSynthesis b hb μ) = ∑' i, μ i * inner ℝ f (b i) := by
    simpa only [atomSynthesis_apply, innerSL_apply_apply, real_inner_smul_right] using
      (innerSL ℝ f).map_tsum (atom_summable b hb μ)
  have hpoint : ∀ i, ‖μ i * inner ℝ f (b i)‖ ≤ ‖μ i‖ := by
    intro i
    rw [norm_mul, Real.norm_eq_abs (inner ℝ f (b i))]
    simpa using mul_le_mul_of_nonneg_left (hf i) (norm_nonneg (μ i))
  have hs : Summable (fun i => ‖μ i * inner ℝ f (b i)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint (l1_hasSum_norm μ).summable
  rw [heq, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hs).trans
    ((Summable.tsum_le_tsum hpoint hs (l1_hasSum_norm μ).summable).trans_eq
      (l1_hasSum_norm μ).tsum_eq)

lemma atom_pairing_iff (b : I → E) {K : ℝ} (hb : ∀ i, ‖b i‖ ≤ K) (f : E) :
    (∀ μ : L1Mass I, |inner ℝ f (atomSynthesis b hb μ)| ≤ ‖μ‖) ↔
      ∀ i, |inner ℝ f (b i)| ≤ 1 := by
  classical
  constructor
  · intro h i
    have hi := h (lp.single 1 i (1 : ℝ))
    rw [atomSynthesis_single, one_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)] at hi
    simpa using hi
  · intro hf μ
    exact atom_pairing_bound b hb hf μ

/-- Exact duality with the individual atom constraints, rather than the
    equivalent but implicit constraint on arbitrary signed path mass. -/
theorem linearCost_atom_duality (b : I → E) {K : ℝ} (hb : ∀ i, ‖b i‖ ≤ K) (x : E) :
    linearCost (atomSynthesis b hb) x = sSup {r : ℝ | ∃ f : E, ‖f‖ ≤ 1 ∧
      (∀ i, |inner ℝ f (b i)| ≤ 1) ∧ r = inner ℝ f x} := by
  rw [linearCost_exact_duality]
  congr 1
  ext r
  simp only [mem_ofPred_eq, atom_pairing_iff]
end AtomDuality


end BoundedTreePotentials

end

end OAI
