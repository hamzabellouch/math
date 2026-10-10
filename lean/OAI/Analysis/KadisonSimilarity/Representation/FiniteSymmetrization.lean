import OAI.Analysis.KadisonSimilarity.Representation.WeakOperatorCompactness

namespace OAI

/-! Finite unitary averaging and weak-operator cluster points. These are the
analytic and algebraic symmetrization steps, before identifying the matrix
unitaries of the free-product model. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open Filter ContinuousLinearMapWOT

variable {Γ V H : Type*} [Fintype Γ] [Nonempty Γ]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Uniform average over a nonempty finite set. -/
def finiteMean (f : Γ → V) : V := (Fintype.card Γ : ℂ)⁻¹ • ∑ g, f g

@[simp] theorem finiteMean_const (v : V) : finiteMean (fun _ : Γ => v) = v := by
  simp only [finiteMean, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

omit [Nonempty Γ] in
theorem finiteMean_sub (f g : Γ → V) :
    finiteMean (fun a => f a - g a) = finiteMean f - finiteMean g := by
  simp [finiteMean, Finset.sum_sub_distrib, smul_sub]

theorem norm_finiteMean_le (f : Γ → V) {c : ℝ} (hc : ∀ g, ‖f g‖ ≤ c) :
    ‖finiteMean f‖ ≤ c := by
  have hcard : (0 : ℝ) < Fintype.card Γ := Nat.cast_pos.mpr Fintype.card_pos
  calc
    ‖finiteMean f‖ = (Fintype.card Γ : ℝ)⁻¹ * ‖∑ g, f g‖ := by
      simp [finiteMean, norm_smul]
    _ ≤ (Fintype.card Γ : ℝ)⁻¹ * ∑ g, ‖f g‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card Γ : ℝ)⁻¹ * ((Fintype.card Γ : ℝ) * c) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using Finset.sum_le_sum (fun g (_ : g ∈ (Finset.univ : Finset Γ)) => hc g)
    _ = c := by field_simp

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [Group Γ]

/-- The twirl associated to a finite unitary representation. Its inverse is
written using the group, so no adjoint identities are hidden in this definition. -/
def finiteTwirl (U : Γ →* (H →L[ℂ] H)) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  finiteMean (fun g => U g * T * U g⁻¹)

omit [Fintype Γ] [Nonempty Γ] in
private theorem representation_mul_inv (U : Γ →* (H →L[ℂ] H)) (g : Γ) :
    U g * U g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]

omit [Fintype Γ] [Nonempty Γ] in
private theorem representation_inv_mul (U : Γ →* (H →L[ℂ] H)) (g : Γ) :
    U g⁻¹ * U g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]

/-- Contractivity of finite averaging of unitary conjugates. -/
theorem norm_finiteTwirl_le (U : Γ →* (H →L[ℂ] H))
    (hU : ∀ g, ‖U g‖ ≤ 1) (T : H →L[ℂ] H) : ‖finiteTwirl U T‖ ≤ ‖T‖ := by
  apply norm_finiteMean_le
  intro g
  calc
    ‖U g * T * U g⁻¹‖ ≤ ‖U g‖ * ‖T‖ * ‖U g⁻¹‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖T‖ * 1 := by gcongr; exact hU _; exact hU _
    _ = ‖T‖ := by ring

omit [Nonempty Γ] in
/-- Reindexing the finite group proves exact invariance under its unitaries. -/
theorem finiteTwirl_conjugate (U : Γ →* (H →L[ℂ] H)) (T : H →L[ℂ] H) (g : Γ) :
    U g * finiteTwirl U T * U g⁻¹ = finiteTwirl U T := by
  simp only [finiteTwirl, finiteMean, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  calc
    ∑ h, U g * (U h * T * U h⁻¹) * U g⁻¹ =
        ∑ h, U (g * h) * T * U (g * h)⁻¹ := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [mul_inv_rev, map_mul]
      noncomm_ring
    _ = ∑ h, U h * T * U h⁻¹ :=
      Equiv.sum_comp (Equiv.mulLeft g) (fun h => U h * T * U h⁻¹)

omit [Nonempty Γ] in
/-- The averaged operator commutes with every unitary in the finite group. -/
theorem finiteTwirl_commute (U : Γ →* (H →L[ℂ] H)) (T : H →L[ℂ] H) (g : Γ) :
    commutator (finiteTwirl U T) (U g) = 0 := by
  have h := congrArg (fun X : H →L[ℂ] H => X * U g) (finiteTwirl_conjugate U T g)
  simp only [mul_assoc, representation_inv_mul, mul_one] at h
  exact sub_eq_zero.mpr h.symm

/-- A bound on the original commutators bounds the distance to the twirl. -/
theorem norm_sub_finiteTwirl_le (U : Γ →* (H →L[ℂ] H))
    (hU : ∀ g, ‖U g‖ ≤ 1) (T : H →L[ℂ] H) {ε : ℝ}
    (hcomm : ∀ g, ‖commutator T (U g)‖ ≤ ε) : ‖T - finiteTwirl U T‖ ≤ ε := by
  have he : T - finiteTwirl U T =
      finiteMean (fun g => (commutator T (U g)) * U g⁻¹) := by
    change T - finiteMean (fun g => U g * T * U g⁻¹) = _
    calc
      _ = finiteMean (fun _ : Γ => T) - finiteMean (fun g => U g * T * U g⁻¹) := by
        rw [finiteMean_const]
      _ = finiteMean (fun g => T - U g * T * U g⁻¹) := (finiteMean_sub _ _).symm
      _ = _ := ?_
    congr 1
    funext g
    simp only [commutator, sub_mul, mul_assoc, representation_mul_inv, mul_one]
  rw [he]
  apply norm_finiteMean_le
  intro g
  calc
    ‖commutator T (U g) * U g⁻¹‖ ≤ ‖commutator T (U g)‖ * ‖U g⁻¹‖ := norm_mul_le _ _
    _ ≤ ε * 1 := by
      apply mul_le_mul (hcomm g) (hU _) (norm_nonneg _) ?_
      exact (norm_nonneg _).trans (hcomm g)
    _ = ε := mul_one _

omit [Fintype Γ] [Nonempty Γ] in
/-- Conjugation transports a commutator by an exact algebraic identity. -/
theorem conjugate_commutator (U : Γ →* (H →L[ℂ] H))
    (T A : H →L[ℂ] H) (g : Γ) :
    commutator (U g * T * U g⁻¹) A =
      U g * commutator T (U g⁻¹ * A * U g) * U g⁻¹ := by
  simp only [commutator, mul_sub, sub_mul, mul_assoc,
    representation_mul_inv, mul_one]
  rw [← mul_assoc (U g) (U g⁻¹), representation_mul_inv, one_mul]

variable [CompleteSpace H]

/-- Twirling by unitaries in the algebra does not increase its scalar
commutator seminorm. -/
theorem scalarCommutatorNorm_finiteTwirl_le (P : VonNeumannAlgebra H)
    (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (hmem : ∀ g, U g ∈ P) (T : H →L[ℂ] H) :
    scalarCommutatorNorm P (finiteTwirl U T) ≤ scalarCommutatorNorm P T := by
  apply (scalarCommutatorNorm_le_iff P _ (scalarCommutatorNorm_nonneg P T)).mpr
  intro A hA
  have he : commutator (finiteTwirl U T) A =
      finiteMean (fun g => commutator (U g * T * U g⁻¹) A) := by
    simp [finiteTwirl, finiteMean, commutator,
      Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib, smul_sub]
  rw [he]
  apply norm_finiteMean_le
  intro g
  have hnorm (g : Γ) (B : H →L[ℂ] H) : ‖U g * B * U g⁻¹‖ ≤ ‖B‖ := by
    calc
      _ ≤ ‖U g‖ * ‖B‖ * ‖U g⁻¹‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖B‖ * 1 := by gcongr; exact hU _; exact hU _
      _ = ‖B‖ := by ring
  have hA' : ‖U g⁻¹ * A * U g‖ ≤ ‖A‖ := by
    simpa using hnorm g⁻¹ A
  rw [conjugate_commutator]
  calc
    _ ≤ ‖commutator T (U g⁻¹ * A * U g)‖ := hnorm g _
    _ ≤ scalarCommutatorNorm P T * ‖U g⁻¹ * A * U g‖ :=
      norm_commutator_le_scalarCommutatorNorm P T _ (P.mul_mem (P.mul_mem (hmem _) hA) (hmem _))
    _ ≤ scalarCommutatorNorm P T * ‖A‖ :=
      mul_le_mul_of_nonneg_left hA' (scalarCommutatorNorm_nonneg P T)

/-- Every bounded sequence of operators has a weak-operator cluster point,
without a separability assumption on the Hilbert space. -/
theorem exists_weakOperator_cluster (T : ℕ → H →L[ℂ] H) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ n, ‖T n‖ ≤ R) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ R ∧ MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)) := by
  have hev : ∀ᶠ n : ℕ in atTop, ofCLM (T n) ∈
      {B : H →WOT[ℂ] H | ‖toCLM B‖ ≤ R} := Eventually.of_forall hbound
  obtain ⟨S, hS, hcluster⟩ :=
    (isCompact_weakOperator_ball (H := H) R hR).exists_mapClusterPt_of_frequently hev.frequently
  exact ⟨toCLM S, hS, hcluster⟩

/-- Operator-norm bounds on affine expressions pass to weak cluster points. -/
theorem norm_sub_le_of_weakOperator_cluster (T : ℕ → H →L[ℂ] H)
    (S A : H →L[ℂ] H)
    (hcluster : MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ n in atTop, ‖T n - A‖ ≤ c) : ‖S - A‖ ≤ c := by
  have hclosed : IsClosed {B : H →WOT[ℂ] H | ‖toCLM B - A‖ ≤ c} :=
    (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      (continuous_id.sub continuous_const)
  exact hclosed.mem_of_mapClusterPt hcluster hbound

/-- Eventual commutator bounds pass to weak cluster points. -/
theorem norm_commutator_le_of_weakOperator_cluster (T : ℕ → H →L[ℂ] H)
    (S A : H →L[ℂ] H)
    (hcluster : MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ n in atTop, ‖commutator (T n) A‖ ≤ c) :
    ‖commutator S A‖ ≤ c := by
  have hclosed : IsClosed {B : H →WOT[ℂ] H | ‖commutator (toCLM B) A‖ ≤ c} :=
    (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      ((continuous_id.mul_const (ofCLM A)).sub (continuous_id.const_mul (ofCLM A)))
  exact hclosed.mem_of_mapClusterPt hcluster hbound

end KadisonSimilarity

end

end OAI
