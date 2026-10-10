import OAI.Analysis.IrrationalRotation.Operators.JointProjectionAtomic
import OAI.Analysis.IrrationalRotation.Analysis.MultiplicationPurePoint

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233

variable {X κ : Type*} [MeasurableSpace X] {μ : Measure X} [Countable κ]

theorem isSelfAdjoint_of_real_sequence_diagonal
    (g : κ → X → ℝ)
    (T : Lp (lp (fun _ : κ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : κ => ℂ) 2) 2 μ)
    (hT : ∀ (v : Lp (lp (fun _ : κ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, T v x k = (g k x : ℂ) * v x k) :
    IsSelfAdjoint T := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro v w
  change inner ℂ (T v) w = inner ℂ v (T w)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  have hv : ∀ᵐ x ∂μ, ∀ k, T v x k = (g k x : ℂ) * v x k := ae_all_iff.2 (hT v)
  have hw : ∀ᵐ x ∂μ, ∀ k, T w x k = (g k x : ℂ) * w x k := ae_all_iff.2 (hT w)
  filter_upwards [hv, hw] with x hvx hwx
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [hvx k, hwx k]
  simp only [RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

theorem commute_of_sequence_diagonal
    (g h : κ → X → ℂ)
    (S T : Lp (lp (fun _ : κ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : κ => ℂ) 2) 2 μ)
    (hS : ∀ (v : Lp (lp (fun _ : κ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, S v x k = g k x * v x k)
    (hT : ∀ (v : Lp (lp (fun _ : κ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, T v x k = h k x * v x k) : Commute S T := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  have hST : ∀ᵐ x ∂μ, ∀ k, S (T v) x k = g k x * T v x k := ae_all_iff.2 (hS (T v))
  have hTS : ∀ᵐ x ∂μ, ∀ k, T (S v) x k = h k x * S v x k := ae_all_iff.2 (hT (S v))
  have hSv : ∀ᵐ x ∂μ, ∀ k, S v x k = g k x * v x k := ae_all_iff.2 (hS v)
  have hTv : ∀ᵐ x ∂μ, ∀ k, T v x k = h k x * v x k := ae_all_iff.2 (hT v)
  filter_upwards [hST, hTS, hSv, hTv] with x hSTx hTSx hSvx hTvx
  apply lp.ext
  funext k
  change S (T v) x k = T (S v) x k
  rw [hSTx k, hTSx k, hSvx k, hTvx k]
  ring

theorem commute_of_mem_generated_selfAdjoint_family
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : I → H →L[ℂ] H) (hD : ∀ i, IsSelfAdjoint (D i))
    (hDD : ∀ i j, Commute (D i) (D j))
    {S T : H →L[ℂ] H} (hS : S ∈ vonNeumannGenerated (Set.range D))
    (hT : T ∈ vonNeumannGenerated (Set.range D)) : Commute S T := by
  have hle : vonNeumannGenerated (Set.range D) ≤
      (vonNeumannGenerated (Set.range D)).commutant := by
    apply vonNeumannGenerated_le
    rintro _ ⟨i, rfl⟩
    change D i ∈ (vonNeumannGenerated (Set.range D)).commutant
    rw [mem_commutant_vonNeumannGenerated_iff]
    rintro _ ⟨j, rfl⟩
    exact ⟨(hDD j i).eq, by simpa only [(hD j).star_eq] using (hDD j i).eq⟩
  exact VonNeumannAlgebra.mem_commutant_iff.mp (hle hT) S hS

theorem finite_orbit_diagonal_algebra_atomic_and_commutative
    {J : Type*} [Finite J] (n : J → ℤ)
    (σ : ℤ → X → X) (hσ : ∀ k, MeasurePreserving (σ k) μ μ)
    (f : X → ℝ) (hf : Measurable f)
    (hcount : ∃ C : Set ℝ, C.Countable ∧ ∀ᵐ x ∂μ, f x ∈ C)
    (D : J → Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ →L[ℂ]
      Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ)
    (hD : ∀ j (v : Lp (lp (fun _ : ℤ => ℂ) 2) 2 μ) k,
      ∀ᵐ x ∂μ, D j v x k = (f (σ (k - n j) x) : ℂ) * v x k) :
    IsAtomicVonNeumannAlgebra (vonNeumannGenerated (Set.range D)) ∧
      ∀ S ∈ vonNeumannGenerated (Set.range D),
        ∀ T ∈ vonNeumannGenerated (Set.range D), Commute S T := by
  have hself (j : J) : IsSelfAdjoint (D j) :=
    isSelfAdjoint_of_real_sequence_diagonal (fun k x => f (σ (k - n j) x)) (D j) (hD j)
  have hcomm (i j : J) : Commute (D i) (D j) :=
    commute_of_sequence_diagonal
      (fun k x => (f (σ (k - n i) x) : ℂ))
      (fun k x => (f (σ (k - n j) x) : ℂ)) (D i) (D j) (hD i) (hD j)
  constructor
  · have hcomplex : ∃ C : Set ℂ, C.Countable ∧ ∀ᵐ x ∂μ, (f x : ℂ) ∈ C := by
      obtain ⟨C, hC, hmem⟩ := hcount
      refine ⟨Complex.ofReal '' C, hC.image _, ?_⟩
      filter_upwards [hmem] with x hx
      exact Set.mem_image_of_mem Complex.ofReal hx
    obtain ⟨C, _hC, hdense⟩ :=
      MultiplicationPurePoint.finite_orbit_family_dense_jointEigenspaces n σ hσ
        (fun x => (f x : ℂ)) (Complex.continuous_ofReal.measurable.comp hf) hcomplex D hD
    apply atomic_generated_of_dense_jointEigenspaces D (fun y : C => y.val) hself
    simpa only [jointEigenspace] using hdense
  · intro S hS T hT
    exact commute_of_mem_generated_selfAdjoint_family D hself hcomm hS hT

end Invariant233

end

end OAI
