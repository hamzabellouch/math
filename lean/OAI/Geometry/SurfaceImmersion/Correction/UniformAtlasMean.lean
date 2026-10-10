import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamilyData
import OAI.Geometry.SurfaceImmersion.Correction.TensorAtlasMean

namespace OAI

/-! Uniform global majorants for the actual charted polynomial means.
Constants precede both scales, all coordinate maps and all local solvers. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance uniformAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance uniformAtlasSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformAtlasSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_atlas_mean_majorants_fixed_ball
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x))) (q : ℕ) :
    let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∀ r : ℝ, 0 ≤ r →
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧ ∃ β κ : ℕ → ℝ → ℝ,
      ∀ {ε τ : ℝ} {s : ℝ≥0}
        (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (A.tensorReadBallConstant*r) ρ R (A.tensorPlaneRead i reference)),
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ loss ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean (τ / s + ε / τ ^ loss)
          (A.tensorMeanOperator (A.atlasMean (fun i => (d i).mean hρ δ q)))) β κ := by
  classical
  dsimp only
  let Ls := fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1)
  let L := Finset.univ.sup Ls
  let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
  choose B K hlocal using fun i : A.centers => uniform_chartedFamilyData_majorants (R := R) (p i) hρ q
  let B' := fun m C => 1 + ∑ i : A.centers, max 1 (B i m C)
  let K' := fun m C => 1 + ∑ i : A.centers, max 1 (K i m C)
  have hB (m : ℕ) (C : ℝ) (_ : 1 ≤ C) : 1 ≤ B' m C := by
    have hn : 0 ≤ ∑ i : A.centers, max 1 (B i m C) :=
      Finset.sum_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))
    change 1 ≤ 1 + ∑ i : A.centers, max 1 (B i m C)
    linarith
  have hK (m : ℕ) (C : ℝ) (_ : 1 ≤ C) : 1 ≤ K' m C := by
    have hn : 0 ≤ ∑ i : A.centers, max 1 (K i m C) :=
      Finset.sum_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))
    change 1 ≤ 1 + ∑ i : A.centers, max 1 (K i m C)
    linarith
  have hBle (i : A.centers) (m : ℕ) (C : ℝ) : B i m C ≤ B' m C := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset A.centers))
      (f := fun j => max 1 (B j m C)) (fun _ _ => zero_le_one.trans (le_max_left _ _)) (Finset.mem_univ i)
    change B i m C ≤ 1 + ∑ j : A.centers, max 1 (B j m C)
    linarith [le_max_right 1 (B i m C)]
  have hKle (i : A.centers) (m : ℕ) (C : ℝ) : K i m C ≤ K' m C := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset A.centers))
      (f := fun j => max 1 (K j m C)) (fun _ _ => zero_le_one.trans (le_max_left _ _)) (Finset.mem_univ i)
    change K i m C ≤ 1 + ∑ j : A.centers, max 1 (K j m C)
    linarith [le_max_right 1 (K i m C)]
  have hall := A.atlasMean_majorants_fixed_ball reference href L B' K' hB hK
  intro r hr
  obtain ⟨hball,β,κ,hm⟩ := hall r hr
  refine ⟨hball,β,κ,?_⟩
  intro ε τ s d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ
  let η := τ / s + ε / τ ^ loss
  have hη : 0 < η := add_pos_of_pos_of_nonneg (div_pos hτ hs)
    (div_nonneg hε (pow_nonneg hτ.le _))
  have hηle (i : A.centers) : τ / s + ε / τ ^ tensorLoss (P i) ≤ η := by
    change τ / s + ε / τ ^ tensorLoss (P i) ≤ τ / s + ε / τ ^ loss
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left hε (pow_pos hτ _)
    apply pow_le_pow_of_le_one hτ.le (hτs.trans hs1)
    exact Finset.le_sup (f := fun i : A.centers => tensorLoss (P i)) (Finset.mem_univ i)
  have hηi (i : A.centers) : 0 < τ / s + ε / τ ^ tensorLoss (P i) :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  have hL (i : A.centers) : Ls i ≤ L := Finset.le_sup (Finset.mem_univ i)
  have hmi (i : A.centers) := hlocal i (d i) (hd i) hτ hs hτs hs1 hε hε1
    ((hηle i).trans hsmall) δ hδ
  apply hm hs hs1 η hη (fun i => (d i).mean hρ δ q)
  · intro i f _ _
    exact (d i).mean_smooth hρ δ q f
  · intro i m C f hC hf hb hbf
    have hh := (hmi i).value _ (hηi i) ((hηle i).trans hsmall) m C f hC hf.contDiffOn hb
      (hbf.mono_order (Nat.add_le_add_left (hL i) m))
    rw [rescaledMean_self (hηi i).ne'] at hh
    apply hh.mono_const
    calc
      _ ≤ η * B i m C := mul_le_mul_of_nonneg_right (hηle i)
        (zero_le_one.trans ((hmi i).B_pos m C hC))
      _ ≤ _ := mul_le_mul_of_nonneg_left (hBle i m C) hη.le
  · intro i m C D f g hC hD hf hg hbf hbg hbf' hbg' hdiff
    have hh := (hmi i).difference _ (hηi i) ((hηle i).trans hsmall) m C D f g hC hD
      hf.contDiffOn hg.contDiffOn hbf hbg
      (hbf'.mono_order (Nat.add_le_add_left (hL i) m))
      (hbg'.mono_order (Nat.add_le_add_left (hL i) m))
      (hdiff.mono_order (Nat.add_le_add_left (hL i) m))
    rw [rescaledMean_self (hηi i).ne'] at hh
    apply hh.mono_const
    apply mul_le_mul_of_nonneg_right _ hD
    exact mul_le_mul (hKle i m C) (hηle i)
      (hηi i).le (zero_le_one.trans (hK m C hC))

theorem uniform_atlas_mean_majorants_all_radii
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x))) (q : ℕ) :
    let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∀ r : ℝ, 0 ≤ r →
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧ ∃ β κ : ℕ → ℝ → ℝ,
      ∀ {ε τ : ℝ} {s : ℝ≥0}
        (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference)),
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ loss ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean (τ / s + ε / τ ^ loss)
          (A.tensorMeanOperator (A.atlasMean (fun i => (d i).mean hρ δ q)))) β κ := by
  exact ⟨A.tensorReadBallConstant,A.one_le_tensorReadBallConstant,
    A.uniform_atlas_mean_majorants_fixed_ball (R := R) p hρ reference href q⟩

theorem uniform_atlas_mean_majorants
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R r : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x))) (q : ℕ) :
    let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧ ∃ β κ : ℕ → ℝ → ℝ,
      ∀ {ε τ : ℝ} {s : ℝ≥0}
        (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference)),
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ loss ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean (τ / s + ε / τ ^ loss)
          (A.tensorMeanOperator (A.atlasMean (fun i => (d i).mean hρ δ q)))) β κ := by
  obtain ⟨D₀,hD₀,h⟩ := A.uniform_atlas_mean_majorants_all_radii (R := R) p hρ reference href q
  obtain ⟨hball,β,κ,hm⟩ := h r hr
  exact ⟨D₀,hD₀,hball,β,κ,hm⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
