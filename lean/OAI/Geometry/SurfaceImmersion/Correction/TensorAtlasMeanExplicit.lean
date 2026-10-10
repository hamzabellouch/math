import OAI.Geometry.SurfaceImmersion.Correction.TensorAtlasMean

namespace OAI

/-! The atlas mean estimate with its read and restore constants exposed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance explicitAtlasMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance explicitAtlasMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance explicitAtlasMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance explicitAtlasMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance explicitAtlasMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance explicitAtlasMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlasMean_majorants_explicit
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (L : ℕ) (B K : ℕ → ℝ → ℝ)
    (hB : ∀ m C, 1 ≤ C → 1 ≤ B m C) (hK : ∀ m C, 1 ≤ C → 1 ≤ K m C)
    (D E : ℕ → ℝ) (hD : ∀ m, 1 ≤ D m) (hE : ∀ m, 0 ≤ E m)
    (hd : ∀ m (i : A.centers) (f : Base → A.centers → TensorFiber) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f → WeightedBound univ s m C f →
      WeightedBound univ s m (D m*C) (A.tensorPlaneRead i (A.tensorDecode f)))
    (he : ∀ m (f : A.centers → SmallModes.Base → Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, WeightedBound univ s m C (f i)) →
      A.TensorWeightedBound s m (E m*C) (A.tensorPlaneRestore f)) :
    ∀ r : ℝ, 0 ≤ r →
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧ ∃ β κ : ℕ → ℝ → ℝ,
      β = (fun m C => max 1 (E m * B m (D (m+L)*C))) ∧
      κ = (fun m C => max 1 (E m * K m (D (m+L)*C) * D (m+L))) ∧
      ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ η : ℝ, 0 < η →
      ∀ μ : A.centers → (SmallModes.Base → Tensor) → SmallModes.Base → Tensor,
      (∀ i f, ContDiff ℝ ∞ f → InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        ContDiff ℝ ∞ (μ i f)) →
      (∀ i m C f, 1 ≤ C → ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        WeightedBound univ s (m+L) C f → WeightedBound univ s m (η * B m C) (μ i f)) →
      (∀ i m C D f g, 1 ≤ C → 0 ≤ D → ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) g →
        WeightedBound univ s (m+L) C f → WeightedBound univ s (m+L) C g →
        WeightedBound univ s (m+L) D (f-g) →
        WeightedBound univ s m (K m C * η * D) (μ i f - μ i g)) →
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean η (A.tensorMeanOperator (A.atlasMean μ))) β κ := by
  classical
  have hball := A.tensorReadBallConstant_ball
  intro r hr
  let β : ℕ → ℝ → ℝ := fun m C => max 1 (E m * B m (D (m+L)*C))
  let κ : ℕ → ℝ → ℝ := fun m C => max 1 (E m * K m (D (m+L)*C) * D (m+L))
  refine ⟨(fun f hf hb i => hball reference href f r hr hf hb i),β,κ,rfl,rfl,?_⟩
  intro s hs hs1 η hη μ hsm hv hdiff
  have hb0 (f : Base → A.centers → TensorFiber) (hf : ContDiff ℝ ∞ f)
      (hb : InTrialBall univ (A.tensorEncode reference) r f) (i : A.centers) :=
    hball reference href f r hr hf hb i
  have hf0 (f : Base → A.centers → TensorFiber) (hf : ContDiff ℝ ∞ f) (i : A.centers) :=
    A.tensorPlaneRead_smooth i (A.tensorDecode_smooth hf)
  have hms (f : Base → A.centers → TensorFiber) (hf : ContDiff ℝ ∞ f)
      (hb : InTrialBall univ (A.tensorEncode reference) r f) :
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (A.atlasMean μ (A.tensorDecode f) x)) :=
    A.tensorPlaneRestore_smooth (fun i => hsm i _ (hf0 f hf i) (hb0 f hf hb i))
  apply rescaledMean_bounds uniqueDiffOn_univ hη
  · exact fun m C _ => le_max_left _ _
  · exact fun m C _ => le_max_left _ _
  · intro f hf hb
    exact (A.tensorEncode_smooth (hms f (contDiffOn_univ.mp hf) hb)).contDiffOn
  · intro m C f hC hf hb hbf
    have hfs := contDiffOn_univ.mp hf
    have hDC : 1 ≤ D (m+L)*C := one_le_mul_of_one_le_of_one_le (hD _) hC
    have hl (i : A.centers) := hv i m (D (m+L)*C) _ hDC (hf0 f hfs i) (hb0 f hfs hb i)
      (hd (m+L) i f s C hs hs1 (zero_le_one.trans hC) hfs hbf)
    have hg := he m (fun i => μ i (A.tensorPlaneRead i (A.tensorDecode f))) s
      (η * B m (D (m+L)*C)) hs hs1 (mul_nonneg hη.le (zero_le_one.trans (hB _ _ hDC)))
      (fun i => hsm i _ (hf0 f hfs i) (hb0 f hfs hb i)) hl
    have henc := A.tensorEncode_bound (hms f hfs hb) hs
      (mul_nonneg (hE m) (mul_nonneg hη.le (zero_le_one.trans (hB _ _ hDC)))) hg
    apply henc.mono_const
    calc
      _ = η * (E m * B m (D (m+L)*C)) := by ring
      _ ≤ η * β m C := mul_le_mul_of_nonneg_left (le_max_right _ _) hη.le
  · intro m C D' f g hC hD' hf hg hbf hbg hbf' hbg' hfg
    have hfs := contDiffOn_univ.mp hf
    have hgs := contDiffOn_univ.mp hg
    have hDC : 1 ≤ D (m+L)*C := one_le_mul_of_one_le_of_one_le (hD _) hC
    have hl (i : A.centers) := hdiff i m (D (m+L)*C) (D (m+L)*D') _ _ hDC
      (mul_nonneg (zero_le_one.trans (hD _)) hD') (hf0 f hfs i) (hf0 g hgs i)
      (hb0 f hfs hbf i) (hb0 g hgs hbg i)
      (hd (m+L) i f s C hs hs1 (zero_le_one.trans hC) hfs hbf')
      (hd (m+L) i g s C hs hs1 (zero_le_one.trans hC) hgs hbg')
      (by rw [← A.tensorPlaneRead_decode_sub]; exact
        hd (m+L) i (f-g) s D' hs hs1 hD' (hfs.sub hgs) hfg)
    have hnon : 0 ≤ K m (D (m+L)*C) * η * (D (m+L)*D') :=
      mul_nonneg (mul_nonneg (zero_le_one.trans (hK _ _ hDC)) hη.le)
        (mul_nonneg (zero_le_one.trans (hD _)) hD')
    have hb := he m (fun i => μ i (A.tensorPlaneRead i (A.tensorDecode f)) -
      μ i (A.tensorPlaneRead i (A.tensorDecode g))) s _ hs hs1 hnon
      (fun i => (hsm i _ (hf0 f hfs i) (hb0 f hfs hbf i)).sub
        (hsm i _ (hf0 g hgs i) (hb0 g hgs hbg i))) hl
    rw [← A.atlasMean_sub μ] at hb
    have hsec := (hms f hfs hbf).sub_section (hms g hgs hbg)
    have henc := A.tensorEncode_bound hsec hs (mul_nonneg (hE m) hnon) hb
    rw [A.tensorEncode_sub] at henc
    apply henc.mono_const
    calc
      _ = (E m * K m (D (m+L)*C) * D (m+L)) * η * D' := by ring
      _ ≤ κ m C * η * D' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hη.le) hD'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
