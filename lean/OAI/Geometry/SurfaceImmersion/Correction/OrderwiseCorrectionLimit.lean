import OAI.Geometry.SurfaceImmersion.Correction.ManifoldCorrectionLimit

namespace OAI

/-! Smooth correction limits with a separate summable bound at each derivative order. -/
noncomputable section
open Filter Manifold
open scoped Topology ContDiff

namespace ClosedSurfaceR4.ExactCorrection

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem smooth_limitMap_orderwise {F : E → V} {U : ℕ → E → V} {ρ : ℕ → ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n))
    (hρ : ∀ m, Summable (ρ m))
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ m n) :
    ContDiff ℝ ∞ (limitMap F U) := by
  apply hF.add
  apply contDiff_tsum_of_eventually (N := ⊤) hU (fun m _ => hρ m)
  intro m _
  simpa only [Nat.cofinite_eq_atTop] using hbound m

theorem hasFDerivAt_limitMap_orderwise
    {F : E → V} {U : ℕ → E → V} {ρ : ℕ → ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n))
    (hρ : ∀ m, Summable (ρ m))
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ m n) (x : E) :
    HasFDerivAt (limitMap F U)
      (fderiv ℝ F x + ∑' n, fderiv ℝ (U n) x) x := by
  have hb0 : ∀ᶠ n in atTop, ∀ y ∈ (Set.univ : Set E), ‖U n y‖ ≤ ρ 0 n := by
    filter_upwards [hbound 0] with n hn y _
    simpa only [norm_iteratedFDeriv_zero] using hn y
  have hb1 : ∀ᶠ n in atTop, ∀ y ∈ (Set.univ : Set E),
      ‖fderiv ℝ (U n) y‖ ≤ ρ 1 n := by
    filter_upwards [hbound 1] with n hn y _
    simpa only [norm_iteratedFDeriv_one] using hn y
  have hval := tendstoUniformlyOn_tsum_nat_eventually (hρ 0) hb0
  have hder := tendstoUniformlyOn_tsum_nat_eventually (hρ 1) hb1
  have hs : HasFDerivAt (fun y => ∑' n, U n y)
      (∑' n, fderiv ℝ (U n) x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn isOpen_univ hder
    · intro N y _
      exact HasFDerivAt.fun_sum fun n _ =>
        ((hU n).differentiable (by simp) y).hasFDerivAt
    · intro y hy
      exact hval.tendsto_at hy
    · exact Set.mem_univ x
  exact ((hF.differentiable (by simp) x).hasFDerivAt.add hs)

theorem tendsto_fderiv_partialMap_orderwise
    {F : E → V} {U : ℕ → E → V} {ρ : ℕ → ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n))
    (hρ : ∀ m, Summable (ρ m))
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ m n) (x : E) :
    Tendsto (fun N => fderiv ℝ (partialMap F U N) x) atTop
      (𝓝 (fderiv ℝ (limitMap F U) x)) := by
  have hb1 : ∀ᶠ n in atTop, ∀ y ∈ (Set.univ : Set E),
      ‖fderiv ℝ (U n) y‖ ≤ ρ 1 n := by
    filter_upwards [hbound 1] with n hn y _
    simpa only [norm_iteratedFDeriv_one] using hn y
  have hder := (tendstoUniformlyOn_tsum_nat_eventually (hρ 1) hb1).tendsto_at (Set.mem_univ x)
  have hfinite (N : ℕ) : fderiv ℝ (partialMap F U N) x =
      fderiv ℝ F x + ∑ n ∈ Finset.range N, fderiv ℝ (U n) x := by
    exact ((hF.differentiable (by simp) x).hasFDerivAt.add
      (HasFDerivAt.fun_sum fun n _ =>
        ((hU n).differentiable (by simp) x).hasFDerivAt)).fderiv
  simp_rw [hfinite]
  rw [(hasFDerivAt_limitMap_orderwise hF hU hρ hbound x).fderiv]
  exact tendsto_const_nhds.add hder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
/-- A representative in any smooth local coordinate map determines the actual
manifold derivative, with the fixed coordinate derivative as the right factor. -/
lemma local_coordinate_representative_derivative
    {c : M → E} {G : M → Space} {K : E → Space} (p : M)
    (hc : ContMDiffAt planeModel 𝓘(ℝ,E) ∞ c p) (hK : ContDiff ℝ ∞ K)
    (heq : G =ᶠ[𝓝 p] K ∘ c) :
    ContMDiffAt planeModel spaceModel ∞ G p ∧
      mfderiv planeModel spaceModel G p =
        (fderiv ℝ K (c p)).comp (mfderiv planeModel 𝓘(ℝ,E) c p) := by
  have hs : ContMDiffAt planeModel spaceModel ∞ (K ∘ c) p :=
    hK.contMDiff.contMDiffAt.comp p hc
  refine ⟨hs.congr_of_eventuallyEq heq,?_⟩
  have hd := heq.mfderiv_eq (I := planeModel) (I' := spaceModel)
  rw [mfderiv_comp p (hK.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv] at hd
  change (mfderiv planeModel spaceModel G p : Plane →L[ℝ] Space) =
    (ContinuousLinearMap.id ℝ Space).comp
      ((fderiv ℝ K (c p)).comp (mfderiv planeModel 𝓘(ℝ,E) c p)) at hd
  simpa only [ContinuousLinearMap.id_comp] using hd

omit [IsManifold planeModel ∞ M] in
/-- Local coordinate representatives with order-dependent summable tails give
smoothness of the series and convergence of the true manifold derivatives. -/
theorem local_coordinate_correction_limit
    {F : M → Space} {U : ℕ → M → Space} {c : M → E}
    {K : E → Space} {A : ℕ → E → Space} {ρ : ℕ → ℕ → ℝ} (p : M)
    (hc : ContMDiffAt planeModel 𝓘(ℝ,E) ∞ c p)
    (hK : ContDiff ℝ ∞ K) (hA : ∀ n, ContDiff ℝ ∞ (A n))
    (hρ : ∀ m, Summable (ρ m))
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (A n) x‖ ≤ ρ m n)
    (heq : ∀ᶠ x in 𝓝 p, F x = K (c x) ∧ ∀ n, U n x = A n (c x)) :
    ContMDiffAt planeModel spaceModel ∞ (manifoldLimitMap F U) p ∧
      Tendsto (fun N => mfderiv planeModel spaceModel (manifoldPartialMap F U N) p) atTop
        (𝓝 (mfderiv planeModel spaceModel (manifoldLimitMap F U) p)) := by
  have hl : manifoldLimitMap F U =ᶠ[𝓝 p] limitMap K A ∘ c := by
    filter_upwards [heq] with x hx
    simp only [manifoldLimitMap,limitMap,Function.comp_apply,hx.1,hx.2]
  have hs := local_coordinate_representative_derivative p hc
    (smooth_limitMap_orderwise hK hA hρ hbound) hl
  refine ⟨hs.1,?_⟩
  have hf (N : ℕ) : mfderiv planeModel spaceModel (manifoldPartialMap F U N) p =
      (fderiv ℝ (partialMap K A N) (c p)).comp (mfderiv planeModel 𝓘(ℝ,E) c p) := by
    apply (local_coordinate_representative_derivative p hc
      (hK.add (ContDiff.sum (fun n _ => hA n))) ?_).2
    filter_upwards [heq] with x hx
    simp only [manifoldPartialMap,Function.comp_apply,hx.1,hx.2]
  simp_rw [hf,hs.2]
  let compose : (E →L[ℝ] Space) →L[ℝ] (Plane →L[ℝ] Space) :=
    (ContinuousLinearMap.compL ℝ Plane E Space).flip
      (mfderiv planeModel 𝓘(ℝ,E) c p)
  exact (compose.continuous.tendsto _).comp
    (tendsto_fderiv_partialMap_orderwise hK hA hρ hbound (c p))

end ClosedSurfaceR4.ExactCorrection

end

end OAI
