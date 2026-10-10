import OAI.Analysis.Mahler.RegularChartStokes
import OAI.Analysis.Mahler.PuncturedBallStokes

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

 theorem continuousOn_extDeriv_coefficient {n : ℕ} {U : Set (Fin (n+1) → ℝ)}
    {ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U) :
    ContinuousOn (fun x => extDeriv ω x (coordinateBasis (n+1))) U := by
  let A := ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Fin (n+1) → ℝ) ℝ (n := n)
  let V := ContinuousAlternatingMap.apply ℝ (Fin (n+1) → ℝ) ℝ (coordinateBasis (n+1))
  intro x hx
  exact (V.continuous.continuousAt.comp (A.continuous.continuousAt.comp
    ((hω.contDiffAt (hU.mem_nhds hx)).continuousAt_fderiv one_ne_zero))).continuousWithinAt

 theorem integrableOn_extDeriv_compact_closure {n : ℕ} {U D : Set (Fin (n+1) → ℝ)}
    {ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U) (hc : IsCompact (closure D))
    (hDU : closure D ⊆ U) :
    IntegrableOn (fun x => extDeriv ω x (coordinateBasis (n+1))) D :=
  (((continuousOn_extDeriv_coefficient hU hω).mono hDU).integrableOn_compact hc).mono_set subset_closure

/-- An actual smooth cutoff removes the singularity at zero and is exactly
one on a neighborhood of every point outside the chosen open ball. -/
theorem exists_puncture_regularization {d n : ℕ} {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) {r : ℝ} (hr : 0 < r)
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 1 ω (U \ {0})) :
    ∃ η : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ,
      ContDiffOn ℝ 1 η U ∧
      (∀ x ∉ coordBall d r, η =ᶠ[𝓝 x] ω) := by
  have hBo : IsOpen (coordBall d r) := isOpen_lt (continuous_radiusSq d) continuous_const
  have h0 : (0 : Fin d → ℝ) ∈ coordBall d r := by
    simpa [coordBall, radiusSq] using sq_pos_of_pos hr
  have hdis : Disjoint ({0} : Set (Fin d → ℝ)) (coordBall d r)ᶜ := by
    simp [h0]
  obtain ⟨χ, hχ0, hχ1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, Fin d → ℝ) isClosed_singleton hBo.isClosed_compl hdis (n := 1)
  have hχ : ContDiff ℝ 1 χ := χ.contMDiff.contDiff
  have hχzero : (fun x => χ x) =ᶠ[𝓝 (0 : Fin d → ℝ)] (fun _ => 0) := by
    rw [nhdsSet_singleton] at hχ0
    filter_upwards [hχ0] with x hx
    exact hx
  refine ⟨fun x => χ x • ω x, ?_, ?_⟩
  · intro x hx
    apply ContDiffAt.contDiffWithinAt
    by_cases hx0 : x = 0
    · subst x
      apply (contDiffAt_const (c := (0 : (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ))).congr_of_eventuallyEq
      filter_upwards [hχzero] with z hz
      simp [hz]
    · exact hχ.contDiffAt.smul (hω.contDiffAt
        ((hU.sdiff isClosed_singleton).mem_nhds ⟨hx, by simpa using hx0⟩))
  · intro x hx
    have hone : ∀ᶠ y in 𝓝 x, χ y = 1 := hχ1.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hone] with y hy
    simp [hy]

/-- The sphere integral uses the outward orientation from the ball. -/
def sphereFlux {n : ℕ} (r : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ) : ℝ :=
  ∑ i : Fin (n+1), (-1 : ℝ)^i.val * ∫ y in coordBall n r,
    ω (i.insertNth (chord r y) y) (i.removeNth (coordinateBasis (n+1))) -
      ω (i.insertNth (-chord r y) y) (i.removeNth (coordinateBasis (n+1)))

 theorem sphereFlux_congr {n : ℕ} (r : ℝ)
    (ω η : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (he : ∀ x, radiusSq x = r^2 → ω x = η x) : sphereFlux r ω = sphereFlux r η := by
  unfold sphereFlux
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply setIntegral_congr_fun (measurableSet_coordBall n r)
  intro y hy
  obtain ⟨hp, hm⟩ := radiusSq_boundary i r (show y ∈ coordClosedBall n r from (show radiusSq y < r^2 from hy).le)
  dsimp only
  rw [he _ hp, he _ hm]

 theorem integral_closedBall_eq_ball {n : ℕ} (r : ℝ) (f : (Fin (n+1) → ℝ) → ℝ) :
    (∫ x in coordClosedBall (n+1) r, f x) = ∫ x in coordBall (n+1) r, f x := by
  apply setIntegral_congr_set
  have hae : ∀ᵐ x : Fin (n+1) → ℝ, x ∉ {x | radiusSq x = r^2} :=
    ae_iff.mpr (by simpa using volume_coordSphere (n := n) r)
  filter_upwards [hae] with x hx
  apply propext
  change radiusSq x ≤ r^2 ↔ radiusSq x < r^2
  exact (lt_iff_le_and_ne.trans (and_iff_left hx)).symm

 theorem integral_extDeriv_ball_local {n : ℕ} {U : Set (Fin (n+1) → ℝ)} (r : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U) (hBU : coordClosedBall (n+1) r ⊆ U) :
    (∫ x in coordBall (n+1) r, extDeriv ω x (coordinateBasis (n+1))) = sphereFlux r ω := by
  apply integral_extDeriv_ball_of_C1 r ω
  · intro x hx
    exact (hω.contDiffAt (hU.mem_nhds (hBU hx))).differentiableAt one_ne_zero
  · intro i x hx
    have hcoeff : ContDiffOn ℝ 1 (fun z => ω z (i.removeNth (coordinateBasis (n+1)))) U :=
      (ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth (coordinateBasis (n+1)))).contDiff.comp_contDiffOn hω
    exact (((hcoeff.contDiffAt (hU.mem_nhds (hBU hx))).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const).continuousWithinAt

 theorem chartBoundaryFlux_congr {n : ℕ}
    (e : OpenPartialHomeomorph (Fin (n+1) → ℝ) (Fin (n+1) → ℝ))
    (k : Fin (n+1)) (R : ℝ)
    (ω η : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (he : ∀ x ∈ e.source, e x k = R → ω x = η x) :
    chartBoundaryFlux e k R ω = chartBoundaryFlux e k R η := by
  unfold chartBoundaryFlux
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : k.insertNth R y ∈ e.target
  · have hlevel : e (e.symm (k.insertNth R y)) k = R := by rw [e.right_inv hy]; simp
    simp [extendedChartForm, hy, pullbackForm, he _ (e.map_target hy) hlevel]
  · simp [extendedChartForm, hy]

end MahlerStokes

end

end OAI
