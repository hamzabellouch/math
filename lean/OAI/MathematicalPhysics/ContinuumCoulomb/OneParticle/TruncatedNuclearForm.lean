import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedNearForm

namespace OAI

/-! The truncated point kernels in the mesh error are controlled on the
entire weak-H1 domain by the separated-nucleus near-field estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace ContinuumCoulomb

theorem truncated_nuclear_integrable_bound {n : ℕ} (u : Coulomb.H1Vector n)
    (s : SpinConfiguration n) (i : Fin n) (a : Position) (r : ℝ) :
    Integrable (fun x => Coulomb.truncatedCoulomb r (Coulomb.position x i-a)*‖u.value s x‖^2) ∧
    (∫ x, Coulomb.truncatedCoulomb r (Coulomb.position x i-a)*‖u.value s x‖^2) ≤
      ∫ x in electronBall i a r, Coulomb.coulombKernel (Coulomb.position x i-a)*‖u.value s x‖^2 := by
  have hi := (u.nuclear_coulomb_integrable_bound s i a (by norm_num : (0:ℝ) < 1)).1
  have hk (z : Position) : Coulomb.truncatedCoulomb r z ≤ Coulomb.coulombKernel z := by
    by_cases hz : z ∈ Metric.ball (0:Position) r
    · simp only [Coulomb.truncatedCoulomb,Set.indicator_of_mem hz,le_refl]
    · simpa only [Coulomb.truncatedCoulomb,Set.indicator_of_notMem hz] using
        Coulomb.coulombKernel_nonneg z
  have hm : AEStronglyMeasurable
      (fun x : Configuration n => Coulomb.truncatedCoulomb r (Coulomb.position x i-a)) volume :=
    ((Coulomb.coulombKernel_measurable.indicator measurableSet_ball).comp
    ((Coulomb.positionCLM i).continuous.sub continuous_const).measurable).aestronglyMeasurable
  have ht : Integrable (fun x =>
      Coulomb.truncatedCoulomb r (Coulomb.position x i-a)*‖u.value s x‖^2) := by
    apply hi.mono' (hm.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2))
    exact Filter.Eventually.of_forall (fun x => by
      change ‖Coulomb.truncatedCoulomb r (Coulomb.position x i-a)*‖u.value s x‖^2‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (Coulomb.truncatedCoulomb_nonneg _ _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hk _) (sq_nonneg _))
  refine ⟨ht,?_⟩
  rw [← integral_indicator (electronBall_measurable i a r)]
  apply integral_mono ht (hi.indicator (electronBall_measurable i a r))
  intro x
  by_cases hx : x ∈ electronBall i a r
  · rw [Set.indicator_of_mem hx]
    exact mul_le_mul_of_nonneg_right (hk _) (sq_nonneg _)
  · rw [Set.indicator_of_notMem hx]
    have hn : Coulomb.position x i-a ∉ Metric.ball (0:Position) r := by
      simp only [Metric.mem_ball,dist_zero_right]
      exact not_lt.mpr (le_of_lt (lt_of_not_ge hx))
    simp only [Coulomb.truncatedCoulomb,Set.indicator_of_notMem hn,zero_mul,le_refl]

theorem transportedGauss_truncated_form {κ : ℝ} (hκ : 0 < κ)
    (K : ℝ≥0) (hK : 0 < K) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {ι : Type} [Fintype ι] (n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (h ρ : ℝ),
      0 < h → h ≤ 1 → 0 ≤ ρ →
      ∀ (index : ι → GaussLatticeIndex), Function.Injective index →
      ∀ (G : Position → Position), AntilipschitzWith K G →
      (ρ*h^3/8)*(∑ a, ∫ x,
        Coulomb.truncatedCoulomb (κ*h) (Coulomb.position x i-G (gaussLatticePoint h (index a)))*
          ‖u.value s x‖^2) ≤
      ρ*A*h^2*((∫ x, ‖u.value s x‖^2)+
        ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) := by
  obtain ⟨A,hA,hbound⟩ := transportedGauss_near_form hκ K hK
  refine ⟨A,hA,?_⟩
  intro ι _ n u s i h ρ hh hh1 hρ index hindex G hG
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have he := hbound (Fintype.card ι) n u s i h ρ hh hh1 hρ (index ∘ e)
    (hindex.comp e.injective) G hG
  have hs : (∑ a : ι, ∫ x in electronBall i (G (gaussLatticePoint h (index a))) (κ*h),
        Coulomb.coulombKernel (Coulomb.position x i-G (gaussLatticePoint h (index a)))*‖u.value s x‖^2) =
      ∑ a : Fin (Fintype.card ι), ∫ x in electronBall i (G (gaussLatticePoint h (index (e a)))) (κ*h),
        Coulomb.coulombKernel (Coulomb.position x i-G (gaussLatticePoint h (index (e a))))*‖u.value s x‖^2 :=
    (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  apply le_trans _ (by simpa only [Function.comp_apply,← hs] using he)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun a _ =>
    (truncated_nuclear_integrable_bound u s i (G (gaussLatticePoint h (index a))) (κ*h)).2)

end ContinuumCoulomb

end

end OAI
