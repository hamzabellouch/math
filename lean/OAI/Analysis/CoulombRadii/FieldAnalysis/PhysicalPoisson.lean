import Mathlib
import OAI.Analysis.CoulombRadii.Packets.CoulombKernel
import OAI.Analysis.CoulombRadii.Screening.CoreScreenedField

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb

lemma coreCoulombPotential_continuousOn {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A) {y : Space} {r t : ℝ}
    (hrt : r<t) (hsep : ∀ a∈A, t ≤ ‖a-y‖) :
    ContinuousOn (coreCoulombPotential u) (Metric.closedBall y r) := by
  let d := t-r
  have hd : 0<d := sub_pos.mpr hrt
  let G : Space → ℝ := fun z => ∑ s : Spins k, ∑ i : Fin k,
    ∫ x, (max d ‖position x i-z‖)⁻¹*‖u.value s x‖^2
  have hG : Continuous G := by
    apply continuous_finsetSum
    intro s hs
    apply continuous_finsetSum
    intro i hi
    apply MeasureTheory.continuous_of_dominated (bound := fun x => d⁻¹*‖u.value s x‖^2)
    · intro z
      exact (((measurable_const.max ((continuous_position i).measurable.sub measurable_const).norm).inv).aestronglyMeasurable).mul
        ((u.value_L2 s).aestronglyMeasurable.norm.pow 2)
    · intro z
      filter_upwards [] with x
      rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (le_max_left _ _ |>.trans' hd.le)) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hd (le_max_left _ _)) (sq_nonneg _)
    · exact ((u.value_L2 s).norm.integrable_sq).const_mul _
    · filter_upwards [] with x
      exact (((continuous_const.max (continuous_const.sub continuous_id).norm).inv₀
        (fun z => ne_of_gt (hd.trans_le (le_max_left _ _)))).mul continuous_const)
  apply hG.continuousOn.congr
  intro z hz
  unfold coreCoulombPotential G
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [hu s] with x hx
  by_cases he : u.value s x=0
  · simp [he]
  · have ha : position x i∈A := (by_contra (fun hn => he (hx hn)) : x∈allPositions A) i
    have hz' : ‖z-y‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have htri : ‖position x i-y‖ ≤ ‖position x i-z‖+‖z-y‖ := by
      simpa only [dist_eq_norm] using dist_triangle (position x i) z y
    have hdist : d ≤ ‖position x i-z‖ := by dsimp [d]; linarith [hsep _ ha]
    simp only [max_eq_right hdist,coulombKernel]

lemma coreCoulombPotential_weak_harmonic {k : ℕ} (u : H1Vector k)
    {A U : Set Space} (hu : SpatiallySupported u A) (hdis : Disjoint A U) :
    NeutralAtom.HasWeakLaplacian (coreCoulombPotential u) U (fun _ => 0) := by
  intro φ hφ hc ht
  have hi : Integrable (NeutralAtom.coordinateLaplacian φ) :=
    (NeutralAtom.continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))).integrable_of_hasCompactSupport
      (NeutralAtom.hasCompactSupport_coordinateLaplacian hc)
  rw [coreCoulombPotential_fubini u _ hi]
  simp only [zero_mul,integral_zero]
  apply Finset.sum_eq_zero
  intro s hs
  apply Finset.sum_eq_zero
  intro i hi
  apply integral_eq_zero_of_ae
  filter_upwards [hu s] with x hx
  by_cases he : u.value s x=0
  · simp [he]
  · have ha : position x i∈A := (by_contra (fun hn => he (hx hn)) : x∈allPositions A) i
    have hn : position x i∉tsupport φ := fun h => Set.disjoint_left.mp hdis ha (ht h)
    have HH := NeutralAtom.integral_translated_coulombKernel_laplacian hφ hc (position x i)
    have heq : (∫ z, coulombKernel (position x i-z)*NeutralAtom.coordinateLaplacian φ z)=0 := by
      simp_rw [coulombKernel_sub_comm (position x i)]
      change (∫ z, NeutralAtom.coulombKernel (z-position x i)*NeutralAtom.coordinateLaplacian φ z)=0
      rw [HH,image_eq_zero_of_notMem_tsupport hn]
      ring
    simp only [heq,zero_mul,Pi.zero_apply]

lemma attraction_weak_harmonic {J : ℕ} (S : Nuclei J) {U : Set Space}
    (hsep : ∀ j, S.position j∉U) :
    NeutralAtom.HasWeakLaplacian (attraction S) U (fun _ => 0) := by
  intro φ hφ hc ht
  have hL := NeutralAtom.continuous_coordinateLaplacian
    (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLc := NeutralAtom.hasCompactSupport_coordinateLaplacian hc
  have hts : tsupport (NeutralAtom.coordinateLaplacian φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    exact hx (NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
  have hi (j : Fin J) : Integrable (fun x => coulombKernel (x-S.position j)*NeutralAtom.coordinateLaplacian φ x) := by
    apply NeutralAtom.integrable_mul_compact_of_continuousAt _ hL hLc
    intro x hx
    have hn : x-S.position j≠0 := sub_ne_zero.mpr (fun he => hsep j (he ▸ ht (hts hx)))
    exact ((continuous_id.sub continuous_const).norm.continuousAt).inv₀ (norm_ne_zero_iff.mpr hn)
  simp only [attraction,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
  simp only [zero_mul,integral_zero]
  apply Finset.sum_eq_zero
  intro j hj
  rw [integral_const_mul]
  change S.charge j*(∫ x, NeutralAtom.coulombKernel (x-S.position j)*NeutralAtom.coordinateLaplacian φ x)=0
  rw [NeutralAtom.integral_translated_coulombKernel_laplacian hφ hc,
    image_eq_zero_of_notMem_tsupport (fun h => hsep j (ht h))]
  ring

lemma attraction_continuousOn {J : ℕ} (S : Nuclei J) {U : Set Space}
    (hsep : ∀ j, S.position j∉U) : ContinuousOn (attraction S) U := by
  change ContinuousOn (fun x => ∑ j : Fin J, S.charge j * ‖x-S.position j‖⁻¹) U
  apply continuousOn_finsetSum
  intro j hj
  refine continuousOn_const.mul ?_
  refine ((continuous_id.sub continuous_const).norm.continuousOn).inv₀ ?_
  intro x hx
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun he => hsep j ((show x=S.position j from he) ▸ hx)))

lemma coreScreenedField_continuousOn {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A) {y : Space} {r t : ℝ}
    (hrt : r<t) (hsep : ∀ a∈A, t ≤ ‖a-y‖)
    (hnuc : ∀ j, S.position j∉Metric.closedBall y r) :
    ContinuousOn (coreScreenedField S u) (Metric.closedBall y r) :=
  (attraction_continuousOn S hnuc).sub (coreCoulombPotential_continuousOn u hu hrt hsep)

lemma coreScreenedField_weak_harmonic {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {A U : Set Space} (hu : SpatiallySupported u A) (hdis : Disjoint A U)
    (hnuc : ∀ j, S.position j∉U) :
    NeutralAtom.HasWeakLaplacian (coreScreenedField S u) U (fun _ => 0) := by
  intro φ hφ hc ht
  have hL := NeutralAtom.continuous_coordinateLaplacian
    (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLc := NeutralAtom.hasCompactSupport_coordinateLaplacian hc
  have hi : Integrable (NeutralAtom.coordinateLaplacian φ) := hL.integrable_of_hasCompactSupport hLc
  have hiC := coreCoulombPotential_mul_integrable u _ hi
  have hiA : Integrable (fun x => attraction S x*NeutralAtom.coordinateLaplacian φ x) := by
    apply NeutralAtom.integrable_mul_compact_of_continuousAt _ hL hLc
    intro x hx
    have hts : tsupport (NeutralAtom.coordinateLaplacian φ) ⊆ tsupport φ := by
      apply closure_minimal _ (isClosed_tsupport _)
      intro x hx
      by_contra hn
      exact hx (NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
    have hx' : x∈tsupport φ := hts hx
    have hs (j) : x≠S.position j := fun h => hnuc j (h ▸ ht hx')
    change ContinuousAt (fun x => ∑ j : Fin J, S.charge j * ‖x-S.position j‖⁻¹) x
    apply tendsto_finsetSum
    intro j hj
    exact continuousAt_const.mul (((continuous_id.sub continuous_const).norm.continuousAt).inv₀
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hs j))))
  simp only [coreScreenedField,sub_mul]
  rw [integral_sub hiA hiC,attraction_weak_harmonic S hnuc φ hφ hc ht,
    coreCoulombPotential_weak_harmonic u hu hdis φ hφ hc ht]
  simp

end Coulomb
end

end
end

end OAI
