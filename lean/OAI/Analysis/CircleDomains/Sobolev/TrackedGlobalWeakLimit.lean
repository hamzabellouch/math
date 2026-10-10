import OAI.Analysis.CircleDomains.Uniformization.RecursiveLimitIdentity
import OAI.Analysis.CircleDomains.Rigidity.RemovableAreaZero
import OAI.Analysis.CircleDomains.Uniformization.ScalarModelInverseConvergence
import OAI.Analysis.CircleDomains.Sobolev.ScalarModelExactEnergy
import OAI.Analysis.CircleDomains.Selection.TrackedTestBounds
import OAI.Analysis.CircleDomains.Sobolev.BoundedEnergyWeakClosure

namespace OAI

/-! The actual continued tracked test converges off the removable dust,
and hence almost everywhere, to its continuous source limit. Its exact
model energy and the recursive budget give a global weak gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "f" => scalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => witness hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "idx" => index hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "sf" => sphereScalar hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem exists_tracked_global_weak_limit
    (hprincipal : PrincipalRealBeltrami) (harea : ExteriorCoefficientAreaTheorem)
    (hconn : IsConnected G) (hrem : IsConformallyRemovable Gᶜ)
    (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
    (hnorm : IsPrincipalNormalized (extendAtInfinity F))
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G}) (i : Fin T.count) :
    ∃ (v : C(Sphere,ℝ)) (g : EuclideanPlane → EuclideanPlane),
      (∀ p, |v p-sphereFromPlaneFunction (T.test i) p| ≤ ε/4) ∧
      MemLp g 2 volume ∧ DeGiorgi.HasWeakGrad g (fun x => v (planeSphere x)) univ ∧
      (∫ x, ‖g x‖^2) ≤
        (‖(T.witness i).weakGrad_memLp.toLp ((T.witness i).weakGrad)‖+ε/4)^2 := by
  obtain ⟨v,hv,hclose⟩ := exists_continuous_limit hsupply hsard hsch hG hinf hTD ha hBa hε T i
  have hid := recursive_limit_eq_id hsupply hsard hsch hG hinf hTD ha hBa hε T
    harea hconn hrem M hσ hnorm hF hlim
  let A := fun n x => sf i (σ n) ((M (σ n)).projection (planeSphere x))
  let V : ∀ n, DeGiorgi.MemW1pWitness 2 (A n) univ :=
    fun n => (M (σ n)).witness (idx i (σ n))
  have hAc (n : ℕ) : Continuous (A n) :=
    ((sf i (σ n)).continuous.comp (M (σ n)).projection_continuous).comp continuous_planeSphere
  obtain ⟨C,hC⟩ := (T.continuous i).bounded_above_of_compact_support (T.compact i)
  have hC0 : 0 ≤ C := (norm_nonneg (T.test i 0)).trans (hC 0)
  have hbound (n : ℕ) (p : Sphere) : ‖sf i n p‖ ≤ C+ε/4 := by
    cases p using OnePoint.rec with
    | infty =>
      simp only [sphereScalar,ContinuousMap.coe_mk,sphereFromPlaneFunction,ite_true,norm_zero]
      positivity
    | coe z =>
      simp only [sphereScalar,ContinuousMap.coe_mk,sphereFromPlaneFunction_coe,Real.norm_eq_abs]
      have he := scalar_initial_error hsupply hsard hsch hG hinf hTD ha hBa hε T i n
        (complexPlaneCoordinates.symm z)
      have ht := norm_le_norm_sub_add (f i n (complexPlaneCoordinates.symm z))
        (T.test i (complexPlaneCoordinates.symm z))
      simp only [Real.norm_eq_abs] at ht
      have hc := hC (complexPlaneCoordinates.symm z)
      rw [Real.norm_eq_abs] at hc
      linarith
  have hnull := removable_complement_volume_zero hprincipal hG hinf hrem
  have hp : ∀ᵐ x ∂volume, Tendsto (fun n => A n x) atTop (𝓝 (v (planeSphere x))) := by
    have hmem : physicalPlaneDomain G ∈ ae volume := by
      simpa only [compl_compl] using (compl_mem_ae_iff.mpr hnull)
    filter_upwards [hmem] with x hx
    have ht := scalar_model_continuations_tendsto hsch hG hinf (fun n => M (σ n)) hF hlim
      (hv.comp hσ.tendsto_atTop) (z := complexPlaneCoordinates x) hx
    rw [hid _ hx] at ht
    exact ht
  let B := ‖(T.witness i).weakGrad_memLp.toLp ((T.witness i).weakGrad)‖+ε/4
  have he (n : ℕ) : (∫ x, ‖(V n).weakGrad x‖^2) ≤ B^2 := by
    rw [(M (σ n)).scalar_energy_eq hG hinf (states (σ n)).family.continuous
      (states (σ n)).family.compact (states (σ n)).family.witness (idx i (σ n))]
    change (∫ x in physicalPlaneDomain G, ‖(W i (σ n)).weakGrad x‖^2) ≤ B^2
    have heq : (∫ x in physicalPlaneDomain G, ‖(W i (σ n)).weakGrad x‖^2) =
        ‖(W i (σ n)).weakGrad_memLp.toLp ((W i (σ n)).weakGrad)‖^2 := by
      rw [Lp.norm_toLp]
      simpa only [eLpNorm_norm _ (W i (σ n)).weakGrad_memLp.aestronglyMeasurable] using
        integral_sq_eq_eLpNorm_toReal_sq (W i (σ n)).weakGrad_memLp.norm
    rw [heq]
    have hb := gradient_norm_bound hsupply hsard hsch hG hinf hTD ha hBa hε T i (σ n)
    have hn := norm_nonneg ((W i (σ n)).weakGrad_memLp.toLp ((W i (σ n)).weakGrad))
    change _ ≤ B at hb
    nlinarith
  obtain ⟨g,hg,hweak,henergy⟩ := exists_bounded_energy_weak_closure V hAc
    (fun n x => hbound (σ n) ((M (σ n)).projection (planeSphere x))) hp he
  exact ⟨v,g,hclose,hg,hweak,henergy⟩

end AppendingSequence
end CircleDomainRigidity

end

end OAI
