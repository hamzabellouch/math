import OAI.Analysis.CircleDomains.Sobolev.SobolevJacobianLocality
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

/-! Locality identifies the actual Sobolev gradient and its energy. A
zero exterior contributes no energy; the intervening circle is null. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakGradient_eq_on_subset
    {Ω V : Set EuclideanPlane} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {u v : EuclideanPlane → ℝ}
    (Hu : DeGiorgi.MemW1pWitness 2 u Ω) (Hv : DeGiorgi.MemW1pWitness 2 v V)
    (heq : EqOn u v V) :
    Hu.weakGrad =ᵐ[volume.restrict V] Hv.weakGrad := by
  let H := Hu.restrict hV hVΩ
  have hi (i : Fin 2) : (fun x => Hu.weakGrad x i) =ᵐ[volume.restrict V]
      fun x => Hv.weakGrad x i := by
    apply (weakPartial_congrOn hV (H.isWeakGrad i) heq).ae_eq hV (Hv.isWeakGrad i)
    · exact (H.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
    · exact (Hv.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
  filter_upwards [ae_all_iff.mpr hi] with x hx
  ext i
  exact hx i

 theorem weakGradient_zero_on_subset
    {Ω V : Set EuclideanPlane} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {u : EuclideanPlane → ℝ} (H : DeGiorgi.MemW1pWitness 2 u Ω)
    (hz : ∀ x ∈ V, u x = 0) : ∀ᵐ x ∂volume.restrict V, H.weakGrad x = 0 := by
  let H₀ := (H.restrict hV hVΩ).smul 0
  have heq : EqOn u (fun x => (0 : ℝ)*u x) V := by
    intro x hx
    change u x = 0*u x
    rw [hz x hx,zero_mul]
  have hg := weakGradient_eq_on_subset hV hVΩ H H₀ heq
  filter_upwards [hg] with x hx
  simpa only [H₀,DeGiorgi.MemW1pWitness.smul,zero_smul] using hx

 theorem localized_weakGradient_energy
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω) {R : ℝ}
    {u v : EuclideanPlane → ℝ} (Hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (Hv : DeGiorgi.MemW1pWitness 2 v (Ω ∩ ball 0 R))
    (heq : EqOn u v (Ω ∩ ball 0 R))
    (hz : ∀ x ∈ Ω, R < ‖x‖ → u x = 0) :
    (∫ x in Ω, ‖Hu.weakGrad x‖^2) = ∫ x in Ω ∩ ball 0 R, ‖Hv.weakGrad x‖^2 := by
  have hV := hΩ.inter (isOpen_ball (x := (0 : EuclideanPlane)) (ε := R))
  have hZ := hΩ.inter (isClosed_closedBall (x := (0 : EuclideanPlane)) (ε := R)).isOpen_compl
  have hgz := weakGradient_zero_on_subset hZ inter_subset_left Hu (fun x hx => hz x hx.1 (by
    simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hx.2))
  have hgz' := (ae_restrict_iff' hZ.measurableSet).mp hgz
  have hcircle : ∀ᵐ x : EuclideanPlane ∂volume, x ∉ sphere 0 R :=
    compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume 0 R)
  have hezero : ∀ᵐ x ∂volume.restrict Ω, x ∉ ball 0 R → ‖Hu.weakGrad x‖^2 = 0 := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet,ae_restrict_of_ae hgz',
      ae_restrict_of_ae hcircle] with x hx hg hc hb
    have hnorm : R < ‖x‖ := by
      have hn : R ≤ ‖x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hb
      have hne : ‖x‖ ≠ R := by simpa only [mem_sphere,dist_zero_right] using hc
      exact lt_of_le_of_ne hn hne.symm
    rw [hg ⟨hx,by simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hnorm⟩]
    simp
  have hrestrict : (volume.restrict Ω).restrict (ball 0 R) = volume.restrict (Ω ∩ ball 0 R) := by
    rw [Measure.restrict_restrict measurableSet_ball,inter_comm]
  calc
    _ = ∫ x in ball 0 R, ‖Hu.weakGrad x‖^2 ∂volume.restrict Ω :=
      (setIntegral_eq_integral_of_ae_compl_eq_zero hezero).symm
    _ = ∫ x in Ω ∩ ball 0 R, ‖Hu.weakGrad x‖^2 := by rw [hrestrict]
    _ = _ := integral_congr_ae ((weakGradient_eq_on_subset hV inter_subset_left Hu Hv heq).mono
      (fun _ hx => congrArg (fun z : EuclideanPlane => ‖z‖^2) hx))

end CircleDomainRigidity

end

end OAI
