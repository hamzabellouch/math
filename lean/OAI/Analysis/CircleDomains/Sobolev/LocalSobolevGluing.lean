import OAI.Analysis.CircleDomains.Sobolev.PartitionWeakGradient
import OAI.Analysis.CircleDomains.Sobolev.CutoffEnergyAlgebra

namespace OAI

/-! Local Sobolev witnesses with one integrable gradient majorant give
an actual witness on the whole open set, with a finite total energy. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_local_sobolev_gluing {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    {u P : EuclideanPlane → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (hP : MemLp P 2 (volume.restrict Ω))
    (hloc : ∀ x ∈ Ω, ∃ V : Set EuclideanPlane, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∃ W : DeGiorgi.MemW1pWitness 2 u V, ∀ k : Fin 2,
        ∀ᵐ y ∂volume.restrict V, |W.weakGrad y k| ≤ P y) :
    ∃ H : DeGiorgi.MemW1pWitness 2 u Ω,
      (∀ k : Fin 2, ∀ᵐ x ∂volume.restrict Ω, |H.weakGrad x k| ≤ P x) ∧
      (∫ x in Ω, ‖H.weakGrad x‖^2) ≤ 2*(∫ x in Ω, P x^2) := by
  classical
  let O : TopologicalSpace.Opens EuclideanPlane := ⟨Ω,hΩ⟩
  choose V hV hxV hVΩ W hW using (fun x : O => hloc x x.property)
  obtain ⟨ι,inst,ρ,c,hsub⟩ := exists_openPlanePartition O
    (fun x => Subtype.val ⁻¹' V x) (fun x => (hV x).preimage continuous_subtype_val |>.mem_nhds (hxV x))
  let : Countable ι := inst
  have hsub' (j : ι) : tsupport (ρ.weight j) ⊆ V (c j) := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := hsub j hx
    exact hp
  obtain ⟨H,hH⟩ := exists_partition_weak_gradient ρ (fun j => V (c j))
    (fun j => hV (c j)) (fun j => hVΩ (c j)) hsub' hu
    (fun j => W (c j)) hP (fun j k => hW (c j) k)
  refine ⟨H,hH,?_⟩
  have hpoint : ∀ᵐ x ∂volume.restrict Ω, ‖H.weakGrad x‖^2 ≤ 2*P x^2 := by
    filter_upwards [hH 0,hH 1] with x hx0 hx1
    rw [plane_norm_sq]
    have hp : 0 ≤ P x := (abs_nonneg _).trans hx0
    have h0 := mul_self_le_mul_self (abs_nonneg _) hx0
    have h1 := mul_self_le_mul_self (abs_nonneg _) hx1
    simp only [← sq, sq_abs] at h0 h1
    nlinarith
  calc
    _ ≤ ∫ x in Ω, 2*P x^2 := integral_mono_ae H.weakGrad_memLp.norm.integrable_sq
      (hP.integrable_sq.const_mul 2) hpoint
    _ = _ := integral_const_mul _ _

end CircleDomainRigidity

end

end OAI
