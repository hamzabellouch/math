import OAI.GroupTheory.PolycyclicRecognition.Algebra.QuotientSectionCoordinates
import Mathlib.Topology.Algebra.Group.Neighborhood

namespace OAI

/-! # Recovering topology from a quotient and its kernel -/

noncomputable section
namespace PolycyclicRecognition

open Filter Topology

variable {G Q A : Type*} [Group G] [Group Q] [Group A]
  [TopologicalSpace G] [TopologicalSpace Q] [TopologicalSpace A]
  [IsTopologicalGroup G] [IsTopologicalGroup Q] [IsTopologicalGroup A]

omit [IsTopologicalGroup Q] in
/-- Near the identity, a continuous quotient coordinate and an inducing
representation on its kernel determine the topology on the whole group. -/
theorem inducing_of_height_kernel
    (ρ : G →* A) (hρ : Continuous ρ) (π : G →* Q) (hπ : Continuous π)
    (s : C(Q, G)) (hs : ∀ q, π (s q) = q) (hsone : s 1 = 1)
    (hk : Topology.IsInducing (fun k : π.ker => ρ k))
    (f : A → Q) (hf : ContinuousAt f 1) (hf1 : f 1 = 1)
    (hfactor : ∀ g, f (ρ g) = π g) : Topology.IsInducing ρ := by
  let F := comap ρ (𝓝 (1 : A))
  have hρF : Tendsto ρ F (𝓝 (1 : A)) := tendsto_comap
  have hπF : Tendsto π F (𝓝 (1 : Q)) := by
    simpa only [Function.comp_def, hfactor, hf1] using hf.tendsto.comp hρF
  let r := quotientSectionResidual π s hs
  have hr : Tendsto r F (𝓝 (1 : π.ker)) := by
    apply hk.tendsto_nhds_iff.mpr
    have hsF : Tendsto (fun g => s (π g)) F (𝓝 (1 : G)) := by
      simpa only [Function.comp_def, hsone] using (s.continuous.tendsto (1 : Q)).comp hπF
    have hρs : Tendsto (fun g => ρ (s (π g))) F (𝓝 (1 : A)) := by
      simpa only [Function.comp_def, map_one] using (hρ.tendsto (1 : G)).comp hsF
    change Tendsto (fun g => ρ (r g)) F (𝓝 (ρ (1 : G)))
    rw [map_one]
    have hres := hρF.mul hρs.inv
    have hbase : ρ (s 1) = 1 := by rw [hsone, map_one]
    simpa only [Function.comp_def, r, quotientSectionResidual,
      map_mul, map_inv, hbase, inv_one, mul_one, map_one] using hres
  let e := quotientSectionHomeomorph π hπ s hs
  have he : Tendsto e F (𝓝 (e 1)) := by
    have heone : e 1 = (1, 1) := by
      apply Prod.ext
      · exact map_one π
      · apply Subtype.ext
        change 1 * (s (π 1))⁻¹ = 1
        rw [map_one, hsone, inv_one, mul_one]
    rw [heone]
    exact hπF.prodMk_nhds hr
  have hid : Tendsto (id : G → G) F (𝓝 (1 : G)) := by
    change Tendsto (fun g : G => g) F (𝓝 (1 : G))
    simpa only [Function.comp_def, e.symm_apply_apply] using
      e.symm.continuous.continuousAt.tendsto.comp he
  apply (IsTopologicalGroup.isInducing_iff_nhds_one (f := ρ)).mpr
  apply le_antisymm
  · exact (hρ.continuousAt.tendsto.mono_right
      (le_of_eq (congrArg nhds ρ.map_one))).le_comap
  · exact tendsto_id'.mp hid

end PolycyclicRecognition

end

end OAI
