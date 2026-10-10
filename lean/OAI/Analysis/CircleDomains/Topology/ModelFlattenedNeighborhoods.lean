import OAI.Analysis.CircleDomains.Transfer.ModelHeightDescent
import OAI.Analysis.CircleDomains.Topology.FlattenedEndNeighborhoods

namespace OAI

/-! Common open source neighborhoods are constructed for the flattened
old tests and the actual descended height. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_common_flattened_neighborhoods (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i))
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0)
    (b : ℕ → ℂ) (O : Fin m → Set ℝ) (hO : ∀ i, IsOpen (O i))
    (V : Set ℝ) (hV : IsOpen V)
    (hbO : ∀ n i, sphereFromPlaneFunction (u i) (b n : Sphere) ∈ O i)
    (hbV : ∀ n, M.heightSection H (b n : Sphere) ∈ V) :
    ∃ W : ℕ → Set ℂ, (∀ n, IsOpen (W n) ∧ b n ∈ W n) ∧
      (∀ n i, EqOn (fun q : ℂ => flattenValues (O i) (sphereFromPlaneFunction (u i) (q : Sphere)))
        (fun _ => flattenValues (O i) (sphereFromPlaneFunction (u i) (b n : Sphere))) (W n)) ∧
      ∀ n, EqOn (fun q : ℂ => flattenValues V (M.heightSection H (q : Sphere)))
        (fun _ => flattenValues V (M.heightSection H (b n : Sphere))) (W n) := by
  have hUc (i : Fin m) : Continuous (fun q : ℂ => sphereFromPlaneFunction (u i) (q : Sphere)) := by
    simpa only [sphereFromPlaneFunction_coe, Function.comp_def] using (hu i).comp complexPlaneCoordinates.symm.continuous
  have hHc := M.heightSection_plane_continuous hsard hsch hG hconn hinf hTD H hHz
  have hex (n : ℕ) : ∃ W : Set ℂ, IsOpen W ∧ b n ∈ W ∧
      (∀ i, EqOn (fun q : ℂ => flattenValues (O i) (sphereFromPlaneFunction (u i) (q : Sphere)))
        (fun _ => flattenValues (O i) (sphereFromPlaneFunction (u i) (b n : Sphere))) W) ∧
      EqOn (fun q : ℂ => flattenValues V (M.heightSection H (q : Sphere)))
        (fun _ => flattenValues V (M.heightSection H (b n : Sphere))) W := by
    obtain ⟨A, hA, hbA, hconst⟩ := flattened_coordinates_constant_near
      (fun (i : Fin m) (q : ℂ) => sphereFromPlaneFunction (u i) (q : Sphere))
      (fun i => (hUc i).continuousAt) O hO (hbO n)
    obtain ⟨J, hJ, hflat⟩ := flattenValues_locally_constant hV (hbV n)
    have hev : Filter.Eventually (fun q : ℂ => flattenValues V (M.heightSection H (q : Sphere)) =
        flattenValues V (M.heightSection H (b n : Sphere))) (𝓝 (b n)) :=
      (hHc.continuousAt.eventually hJ).mono (fun q hq => hflat hq)
    obtain ⟨C, hCsub, hC, hbC⟩ := mem_nhds_iff.mp hev
    exact ⟨A ∩ C, hA.inter hC, ⟨hbA, hbC⟩,
      fun i q hq => hconst i hq.1, fun q hq => hCsub hq.2⟩
  choose W hW using hex
  exact ⟨W, fun n => ⟨(hW n).1, (hW n).2.1⟩,
    fun n => (hW n).2.2.1, fun n => (hW n).2.2.2⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
