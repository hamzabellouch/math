import OAI.Analysis.CircleDomains.Transfer.RetainedScalarTails
import OAI.Analysis.CircleDomains.Modulus.TerminalLinePayment

namespace OAI

/-! Constant values for the actual finite target holes. Every finite cluster
value differs from the chosen fill by at most the original terminal oscillation. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem TerminalComponentAssignment.exists_scalar_fill_values
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (heq : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (w : (ℝ × ℝ) → ℝ) {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O) (hw : ContinuousOn w O) :
    ∃ value : I → ℝ, ∀ i t,
      t ∈ componentClusterValues V (a.point i) (sphereRealFunction w ∘ fi) →
      |t - value i| ≤ terminalOscillation (T i) w := by
  have hne (i : I) : (frontier (realJordanInterior (T i))).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (T i)).nonempty
    refine ⟨Complex.equivRealProdCLM z, ?_⟩
    rw [frontier_realJordanInterior]
    exact mem_image_of_mem _ hz
  choose point hpoint using hne
  refine ⟨fun i => w (point i), ?_⟩
  intro i t ht
  have hsub := a.cluster_values_subset_boundary heq i (sphereRealFunction w) (by
    rintro _ ⟨z, hz, rfl⟩
    apply continuousAt_sphereRealFunction
    apply hw.continuousAt (hO.mem_nhds (hTO i ?_))
    rw [frontier_realJordanInterior]
    exact mem_image_of_mem _ hz)
  obtain ⟨_, ⟨z, hz, rfl⟩, hzt⟩ := hsub ht
  have hzt' : w (Complex.equivRealProdCLM z) = t := by
    simpa only [sphereRealFunction, finiteCoord_coe] using hzt
  have hz' : Complex.equivRealProdCLM z ∈ frontier (realJordanInterior (T i)) := by
    rw [frontier_realJordanInterior]
    exact mem_image_of_mem _ hz
  have hb := ((realJordanInterior_geometry (T i)).2.1.image_of_continuousOn
    (hw.mono (hTO i))).isBounded
  simpa only [terminalOscillation, Real.dist_eq, hzt'] using
    dist_le_diam_of_mem hb (mem_image_of_mem w hz') (mem_image_of_mem w (hpoint i))

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

structure HoleFilling (i : Fin m) (n : ℕ) where
  center : (R.model.stages n).indices → ℂ
  radius : (R.model.stages n).indices → ℝ
  radius_nonneg : ∀ s, 0 ≤ radius s
  component : ∀ s, connectedComponentIn (R.model.stages n).domainᶜ
    ((R.limit.assignment n).point s) = ((↑) : ℂ → Sphere) '' closedBall (center s) (radius s)
  disjoint : Pairwise (Disjoint on fun s => closedBall (center s) (radius s))
  complement : ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain =
    (⋃ s, closedBall (center s) (radius s))ᶜ
  value : (R.model.stages n).indices → ℝ
  cluster_error : ∀ s t, t ∈ componentClusterValues (R.model.stages n).domain
    ((R.limit.assignment n).point s)
    (sphereRealFunction ((R.model.stages n).functions (prefixIndex (R.index i) n)) ∘
      (R.model.stages n).inverse) →
    |t - value s| ≤ terminalOscillation ((R.model.stages n).terminals.H s)
      ((R.model.stages n).functions (prefixIndex (R.index i) n))

 theorem exists_hole_filling (i : Fin m) (n : ℕ) : Nonempty (R.HoleFilling i n) := by
  let M := R.model.stages n
  let a := R.limit.assignment n
  obtain ⟨c, r, hr, he, hd, hcomp⟩ := a.exists_disk_coordinates M.circle_domain
    (M.equivalence.infty_mem_target M.source_infty M.principal.1)
  obtain ⟨v, hv⟩ := a.exists_scalar_fill_values M.equivalence
    (M.functions (prefixIndex (R.index i) n)) M.extension_open M.terminal_frontier_extension
    (M.functions_smooth (prefixIndex (R.index i) n)).continuousOn
  exact ⟨⟨c, r, hr, he, hd, hcomp, v, hv⟩⟩

 theorem HoleFilling.radius_sq_bound
    (harea : ExteriorCoefficientAreaTheorem) {i : Fin m} {n : ℕ}
    (F : R.HoleFilling i n) :
    ∑' s, F.radius s ^ 2 ≤ (3 * R.model.radius) ^ 2 := by
  let M := R.model.stages n
  let : Fintype M.indices := M.finite_indices.fintype
  have hbound := (normalized_model_uniform_bound harea M.equivalence M.circle_domain.1
    R.model.radius_pos ((R.model.exterior_core n).trans (R.model.core_model n))
    ((R.model.core_conformal n).mono
      ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (R.model.exterior_core n)))
    M.principal).1
  simpa only [tsum_fintype] using sum_radii_sq_le_of_disjoint_closed_disks F.center F.radius
    F.radius_nonneg (mul_nonneg (by norm_num) R.model.radius_pos.le) F.disjoint
    (fun s => terminal_disk_subset_bound (F.component s) hbound)

 theorem eventually_hole_cost_bound (harea : ExteriorCoefficientAreaTheorem)
    (i : Fin m) (hQ : Continuous (Q i).quotient) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n,
      (∑' s, F.radius s * terminalOscillation ((R.model.stages n).terminals.H s)
        ((R.model.stages n).functions (prefixIndex (R.index i) n))) <
      3 * R.model.radius * modelError n := by
  filter_upwards [R.eventually_oscillation i hQ] with n hn F
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  rw [tsum_fintype]
  have hrad : Real.sqrt (∑ s, F.radius s ^ 2) ≤ 3 * R.model.radius := by
    have h := F.radius_sq_bound R harea
    rw [tsum_fintype] at h
    exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq (mul_nonneg (by norm_num) R.model.radius_pos.le))
  refine (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ F.radius _).trans_lt ?_
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrad (Real.sqrt_nonneg _))
  apply mul_lt_mul_of_pos_left _ (mul_pos (by norm_num) R.model.radius_pos)
  simpa only [tsum_fintype] using hn

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
