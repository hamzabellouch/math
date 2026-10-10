import OAI.Analysis.CircleDomains.Topology.TerminalBoundaryLimits
import OAI.Analysis.CircleDomains.Rigidity.PhysicalMaskedBranches

namespace OAI

/-!
# Cluster oscillation of transported terminal branches

The finite model's actual inverse transports a real branch near a physical
terminal. All its cluster values at the assigned complementary component
come from the physical boundary. Thus the physical square-sum oscillation
estimate survives uniformization without a boundary-extension hypothesis.
-/

open Set Function Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

/-- Finite real cluster values approached from the domain at a component. -/
def componentClusterValues (V : Set Sphere) (p : Sphere) (v : Sphere → ℝ) : Set ℝ :=
  {t | ∃ y ∈ connectedComponentIn Vᶜ p, ∃ yn : ℕ → Sphere,
    Tendsto yn atTop (𝓝 y) ∧ (∀ᶠ n in atTop, yn n ∈ V) ∧
      Tendsto (v ∘ yn) atTop (𝓝 t)}

theorem TerminalComponentAssignment.cluster_values_subset_boundary
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (w : Sphere → ℝ)
    (hw : ∀ q ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)),
      ContinuousAt w q) :
    componentClusterValues V (a.point i) (w ∘ fi) ⊆
      w '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i))) := by
  rintro t ⟨y, hy, yn, hyn, hynV, ht⟩
  obtain ⟨q, _, s, hs, hqs⟩ := isCompact_univ.tendsto_subseq
    (fun n => mem_univ (fi (yn n)))
  have hxQ : ∀ᶠ n in atTop, fi (yn (s n)) ∈ openCompletedRegion T := by
    filter_upwards [hs.tendsto_atTop hynV] with n hn
    exact hf.mapsTo_inv hn
  have hfy : Tendsto (fun n => f (fi (yn (s n)))) atTop (𝓝 y) := by
    apply (hyn.comp hs.tendsto_atTop).congr'
    filter_upwards [hs.tendsto_atTop hynV] with n hn
    exact (hf.right_inv _ hn).symm
  have hq := a.source_cluster_mem_boundary hf hy hqs hxQ hfy
  refine ⟨q, hq, ?_⟩
  exact tendsto_nhds_unique ((hw q hq).tendsto.comp hqs) (ht.comp hs.tendsto_atTop)

/-- A real-coordinate function, with an arbitrary unused value at infinity. -/
def sphereRealFunction {Y : Type*} (w : (ℝ × ℝ) → Y) (p : Sphere) : Y :=
  w (Complex.equivRealProdCLM (finiteCoord p))

theorem continuousAt_sphereRealFunction {Y : Type*} [TopologicalSpace Y]
    {w : (ℝ × ℝ) → Y} {z : ℂ}
    (hw : ContinuousAt w (Complex.equivRealProdCLM z)) :
    ContinuousAt (sphereRealFunction w) (z : Sphere) := by
  apply OnePoint.continuousAt_coe.mpr
  have heq : sphereRealFunction w ∘ ((↑) : ℂ → Sphere) =
      w ∘ Complex.equivRealProdCLM := by
    funext x
    simp only [sphereRealFunction, comp_apply, finiteCoord_coe]
  rw [heq]
  exact hw.comp Complex.equivRealProdCLM.continuous.continuousAt

theorem sphere_branch_of_real_branch {T : ℂ ≃ₜ ℂ}
    {w : (ℝ × ℝ) → ℝ} {F : (ℝ × ℝ) → UnitAddCircle}
    (hbranch : ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior T)),
      (w x : UnitAddCircle) = F x) :
    ∀ᶠ q in 𝓝ˢ (((↑) : ℂ → Sphere) '' frontier (jordanInterior T)),
      ((sphereRealFunction w q : ℝ) : UnitAddCircle) = sphereRealFunction F q := by
  apply eventually_nhdsSet_iff_forall.mpr
  rintro q ⟨z, hz, rfl⟩
  have hreal : Complex.equivRealProdCLM z ∈ frontier (realJordanInterior T) := by
    rw [frontier_realJordanInterior]
    exact mem_image_of_mem _ hz
  have hp := eventually_nhdsSet_iff_forall.mp hbranch _ hreal
  have hc := continuousAt_sphereRealFunction (w := id) (z := z) continuousAt_id
  exact hc.tendsto hp

theorem TerminalComponentAssignment.real_cluster_diameter_le
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (w : (ℝ × ℝ) → ℝ)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hAO : frontier (realJordanInterior (T i)) ⊆ O)
    (hw : ContinuousOn w O) :
    Metric.diam (componentClusterValues V (a.point i) (sphereRealFunction w ∘ fi)) ≤
      Metric.diam (w '' frontier (realJordanInterior (T i))) := by
  have hfront := frontier_realJordanInterior (T i)
  have hsub := a.cluster_values_subset_boundary hf i (sphereRealFunction w) (by
    rintro q ⟨z, hz, rfl⟩
    apply continuousAt_sphereRealFunction
    apply hw.continuousAt (hO.mem_nhds (hAO ?_))
    rw [hfront]
    exact mem_image_of_mem _ hz)
  have himage : sphereRealFunction w '' (((↑) : ℂ → Sphere) ''
      frontier (jordanInterior (T i))) = w '' frontier (realJordanInterior (T i)) := by
    rw [hfront, image_image, image_image]
    rfl
  rw [himage] at hsub
  apply Metric.diam_mono hsub
  exact ((realJordanInterior_geometry (T i)).2.1.image_of_continuousOn
    (hw.mono hAO)).isBounded

theorem TerminalComponentAssignment.transported_branch_eventually
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    {i : I} {y : Sphere} (hy : y ∈ connectedComponentIn Vᶜ (a.point i))
    {yn : ℕ → Sphere} (hyn : Tendsto yn atTop (𝓝 y))
    (hynV : ∀ᶠ n in atTop, yn n ∈ V)
    {w : Sphere → ℝ} {F : Sphere → UnitAddCircle}
    (hbranch : ∀ᶠ q in 𝓝ˢ (((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i))),
      (w q : UnitAddCircle) = F q) :
    ∀ᶠ n in atTop, (w (fi (yn n)) : UnitAddCircle) = F (fi (yn n)) :=
  a.inverse_tendsto_boundary hf hy hyn hynV hbranch

theorem TerminalComponentAssignment.real_cluster_excess_le
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ}
    {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (S : Finset I) (w : I → (ℝ × ℝ) → ℝ) (c : I → ℝ)
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hAO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O i)
    (hw : ∀ i ∈ S, ContinuousOn (w i) (O i)) :
    Real.sqrt (∑ i ∈ S, max (Metric.diam
      (componentClusterValues V (a.point i) (sphereRealFunction (w i) ∘ fi)) - c i) 0 ^ 2) ≤
    Real.sqrt (∑ i ∈ S, max (Metric.diam
      (w i '' frontier (realJordanInterior (T i))) - c i) 0 ^ 2) := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i hi
  apply pow_le_pow_left₀ (le_max_right _ _)
  exact max_le_max (sub_le_sub_right
    (a.real_cluster_diameter_le hf i (w i) (hO i) (hAO i) (hw i hi)) _) le_rfl

theorem TerminalComponentAssignment.real_transported_branch_eventually
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    {i : I} {y : Sphere} (hy : y ∈ connectedComponentIn Vᶜ (a.point i))
    {yn : ℕ → Sphere} (hyn : Tendsto yn atTop (𝓝 y))
    (hynV : ∀ᶠ n in atTop, yn n ∈ V)
    {w : (ℝ × ℝ) → ℝ} {F : (ℝ × ℝ) → UnitAddCircle}
    (hbranch : ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior (T i))),
      (w x : UnitAddCircle) = F x) :
    ∀ᶠ n in atTop, ((sphereRealFunction w (fi (yn n)) : ℝ) : UnitAddCircle) =
      sphereRealFunction F (fi (yn n)) :=
  a.transported_branch_eventually hf hy hyn hynV (sphere_branch_of_real_branch hbranch)

end CircleDomainRigidity

end

end OAI
