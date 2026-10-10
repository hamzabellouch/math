import OAI.Analysis.CircleDomains.Rigidity.MaskedCoordinateStage
import OAI.Analysis.CircleDomains.Transfer.TransportedTerminalBranches

namespace OAI

/-! The actual nonsingular terminal branches give real lifts on open
sphere neighborhoods, as required by the finite Stokes estimate. -/

open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem exists_sphere_terminal_lift
    (H : ℂ ≃ₜ ℂ) (F : (ℝ × ℝ) → UnitAddCircle) (w : (ℝ × ℝ) → ℝ)
    (E : Set (ℝ × ℝ)) (hE : IsOpen E)
    (hHE : frontier (realJordanInterior H) ⊆ E)
    (hw : ContDiffOn ℝ ∞ w E)
    (hproj : ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior H)), (w x : UnitAddCircle) = F x) :
    ∃ V : Set Sphere, IsOpen V ∧
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ V ∧
      ContinuousOn (sphereRealFunction w) V ∧
      (∀ x ∈ V, ((sphereRealFunction w x : ℝ) : UnitAddCircle) = sphereRealFunction F x) ∧
      ∀ x ∈ frontier (jordanInterior H), ∀ y ∈ frontier (jordanInterior H),
        |sphereRealFunction w (x : Sphere) - sphereRealFunction w (y : Sphere)| ≤
          Metric.diam (w '' frontier (realJordanInterior H)) := by
  obtain ⟨P, hP, hHP, hPeq⟩ := mem_nhdsSet_iff_exists.mp (sphere_branch_of_real_branch hproj)
  let V := ((↑) : ℂ → Sphere) '' (Complex.equivRealProdCLM ⁻¹' E) ∩ P
  have hVE : IsOpen V :=
    (OnePoint.isOpenEmbedding_coe.isOpenMap _ (hE.preimage Complex.equivRealProdCLM.continuous)).inter hP
  have hHV : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hHE (by rw [frontier_realJordanInterior]; exact mem_image_of_mem _ hz), rfl⟩,
      hHP (mem_image_of_mem _ hz)⟩
  refine ⟨V, hVE, hHV, ?_, fun _ hx => hPeq hx.2, ?_⟩
  · rintro p ⟨⟨z, hz, rfl⟩, _⟩
    exact (continuousAt_sphereRealFunction (hw.continuousOn.continuousAt (hE.mem_nhds hz))).continuousWithinAt
  · intro x hx y hy
    have hxf : Complex.equivRealProdCLM x ∈ frontier (realJordanInterior H) := by
      rw [frontier_realJordanInterior]
      exact mem_image_of_mem _ hx
    have hyf : Complex.equivRealProdCLM y ∈ frontier (realJordanInterior H) := by
      rw [frontier_realJordanInterior]
      exact mem_image_of_mem _ hy
    have hb : Bornology.IsBounded (w '' frontier (realJordanInterior H)) :=
      ((realJordanInterior_geometry H).2.1.image_of_continuousOn (hw.continuousOn.mono hHE)).isBounded
    simpa only [sphereRealFunction, finiteCoord_coe, Real.dist_eq] using
      Metric.dist_le_diam_of_mem hb (mem_image_of_mem w hxf) (mem_image_of_mem w hyf)

theorem MaskedCoordinateStage.nonsingular_terminal_lift
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n) (s : T.indices)
    (hs : σ s ∈ (C l).mask) (hne : σ s ≠ σ (C l).singular) :
    ∃ V : Set Sphere, IsOpen V ∧
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T.terminals.H s)) ⊆ V ∧
      ContinuousOn (sphereRealFunction (T.terminal_branch s l)) V ∧
      (∀ x ∈ V, ((sphereRealFunction (T.terminal_branch s l) x : ℝ) : UnitAddCircle) =
        sphereRealFunction (T.model.functions l) x) ∧
      ∀ x ∈ frontier (jordanInterior (T.terminals.H s)),
        ∀ y ∈ frontier (jordanInterior (T.terminals.H s)),
          |sphereRealFunction (T.terminal_branch s l) (x : Sphere) -
            sphereRealFunction (T.terminal_branch s l) (y : Sphere)| ≤
              Metric.diam (T.terminal_branch s l '' frontier (realJordanInterior (T.terminals.H s))) :=
  exists_sphere_terminal_lift (T.terminals.H s) (T.model.functions l) (T.terminal_branch s l)
    (T.terminal_domain s) (T.terminal_open s) (T.terminal_frontier s)
    (T.terminal_lift l s hs hne).1 (T.terminal_lift l s hs hne).2

end CircleDomainRigidity.FiniteTransfer

end

end OAI
