import OAI.Analysis.CircleDomains.Transfer.TransportedTerminalBranches

namespace OAI

/-!
# Terminal estimates on an actual finite circle model

The terminal assignment is constructed from the smooth model. The same
branches produced on physical terminal collars have the required summed
cluster-oscillation bound at their assigned target components.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_finite_model_terminal_estimates
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {I J : Type*} [Fintype I] [Fintype J] {n : ℕ}
    (T : I → ℂ ≃ₜ ℂ) (H : J → ℂ ≃ₜ ℂ)
    (hTd : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    {φ φi : Sphere → Sphere} {V : Set Sphere}
    (heq : IsSmoothSphereEquivalence φ φi (openCompletedRegion T) V)
    (hV : IsOpen V) (hfix : φ OnePoint.infty = OnePoint.infty)
    {Ω : Set (ℝ × ℝ)} (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O i)
    (M : Fin n → Set (ℝ × ℝ)) (f F : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (u : I → Fin n → (ℝ × ℝ) → ℝ)
    (S : Fin n → Finset I) (c : I → Fin n → ℝ)
    (hu : ∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ l i, i ∈ S l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (N : ℕ) {δ η : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4)
    (θ : Fin n → ℝ)
    (hF : IsMaskedFilledCircleFamily (fun j => realJordanInterior (H j)) Ω M
      (circleCutoffFamily f χ N δ θ) F)
    (hc : ∀ l i, i ∈ S l → 0 ≤ c i l)
    (hbound : ∀ l i, i ∈ S l → ∀ x ∈ frontier (jordanInterior (T i)),
      ∀ y ∈ frontier (jordanInterior (T i)),
      |shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l (Complex.equivRealProdCLM x)) -
        shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l (Complex.equivRealProdCLM y))| ≤
          c i l + 4 * reciprocalGridStep N)
    (hsmall : reciprocalGridStep N * Real.sqrt (Fintype.card I : ℝ) < η) :
    ∃ (a : TerminalComponentAssignment T φ V) (w : I → Fin n → (ℝ × ℝ) → ℝ),
      (∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (w i l) (O i) ∧
        ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior (T i))), (w i l x : UnitAddCircle) = F l x) ∧
      (∀ l, Real.sqrt (∑ i ∈ S l,
        max (Metric.diam (w i l '' frontier (realJordanInterior (T i))) - c i l) 0 ^ 2) < 4 * η) ∧
      (∀ l, Real.sqrt (∑ i ∈ S l, max (Metric.diam
        (componentClusterValues V (a.point i) (sphereRealFunction (w i l) ∘ φi)) - c i l) 0 ^ 2)
          < 4 * η) := by
  obtain ⟨a⟩ := exists_terminal_component_assignment hsard hsch T hTd heq hV hfix
  obtain ⟨w, hw, hexcess⟩ := physical_masked_terminal_branches T H hTH O hO hTO
    M f F χ u S c hu hproj hχone N hδ hδh θ hF hc hbound hsmall
  refine ⟨a, w, hw, hexcess, ?_⟩
  intro l
  exact (a.real_cluster_excess_le heq (S l) (fun i => w i l) (fun i => c i l)
    O hO hTO (fun i hi => (hw l i hi).1.continuousOn)).trans_lt (hexcess l)

end CircleDomainRigidity

end

end OAI
