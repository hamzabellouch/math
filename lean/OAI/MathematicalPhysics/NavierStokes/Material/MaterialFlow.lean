import OAI.MathematicalPhysics.NavierStokes.Material.Energy

namespace OAI

namespace Alternating
open scoped Topology BigOperators NNReal
open Filter MeasureTheory

noncomputable section

theorem finite_lipschitz_bound {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u))
    {K : Set Space} (hK : IsCompact K) (hs : SupportedIn K u) (T : ℝ) :
    ∃ L : ℝ≥0, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∀ x, ‖u t x‖ ≤ L) ∧ LipschitzWith L (u t) := by
  obtain ⟨C, hC⟩ := bounded_finite_cylinder hu hK hs T
  let L : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨L, ?_⟩
  intro t ht
  constructor
  · intro x
    exact (le_add_of_nonneg_right (norm_nonneg (fderiv ℝ (u t) x))).trans
      ((hC t ht x).trans (le_max_left _ _))
  · apply lipschitzWith_of_nnnorm_fderiv_le
      ((hu.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
    intro x
    change ‖fderiv ℝ (u t) x‖ ≤ max C 0
    exact (le_add_of_nonneg_left (norm_nonneg (u t x))).trans
      ((hC t ht x).trans (le_max_left _ _))

theorem finiteParticle_unique {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u))
    {K : Set Space} (hK : IsCompact K) (hs : SupportedIn K u)
    {f g : ℝ → Space} {A B T : ℝ} (hTA : T ≤ A) (hTB : T ≤ B)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) A, HasDerivWithinAt f (u t (f t)) (Set.Icc 0 A) t)
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) B, HasDerivWithinAt g (u t (g t)) (Set.Icc 0 B) t)
    (h0 : f 0 = g 0) : Set.EqOn f g (Set.Icc (0 : ℝ) T) := by
  obtain ⟨L, hL⟩ := finite_lipschitz_bound hu hK hs T
  have hsubA : Set.Icc (0 : ℝ) T ⊆ Set.Icc 0 A := Set.Icc_subset_Icc_right hTA
  have hsubB : Set.Icc (0 : ℝ) T ⊆ Set.Icc 0 B := Set.Icc_subset_Icc_right hTB
  apply ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun t ht => (hL t ⟨ht.1, ht.2.le⟩).2.lipschitzOnWith)
    ((HasDerivWithinAt.continuousOn hf).mono hsubA) _ (fun _ _ => Set.mem_univ _)
    ((HasDerivWithinAt.continuousOn hg).mono hsubB) _ (fun _ _ => Set.mem_univ _) h0
  · intro t ht
    exact (hf t (hsubA ⟨ht.1, ht.2.le⟩)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2.trans_le hTA⟩)
  · intro t ht
    exact (hg t (hsubB ⟨ht.1, ht.2.le⟩)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2.trans_le hTB⟩)

theorem solvesParticle_unique {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u))
    {K : Set Space} (hK : IsCompact K) (hs : SupportedIn K u)
    {a : Space} {f g : ℝ → Space} (hf : SolvesParticle u a f) (hg : SolvesParticle u a g)
    {t : ℝ} (ht : 0 ≤ t) : f t = g t := by
  apply finiteParticle_unique hu hK hs (A := t) (B := t) le_rfl le_rfl
    (fun s hs => (hf.2 s hs.1).mono Set.Icc_subset_Ici_self)
    (fun s hs => (hg.2 s hs.1).mono Set.Icc_subset_Ici_self)
    (hf.1.trans hg.1.symm) ⟨ht, le_rfl⟩

theorem exists_finiteParticle {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u))
    {K : Set Space} (hK : IsCompact K) (hs : SupportedIn K u) (a : Space)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ γ : ℝ → Space, γ 0 = a ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt γ (u t (γ t)) (Set.Icc 0 T) t := by
  obtain ⟨L, hL⟩ := finite_lipschitz_bound hu hK hs T
  let R : ℝ≥0 := L * ⟨T, hT⟩
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hpl : IsPicardLindelof u t₀ a R 0 L L := {
    lipschitzOnWith := fun t ht => (hL t ht).2.lipschitzOnWith
    continuousOn := fun x _hx =>
      (hu.comp (contDiff_id.prodMk contDiff_const)).continuous.continuousOn
    norm_le := fun t ht x _hx => (hL t ht).1 x
    mul_max_le := by
      simp only [t₀, sub_zero, sub_self, max_eq_left hT, NNReal.coe_zero]
      exact le_rfl }
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem exists_globalMaterialFlow {u : Field}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u))
    {K : Set Space} (hK : IsCompact K) (hs : SupportedIn K u) :
    ∃ X : ℝ → Space → Space, GlobalMaterialFlow u X := by
  have hfin (n : ℕ) (a : Space) := exists_finiteParticle hu hK hs a (show 0 ≤ (n : ℝ) + 1 by positivity)
  choose F hF0 hFD using hfin
  let X : ℝ → Space → Space := fun t a => F ⌊t⌋₊ a t
  have hmatch (a : Space) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (hN : t ≤ (N : ℝ) + 1) :
      X t a = F N a t := by
    let A : ℝ := (⌊t⌋₊ : ℝ) + 1
    let B : ℝ := (N : ℝ) + 1
    apply finiteParticle_unique hu hK hs (T := min A B) (min_le_left _ _) (min_le_right _ _)
      (hFD ⌊t⌋₊ a) (hFD N a) ((hF0 ⌊t⌋₊ a).trans (hF0 N a).symm)
    exact ⟨ht, le_min (Nat.lt_floor_add_one t).le hN⟩
  have hsolve (a : Space) : SolvesParticle u a (fun t => X t a) := by
    constructor
    · change F ⌊(0 : ℝ)⌋₊ a 0 = a
      exact hF0 _ a
    · intro t ht
      obtain ⟨N, hN⟩ := exists_nat_gt t
      have hN' : t < (N : ℝ) + 1 := by linarith
      have hmem : Set.Icc (0 : ℝ) ((N : ℝ) + 1) ∈ 𝓝[Set.Ici 0] t := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hN')] with s hs0 hsN
        exact ⟨hs0, hsN.le⟩
      have he : (fun s => X s a) =ᶠ[𝓝[Set.Ici 0] t] F N a := by
        filter_upwards [hmem] with s hs'
        exact hmatch a N hs'.1 hs'.2
      have hd := (hFD N a t ⟨ht, hN'.le⟩).mono_of_mem_nhdsWithin hmem
      rw [← hmatch a N ht hN'.le] at hd
      exact hd.congr_of_eventuallyEq he (hmatch a N ht hN'.le)
  refine ⟨X, hsolve, ?_⟩
  intro a γ hγ t ht
  exact solvesParticle_unique hu hK hs hγ (hsolve a) ht

def constructedFlow (I : MachineInput) : ℝ → Space → Space :=
  Classical.choose (exists_globalMaterialFlow (constructedVelocity_contDiff I)
    (isCompact_closedBall 0 3) (constructedVelocity_support I))

theorem constructedFlow_material (I : MachineInput) :
    GlobalMaterialFlow (constructedVelocity I) (constructedFlow I) :=
  Classical.choose_spec (exists_globalMaterialFlow (constructedVelocity_contDiff I)
    (isCompact_closedBall 0 3) (constructedVelocity_support I))

theorem constructedFlow_observed (I : MachineInput) (hI : ValidInput I) {t : ℝ} (ht : 0 ≤ t) :
    constructedFlow I t observedParticle = constructedTrajectory I hI t :=
  ((constructedFlow_material I).2 observedParticle (constructedTrajectory I hI)
    (constructedTrajectory_solves I hI) t ht).symm

theorem constructedFlow_reaches_iff (I : MachineInput) (hI : ValidInput I) :
    (∃ t : ℝ, 0 ≤ t ∧ 0 < constructedFlow I t observedParticle 0) ↔ Halts I := by
  rw [← constructedTrajectory_reaches_iff I hI]
  constructor
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, ht, by simpa only [constructedFlow_observed I hI ht] using hp⟩
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, ht, by simpa only [constructedFlow_observed I hI ht] using hp⟩

theorem explicit_navierStokes_material_simulation (ν : ℝ) (I : MachineInput) (hI : ValidInput I) :
    SmoothUpToZero (constructedVelocity I) ∧ SmoothUpToZero (constructedForce ν I) ∧
    SupportedIn (Metric.closedBall 0 3) (constructedVelocity I) ∧
    SupportedIn (Metric.closedBall 0 3) (constructedForce ν I) ∧
    NSSolution ν (constructedForce ν I) (constructedVelocity I) (fun _ _ => 0) ∧
    EnergyClass (constructedVelocity I) (fun _ _ => 0) ∧
    GlobalMaterialFlow (constructedVelocity I) (constructedFlow I) ∧
    ((∃ t : ℝ, 0 ≤ t ∧ 0 < constructedFlow I t observedParticle 0) ↔ Halts I) :=
  ⟨constructedVelocity_smooth I, constructedForce_smooth ν I,
    constructedVelocity_support I, constructedForce_support ν I,
    constructedVelocity_nsSolution ν I, constructedVelocity_energyClass I,
    constructedFlow_material I, constructedFlow_reaches_iff I hI⟩

end
end Alternating

end OAI
