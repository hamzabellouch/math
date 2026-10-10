import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserRegularity
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Uniform boundedness and spatial Lipschitz regularity of the actual Moser
field on the complete transport interval. Compact support is used only to
obtain finite constants; quantitative cubature constants are a separate step. -/

noncomputable section
open scoped Topology NNReal
namespace ContinuumCoulomb

theorem moserVelocity_joint_tsupport_subset (rho : ℝ) (V : Position → ℝ) :
    tsupport (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) ⊆
      Set.univ ×ˢ tsupport V := by
  apply closure_minimal _ (isClosed_univ.prod (isClosed_tsupport V))
  intro p hp
  refine ⟨Set.mem_univ _, ?_⟩
  by_contra hx
  exact hp (moserVelocity_zero hx)

/-- Bounds are uniform over every position and all times from zero to one. -/
theorem moserVelocity_uniform_bounds {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ L K : ℝ≥0, (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖moserVelocity rho V t x‖ ≤ L) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, LipschitzWith K (moserVelocity rho V t)) ∧
      (∀ x, ContinuousOn (fun t => moserVelocity rho V t x) (Set.Icc (0 : ℝ) 1)) := by
  let F : ℝ × Position → Position := fun p => moserVelocity rho V p.1 p.2
  let S : Set (ℝ × Position) := Set.Icc (0 : ℝ) 1 ×ˢ Set.univ
  let T : Set (ℝ × Position) := Set.Icc (0 : ℝ) 1 ×ˢ tsupport V
  have hT : IsCompact T := isCompact_Icc.prod hc
  have hdom : S ⊆ moserDomain rho V := moserDomain_contains_time_slab hrho V hbound
  have hTD : T ⊆ moserDomain rho V := fun p hp => hdom ⟨hp.1, Set.mem_univ _⟩
  have hreg : ContDiffOn ℝ 4 F (moserDomain rho V) := moserVelocity_joint_C4 rho V hV
  have hopen := moserDomain_isOpen rho V hV
  have hDcont : ContinuousOn (fderiv ℝ F) (moserDomain rho V) :=
    hreg.continuousOn_fderiv_of_isOpen hopen (by norm_num)
  obtain ⟨A, hA⟩ := hT.bddAbove_image ((hreg.continuousOn.mono hTD).norm)
  obtain ⟨B, hB⟩ := hT.bddAbove_image ((hDcont.mono hTD).norm)
  let L : ℝ≥0 := ⟨max 0 A, le_max_left _ _⟩
  let K : ℝ≥0 := ⟨max 0 B, le_max_left _ _⟩
  have hnorm (p : ℝ × Position) (hp : p ∈ S) : ‖F p‖ ≤ L := by
    by_cases hx : p.2 ∈ tsupport V
    · exact (hA ⟨p, ⟨hp.1, hx⟩, rfl⟩).trans (le_max_right _ _)
    · rw [show F p = 0 from moserVelocity_zero hx, norm_zero]
      exact L.coe_nonneg
  have hderiv (p : ℝ × Position) (hp : p ∈ S) : ‖fderiv ℝ F p‖ ≤ K := by
    by_cases hx : p.2 ∈ tsupport V
    · exact (hB ⟨p, ⟨hp.1, hx⟩, rfl⟩).trans (le_max_right _ _)
    · have hn : p ∉ tsupport F := fun h => hx ((moserVelocity_joint_tsupport_subset rho V h).2)
      rw [fderiv_of_notMem_tsupport ℝ hn, norm_zero]
      exact K.coe_nonneg
  have hLip : LipschitzOnWith K F S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun p hp => (hreg.contDiffAt (hopen.mem_nhds (hdom hp))).differentiableAt (by norm_num))
      (fun p hp => by exact_mod_cast hderiv p hp)
      ((convex_Icc (0 : ℝ) 1).prod convex_univ)
  refine ⟨L, K, fun t ht x => hnorm (t, x) ⟨ht, Set.mem_univ _⟩, ?_, ?_⟩
  · intro t ht
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [F, dist_prod_same_left] using
      hLip.dist_le_mul (t, x) (show (t, x) ∈ S from ⟨ht, Set.mem_univ _⟩)
        (t, y) (show (t, y) ∈ S from ⟨ht, Set.mem_univ _⟩)
  · intro x
    exact (hreg.continuousOn.mono hdom).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, Set.mem_univ _⟩)

end ContinuumCoulomb

end

end OAI
