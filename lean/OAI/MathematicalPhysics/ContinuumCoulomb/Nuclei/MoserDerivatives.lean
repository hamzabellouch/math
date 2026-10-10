import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserBounds

namespace OAI

/-! Uniform finite bounds for all joint field derivatives through order four.
These bounds control the explicit velocity in the differentiated flow equations. -/

noncomputable section
open scoped Topology NNReal BigOperators
namespace ContinuumCoulomb

theorem moserVelocity_iterated_derivative_bound {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    (r : ℕ) (hr : r ≤ 4) :
    ∃ B : ℝ≥0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ r (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) (t, x)‖ ≤ B := by
  let F : ℝ × Position → Position := fun p => moserVelocity rho V p.1 p.2
  let T : Set (ℝ × Position) := Set.Icc (0 : ℝ) 1 ×ˢ tsupport V
  have hT : IsCompact T := isCompact_Icc.prod hc
  have hopen := moserDomain_isOpen rho V hV
  have hreg : ContDiffOn ℝ 4 F (moserDomain rho V) := moserVelocity_joint_C4 rho V hV
  have hcont : ContinuousOn (iteratedFDeriv ℝ r F) (moserDomain rho V) := by
    apply (hreg.continuousOn_iteratedFDerivWithin (by exact_mod_cast hr) hopen.uniqueDiffOn).congr
    intro p hp
    exact (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := F) r hopen hp).symm
  have hTD : T ⊆ moserDomain rho V := fun p hp =>
    moserDomain_contains_time_slab hrho V hbound ⟨hp.1, Set.mem_univ _⟩
  obtain ⟨A, hA⟩ := hT.bddAbove_image ((hcont.mono hTD).norm)
  refine ⟨⟨max 0 A, le_max_left _ _⟩, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport V
  · exact (hA ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_right _ _)
  · have hn : (t, x) ∉ tsupport (iteratedFDeriv ℝ r F) := fun hp =>
      hx ((moserVelocity_joint_tsupport_subset rho V (tsupport_iteratedFDeriv_subset r hp)).2)
    rw [image_eq_zero_of_notMem_tsupport hn, norm_zero]
    exact le_max_left _ _

/-- A common finite bound works for all five derivative orders. -/
theorem moserVelocity_four_derivative_bounds {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ B : ℝ≥0, ∀ r ≤ 4, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ r (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) (t, x)‖ ≤ B := by
  have h (r : Fin 5) := moserVelocity_iterated_derivative_bound hrho V hV hc hbound
    r (by omega)
  choose B hB using h
  refine ⟨∑ r : Fin 5, B r, fun r hr t ht x => ?_⟩
  let i : Fin 5 := ⟨r, by omega⟩
  exact (hB i t ht x).trans (by
    exact_mod_cast (Finset.single_le_sum (fun j _ => (show (0 : ℝ≥0) ≤ B j from zero_le))
      (Finset.mem_univ i)))

end ContinuumCoulomb

end

end OAI
