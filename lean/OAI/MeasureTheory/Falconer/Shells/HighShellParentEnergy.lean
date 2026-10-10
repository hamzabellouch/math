import OAI.MeasureTheory.Falconer.Shells.HighShellMainEnergy
import OAI.MeasureTheory.Falconer.Shells.SmoothShellDomination
import OAI.MeasureTheory.Falconer.Recursion.ParentHFBridge

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

noncomputable def inversePhasedHF (d : PositiveDistanceData) (v : ℝ) (Ψ : ℝ → ℝ)
    (k : PairMaskIndex → ℕ) (ξ : Plane) : ℝ≥0∞ :=
  sourceParentHF d.a v Ψ (d.Q.descendant d.X) (d.Q.descendant d.Y)
    d.ρ d.ρ d.levelMass d.levelMass
    (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol k 0))
    (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol k 1))

theorem inversePhasedHF_finite_eq (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (j : ℕ) {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList))
    (v : ℝ) (Ψ : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hΨW : ∀ x, Ψ x ≤ W) (hs : ∀ x, 4 < x → Ψ x = 0) (ξ : Plane) :
    d.inversePhasedHF v Ψ b.2 ξ ≠ ⊤ ∧
      (d.inversePhasedHF v Ψ b.2 ξ).toReal =
        sourceRadialSquareEnergy d.a v Ψ (d.inversePhasedForm b.2 ξ) := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  apply sourceParentHF_finite_eq _ _ _ _ _ d.ρ d.ρ
    (show 0 < d.levelMass by unfold levelMass; positivity)
    (show 0 < d.levelMass by unfold levelMass; positivity) _ _
    (spatialPhasedSymbol_measurable _ _ _ (d.inverseEndpointSymbol_measurable b.2 0))
    (spatialPhasedSymbol_measurable _ _ _ (d.inverseEndpointSymbol_measurable b.2 1)) hC hC hW
    _ _ hΨW hs
  · intro x dir
    rw [spatialPhasedSymbol_norm]
    exact d.inverseEndpointSymbol_norm hQ j hb 0 x dir
  · intro x dir
    rw [spatialPhasedSymbol_norm]
    exact d.inverseEndpointSymbol_norm hQ j hb 1 x dir

theorem normalizedHighShellF_parent_energy (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hsep : d.StronglySeparated) (hsig : 0 ≤ d.sig)
    (hq : 0 < d.q) (hqs : d.sig*d.N ≤ (d.q:ℝ)) (hw : d.a+100*d.q < d.t)
    {v : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (n : ℕ)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ x, Ψ x ≤ W)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
        (d.inversePhasedHF v Ψ b.2 ξ).toReal ≤ H) :
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖d.normalizedHighShellF n v r‖^2) ≤
      2*(∑ j ∈ Finset.range (n+1), spatialLeibnizCost 96 2004 (by norm_num) (by norm_num) j
        (fun k => d.mass k-(k:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)^2*H := by
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hE := d.normalizedHighShellF_shell hQ hsep hsig hq hqs hw hv n
    (B := ((2:ℝ)^v/(2:ℝ)^(2*(v-d.a)))*H) (by positivity) (by
      intro j hj b hb ξ
      have hd := d.inversePhasedForm_data hQ j hb
      have hm : Measurable (d.inversePhasedForm b.2 ξ) :=
        hd.1.comp (f := fun r : ℝ => (ξ,r)) (measurable_const.prodMk measurable_id)
      apply dyadic_shell_le_radial_energy d.a v Ψ hΨ hpos hs hW hΨW hone _ hm
        (d.inversePhasedBound_nonneg j) (fun r => hd.2 (ξ,r))
      rw [← (d.inversePhasedHF_finite_eq hQ j hb v Ψ hW hΨW hsupport ξ).2]
      exact hH j hj b hb ξ)
  apply (mul_le_mul_of_nonneg_left hE (show 0 ≤ (2:ℝ)^(-(d.a:ℝ)) by positivity)).trans_eq
  let S := ∑ j ∈ Finset.range (n+1), spatialLeibnizCost 96 2004 (by norm_num) (by norm_num) j
    (fun k => d.mass k-(k:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
  change (2:ℝ)^(-(d.a:ℝ))*(2*(2:ℝ)^(v-d.a)*S^2*
    (((2:ℝ)^v/(2:ℝ)^(2*(v-d.a)))*H)) = 2*S^2*H
  calc
    _ = 2*S^2*H*((2:ℝ)^(-(d.a:ℝ))*(2:ℝ)^v*(2:ℝ)^(v-d.a)/(2:ℝ)^(2*(v-d.a))) := by ring
    _ = _ := by rw [high_shell_energy_prefactor,div_self (by positivity),mul_one]

end PositiveDistanceData

end PlanarFalconer

end OAI
