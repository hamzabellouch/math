import OAI.MeasureTheory.Falconer.Shells.RootShellMain
import OAI.MeasureTheory.Falconer.Shells.SmoothShellDomination
import OAI.MeasureTheory.Falconer.Recursion.ParentHFBridge

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace RootShellData

noncomputable def inversePhasedHF (d : RootShellData) (v : ℝ) (Ψ : ℝ → ℝ)
    (k : RootMaskIndex → ℕ) (ξ : Plane) : ℝ≥0∞ :=
  sourceParentHF (0:ℝ) v Ψ d.U d.V
    d.left.ρ d.right.ρ 1 1
    (spatialPhasedSymbol 1 ξ (d.endpointLeft k))
    (spatialPhasedSymbol 1 ξ (d.endpointRight k))

theorem inversePhasedHF_finite_eq (d : RootShellData) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (j : ℕ) {b : ℂ × (RootMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (d.indices))
    (v : ℝ) (Ψ : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hΨW : ∀ x, Ψ x ≤ W) (hs : ∀ x, 4 < x → Ψ x = 0) (ξ : Plane) :
    d.inversePhasedHF v Ψ b.2 ξ ≠ ⊤ ∧
      (d.inversePhasedHF v Ψ b.2 ξ).toReal =
        sourceRadialSquareEnergy (0:ℝ) v Ψ (d.inversePhasedForm b.2 ξ) := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  apply sourceParentHF_finite_eq _ _ _ _ _ d.left.ρ d.right.ρ
    (show (0:ℝ) < 1 by norm_num)
    (show (0:ℝ) < 1 by norm_num) _ _
    (spatialPhasedSymbol_measurable _ _ _ (d.endpointLeft_measurable b.2))
    (spatialPhasedSymbol_measurable _ _ _ (d.endpointRight_measurable b.2)) hC hC hW
    _ _ hΨW hs
  · intro x dir
    rw [spatialPhasedSymbol_norm]
    exact d.endpointLeft_norm hd j hb x dir
  · intro x dir
    rw [spatialPhasedSymbol_norm]
    exact d.endpointRight_norm he j hb x dir

theorem mainF_parent_energy (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (hsig : 0 ≤ d.sig)
    (hL₁ : ∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2)
    (hL₂ : ∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2)
    (hcarry₁ : ∀ᵐ x ∂d.left.ρ, x ∈ d.U.carrier) (hcarry₂ : ∀ᵐ y ∂d.right.ρ, y ∈ d.V.carrier)
    (hsep : ∀ x ∈ d.U.carrier, ∀ y ∈ d.V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) (n : ℕ)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ x, Ψ x ≤ W)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∀ j ∈ Finset.range (n+1), ∀ b ∈ inverseLeibnizTerms j d.indices, ∀ ξ,
      (d.inversePhasedHF d.N Ψ b.2 ξ).toReal ≤ H) :
    (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖d.mainF n r‖^2) ≤
      2*(∑ j ∈ Finset.range (n+1), d.cost δ L hδ hL j)^2*H := by
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hE := d.mainF_shell δ L hδ hL hd he hsig hL₁ hL₂ hcarry₁ hcarry₂ hsep n
    (B := ((2:ℝ)^(d.N:ℝ)/(2:ℝ)^(2*(d.N:ℝ)))*H) (by positivity) (by
      intro j hj b hb ξ
      have hdata := d.inversePhasedForm_data hd he j hb
      have hm : Measurable (d.inversePhasedForm b.2 ξ) :=
        hdata.1.comp (f := fun r : ℝ => (ξ,r)) (measurable_const.prodMk measurable_id)
      have hrad : sourceRadialSquareEnergy 0 d.N Ψ (d.inversePhasedForm b.2 ξ) ≤ H := by
        rw [← (d.inversePhasedHF_finite_eq hd he j hb d.N Ψ hW hΨW hsupport ξ).2]
        exact hH j hj b hb ξ
      simpa only [sub_zero] using dyadic_shell_le_radial_energy 0 d.N Ψ hΨ hpos hs hW hΨW hone _ hm
        (d.inversePhasedBound_nonneg j) (fun r => hdata.2 (ξ,r)) hrad)
  apply hE.trans_eq
  let S := ∑ j ∈ Finset.range (n+1), d.cost δ L hδ hL j
  change 2*(2:ℝ)^(d.N:ℝ)*S^2*(((2:ℝ)^(d.N:ℝ)/(2:ℝ)^(2*(d.N:ℝ)))*H) = 2*S^2*H
  have hp : (2:ℝ)^(d.N:ℝ)*(2:ℝ)^(d.N:ℝ) = (2:ℝ)^(2*(d.N:ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  calc
    _ = 2*S^2*H*((2:ℝ)^(d.N:ℝ)*(2:ℝ)^(d.N:ℝ)/(2:ℝ)^(2*(d.N:ℝ))) := by ring
    _ = _ := by rw [hp,div_self (by positivity),mul_one]

end RootShellData

end PlanarFalconer

end OAI
