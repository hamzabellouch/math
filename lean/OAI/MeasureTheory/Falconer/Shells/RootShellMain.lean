import OAI.MeasureTheory.Falconer.Shells.RootShellOrder
import OAI.MeasureTheory.Falconer.Shells.HighShellRadialBounds
import OAI.MeasureTheory.Falconer.Estimates.FiniteSquareIntegrable

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace RootShellData

theorem mainF_shell (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (hsig : 0 ≤ d.sig)
    (hL₁ : ∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2)
    (hL₂ : ∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2)
    (hcarry₁ : ∀ᵐ x ∂d.left.ρ, x ∈ d.U.carrier) (hcarry₂ : ∀ᵐ y ∂d.right.ρ, y ∈ d.V.carrier)
    (hsep : ∀ x ∈ d.U.carrier, ∀ y ∈ d.V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) (n : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (d.indices), ∀ ξ,
      (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖d.inversePhasedForm b.2 ξ r‖^2) ≤ B) :
    (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖d.mainF n r‖^2) ≤
      2*(2:ℝ)^((d.N:ℝ)) *
        (∑ j ∈ Finset.range (n+1), d.cost δ L hδ hL j)^2*B := by
  let μ := volume.restrict (Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)))
  let u := fun j (r : ℝ) => ((((r/(2:ℝ)^(d.N:ℝ))⁻¹)^j:ℝ):ℂ)
  let F := fun j r => u j r*d.inverseOrderForm δ L hδ hL j r
  let w := fun j => d.cost δ L hδ hL j
  have hu (j : ℕ) : Measurable (u j) := by dsimp [u]; fun_prop
  have huw (j : ℕ) : ∀ᵐ r ∂μ, ‖u j r‖ ≤ (2:ℝ)^j := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact high_shell_radial_inverse hr.1 j
  have hwn (j : ℕ) : 0 ≤ w j := by
    apply mul_nonneg (spatialFourierCost_nonneg ..)
    apply mul_nonneg _ (by positivity)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    positivity
  have hm (j : ℕ) : Measurable (F j) := (hu j).mul (d.inverseOrderForm_data δ L hδ hL hd he j).1
  have hi (j : ℕ) : Integrable (fun r => ‖F j r‖^2) μ := by
    obtain ⟨hm,C,hC,hCb⟩ := d.inverseOrderForm_data δ L hδ hL hd he j
    exact (shell_multiplier_square μ (u j) _ (hu j) hm
      (integrable_norm_square_bounded μ _ hm hC (Eventually.of_forall hCb))
      (by positivity) (huw j)).1
  have hE (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∫ r, ‖F j r‖^2 ∂μ) ≤ (w j)^2*B := by
    obtain ⟨hm,C,hC,hCb⟩ := d.inverseOrderForm_data δ L hδ hL hd he j
    have hmul := (shell_multiplier_square μ (u j) _ (hu j) hm
      (integrable_norm_square_bounded μ _ hm hC (Eventually.of_forall hCb))
      (by positivity) (huw j)).2
    apply hmul.trans
    apply (mul_le_mul_of_nonneg_left
      (d.inverseOrderForm_shell δ L hδ hL hd he hsig hL₁ hL₂ j μ hB0 (hB j hj))
      (sq_nonneg ((2:ℝ)^j))).trans_eq
    dsimp [w,cost,rootSpatialLeibnizCost,indices]
    ring
  let G := fun r => ∑ j ∈ Finset.range (n+1), F j r
  have hGm : Measurable G := Finset.measurable_sum _ (fun j _ => hm j)
  have hGi : Integrable (fun r => ‖G r‖^2) μ :=
    finite_sum_square_integrable _ μ F (fun j _ => hm j) (fun j _ => hi j)
  have hGE := finite_weighted_shell_square (Finset.range (n+1)) μ F w
    (fun j _ => hwn j) (fun j _ => hi j) (fun j _ => (hm j).aestronglyMeasurable) hE
  let p := fun r : ℝ => (((r)^(1/2:ℝ):ℝ):ℂ)
  have hpm : Measurable p := by dsimp [p]; fun_prop
  have hp : ∀ᵐ r ∂μ, ‖p r‖ ≤ Real.sqrt (2*(2:ℝ)^((d.N:ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simpa only [sub_zero,neg_zero,Real.rpow_zero,mul_one] using (high_shell_radial_sqrt (a := 0) hr)
  have hE' := (shell_multiplier_square μ p G hpm hGm hGi (Real.sqrt_nonneg _) hp).2
  rw [Real.sq_sqrt (by positivity)] at hE'
  have he (r : ℝ) : d.mainF n r = p r*G r :=
    by
      simpa only [p,G,F,u,mainF,indices,coefficient,endpointLeft,endpointRight,inverseOrderForm,
        inverseSpatialMixture,inversePhasedForm] using
        rootNormalizedF_finite_separation δ L hδ hL d.left d.right d.N d.sig hd he d.U d.V
          hcarry₁ hcarry₂ hsep n r
  simp_rw [he]
  exact hE'.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hGE
      (show 0 ≤ 2*(2:ℝ)^((d.N:ℝ)) by positivity))

end RootShellData

end PlanarFalconer

end OAI
