import OAI.MeasureTheory.Falconer.Estimates.PolicyLowBand
import OAI.MeasureTheory.Falconer.Geometry.MaskedGeometry

namespace OAI

/-! # The positive prefix lowpass inequality with the actual old masks -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem uniform_policy_prefix_lowpass (d : ℕ) (hd : 1 ≤ d)
    {σ : ℝ} (hσ : 0 < σ) {J : ℕ} (hJ : 0 < J) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (w₀ : Sphere d) (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
        (q i a t : ℕ), 0 < q → t ≤ N → a ≤ t →
      ∀ (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)),
      (∀ b ∈ PlanarFalconer.policyDescriptorList A N q a t, ∀ w : Sphere d,
        ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (X Y : List (Fin d → Bool)), X.length = a → Y.length = a →
      125*((d:ℝ)+1)*(Q.descendant X).side ≤
        ‖(Q.descendant X).center-(Q.descendant Y).center‖ →
      ‖(Q.descendant X).center-(Q.descendant Y).center‖ ≤
        2000*((d:ℝ)+1)*(Q.descendant X).side →
      (positiveCollisionCount w₀ Q ρ (fun u => m (u/N)) A N σ J i q a t X Y).toReal ≤
        (C/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t),
          ‖charFun (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
            (Q.descendant X) (Q.descendant Y)) r‖^2 := by
  obtain ⟨C₀,hC₀,hband⟩ := dyadic_collision_fourier_of_domination d
  obtain ⟨N₀,h₀⟩ := uniform_maskedCellDistance_dominates hσ hJ hd
  let U : ℝ := 2002*((d:ℝ)+1)
  let c : ℝ := U^(-(((d:ℝ)-1)/2))
  have hU : 0 < U := by dsimp [U]; positivity
  have hc : 0 < c := Real.rpow_pos_of_pos hU _
  refine ⟨C₀/c^2,by positivity,N₀,?_⟩
  intro N hN w₀ Q hQ ρ _ m A q i a t hq ht hat S hcover X Y hX hY hlo hhi
  let B := PlanarFalconer.policyDescriptorList A N q a t
  let π := (ρ.restrict (Q.descendant X).carrier).prod (ρ.restrict (Q.descendant Y).carrier)
  have hgeo : ∀ᵐ z ∂π, 100*((d:ℝ)+1) ≤ dist z.1 z.2*(2:ℝ)^a ∧
      dist z.1 z.2*(2:ℝ)^a ≤ U := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (Q.descendant X).measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (Q.descendant Y).measurable)] with z hx hy
    exact separated_cell_distance_bounds Q hQ a X Y hX hY hlo hhi hx hy
  have hpositive : ∀ᵐ z ∂π, 0 < dist z.1 z.2*(2:ℝ)^a ∧
      dist z.1 z.2*(2:ℝ)^a ≤ U := hgeo.mono fun _ hz =>
    ⟨(by positivity : (0:ℝ) < 100*((d:ℝ)+1)).trans_le hz.1,hz.2⟩
  have hsep : ∀ᵐ z ∂π, 1 ≤ dist z.1 z.2*(2:ℝ)^a := hgeo.mono fun _ hz =>
    (by nlinarith [Nat.cast_nonneg (α := ℝ) d] : (1:ℝ) ≤ 100*((d:ℝ)+1)).trans hz.1
  have hf := maskedCellDistance_finite w₀ Q ρ m N σ J i a B S hcover hd
    (by norm_num : (0:ℝ) < 1) (Q.descendant X) (Q.descendant Y) hsep
  let := hf
  have hdom := h₀ N hN Q hQ ρ m B (fun b hb => policy_descriptor_valid A hq ht hb)
    S hcover i a w₀ X Y U hU hpositive
  have hbound := hband
    (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
      (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J i B))
    (maskedCellDistance w₀ Q ρ m N σ J i a B S (Q.descendant X) (Q.descendant Y))
    ((profileModelMass m N a)⁻¹^2*c) (by positivity) hdom a t hat
  have he : ((profileModelMass m N a)⁻¹^2*c)^2 = c^2*((2:ℝ)^N)^(4*m ((a:ℝ)/N)) := by
    rw [mul_pow,← pow_mul,show 2*2 = 4 from rfl,profileModelMass_inverse_four]
    ring
  rw [he] at hbound
  have hn : c^2*(positiveCollisionCount w₀ Q ρ (fun u => m (u/N)) A N σ J i q a t X Y).toReal ≤
      (C₀/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t),
        ‖charFun (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
          (Q.descendant X) (Q.descendant Y)) r‖^2 := by
    simp only [positiveCollisionCount,policyTestPairs,policyMaskedDistance,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal (show 0 ≤ (2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m ((a:ℝ)/N)) by positivity)]
    simpa only [B,measureReal_def,mul_assoc,mul_left_comm,mul_comm] using hbound
  calc
    _ ≤ ((C₀/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t),
        ‖charFun (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
          (Q.descendant X) (Q.descendant Y)) r‖^2)/c^2 :=
      (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by simpa only [mul_comm] using hn)
    _ = _ := by ring

end Falconer

end OAI
