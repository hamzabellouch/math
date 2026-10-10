import OAI.MeasureTheory.Falconer.Estimates.KernelL1Comparison
import OAI.MeasureTheory.Falconer.Estimates.ComparableBands

namespace OAI

/-! # Normalized comparable-band bound for the actual stationary kernel -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem exists_jetState_far_band (m K L M : ℕ) (hML : 2*M ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (F : Finset PolicyDescriptor) (w₀ : Sphere (m+3))
        (Q : DyadicCube (m+3)), Q.side = 1 →
      ∀ (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ) (N : ℕ) (s lam : ℝ),
      Regularization.RegularizedProfileData Q ρ N s lam profile → 0 < N →
      ∀ (A : ℕ → ℝ) (σ : ℝ) (J i q a b t : ℕ), a ≤ b → b ≤ N → b ≤ t →
      ∀ (S : PolicyDescriptor → Finset (Sphere (m+3))),
      PlanarFalconer.policyDescriptorList A N q b t ⊆ F →
      (∀ c ∈ F, ∀ w ∈ S c, ∀ z ∈ S c, w ≠ z → descriptorMaskRadius N σ c/2 ≤ dist w z) →
      ∀ Dq Dmask E Z : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < Z →
      1 ≤ 2*(E+Dq) → (∀ c ∈ F, (descriptorMaskRadius N σ c)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E → (2*(E+Dq))^2 ≤ (2:ℝ)^((t:ℝ)-b) →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq)
        (X Y : List (Fin (m+3) → Bool)), X.length = a → Y.length = a →
      ∀ U : Set ((Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))),
      MeasurableSet U → U ⊆ comparableLengthBand (m+3) b →
      ENNReal.ofReal ((2:ℝ)^(((m+3:ℕ):ℝ)*((t:ℝ)-a))*(profileModelMass profile N a)⁻¹^4)*
        (∫⁻ z in U, ENNReal.ofReal ‖jetStateStationaryKernel f g w₀ Q ρ
          (fun s => profile (s/N)) N σ J i S Z M ((2:ℝ)^t) Ψ z‖
          ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ) ≤
      ENNReal.ofReal (C*(B^K*Z⁻¹)^4*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
        ((2:ℝ)^N)^(-2*((profile ((b:ℝ)/N)-((m+3:ℕ):ℝ)/2*(b:ℝ)/N)-
          (profile ((a:ℝ)/N)-((m+3:ℕ):ℝ)/2*(a:ℝ)/N))+4*(((m+3:ℕ):ℝ)+1)*lam)) *
        (PlanarFalconer.binKernelConstant *
          farCollisionMaximum w₀ Q ρ (fun s => profile (s/N)) A N σ J (i+1) q b t X Y (b-a)) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := exists_jetState_far_collision_integral m K L M hML hΨ hs
  refine ⟨B,C,hB,hC,?_⟩
  intro F w₀ Q hQ ρ profile N s lam hreg hN A σ J i q a b t hab hbN hbt
    S hHF hsep Dq Dmask E Z hDq hDm hZ hD hscale hE hDfreq f g X Y hX hY U hU hband
  let := hreg.probability
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hg := hbound F w₀ Q ρ hQpos (fun s => profile (s/N)) A N σ J i q b t S hHF hsep
    Dq Dmask E Z hDq hDm hZ hD hscale hE f g X Y (b-a) U hU
    (fun z hz => comparableLengthBand_descendants Q hQ X Y hX hY hab (hband hz))
    (by
      intro z hz
      obtain ⟨h₁,h₂⟩ := comparableLengthBand_dist_lower (hband hz)
      have hbase : (2:ℝ)^t*(2:ℝ)^(-(b:ℝ)) = (2:ℝ)^((t:ℝ)-b) := by
        rw [← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
      refine ⟨h₁,h₂,?_,?_⟩
      · exact hDfreq.trans (by rw [← hbase]; exact mul_le_mul_of_nonneg_left h₁ (by positivity))
      · exact hDfreq.trans (by rw [← hbase]; exact mul_le_mul_of_nonneg_left h₂ (by positivity)))
  have hnorm : (2:ℝ)^(t-b)*((2:ℝ)^N)^(4*profile ((b:ℝ)/N)) =
      (2:ℝ)^((t:ℝ)-b)*(profileModelMass profile N b)⁻¹^4 := profile_collision_scale profile N hbt
  have hd : ((m+3:ℕ):ℝ)-1 = ((m+2:ℕ):ℝ) := by push_cast; ring
  have hresult := profile_far_collision_bound hN (m+3) profile a b t lam
    (C := C*(B^K*Z⁻¹)^4) (mul_nonneg hC (pow_nonneg (mul_nonneg
      (pow_nonneg (zero_le_one.trans hB) _) (inv_nonneg.mpr hZ.le)) _))
    (Cdim := ((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)) (Nat.cast_nonneg _)
    (farCellPartners_regular_card hreg hQpos hab hbN X Y hX hY)
    (I := ∫⁻ z in U, ENNReal.ofReal ‖jetStateStationaryKernel f g w₀ Q ρ
      (fun s => profile (s/N)) N σ J i S Z M ((2:ℝ)^t) Ψ z‖
      ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ)
    (X := PlanarFalconer.binKernelConstant *
      farCollisionMaximum w₀ Q ρ (fun s => profile (s/N)) A N σ J (i+1) q b t X Y (b-a))
    (by simpa only [hnorm,hd,mul_assoc] using hg)
  exact hresult

end Falconer

end OAI
