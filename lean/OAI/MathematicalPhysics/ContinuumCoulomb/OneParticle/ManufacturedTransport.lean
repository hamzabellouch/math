import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedUniformFlow
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserUniformInverse

namespace OAI

/-! The actual manufactured fields admit transport maps with common
C4 and inverse Lipschitz constants, chosen before the instance. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb

theorem manufactured_transport_family_with_charge (hpublished : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧
      ∀ (freq scale S : ℝ), 0 < scale → 1 ≤ S →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
      (∀ i, localizedCounterterm freq u i ≤ scale) →
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ∃ G : Position → ℝ → Position,
        IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
        Function.Bijective (fun x => G x 1) ∧
        LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
        (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
        ContDiff ℝ 4 (fun x => G x 1) ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x,
          ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) := by
  obtain ⟨rho,hrho,D,hD,hfamily⟩ := manufactured_uniform_density_and_flow hpublished
  have hrhop : (0:ℝ) < rho := by exact_mod_cast hrho
  obtain ⟨K,hK,hKb⟩ := moserFlow_family_inverse_bound hrhop
    manufacturedFieldDerivativeConstant_positive.le
  refine ⟨rho,hrho,⟨D,hD.le⟩,K,by exact_mod_cast hD,hK,?_⟩
  intro freq scale S hscale hS m u hsep hcounter
  let V := manufacturedWellField freq scale S u
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 freq scale S u).of_le (by norm_num)
  obtain ⟨hc,hderiv⟩ := hfamily freq scale S hscale hS m u hsep hcounter
  refine ⟨hc,?_⟩
  obtain ⟨G,C,Cinv,D',hD',hflow,hbij,hLip,hAnti,hfix,hreg,hderiv'⟩ :=
    moser_C4_bilipschitz_flow_exists hpublished hrhop V hV
      (manufacturedWellField_compact freq scale (lt_of_lt_of_le zero_lt_one hS) u) hc
  have h1 : (1:ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num,le_rfl⟩
  have hDb (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) (x : Position) :
      ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ D := hderiv G hflow k hk hk' 1 h1 x
  have hLipD : LipschitzWith (⟨D,hD.le⟩ : ℝ≥0) (fun x => G x 1) :=
    lipschitzWith_of_nnnorm_fderiv_le (hreg.differentiable (by norm_num)) (fun x => by
      have h := hDb 1 (by norm_num) (by norm_num) x
      rw [norm_iteratedFDeriv_one] at h
      exact_mod_cast h)
  have hAntiK := hKb V hV
    (fun k hk x => manufacturedWellField_derivative_bound freq hscale hS u hsep hcounter hk x)
    hc G hflow
  exact ⟨G,hflow,hbij,hLipD,hAntiK,hfix,hreg,hDb⟩

/-- The original flow interface, retaining the same fixed constants. -/
theorem manufactured_transport_family (hpublished : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧
      ∀ (freq scale S : ℝ), 0 < scale → 1 ≤ S →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
      (∀ i, localizedCounterterm freq u i ≤ scale) →
      ∃ G : Position → ℝ → Position,
        IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
        Function.Bijective (fun x => G x 1) ∧
        LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
        (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
        ContDiff ℝ 4 (fun x => G x 1) ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x,
          ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) := by
  obtain ⟨rho,hrho,L,K,hL,hK,hfamily⟩ := manufactured_transport_family_with_charge hpublished
  exact ⟨rho,hrho,L,K,hL,hK,fun freq scale S hs hS m u hsep hc =>
    (hfamily freq scale S hs hS m u hsep hc).2⟩

end ContinuumCoulomb

end

end OAI
