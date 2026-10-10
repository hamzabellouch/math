import OAI.MeasureTheory.Falconer.Shells.RegularRestrictedShell
import OAI.MeasureTheory.Falconer.Estimates.RegularRoot
import OAI.MeasureTheory.Falconer.Estimates.OuterParameters

namespace OAI

/-! # A uniform shell estimate for the original regularized class laws

The parameters are chosen before the scale and the classes. A single entry
index for each class pair works for every measurable product restriction.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff

 theorem exists_regular_class_shell
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {χ : ℝ} (hχ : 0 < χ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) :
    ∃ lam σ κ β : ℝ, 0 < lam ∧ 0 < σ ∧ lam ≤ σ ∧ 0 < κ ∧ 0 < β ∧
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q₁ Q₂ : DyadicCube (m+3)), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ),
      Regularization.RegularizedProfileData Q₁ ρ₁ N ((m+3:ℕ)/2+χ) lam profile₁ →
      Regularization.RegularizedProfileData Q₂ ρ₂ N ((m+3:ℕ)/2+χ) lam profile₂ →
      ρ₁ Q₁.carrierᶜ = 0 → ρ₂ Q₂.carrierᶜ = 0 →
      (∀ᵐ z ∂ρ₁.prod ρ₂, δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂ρ₁.prod ρ₂,
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      ∃ c : ℕ, 4*c ≤ N ∧ c+100*PlanarFalconer.sourcePolicyBlock N κ < N ∧
        β*N/(2*(m+3:ℕ)) ≤ (c:ℝ) ∧
      ∀ A₁ A₂ : Set (Space (m+3)), MeasurableSet A₁ → MeasurableSet A₂ →
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)),
        ‖charFun (endpointWeightedDistance (ρ₁.restrict A₁) (ρ₂.restrict A₂) 1 1 1
          (descriptorAmbientProduct Q₁ ρ₁ (fun u => profile₁ (u/N)) N σ
            (PlanarFalconer.sourceSmoothingLevels σ κ) 0 (regularOuterList (d := m+3) profile₁ N κ c)
            (descriptorNets (m+3) N σ))
          (descriptorAmbientProduct Q₂ ρ₂ (fun u => profile₂ (u/N)) N σ
            (PlanarFalconer.sourceSmoothingLevels σ κ) 0 (regularOuterList (d := m+3) profile₂ N κ c)
            (descriptorNets (m+3) N σ))) r‖^2) ≤ ((2:ℝ)^N)^(-β/16) := by
  obtain ⟨β,κ,σ,lam,η,T,hβ,hκ,hκ1,hκsmall,hσ,hgap,hlam,hlamσ,hη,hη1,hloss,hT,hTβ,hentry,hdecay⟩ :=
    exists_outer_shell_parameters m hχ
  obtain ⟨Z,N₀,hZ,hN₀,hmain⟩ := exists_regular_outer_restricted_shell hgnomonic hquadratic m
    hlam.le hσ hκ hκ1 hgap hη hη1 hloss hT hχ hβ hκsmall hTβ hentry hdecay
    φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp δ W hδ hW
  refine ⟨lam,σ,κ,β,hlam,hσ,hlamσ,hκ,hβ,N₀,hN₀,?_⟩
  intro N hN Q₁ Q₂ hQ₁ hQ₂ ρ₁ ρ₂ profile₁ profile₂ hreg₁ hreg₂ hcarry₁ hcarry₂ hsep hnear
  have hNp : 0 < N := hN₀.trans_le hN
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  let P := regularRoot Q₁ hQ₁ ρ₁ profile₁ (σ := σ) hreg₁ hNp hκ hZp
  let Q := regularRoot Q₂ hQ₂ ρ₂ profile₂ (σ := σ) hreg₂ hNp hκ hZp
  have hρ₁ : ρ₁.restrict Q₁.carrier = ρ₁ :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hcarry₁)
  have hρ₂ : ρ₂.restrict Q₂.carrier = ρ₂ :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hcarry₂)
  have hp : P.ρ.restrict (P.Q.descendant P.X).carrier = ρ₁ := by
    simpa only [P,regularRoot,DyadicCube.descendant_nil] using hρ₁
  have hq : Q.ρ.restrict (Q.Q.descendant Q.X).carrier = ρ₂ := by
    simpa only [Q,regularRoot,DyadicCube.descendant_nil] using hρ₂
  obtain ⟨c,hc,hw,hclo,hbound⟩ := hmain P Q rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl hN rfl rfl rfl rfl
    (descriptorNets_cover (m+3) N σ) (descriptorNets_cover (m+3) N σ)
    (descriptorNets_separated (m+3) N σ) (descriptorNets_separated (m+3) N σ)
    (by rwa [hp,hq]) (by rwa [hp,hq])
  refine ⟨c,hc,hw,hclo,?_⟩
  intro A₁ A₂ hA₁ hA₂
  have hb := hbound A₁ A₂ hA₁ hA₂
  simpa only [PolicyJetData.outerRestrictedDistance,hp,hq,P,Q,regularRoot,
    PolicyJetData.outerList,PolicyJetData.list,regularOuterList,profileModelMass,
    DyadicCube.descendant_nil,hρ₁,hρ₂,
    Nat.cast_zero,zero_div,hreg₁.zero,hreg₂.zero,neg_zero,Real.rpow_zero] using hb

end Falconer

end OAI
