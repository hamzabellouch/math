import OAI.MeasureTheory.Falconer.Estimates.SourceFamily
import OAI.MeasureTheory.Falconer.Shells.RegularizationScalarShell
import OAI.MeasureTheory.Falconer.Estimates.RegularizationVariation
import OAI.MeasureTheory.Falconer.Angular.OriginalCapRemoval
import OAI.MeasureTheory.Falconer.Fourier.AssemblyCutoff
import OAI.MeasureTheory.Falconer.Shells.AssemblyErrorBound
import OAI.MeasureTheory.Falconer.Shells.DecayEndgame

namespace OAI

/-! # Completion for an original separated pair in unit cubes -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open Regularization

theorem unit_pair_positive_distance
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {χ : ℝ} (hχ : 0 < χ) (hsd : (m+3:ℕ)/2+χ ≤ (m+3:ℕ))
    (Q₁ Q₂ : DyadicCube (m+3)) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (μ ν : ProbabilityMeasure (Space (m+3)))
    (hcarry₁ : (μ : Measure (Space (m+3))) Q₁.carrierᶜ = 0)
    (hcarry₂ : (ν : Measure (Space (m+3))) Q₂.carrierᶜ = 0)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hball₁ : ∀ x : Space (m+3), ∀ r > 0,
      (μ : Measure (Space (m+3))) (Metric.ball x r) ≤ ENNReal.ofReal (C₁*r^((m+3:ℕ)/2+χ)))
    (hball₂ : ∀ x : Space (m+3), ∀ r > 0,
      (ν : Measure (Space (m+3))) (Metric.ball x r) ≤ ENNReal.ofReal (C₂*r^((m+3:ℕ)/2+χ)))
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (hsep : ∀ᵐ z ∂(μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))),
      δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W)
    (hnear : ∀ᵐ z : Space (m+3) × Space (m+3)
      ∂(μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))),
      ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8)
    (D : Set ℝ) (hD : MeasurableSet D)
    (hcarried : ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))))
      ((fun z => dist z.1 z.2) ⁻¹' Dᶜ) = 0)
    (hfilters : ∀ ω : ℝ, 0 < ω → ω ≤ 1 →
      ∃ Γ : ℕ → Set (Space (m+3) × Space (m+3)),
        (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
        0 < ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3)))) (⋂ N, Γ N) ∧
        (∀ N, ∀ z ∈ Γ N, z.1 ≠ z.2) ∧
        (∀ N, HasBorelProductPartition (Γ N) ((2:ℝ)^(2*(m+3:ℕ)*ω*(N:ℝ)))) ∧
        CapAvailable μ ν Γ ((m+3:ℕ)/2)) :
    0 < volume D := by
  classical
  obtain ⟨φ,Ψ,hφ,hΨ,hsmooth,hpos,hzero,hone,hΨV,hsupp⟩ := exists_scalar_assembly_cutoff
  obtain ⟨lam,σ,κ,β,hlam,hσ,hlamσ,hκ,hβ,Ns,hNs,hscalar⟩ :=
    exists_regularization_scalar_shell hgnomonic hquadratic m hχ φ Ψ hφ hΨ hsmooth
      hpos hzero hone (by norm_num : (0:ℝ) ≤ 1) hΨV hsupp δ W hδ hW
  have hside₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hside₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  have hs : (0:ℝ) ≤ (m+3:ℕ)/2+χ := by positivity
  obtain ⟨H₁,N₁,_hH₁,hfam₁⟩ := eventual_source_family (by omega) Q₁ hside₁ μ hcarry₁ hs hsd hC₁ hlam hball₁
  obtain ⟨H₂,N₂,_hH₂,hfam₂⟩ := eventual_source_family (by omega) Q₂ hside₂ ν hcarry₂ hs hsd hC₂ hlam hball₂
  let ω : ℝ := min 1 (β/(256*(m+3:ℕ)))
  have hω : 0 < ω := lt_min zero_lt_one (by positivity)
  have hω1 : ω ≤ 1 := min_le_left _ _
  have hθ : 2*(2*(m+3:ℕ)*ω) ≤ β/64 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 256*(m+3:ℕ))).mp (min_le_right 1 (β/(256*(m+3:ℕ))))
    dsimp only [ω]
    nlinarith
  obtain ⟨Γ,hΓ,hmono,hpositive,hne,hparts,hcaps⟩ := hfilters ω hω hω1
  obtain ⟨a,Ccap,ha,hCcap,Ncap,hcap⟩ := original_cap_removal μ ν Γ hcaps hne hσ
  obtain ⟨Nt,htest⟩ := uniform_regularizationPairExceptional_bound (d := m+3) hσ
  obtain ⟨Nv,hvar⟩ := uniform_regularization_variation (d := m+3) hσ hκ (by omega)
  obtain ⟨Np,hpartition⟩ := eventual_partition_shell_decay hβ hθ
  let N₀ := Ns+N₁+N₂+Ncap+Nt+Nv+Np
  let π : Measure (Space (m+3) × Space (m+3)) := (μ : Measure _).prod (ν : Measure _)
  let Cw : ℝ := δ^(-((((m+3:ℕ):ℝ)-1)/2))
  have hCw : 0 < Cw := Real.rpow_pos_of_pos hδ _
  let ρ := π.withDensity (distanceWeight ((((m+3:ℕ):ℝ)-1)/2))
  let : IsFiniteMeasure ρ := finite_withDensity_of_bounded π _ ENNReal.ofReal_lt_top
    (distanceWeight_upper (by omega) hδ (hsep.mono fun _ h => h.1))
  have happ : ∀ N ≥ N₀, ∃ τ : FiniteMeasure ℝ,
      PlanarFalconer.variationDistance
        ⟨filteredPushforward (fun z : Space (m+3) × Space (m+3) => dist z.1 z.2) ρ (Γ N),inferInstance⟩ τ ≤
          ENNReal.ofReal (restorationError Cw Ccap a lam σ (4*H₁+2) (4*H₂+2) N) ∧
      PlanarFalconer.shellEnergy τ N ≤ ((2:ℝ)^N)^(-β/32) := by
    intro N hN
    have hNsN : Ns ≤ N := by dsimp only [N₀] at hN; omega
    have hN₁ : N₁ ≤ N := by dsimp only [N₀] at hN; omega
    have hN₂ : N₂ ≤ N := by dsimp only [N₀] at hN; omega
    have hNcap : Ncap ≤ N := by dsimp only [N₀] at hN; omega
    have hNt : Nt ≤ N := by dsimp only [N₀] at hN; omega
    have hNv : Nv ≤ N := by dsimp only [N₀] at hN; omega
    have hNp : Np ≤ N := by dsimp only [N₀] at hN; omega
    let B₁ := N/H₁
    let B₂ := N/H₂
    let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
    have ht : 0 < t := ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨hNpos,hB₁,hw₁,hl₁,hdiscard₁,p₁,hp₁,he₁,hreg₁⟩ := hfam₁ N hN₁
    obtain ⟨_hNpos,hB₂,hw₂,hl₂,hdiscard₂,p₂,hp₂,he₂,hreg₂⟩ := hfam₂ N hN₂
    have hwidth₁ : (B₁:ℝ) ≤ σ*N := hw₁.trans (mul_le_mul_of_nonneg_right hlamσ (Nat.cast_nonneg N))
    have hwidth₂ : (B₂:ℝ) ≤ σ*N := hw₂.trans (mul_le_mul_of_nonneg_right hlamσ (Nat.cast_nonneg N))
    have hR1 : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hlarge₁ : (2:ℝ)^(N/B₁+2) ≤ ((2:ℝ)^N)^σ := hl₁.trans (Real.rpow_le_rpow_of_exponent_le hR1 hlamσ)
    have hlarge₂ : (2:ℝ)^(N/B₂+2) ≤ ((2:ℝ)^N)^σ := hl₂.trans (Real.rpow_le_rpow_of_exponent_le hR1 hlamσ)
    obtain ⟨c,hc,hsc⟩ := hscalar N hNsN Q₁ Q₂ hQ₁ hQ₂ μ ν B₁ B₂ t t ht ht p₁ p₂ he₁ he₂ hreg₁ hreg₂ hsep hnear
    obtain ⟨Dcap,hDcap,_hDsub,hDmass,hcaplaw⟩ := hcap N hNcap
    let w₀ : Sphere (m+3) := gnomonicChart (0 : Space (m+2))
    obtain ⟨τ,hτ,htv⟩ := hvar N hNv hNpos Q₁ Q₂ hQ₁ hQ₂ μ ν B₁ B₂ t t p₁ p₂ hp₁ hp₂ c hc w₀ (Γ N) Dcap (hΓ N)
      δ hδ (hsep.mono fun _ h => h.1)
    have hbad := htest N hNt Q₁ Q₂ hQ₁ hQ₂ μ ν B₁ B₂ hB₁ hB₂ hwidth₁ hwidth₂ hlarge₁ hlarge₂
      t t ht ht p₁ p₂ hp₁ hp₂ he₁ he₂ w₀ (Γ N \ Dcap) ((hΓ N).diff hDcap)
      (hcaplaw w₀).1 (hcaplaw w₀).2 κ
    refine ⟨τ,?_,?_⟩
    · apply restoration_numeric_bound N (4*H₁+2) (4*H₂+2) hCw.le hCcap.le hDmass hdiscard₁ hdiscard₂
      exact htv.trans (mul_le_mul' le_rfl (add_le_add le_rfl hbad))
    · obtain ⟨k,hk,A,B,hm,hdis,hΓeq⟩ := hparts N
      have hh := hsc k A B hm hdis
      rw [← hΓeq] at hh
      rw [hτ]
      apply hh.trans (hpartition N hNp k ?_)
      simpa only [dyadic_scale_power] using hk
  let τ : ℕ → FiniteMeasure ℝ := fun N => if hN : N₀ ≤ N then (happ N hN).choose else 0
  have herror : Summable (fun N => (PlanarFalconer.variationDistance
      ⟨filteredPushforward (fun z : Space (m+3) × Space (m+3) => dist z.1 z.2) ρ (Γ N),inferInstance⟩ (τ N)).toReal) := by
    apply summable_of_restoration_error hCw.le hCcap.le ha hlam hσ (4*H₁+2) (4*H₂+2) N₀
    intro N hN
    simpa only [τ,dite_eq_left hN] using (happ N hN).choose_spec.1
  have hshell : ∀ N ≥ N₀, PlanarFalconer.shellEnergy (τ N) N ≤ (1:ℝ)*(2:ℝ)^(-(β/32)*(N:ℝ)) := by
    intro N hN
    simpa only [τ,dite_eq_left hN,dyadic_scale_power,neg_div,one_mul] using (happ N hN).choose_spec.2
  have hρcarried : ρ ((fun z : Space (m+3) × Space (m+3) => dist z.1 z.2) ⁻¹' Dᶜ) = 0 :=
    withDensity_absolutelyContinuous _ _ hcarried
  have hlower : ∀ᵐ z ∂π, ENNReal.ofReal (W^(-((((m+3:ℕ):ℝ)-1)/2))) ≤
      distanceWeight ((((m+3:ℕ):ℝ)-1)/2) z := by
    filter_upwards [hsep] with z hz
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_nonpos (hδ.trans_le hz.1) hz.2
    have hd : (1:ℝ) ≤ (m+3:ℕ) := by exact_mod_cast (show 1 ≤ m+3 by omega)
    linarith
  have hρpositive : 0 < ρ (⋂ N, Γ N) := withDensity_positive_of_lower π _
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hW _)) hlower _ (MeasurableSet.iInter hΓ) hpositive
  exact positive_volume_of_same_scale_summable _ (by fun_prop) ρ Γ hΓ hmono D hD hρcarried
    hρpositive τ herror (by positivity : 0 < β/32) zero_lt_one N₀ hshell

end Falconer

end OAI
