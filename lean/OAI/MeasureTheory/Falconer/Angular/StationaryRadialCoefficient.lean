import OAI.MeasureTheory.Falconer.Angular.RadialStationaryProfile
import OAI.MeasureTheory.Falconer.Angular.NormalizedStationaryJet

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def stationaryRadialCoefficient (Ψ : ℝ → ℝ) (j k : ℕ)
    (f g : ℝ → ℂ) (θ φ A B : ℝ) (s : ℝ) : ℂ :=
  (((A^(-1/2:ℝ)*B^(-1/2:ℝ):ℝ):ℂ) *
    (normalizedStationaryJet j f θ A * normalizedStationaryJet k g φ B)) *
      radialStationaryProfile Ψ (-((j:ℝ)+(k:ℝ)+1)) s

 theorem stationaryRadialCoefficient_derivatives {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (j k n : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ {f g : ℝ → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    ∀ {C E D A B : ℝ}, 0 ≤ C → 0 ≤ E → 1 ≤ D → 0 < A → 0 < B →
    D^2 ≤ A → D^2 ≤ B → ∀ θ φ : ℝ,
    (∀ l ≤ 2*j, ‖iteratedDeriv l f θ‖ ≤ C*D^l) →
    (∀ l ≤ 2*k, ‖iteratedDeriv l g φ‖ ≤ E*D^l) →
    ContDiff ℝ ∞ (stationaryRadialCoefficient Ψ j k f g θ φ A B) ∧
    tsupport (stationaryRadialCoefficient Ψ j k f g θ φ A B) ⊆ Icc (1/4:ℝ) 4 ∧
    ∀ l ≤ n, ∀ s, ‖iteratedDeriv l (stationaryRadialCoefficient Ψ j k f g θ φ A B) s‖ ≤
      H*C*E*(A^(-1/2:ℝ)*B^(-1/2:ℝ)) := by
  obtain ⟨P,hP,hp⟩ := radialStationaryProfile_derivatives hΨ hs (-((j:ℝ)+(k:ℝ)+1)) n
  let H := P*(directStationaryExpr j).cost*(directStationaryExpr k).cost
  have hj := (directStationaryExpr j).cost_nonneg
  have hk := (directStationaryExpr k).cost_nonneg
  refine ⟨H,by dsimp [H]; positivity,?_⟩
  intro f g hf hg C E D A B hC hE hD hA hB hDA hDB θ φ hbf hbg
  refine ⟨contDiff_const.mul (radialStationaryProfile_contDiff hΨ hs _),
    tsupport_mul_subset_right.trans (radialStationaryProfile_tsupport hs _),?_⟩
  intro l hl s
  change ‖iteratedDeriv l (fun t =>
    (((A^(-1/2:ℝ)*B^(-1/2:ℝ):ℝ):ℂ) *
      (normalizedStationaryJet j f θ A * normalizedStationaryJet k g φ B)) *
        radialStationaryProfile Ψ (-((j:ℝ)+(k:ℝ)+1)) t) s‖ ≤ _
  rw [iteratedDeriv_const_mul_field]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hA _),abs_of_pos (Real.rpow_pos_of_pos hB _)]
  have hfj := normalizedStationaryJet_bound hf hC hD hA hDA j θ hbf
  have hgk := normalizedStationaryJet_bound hg hE hD hB hDB k φ hbg
  calc
    _ ≤ (A^(-1/2:ℝ)*B^(-1/2:ℝ))*
        (((directStationaryExpr j).cost*C)*((directStationaryExpr k).cost*E))*P := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left (mul_le_mul hfj hgk (norm_nonneg _) (mul_nonneg hj hC))
          (by positivity)) (hp l hl s) (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [H]; ring

 theorem stationaryRadialCoefficient_kernel {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (j k : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ {f g : ℝ → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    ∀ {C E D R d₁ d₂ : ℝ}, 0 ≤ C → 0 ≤ E → 1 ≤ D → 0 < R → 0 < d₁ → 0 < d₂ →
    D^2 ≤ R*d₁ → D^2 ≤ R*d₂ → ∀ θ φ s₁ s₂ : ℝ,
    (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) →
    (∀ l ≤ 2*j, ‖iteratedDeriv l f θ‖ ≤ C*D^l) →
    (∀ l ≤ 2*k, ‖iteratedDeriv l g φ‖ ≤ E*D^l) →
    ‖radialPhaseIntegral (stationaryRadialCoefficient Ψ j k f g θ φ (R*d₁) (R*d₂))
      (R*(s₁*d₁+s₂*d₂))‖ ≤
      H*C*E*((R*d₁)^(-1/2:ℝ)*(R*d₂)^(-1/2:ℝ))/(1+R*|d₁-d₂|)^2 := by
  obtain ⟨H,hH,hh⟩ := stationaryRadialCoefficient_derivatives hΨ hs j k 2
  refine ⟨15*H,by positivity,?_⟩
  intro f g hf hg C E D R d₁ d₂ hC hE hD hR h1 h2 hDA hDB θ φ s₁ s₂ hs1 hs2 hbf hbg
  obtain ⟨ha,hsa,hba⟩ := hh hf hg hC hE hD (mul_pos hR h1) (mul_pos hR h2)
    hDA hDB θ φ hbf hbg
  have hb0 := hba 0 (by omega)
  simp only [iteratedDeriv_zero] at hb0
  have hx := angular_radial_kernel_bound ha hsa (C := H*C*E)
    (by positivity) (by positivity) hR.le h1.le h2.le hs1 hs2 hb0 (hba 2 le_rfl)
  apply hx.trans_eq
  ring

end PlanarFalconer

end OAI
