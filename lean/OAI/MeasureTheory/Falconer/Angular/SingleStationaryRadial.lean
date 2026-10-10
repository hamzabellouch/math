import OAI.MeasureTheory.Falconer.Angular.RadialStationaryProfile
import OAI.MeasureTheory.Falconer.Angular.SignedStationaryJet

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def singleStationaryRadialCoefficient (Ψ : ℝ → ℝ) (plus : Bool)
    (j : ℕ) (f : ℝ → ℂ) (θ A : ℝ) (s : ℝ) : ℂ :=
  (((A^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus j f θ A) *
    radialStationaryProfile Ψ (-((j:ℝ)+1/2)) s

 theorem singleStationaryRadial_derivatives {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (j n : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ {C D A : ℝ}, 0 ≤ C → 1 ≤ D → 0 < A →
    D^2 ≤ A → ∀ plus : Bool, ∀ θ : ℝ,
    (∀ l ≤ 2*j, ∀ t, ‖iteratedDeriv l f t‖ ≤ C*D^l) →
    ContDiff ℝ ∞ (singleStationaryRadialCoefficient Ψ plus j f θ A) ∧
    tsupport (singleStationaryRadialCoefficient Ψ plus j f θ A) ⊆ Icc (1/4:ℝ) 4 ∧
    ∀ l ≤ n, ∀ s, ‖iteratedDeriv l (singleStationaryRadialCoefficient Ψ plus j f θ A) s‖ ≤
      H*C*A^(-1/2:ℝ) := by
  obtain ⟨P,hP,hp⟩ := radialStationaryProfile_derivatives hΨ hs (-((j:ℝ)+1/2)) n
  have hj := (directStationaryExpr j).cost_nonneg
  refine ⟨P*(directStationaryExpr j).cost,by positivity,?_⟩
  intro f hf C D A hC hD hA hDA plus θ hb
  refine ⟨contDiff_const.mul (radialStationaryProfile_contDiff hΨ hs _),
    tsupport_mul_subset_right.trans (radialStationaryProfile_tsupport hs _),?_⟩
  intro l hl s
  change ‖iteratedDeriv l (fun t =>
    (((A^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus j f θ A) *
      radialStationaryProfile Ψ (-((j:ℝ)+1/2)) t) s‖ ≤ _
  rw [iteratedDeriv_const_mul_field]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hA _)]
  calc
    _ ≤ A^(-1/2:ℝ)*((directStationaryExpr j).cost*C)*P := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left (signedStationaryJet_bound hf hC hD hA hDA plus j θ hb)
          (by positivity)) (hp l hl s) (norm_nonneg _) (by positivity)
    _ = _ := by ring

 theorem singleStationaryRadial_noncomparable {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (j n : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ {C D R large small t sign : ℝ},
    0 ≤ C → 1 ≤ D → 0 < R → 0 < large → 2*small ≤ large → |t| ≤ small →
    (sign = 1 ∨ sign = -1) → D^2 ≤ R*large → ∀ plus : Bool, ∀ θ : ℝ,
    (∀ l ≤ 2*j, ∀ u, ‖iteratedDeriv l f u‖ ≤ C*D^l) →
    ‖radialPhaseIntegral (singleStationaryRadialCoefficient Ψ plus j f θ (R*large))
      (R*(sign*large+t))‖ ≤ H*C*(R*large)^(-1/2:ℝ)/(R*large/2)^n := by
  obtain ⟨H,hH,hh⟩ := singleStationaryRadial_derivatives hΨ hs j n
  refine ⟨H*(15/4),by positivity,?_⟩
  intro f hf C D R large small t sign hC hD hR hl hsep ht hsign hDA plus θ hb
  obtain ⟨ha,hsa,hba⟩ := hh hf hC hD (mul_pos hR hl) hDA plus θ hb
  have hfreq : R*large/2 ≤ |R*(sign*large+t)| := by
    rw [abs_mul,abs_of_pos hR]
    have hx := mul_le_mul_of_nonneg_left (noncomparable_radial_frequency hsep ht hsign) hR.le
    linarith
  have hpos : 0 < R*large/2 := by positivity
  have hne : R*(sign*large+t) ≠ 0 := abs_pos.mp (hpos.trans_le hfreq)
  have hx := radialPhaseIntegral_nonzero ha hsa (by norm_num) hne n (hba n le_rfl)
  apply hx.trans
  have hnum : H*C*(R*large)^(-1/2:ℝ)*((4:ℝ)-1/4) =
      (H*(15/4))*C*(R*large)^(-1/2:ℝ) := by ring
  rw [hnum]
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hpos n)
    (pow_le_pow_left₀ hpos.le hfreq n)

end PlanarFalconer

end OAI
