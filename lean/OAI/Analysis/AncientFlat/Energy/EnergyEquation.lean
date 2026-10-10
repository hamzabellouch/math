import OAI.Analysis.AncientFlat.Energy.EnergyCoercive
import OAI.Analysis.AncientFlat.Energy.EnergyTime

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BoundedContinuousFunction Laplacian
namespace ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma zeroth_energy_le (u b : V →ᵇ ℂ) (B : ℝ) (_hB : 0≤B) (hb : ‖b‖≤B) :
    -pair u (↑(b*u)) ≤ B*mass (u : V → ℂ) := by
  unfold pair mass
  rw [←integral_neg,←integral_const_mul]
  apply integral_mono (integrable_pair u.continuous (b*u).continuous (bounded_bcf _) (bounded_bcf _)).neg
    ((integrable_mass u.continuous (bounded_bcf _)).const_mul B)
  intro x
  have hh : -(inner ℝ (u x) (b x*u x))≤B*‖u x‖^2 := by
    calc
      _ ≤ |inner ℝ (u x) (b x*u x)| := neg_le_abs _
      _ ≤ ‖u x‖*‖b x*u x‖ := by simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) (u x) (b x*u x))
      _ = ‖u x‖*(‖b x‖*‖u x‖) := by rw [norm_mul]
      _ ≤ ‖u x‖*(B*‖u x‖) := by
        gcongr
        exact (b.norm_coe_le_norm x).trans hb
      _ = _ := by ring
  change -(weight x*inner ℝ (u x) (b x*u x)) ≤ B*(weight x*‖u x‖^2)
  nlinarith [mul_le_mul_of_nonneg_left hh (weight_pos x).le]
lemma pair_equation (a : V →ᵇ ℝ) (b u v : V →ᵇ ℂ)
    (hu : ContDiff ℝ 4 (u : V → ℂ)) (hub : BoundedJets 4 (u : V → ℂ))
    (hv : ∀ x, v x=-(a x : ℂ)*Δ (Δ (u : V → ℂ)) x-b x*u x) :
    pair u v = -principal a u-pair u (↑(b*u)) := by
  have hlu := ClassicalIBP.contDiff_laplacian (u : V → ℂ) 2 hu
  have hllc := (ClassicalIBP.contDiff_laplacian _ 0 hlu).continuous
  have hllb := ((hub.laplacian 2 hu).laplacian 0 hlu).zero
  have hab : Bounded (a : V → ℝ) := ⟨‖a‖,norm_nonneg _,a.norm_coe_le_norm⟩
  have hi1 : Integrable (fun x => (weight x*a x)*inner ℝ (u x) (Δ (Δ (u : V → ℂ)) x)) :=
    integral_coeff_pair u.continuous hllc (bounded_bcf u) hllb
      ((contDiff_weight 0).continuous.mul a.continuous) (decays_weight_mul hab)
  have hi2 := integrable_pair u.continuous (b*u).continuous (bounded_bcf u) (bounded_bcf (b*u))
  have he (x : V) : weight x*inner ℝ (u x) (v x) =
      -((weight x*a x)*inner ℝ (u x) (Δ (Δ (u : V → ℂ)) x)) -
      weight x*inner ℝ (u x) (b x*u x) := by
    rw [hv]
    simp only [neg_mul,←Complex.real_smul,inner_sub_right,inner_neg_right,real_inner_smul_right]
    ring
  unfold pair principal
  simp_rw [he]
  erw [integral_sub hi1.neg hi2,integral_neg]
lemma energy_rhs_le {α C K B : ℝ} (hα : 0<α) (hB : 0≤B)
    (a : V →ᵇ ℝ) (b u v : V →ᵇ ℂ) (hb : ‖b‖≤B)
    (ha : ContDiff ℝ 2 (a : V → ℝ))
    (haj : ∀ n : ℕ, n≤2 → ∀ x, ‖iteratedFDeriv ℝ n (a : V → ℝ) x‖≤C)
    (ha0 : ∀ x, α≤a x)
    (hu : ContDiff ℝ 4 (u : V → ℂ)) (hub : BoundedJets 4 (u : V → ℂ))
    (hK : ∀ (a : V → ℝ) (u : V → ℂ), ContDiff ℝ 2 a →
      (∀ n : ℕ, n≤2 → ∀ x, ‖iteratedFDeriv ℝ n a x‖≤C) →
      (∀ x, α≤a x) → ContDiff ℝ 4 u → BoundedJets 4 u →
      (α/2)*mass (Δ u)-K*mass u≤principal a u)
    (hv : ∀ x, v x=-(a x : ℂ)*Δ (Δ (u : V → ℂ)) x-b x*u x) :
    2*pair u v ≤ (2*K+2*B)*mass (u : V → ℂ) := by
  have hh := hK a u ha haj ha0 hu hub
  have hz := zeroth_energy_le u b B hB hb
  rw [pair_equation a b u v hu hub hv]
  nlinarith [mul_nonneg (by positivity : 0≤α/2) (mass_nonneg (Δ (u : V → ℂ)))]
end ParametrixUniqueness

end

end OAI
