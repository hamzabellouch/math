import OAI.Probability.ClassicalON.CenteredAnnulus

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def firstSpinProduct (x y : V) (s : V → Spin 3) : ℝ := (s x).val 0*(s y).val 0

omit [Fintype V] [Fintype E] in
theorem continuous_firstSpinProduct (x y : V) : Continuous (firstSpinProduct x y) := by
  unfold firstSpinProduct
  fun_prop

omit [Fintype V] [Fintype E] in
theorem cylindrical_firstSpinProduct (x y : V) (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) :
    firstSpinProduct x y (cylindricalConfiguration r τ θ)=
      (r x:ℝ)*(r y:ℝ)*(signValue (τ x)*signValue (τ y)) := by
  change ((r x:ℝ)*signValue (τ x))*((r y:ℝ)*signValue (τ y))=_
  ring

theorem integral_cylinder_firstSpin (left right : E → V) (b : E → ℝ) (x y : V) (r : V → Amplitude) :
    (∫ τ,∫ θ,Real.exp (freeSpinEnergy 3 left right b (cylindricalConfiguration r τ θ))*
      firstSpinProduct x y (cylindricalConfiguration r τ θ) ∂planarReference ∂isingReference)=
      ∑ η,amplitudeBondWeight left right b r η*
        ((r x:ℝ)*(r y:ℝ)*(if bondConnected left right η x y then 1 else 0)) := by
  have he (τ : V → Bool) (θ : V → PlanarAngle) :
      Real.exp (freeSpinEnergy 3 left right b (cylindricalConfiguration r τ θ))*
        firstSpinProduct x y (cylindricalConfiguration r τ θ)=
      ((r x:ℝ)*(r y:ℝ))*(Real.exp (edgeHamiltonian (isingEnergy left right)
        (amplitudeCoupling left right b (fun v => (r v:ℝ))) τ)*(signValue (τ x)*signValue (τ y)))*
      Real.exp (edgeHamiltonian (planarEnergy left right)
        (amplitudeCoupling left right b (fun v => transverseAmplitude (r v))) θ) := by
    rw [cylindricalConfiguration_energy,Real.exp_add,cylindrical_firstSpinProduct]
    ring
  simp_rw [he,integral_const_mul]
  rw [integral_mul_const,integral_const_mul,ising_numerator_bond_sum,amplitudeBondParam_eq]
  change ((r x:ℝ)*(r y:ℝ))*((2:ℝ)⁻¹^Fintype.card V*
    Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
      ∑ η,bondWeight left right (amplitudeBondParam left right b r) η*
        (if bondConnected left right η x y then 1 else 0))*planarAmplitudePartition left right b r=_
  rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro η _
  unfold amplitudeBondWeight amplitudeBondPrefactor
  ring

theorem firstSpinMean_eq_jointBondMean (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e) (x y : V) :
    freeSpinMean 3 left right b (firstSpinProduct x y)=
      jointBondMean sphericalAmplitudeLaw left right b
        (fun r η => (r x:ℝ)*(r y:ℝ)*(if bondConnected left right η x y then 1 else 0)) := by
  rw [jointBondMean_raw _ _ _ _ hb]
  unfold freeSpinMean weightedMean
  rw [integral_freeSpinWeight]
  simp_rw [amplitudeBondWeight_sum]
  congr 1
  have hc : Continuous (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s)*firstSpinProduct x y s) :=
    (continuous_freeSpinEnergy 3 left right b).rexp.mul (continuous_firstSpinProduct x y)
  rw [integral_freeSpinReference_cylinder _ hc]
  simp_rw [integral_cylinder_firstSpin]

theorem jointBondMean_nonneg (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    {f : (V → Amplitude) → (E → Bool) → ℝ} (hf : ∀ r η,0≤f r η) :
    0≤jointBondMean μ left right b f :=
  weightedMean_nonneg (continuous_amplitudeDensity _ _ _) (amplitudeDensity_pos _ _ _)
    (bondConditionalMean_nonneg _ _ _ hb hf)

theorem jointBondMean_mono (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    {f g : (V → Amplitude) → (E → Bool) → ℝ}
    (hf : ∀ η,Continuous (fun r => f r η)) (hg : ∀ η,Continuous (fun r => g r η))
    (hfg : ∀ r η,f r η≤g r η) : jointBondMean μ left right b f≤jointBondMean μ left right b g := by
  apply weightedMean_mono (continuous_amplitudeDensity _ _ _) (amplitudeDensity_pos _ _ _)
    (continuous_bondConditionalMean _ _ _ hb hf) (continuous_bondConditionalMean _ _ _ hb hg)
  intro r
  exact finiteMean_mono (bondWeight_nonneg _ _ (amplitudeBondParam_nonneg _ _ _ hb r)) (hfg r)

theorem firstSpinMean_bounds (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e) (x y : V) :
    0≤freeSpinMean 3 left right b (firstSpinProduct x y) ∧
      freeSpinMean 3 left right b (firstSpinProduct x y)≤
        freeBondMean left right b (fun η => if bondConnected left right η x y then 1 else 0) := by
  rw [firstSpinMean_eq_jointBondMean _ _ _ hb,freeBondMean_eq_jointBondMean _ _ _ hb]
  constructor
  · apply jointBondMean_nonneg _ _ _ _ hb
    intro r η
    exact mul_nonneg (mul_nonneg (r x).property.1 (r y).property.1) (by split_ifs <;> norm_num)
  · apply jointBondMean_mono _ _ _ _ hb
    · intro η; fun_prop
    · intro η; exact continuous_const
    · intro r η
      split_ifs <;> simp only [mul_one,mul_zero,le_refl]
      exact (mul_le_of_le_one_left (r y).property.1 (r x).property.2).trans (r y).property.2

end ClassicalON

end

end OAI
