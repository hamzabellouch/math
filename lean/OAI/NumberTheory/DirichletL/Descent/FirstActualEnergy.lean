import OAI.NumberTheory.DirichletL.Descent.FirstEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation FourierBridge ActualEisensteinCubic FirstPassCubeLabels
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstModeEnergyCoefficient (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (d : Eis)
    (z : Frequency × (Fin 9 → ℝ)) : Finset ι → ℂ :=
  firstModeCubeCoefficient p hp hcop hg B v ε₁ ε₂ negative C y
    (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 (if negative then 7 else 8)) d

theorem firstModeEnergyCoefficient_continuous (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (d : Eis) (S : Finset ι) :
    Continuous (fun z => firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ negative C y d z S) := by
  simp only [firstModeEnergyCoefficient,firstModeCubeCoefficient_eq]
  apply (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ negative C (fun _ => 1) y d S).comp
  unfold profileHeight
  fun_prop

theorem firstModeEnergyCoefficient_norm (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (d : Eis)
    (z : Frequency × (Fin 9 → ℝ)) (S : Finset ι) :
    ‖firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ negative C y d z S‖ =
      ‖firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ negative C y d 0 S‖ := by
  simp only [firstModeEnergyCoefficient,firstModeCubeCoefficient_eq]
  exact (norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ negative C (fun _ => 1) y _ d S).trans
    (norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ negative C (fun _ => 1) y _ d S).symm

theorem firstOuterPhase_norm (h : Fin 9 → ℝ) (a : Fin 7 → ℝ) :
    ‖firstOuterPhase h a‖ = 1 := by
  simp [firstOuterPhase,norm_prod,logPhase_norm]

theorem actual_first_common_energy (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ)
    (g : Fin 9 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
      firstModeIdealRows p hp hcop hg F B v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z‖ ≤
    Real.sqrt (∫ z : Frequency × (Fin 9 → ℝ), ‖fullProfileDensity g b₁ b₂ b₃ z‖ *
      ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
      rayIdealEnergy p hg F (firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ true C₁ y₁ d z) true h) *
    Real.sqrt (∫ z : Frequency × (Fin 9 → ℝ), ‖fullProfileDensity g b₁ b₂ b₃ z‖ *
      ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
      rayIdealEnergy p hg F (firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ false C₂ y₂ d z) false h) := by
  let b := fun z : Frequency × (Fin 9 → ℝ) => fullProfileDensity g b₁ b₂ b₃ z *
    firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a
  have hphase : Continuous (fun z : Frequency × (Fin 9 → ℝ) =>
      firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a) := by
    unfold firstOuterPhase profileHeight logPhase
    fun_prop
  have hb : Integrable b := (full_density_integrable g b₁ b₂ b₃).mul_bdd
    hphase.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => (firstOuterPhase_norm _ _).le))
  have hbc : Continuous b := by
    apply Continuous.mul _ hphase
    unfold fullProfileDensity coordinateDensity tripleCoefficient
    fun_prop
  have hbn (z : Frequency × (Fin 9 → ℝ)) : ‖b z‖ = ‖fullProfileDensity g b₁ b₂ b₃ z‖ := by
    simp only [b,norm_mul,firstOuterPhase_norm,mul_one]
  have hh := full_cube_integral_norm_le_energy p hg F
    (firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ true C₁ y₁ d)
    (firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ false C₂ y₂ d)
    (firstModeEnergyCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true C₁ y₁ d)
    (firstModeEnergyCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false C₂ y₂ d)
    (firstModeEnergyCoefficient_norm p hp hcop hg B v ε₁ ε₂ true C₁ y₁ d)
    (firstModeEnergyCoefficient_norm p hp hcop hg B v ε₁ ε₂ false C₂ y₂ d)
    h b hb hbc (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  simp only [hbn] at hh
  convert hh using 1
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  simp only [firstModeIdealRows,firstModeEnergyCoefficient,firstModeCubeCoefficient,
    Bool.false_eq_true,ite_false,ite_true,b]
  ring

end
end SevenEighths.InverseMoment

end OAI
