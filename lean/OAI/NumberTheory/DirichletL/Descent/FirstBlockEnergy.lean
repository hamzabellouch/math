import OAI.NumberTheory.DirichletL.Descent.FirstBlocks
import OAI.NumberTheory.DirichletL.Descent.FirstActualEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstBlockOuterWeight (selector : Finset ι → ℂ)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : Eis) : ℂ :=
  crossCoeff r.1 r.2 * selector D * supportMobius (fun i => Ideal.span {p i}) D *
    rowCoprimeMask (fun i => Ideal.span {p i}) D h

def firstBlockEnergy (F : Finset ι) (selector : Finset ι → ℂ)
    (C : Finset ι → ℂ) (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : Eis) : ℝ :=
  ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖firstBlockOuterWeight p selector r D h‖ *
      ‖firstCommonColumn p hg F D C negative (if negative then r.1 else r.2) ω X t h‖^2

theorem firstBlockEnergy_nonneg (F : Finset ι) (selector : Finset ι → ℂ)
    (C : Finset ι → ℂ) (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : Eis) :
    0 ≤ firstBlockEnergy p hg F selector C negative ω X t h := by
  unfold firstBlockEnergy
  positivity

theorem first_block_energy (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ)
    (d h : Eis) (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) :
    let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
    ‖firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      Real.sqrt (firstBlockEnergy p hg F selector C₁ true ω₁ (s 7) (H 7) h) *
      Real.sqrt (firstBlockEnergy p hg F selector C₂ false ω₂ (s 8) (H 8) h) := by
  dsimp only
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  let w := fun j : (RayCharacter × RayCharacter) × Finset ι =>
    firstBlockOuterWeight p selector j.1 j.2 h *
      firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h j.2 s)
  have hn (j : (RayCharacter × RayCharacter) × Finset ι) :
      ‖w j‖ = ‖firstBlockOuterWeight p selector j.1 j.2 h‖ := by
    simp only [w,norm_mul,firstOuterPhase_norm,mul_one]
  have hc := DescentWeightedCauchy.weighted_cauchy
    ((Finset.univ : Finset (RayCharacter × RayCharacter)) ×ˢ F.powerset) w
    (fun j => firstCommonColumn p hg F j.2 C₂ false j.1.2 ω₂ (s 8) (H 8) h)
    (fun j => firstCommonColumn p hg F j.2 C₁ true j.1.1 ω₁ (s 7) (H 7) h)
  simp only [hn,Finset.sum_product] at hc
  have he : (∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      w (r,D) * firstCommonColumn p hg F D C₂ false r.2 ω₂ (s 8) (H 8) h *
        star (firstCommonColumn p hg F D C₁ true r.1 ω₁ (s 7) (H 7) h)) =
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
    simp only [firstBlockedSeparatedRow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro D hD
    dsimp only [w,firstBlockOuterWeight,H]
    ring
  rw [he] at hc
  change ‖firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
    Real.sqrt (firstBlockEnergy p hg F selector C₂ false ω₂ (s 8) (H 8) h) *
    Real.sqrt (firstBlockEnergy p hg F selector C₁ true ω₁ (s 7) (H 7) h) at hc
  exact hc.trans_eq (mul_comm _ _)

theorem first_block_integral_of_energy (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ)
    (d h : Eis) (s : Fin 9 → ℝ) (density : Frequency × (Fin 9 → ℝ) → ℂ)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hDensity : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstBlockEnergy p hg F selector C₁ true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstBlockEnergy p hg F selector C₂ false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
    B*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖ := by
  have hb (z : Frequency × (Fin 9 → ℝ)) :
      ‖firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      B*(tripleHeight J z.1*coordinateHeight J z.2) := by
    apply (first_block_energy p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z).trans
    have h := mul_le_mul (Real.sqrt_le_sqrt (hleft z)) (Real.sqrt_le_sqrt (hright z))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact h.trans_eq (by rw [← sq,Real.sq_sqrt]; unfold tripleHeight coordinateHeight; positivity)
  calc
    _ ≤ ∫ z : Frequency × (Fin 9 → ℝ),B*(tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul B)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end SevenEighths.InverseMoment

end OAI
