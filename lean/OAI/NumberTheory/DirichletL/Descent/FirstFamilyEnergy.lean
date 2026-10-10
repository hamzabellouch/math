import OAI.NumberTheory.DirichletL.Descent.FirstBlockEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstFamilySeparatedRow (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  ∑ x∈source,w x*firstBlockedSeparatedRow p hg F (selector x) (C₁ x) (C₂ x)
    ω₁ ω₂ (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s z

def firstFamilyEnergy (source : Finset κ) (F : Finset ι)
    (selector C : κ → Finset ι → ℂ) (w : κ → ℂ)
    (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : κ → Eis) : ℝ :=
  ∑ x∈source,‖w x‖*firstBlockEnergy p hg F (selector x) (C x) negative ω X t (h x)

theorem firstFamilyEnergy_nonneg (source : Finset κ) (F : Finset ι)
    (selector C : κ → Finset ι → ℂ) (w : κ → ℂ)
    (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : κ → Eis) :
    0 ≤ firstFamilyEnergy p hg source F selector C w negative ω X t h :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (norm_nonneg _)
    (firstBlockEnergy_nonneg p hg F (selector x) (C x) negative ω X t (h x)))

theorem first_family_cauchy (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) :
    let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
    ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      Real.sqrt (firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7) (H 7) h)*
      Real.sqrt (firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8) (H 8) h) := by
  dsimp only
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  let weight (j : κ × (RayCharacter × RayCharacter) × Finset ι) : ℂ :=
    w j.1*firstBlockOuterWeight p (selector j.1) j.2.1 j.2.2 (h j.1)*
      firstOuterPhase H (firstCommonOuterLog p (A₁ j.1) (A₂ j.1) (C j.1) (R j.1)
        (d j.1) (h j.1) j.2.2 s)
  have hn (j : κ × (RayCharacter × RayCharacter) × Finset ι) :
      ‖weight j‖ = ‖w j.1‖*‖firstBlockOuterWeight p (selector j.1) j.2.1 j.2.2 (h j.1)‖ := by
    simp only [weight,norm_mul,firstOuterPhase_norm,mul_one]
  have hc := DescentWeightedCauchy.weighted_cauchy
    (source ×ˢ ((Finset.univ : Finset (RayCharacter × RayCharacter)) ×ˢ F.powerset)) weight
    (fun j => firstCommonColumn p hg F j.2.2 (C₂ j.1) false j.2.1.2 ω₂ (s 8) (H 8) (h j.1))
    (fun j => firstCommonColumn p hg F j.2.2 (C₁ j.1) true j.2.1.1 ω₁ (s 7) (H 7) (h j.1))
  simp only [hn,Finset.sum_product] at hc
  have he : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      weight (x,r,D)*firstCommonColumn p hg F D (C₂ x) false r.2 ω₂ (s 8) (H 8) (h x)*
        star (firstCommonColumn p hg F D (C₁ x) true r.1 ω₁ (s 7) (H 7) (h x))) =
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z := by
    simp only [firstFamilySeparatedRow,firstBlockedSeparatedRow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro D hD
    dsimp only [weight,firstBlockOuterWeight,H]
    ring
  rw [he] at hc
  have hleft : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      ‖w x‖*‖firstBlockOuterWeight p (selector x) r D (h x)‖*
        ‖firstCommonColumn p hg F D (C₁ x) true r.1 ω₁ (s 7) (H 7) (h x)‖^2) =
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7) (H 7) h := by
    simp only [firstFamilyEnergy,firstBlockEnergy,Finset.mul_sum,mul_assoc,ite_true]
  have hright : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      ‖w x‖*‖firstBlockOuterWeight p (selector x) r D (h x)‖*
        ‖firstCommonColumn p hg F D (C₂ x) false r.2 ω₂ (s 8) (H 8) (h x)‖^2) =
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8) (H 8) h := by
    simp only [firstFamilyEnergy,firstBlockEnergy,Finset.mul_sum,mul_assoc,Bool.false_eq_true,ite_false]
  rw [hleft,hright] at hc
  exact hc.trans_eq (mul_comm _ _)

theorem first_family_integral_of_energy (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (density : Frequency × (Fin 9 → ℝ) → ℂ)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hDensity : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
    B*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖ := by
  have hb (z : Frequency × (Fin 9 → ℝ)) :
      ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      B*(tripleHeight J z.1*coordinateHeight J z.2) := by
    apply (first_family_cauchy p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z).trans
    have hh := mul_le_mul (Real.sqrt_le_sqrt (hleft z)) (Real.sqrt_le_sqrt (hright z))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact hh.trans_eq (by rw [←sq,Real.sq_sqrt]; unfold tripleHeight coordinateHeight; positivity)
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
