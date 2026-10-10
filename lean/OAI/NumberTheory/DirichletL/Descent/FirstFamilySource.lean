import OAI.NumberTheory.DirichletL.Descent.FirstFamilyEnergy
import OAI.NumberTheory.DirichletL.Descent.FirstBalancedSource

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

theorem integrable_first_block_density (F : Finset ι) (selector C₁ C₂ : Finset ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density) :
    Integrable (fun z : Frequency × (Fin 9 → ℝ) => density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z) := by
  let coef (j : FirstCommonIndex ι) :=
    (selector j.2.1*firstCommonWeight p hg C₁ C₂ h j)*
      (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8))
  have he : (fun z : Frequency × (Fin 9 → ℝ) => density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z) =
      fun z => ∑ j∈firstCommonIndices F,coef j*(density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
          (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) := by
    funext z
    rw [←first_block_modes_eq_columns]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [coef]
    ring
  rw [he]
  exact integrable_finsetSum _ (fun j hj => (integrable_density_mode density hDensity
    firstLeftSlope firstRightSlope firstKernelSlope
    (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s)).const_mul (coef j))

theorem first_family_density_sum (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density) :
    (∑ x∈source,w x*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstBlockedSeparatedRow p hg F (selector x) (C₁ x) (C₂ x) ω₁ ω₂
        (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s z) =
    ∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z := by
  simp only [←integral_const_mul]
  rw [←integral_finsetSum source (fun x hx =>
    (integrable_first_block_density p hg F (selector x) (C₁ x) (C₂ x) ω₁ ω₂
      (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s density hDensity).const_mul (w x))]
  apply integral_congr_ae
  filter_upwards with z
  simp only [firstFamilySeparatedRow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def firstFamilyPhysicalRows (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ → ℝ) (K : ℝ)
    (d h : κ → Eis) (s : Fin 9 → ℝ) : ℂ :=
  ∑ x∈source,w x*firstBlockedPhysicalRows p hg F (selector x) (C₁ x) (C₂ x)
    (fun y => W₁ (y/(s 0*s 2*s 5*s 7))) (fun y => W₂ (y/(s 1*s 2*s 5*s 8)))
    Φ (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x)

theorem actual_first_balanced_family (hp : ∀ i,p i ≠ 0)
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (hs : ∀ i,0 < s i) (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₁ (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₂ (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i) = 1) :
    (Real.exp (-(9/2:ℝ)*L):ℂ)*firstFamilyPhysicalRows p hg source F selector C₁ C₂ w
      W₁ W₂ Φ A₁ A₂ C R K d h s =
    (firstRootScale s:ℂ)⁻¹*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z := by
  have hb (x : κ) (hx : x∈source) := actual_first_balanced_block p hp hg F (selector x) (C₁ x) (C₂ x)
    W₁ W₂ ω₁ ω₂ Φ V (A₁ x) (A₂ x) (C x) (R x) K L
    (hpos x hx).1 (hpos x hx).2.1 (hpos x hx).2.2.1 (hpos x hx).2.2.2.1
    (d x) (h x) (hpos x hx).2.2.2.2.1 (hpos x hx).2.2.2.2.2 s hs density hDensity hsep
    (hω₁ x hx) (hω₂ x hx) (hcut x hx)
  rw [←first_family_density_sum p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s density hDensity]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    _ = w x*((Real.exp (-(9/2:ℝ)*L):ℂ)*firstBlockedPhysicalRows p hg F (selector x) (C₁ x) (C₂ x)
      (fun y => W₁ (y/(s 0*s 2*s 5*s 7))) (fun y => W₂ (y/(s 1*s 2*s 5*s 8)))
      Φ (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x)) := by ring
    _ = _ := by rw [hb x hx]; ring

end
end SevenEighths.InverseMoment

end OAI
