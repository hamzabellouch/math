import OAI.NumberTheory.DirichletL.Descent.SecondSectorAssembly
import OAI.NumberTheory.DirichletL.Descent.SecondInheritedEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondInheritedProfile {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) : SecondProfileData ι :=
  actualMarkedSecondProfileData p x Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z ∅ ∅

def secondModeLeft (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : SecondChild → ℂ :=
  secondCanonicalPolynomial p hp hcop hg pool (fun _ => secondRayMinus Ψ z)
    (actualSecondInheritedPuncture m) slots lists a
    (fun _ => childLogTest ω (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4)) X

def secondModeRight (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (X : ℝ) (t : Frequency × (Fin 6 → ℝ)) (c : SecondChild) : ℂ :=
  secondCanonicalPolynomial p hp hcop hg pool (fun _ => secondRayPlus Ψ z)
    (actualSecondInheritedPuncture m) slots lists a
    (fun _ => childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) X
    (c.1,c.2.1,-c.2.2)

def secondModeOuter {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2)
    (secondRelativeLog (secondActualNorms p (secondInheritedProfile p x Ψ m z) ∅ ∅) G E V B X)

def secondModeBranch {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  secondModeOuter p x Ψ m z G E V B X t *
    (star (primeMark J₁ lists₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
      primeMark J₂ lists₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
    star (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t (actualSecondChild p u v x)) *
    secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t (actualSecondChild p u v x)

theorem second_inherited_mode_canonical {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (hx : SecondPairCanonicalAt (σ:=σ) p hp hcop hg x u v)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) :
    secondSeparatedPair p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t =
    ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X t := by
  have he := hx pool Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z ∅ ∅
    (Finset.empty_subset _) (Finset.empty_subset _) slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t
  dsimp only at he
  have hq : (actualSecondChild p u v x).1.quotient = x.quotient := rfl
  simpa only [secondInheritedProfile,secondModeBranch,secondModeOuter,secondModeLeft,secondModeRight,
    secondCanonicalPolynomial,actualSecondInheritedPuncture,actualSecondChild_neg_frequency,
    Finset.empty_union,Finset.mul_sum,mul_assoc,hq] using he

theorem actual_second_modes_common_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ))
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      (∑ x ∈ source,w x * secondSeparatedPair p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t) =
      ∑ uv : Eisˣ × Eisˣ, ∑ x ∈ secondSourceSector source sector uv, w x *
        ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := exists_second_uniform_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t w
  rw [secondSourceSector_partition source sector]
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hx,hxs⟩ := Finset.mem_filter.mp hx
  congr 1
  have hh := hsector x hx
  rw [hxs] at hh
  exact second_inherited_mode_canonical p hp hcop hg x uv.1 uv.2 hh
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t

end
end SevenEighths.InverseMoment

end OAI
