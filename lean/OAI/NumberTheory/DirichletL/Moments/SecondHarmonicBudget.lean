import OAI.NumberTheory.DirichletL.Moments.SecondSquarefreeBlock
import OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentSecondHarmonicBudget
open CenteredMomentSecondWindowBudget CenteredMomentMobiusHarmonicMass
open CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

lemma paired_divisor (J₁ J₂:ℕ) (t E₁ E₂ n:ℝ) (hn:0≤n) :
    windowBudget J₁ t (E₁/n)*windowBudget J₂ t (E₂/n)=
      (windowBudget J₁ t E₁*windowBudget J₂ t E₂)/n := by
  simp only [windowBudget,Real.sqrt_div' _ hn]
  calc
    _=(Real.sqrt E₁*heightEnvelope t^J₁*profileMoment J₁*
        (Real.sqrt E₂*heightEnvelope t^J₂*profileMoment J₂))/
          (Real.sqrt n*Real.sqrt n):=by ring
    _=_:=by rw [Real.mul_self_sqrt hn]

 theorem actual_divisor_budget (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀{α:Type*} (T:Finset α) (v:α→Ideal O),(∀j∈T,v j≠0) →
      (∀j∈T,(Ideal.absNorm (v j):ℝ)≤Z^B) →
      ∀J₁ J₂:ℕ,∀t E₁ E₂:ℝ,
      (∑L∈divisorPool T v,‖(moebius L:ℂ)‖*
        (windowBudget J₁ t (E₁/(Ideal.absNorm L:ℝ))*
          windowBudget J₂ t (E₂/(Ideal.absNorm L:ℝ))))≤
      C*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨C,hC,hbound⟩:=actual_divisorPool_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α T v hv hn J₁ J₂ t E₁ E₂
  have he:(∑L∈divisorPool T v,‖(moebius L:ℂ)‖*
      (windowBudget J₁ t (E₁/(Ideal.absNorm L:ℝ))*windowBudget J₂ t (E₂/(Ideal.absNorm L:ℝ))))=
      (∑L∈divisorPool T v,‖(moebius L:ℂ)‖/(Ideal.absNorm L:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂):=by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro L hL
    rw [paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (hZ.2 T v hv hn)
    (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _))

end SevenEighths.CenteredMomentSecondHarmonicBudget

end

end OAI
