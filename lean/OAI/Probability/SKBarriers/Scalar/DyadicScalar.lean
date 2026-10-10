import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarTimeChain

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarTimeChain_uniform_nonexpansive {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (β : ℝ)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p ∈ l, 0 ≤ p.1) {ε : ℝ}
    (hε : ∀ x, |f x-g x| ≤ ε) (x : ℝ) :
    |scalarTimeChain β l f x-scalarTimeChain β l g x| ≤ ε := by
  induction l generalizing x with
  | nil => exact hε x
  | cons p l ih =>
    exact scalarStep_uniform_nonexpansive (scalarTimeChain_regular hf β l)
      (scalarTimeChain_regular hg β l) (hm p (List.mem_cons_self))
      (fun z => ih (fun q hq => hm q (List.mem_cons_of_mem p hq)) z) _ x

def dyadicIntervals (α : ℝ → ℝ) : ℕ → ℝ → ℝ≥0 → List (ℝ × ℝ≥0)
  | 0,s,t => [(α s,t)]
  | n+1,s,t => dyadicIntervals α n s (t/2) ++
      dyadicIntervals α n (s+(t:ℝ)/2) (t/2)

def dyadicScalar (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ)
    (t : ℝ≥0) (f : ℝ → ℝ) : ℝ → ℝ :=
  scalarTimeChain β (dyadicIntervals α n s t) f

@[simp] theorem dyadicScalar_zero (β : ℝ) (α : ℝ → ℝ) (s : ℝ)
    (t : ℝ≥0) (f : ℝ → ℝ) :
    dyadicScalar β α 0 s t f=scalarTimeStep β (α s) t f := rfl

@[simp] theorem dyadicScalar_succ (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ)
    (t : ℝ≥0) (f : ℝ → ℝ) :
    dyadicScalar β α (n+1) s t f=dyadicScalar β α n s (t/2)
      (dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f) := by
  exact scalarTimeChain_append β _ _ f

theorem dyadicIntervals_mem_bounds {α : ℝ → ℝ} (hα : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) {p : ℝ × ℝ≥0} (hp : p ∈ dyadicIntervals α n s t) :
    α s ≤ p.1 ∧ p.1 ≤ α (s+t) ∧ p.2 ≤ t := by
  induction n generalizing s t with
  | zero =>
    simp only [dyadicIntervals,List.mem_singleton] at hp
    subst p
    exact ⟨le_rfl,hα (by linarith [t.coe_nonneg]),le_rfl⟩
  | succ n ih =>
    simp only [dyadicIntervals,List.mem_append] at hp
    have ht : t/2 ≤ t := by exact div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)
    have htc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    rcases hp with hp|hp
    · obtain ⟨h₁,h₂,h₃⟩ := ih s (t/2) hp
      exact ⟨h₁,h₂.trans (hα (by rw [htc]; linarith [t.coe_nonneg])),h₃.trans ht⟩
    · obtain ⟨h₁,h₂,h₃⟩ := ih (s+(t:ℝ)/2) (t/2) hp
      refine ⟨(hα (by linarith [t.coe_nonneg])).trans h₁,?_,h₃.trans ht⟩
      simpa only [htc,show s+(t:ℝ)/2+(t:ℝ)/2=s+t by ring] using h₂

theorem dyadicIntervals_mass_bounds {α : ℝ → ℝ} (hα : ∀ s, α s ∈ Icc (0:ℝ) 1)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) {p : ℝ × ℝ≥0} (hp : p ∈ dyadicIntervals α n s t) :
    p.1 ∈ Icc (0:ℝ) 1 := by
  induction n generalizing s t with
  | zero =>
    simp only [dyadicIntervals,List.mem_singleton] at hp
    subst p
    exact hα s
  | succ n ih =>
    simp only [dyadicIntervals,List.mem_append] at hp
    exact hp.elim (ih s (t/2)) (ih (s+(t:ℝ)/2) (t/2))

theorem dyadicScalar_regular {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    BoundedDerivs (dyadicScalar β α n s t f) := scalarTimeChain_regular hf β _

theorem dyadicScalar_lipschitz {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    LipschitzWith K (dyadicScalar β α n s t f) :=
  scalarTimeChain_lipschitz hf hLip β _ (fun _ hp => (dyadicIntervals_mass_bounds hα n s t hp).1)

theorem dyadicScalar_uniform_nonexpansive {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (n : ℕ) (s : ℝ) (t : ℝ≥0)
    {ε : ℝ} (hε : ∀ x, |f x-g x| ≤ ε) (x : ℝ) :
    |dyadicScalar β α n s t f x-dyadicScalar β α n s t g x| ≤ ε :=
  scalarTimeChain_uniform_nonexpansive hf hg β _
    (fun _ hp => (dyadicIntervals_mass_bounds hα n s t hp).1) hε x

def scalarTimeMassConstant (β : ℝ) : ℝ := gaussianMassBound |β| * β^2

theorem scalarTimeMassConstant_nonneg (β : ℝ) : 0 ≤ scalarTimeMassConstant β :=
  mul_nonneg (gaussianMassBound_pos _).le (sq_nonneg _)

theorem dyadicScalar_successive_bound {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α (n+1) s t f x-dyadicScalar β α n s t f x| ≤
      scalarTimeMassConstant β*(t:ℝ)/(2:ℝ)^(n+1)*(α (s+t)-α s) := by
  induction n generalizing f s t x with
  | zero =>
    simp only [dyadicScalar_succ,dyadicScalar_zero]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    have htc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    have H (z) := scalarTimeStep_mass_lipschitz hf hLip β hhalf (hα s)
      (hα (s+(t:ℝ)/2)) z
    have H' := scalarStep_uniform_nonexpansive
      (scalarTimeStep_regular hf β (α (s+(t:ℝ)/2)) (t/2))
      (scalarTimeStep_regular hf β (α s) (t/2)) (hα s).1 H
      (β*Real.sqrt ((t/2:ℝ≥0):ℝ)) x
    change |scalarTimeStep β (α s) (t/2) _ x-scalarTimeStep β (α s) (t/2) _ x| ≤ _ at H'
    rw [scalarTimeStep_semigroup hf,show t/2+t/2=t by ring] at H'
    apply H'.trans
    rw [htc,abs_of_nonneg (sub_nonneg.mpr (hmono (by linarith [t.coe_nonneg])))]
    change scalarTimeMassConstant β*((t:ℝ)/2)*(α (s+(t:ℝ)/2)-α s) ≤ _
    have hM := hmono (show s+(t:ℝ)/2 ≤ s+(t:ℝ) by linarith [t.coe_nonneg])
    have hC := scalarTimeMassConstant_nonneg β
    calc
      _  ≤  scalarTimeMassConstant β*((t:ℝ)/2)*(α (s+t)-α s) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hM _) (by positivity)
      _ = _ := by ring
  | succ n ih =>
    rw [dyadicScalar_succ β α (n+1) s t f,dyadicScalar_succ β α n s t f]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    have htc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    let f₁ := dyadicScalar β α (n+1) (s+(t:ℝ)/2) (t/2) f
    let f₀ := dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f
    have hf₁ : BoundedDerivs f₁ := dyadicScalar_regular hf β α _ _ _
    have hf₀ : BoundedDerivs f₀ := dyadicScalar_regular hf β α _ _ _
    have hl₀ : LipschitzWith 1 f₀ := dyadicScalar_lipschitz hf hLip β hα _ _ _
    have H₁ := dyadicScalar_uniform_nonexpansive hf₁ hf₀ β hα (n+1) s (t/2)
      (fun z => ih hf hLip (s+(t:ℝ)/2) (t/2) hhalf z) x
    have H₂ := ih hf₀ hl₀ s (t/2) hhalf x
    calc
      _  ≤  |dyadicScalar β α (n+1) s (t/2) f₁ x-dyadicScalar β α (n+1) s (t/2) f₀ x|+
          |dyadicScalar β α (n+1) s (t/2) f₀ x-dyadicScalar β α n s (t/2) f₀ x| := abs_sub_le _ _ _
      _  ≤  _+_ := add_le_add H₁ H₂
      _ = _ := by rw [htc,show s+(t:ℝ)/2+(t:ℝ)/2=s+t by ring,pow_succ (2:ℝ) (n+1)]; ring

end SK.Analytic

end
end

end OAI
