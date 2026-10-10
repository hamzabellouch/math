import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationDeficits

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset WeightedRounding
variable {E T Ω : Type} [Fintype E] [DecidableEq T]

noncomputable def activationCount (D : E → Finset T) (m : E → ℕ)
    (S : Ω → E → Finset T) (t : T) (e : E) (ω : Ω) : ℕ :=
  if t ∈ D e then m e+if t ∈ S ω e then 1 else 0 else 0

omit [Fintype E] in
 theorem activationCount_cast (D : E → Finset T) (m : E → ℕ)
    (S : Ω → E → Finset T) (t : T) (e : E) (ω : Ω) :
    (activationCount D m S t e ω:ℝ)=activation D m S t e ω := by
  unfold activationCount activation indicator
  split_ifs <;> simp

theorem grid_clip {Δ : ℕ} {g : ℝ} (hg : 0 < g) (heven : Even Δ)
    (hunit : g*(Δ:ℝ)=1) (Z : ℕ) :
    min (g*(Z:ℝ)) (1/2)=g*(min Z (Δ/2):ℕ) ∧
    1-min (g*(Z:ℝ)) (1/2)=g*(Δ-min Z (Δ/2):ℕ) ∧
    (1/2:ℝ) ≤ g*(Δ-min Z (Δ/2):ℕ) ∧
    g*(Δ-min Z (Δ/2):ℕ) ≤ 1 := by
  have htwo : Δ/2+Δ/2=Δ := by
    obtain ⟨n,hn⟩ := heven
    omega
  have hhalf : g*(Δ/2:ℕ)= (1/2:ℝ) := by
    have hh : (Δ/2:ℕ)+(Δ/2:ℕ)=(Δ:ℝ) := by exact_mod_cast htwo
    have he := congrArg (fun x : ℝ => g*x) hh
    rw [mul_add,hunit] at he
    linarith only [he]
  have hle : min Z (Δ/2) ≤ Δ := (min_le_right _ _).trans (Nat.div_le_self _ _)
  have hc : min (g*(Z:ℝ)) (1/2)=g*(min Z (Δ/2):ℕ) := by
    rw [← hhalf,Nat.cast_min,mul_min_of_nonneg _ _ hg.le]
  have hm : 1-min (g*(Z:ℝ)) (1/2)=g*(Δ-min Z (Δ/2):ℕ) := by
    rw [hc,Nat.cast_sub hle,mul_sub,hunit]
  refine ⟨hc,hm,?_,?_⟩
  · rw [← hm]
    have hc' : min (g*(Z:ℝ)) (1/2) ≤ (1/2:ℝ) := min_le_right _ _
    linarith only [hc']
  · rw [← hm]
    have hz : 0 ≤ min (g*(Z:ℝ)) (1/2) := le_min (mul_nonneg hg.le (Nat.cast_nonneg _)) (by norm_num)
    linarith only [hz]

theorem deficit_cast (D : E → Finset T) (m : E → ℕ)
    (S : Ω → E → Finset T) (g : ℝ) (t : T) (ω : Ω) :
    deficit D m S g t ω=g*((∑ e, activationCount D m S t e ω):ℕ) := by
  simp only [deficit,Nat.cast_sum,activationCount_cast]

end MetricKMedian.Preparation
end
end

end OAI
