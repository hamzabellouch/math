import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMellinRows

namespace OAI

/-! Exact shortening for a divisor-restricted stopped row. The shortened
coefficient remains the original coefficient evaluated at d*n; no new
prime-factor independence is asserted. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stoppedDivisorSlice (ι : Type*) [Fintype ι] [DecidableEq ι]
    (X l b : ℝ) (e d : Eisenstein) : Finset Eisenstein :=
  (primaryElementBall (b/norm d)).filter
    (fun n => d*n ∈ stoppedIntervalSupport ι X l b e)

lemma stoppedDivisorSlice_spec (X l b : ℝ) (e d : Eisenstein)
    {n : Eisenstein} (hn : n ∈ stoppedDivisorSlice ι X l b e d) :
    primary n ∧ Squarefree n ∧ norm n ≤ b/norm d := by
  obtain ⟨hm,hp⟩ := Finset.mem_filter.mp hn
  have hs := (stoppedIntervalSupport_spec X l b e hp).2.1
  exact ⟨(mem_primaryElementBall.mp hm).1,
    hs.squarefree_of_dvd (dvd_mul_left _ _),(mem_primaryElementBall.mp hm).2⟩

lemma stoppedDivisorSlice_complete (X l b : ℝ) (e : Eisenstein)
    {d : Eisenstein} (hd : primary d) (n : Eisenstein)
    (hn : d*n ∈ stoppedIntervalSupport ι X l b e) :
    n ∈ stoppedDivisorSlice ι X l b e d := by
  have hp := stoppedIntervalSupport_spec X l b e hn
  apply Finset.mem_filter.mpr
  refine ⟨mem_primaryElementBall.mpr ⟨primary_of_mul hd hp.1,?_⟩,hn⟩
  apply (le_div_iff₀ (norm_pos_of_ne_zero (primary_ne_zero hd))).mpr
  simpa only [norm_mul_eq,mul_comm] using hp.2.2

theorem stopped_divisor_sum_eq_slice (X l b : ℝ) (e : Eisenstein)
    {d : Eisenstein} (hd : primary d) (F : Eisenstein → ℂ) :
    (∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n), F n) =
      ∑ n ∈ stoppedDivisorSlice ι X l b e d, F (d*n) := by
  symm
  apply Finset.sum_bij (fun n _ => d*n)
  · intro n hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).2,dvd_mul_right _ _⟩
  · intro n _ m _ hnm
    exact mul_left_cancel₀ (primary_ne_zero hd) hnm
  · intro n hn
    obtain ⟨m,hm⟩ := (Finset.mem_filter.mp hn).2
    refine ⟨m,?_,hm.symm⟩
    apply stoppedDivisorSlice_complete X l b e hd
    simpa only [←hm] using (Finset.mem_filter.mp hn).1
  · intro n _
    rfl

theorem stopped_divisor_character_sum (X w z l b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e v : Eisenstein)
    {d : Eisenstein} (hd : primary d) :
    (∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
      stoppedRowCoefficient X w z u W selected n*cubicSymbol n v) =
      cubicSymbol d v*∑ n ∈ stoppedDivisorSlice ι X l b e d,
        stoppedRowCoefficient X w z u W selected (d*n)*cubicSymbol n v := by
  rw [stopped_divisor_sum_eq_slice X l b e hd,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [cubicSymbol_mul_lower (primary_ne_zero hd)
    (primary_ne_zero (stoppedDivisorSlice_spec X l b e d hn).1)]
  ring

theorem stopped_divisor_character_norm_le (X w z l b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e v : Eisenstein)
    {d : Eisenstein} (hd : primary d) :
    ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
      stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖ ≤
      ‖∑ n ∈ stoppedDivisorSlice ι X l b e d,
        stoppedRowCoefficient X w z u W selected (d*n)*cubicSymbol n v‖ := by
  rw [stopped_divisor_character_sum X w z l b u W selected e v hd,norm_mul]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hd v)

theorem stopped_slice_energy (X w z l b u M : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e d : Eisenstein)
    (hb : 0 ≤ b)
    (hcoeff : ∀ n ∈ stoppedIntervalSupport ι X l b e,
      ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) :
    (∑ n ∈ stoppedDivisorSlice ι X l b e d,
      ‖stoppedRowCoefficient X w z u W selected (d*n)‖^2) ≤
        18*(b/norm d)*M^2 := by
  have hc := primary_support_card_le (stoppedDivisorSlice ι X l b e d)
    (div_nonneg hb (norm_nonneg d))
    (fun n hn => ⟨(stoppedDivisorSlice_spec X l b e d hn).1,
      (stoppedDivisorSlice_spec X l b e d hn).2.2⟩)
  calc
    _ ≤ ∑ _n ∈ stoppedDivisorSlice ι X l b e d, M^2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hcoeff _ (Finset.mem_filter.mp hn).2) 2
    _ = ((stoppedDivisorSlice ι X l b e d).card:ℝ)*M^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg M)

end CubicFirstMoment

end

end OAI
