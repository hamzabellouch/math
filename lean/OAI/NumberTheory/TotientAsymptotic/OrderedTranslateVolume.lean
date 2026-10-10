import OAI.NumberTheory.TotientAsymptotic.TranslatedOrder
import OAI.NumberTheory.TotientAsymptotic.PrefixBudgetLower

namespace OAI

/-! Positive volume of the ordered part of a renewal translate. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

def orderedSlackRegion (N : ℕ) (B t : ℝ) : Set (Fin N → ℝ) :=
  {v | v ∈ prefixRegion N B 0 0 ∧ StrictAnti v ∧
    ∀ i,t*a (N-i.val) ≤ prefixLinear N v i}

lemma prefix_budget_volume_lower {N : ℕ} (hN : 0 < N)
    {B E : ℝ} (hB : 0 < B) (hE : 0 ≤ E) (hEB : 2*E ≤ B) :
    Real.exp (-2*(N:ℝ)*E/B)*volume.real (prefixRegion N B 0 0) ≤
      volume.real (prefixRegion N (B-E) 0 0) := by
  have hBE : 0 ≤ B-E := by linarith only [hE,hEB]
  have hd : 0 < ((N.factorial:ℝ)*∏ i : Fin N,g (i.val+1)) :=
    mul_pos (by exact_mod_cast Nat.factorial_pos N)
      (Finset.prod_pos (fun i _ => g_pos _))
  have hp := prefix_budget_power_lower hB hE hEB N
  simp only [Measure.real,volume_prefixRegion_explicit N hN,Pi.zero_apply,
    mul_zero,Finset.sum_const_zero,sub_zero,max_eq_left hB.le,max_eq_left hBE,
    ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hB.le N) hd.le),
    ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hBE N) hd.le)]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hp hd.le

lemma ordered_translate_half_volume {N : ℕ} (hN : 0 < N) {B t : ℝ}
    (ht : 0 ≤ t)
    (hbad : volume.real {u : Fin N → ℝ |
      u ∈ prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0 ∧
        ¬StrictAnti (fun i => u i+renewalBackground N t i)} ≤
      volume.real (prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0)/2) :
    volume.real (prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0)/2 ≤
      volume.real (orderedSlackRegion N B t) := by
  classical
  let S := prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0
  let U : Set (Fin N → ℝ) :=
    {u | u ∈ S ∧ StrictAnti (fun i => u i+renewalBackground N t i)}
  let E : Set (Fin N → ℝ) :=
    {u | u ∈ S ∧ ¬StrictAnti (fun i => u i+renewalBackground N t i)}
  have hsplit : S = U ∪ E := by
    ext u
    simp only [U,E,Set.mem_union,Set.mem_ofPred_eq]
    tauto
  have hsum : volume.real S ≤ volume.real U+volume.real E := by
    rw [hsplit]
    exact measureReal_union_le _ _
  have hhalf : volume.real S/2 ≤ volume.real U := by
    change volume.real E ≤ volume.real S/2 at hbad
    linarith only [hsum,hbad]
  have hsub : U ⊆ (fun u : Fin N → ℝ => u+renewalBackground N t) ⁻¹'
      orderedSlackRegion N B t := by
    intro u hu
    have hh := renewal_translate_prefix ht hu.1
    exact ⟨hh.1,hu.2,hh.2⟩
  have hshift := measure_preimage_add_right (volume : Measure (Fin N → ℝ))
    (renewalBackground N t) (orderedSlackRegion N B t)
  have htarget : volume (orderedSlackRegion N B t) ≠ ⊤ :=
    measure_ne_top_of_subset (fun _ hv => hv.1) (prefixRegion_volume_ne_top hN B)
  have hmono := measureReal_mono hsub (by rw [hshift]; exact htarget)
  simp only [Measure.real,hshift] at hmono
  exact hhalf.trans hmono

theorem ordered_translate_volume : ∃ A c s : ℝ,0 < A ∧ 0 < c ∧ 0 < s ∧
    ∀ (N : ℕ) (B t T : ℝ),0 < B → 0 ≤ t →
      0 ≤ t*(g (N+3)-a (N+3)) → 2*t*(g (N+3)-a (N+3)) ≤ B →
      0 ≤ T → s*T ≤ B-t*(g (N+3)-a (N+3)) →
      (∀ i : Fin (N+1),rho^(i.val+1)*T ≤
        renewalBackground (N+2) t i.castSucc-renewalBackground (N+2) t i.succ) →
      Real.exp (A-s*(N+2:ℝ)*T/(B-t*(g (N+3)-a (N+3))))/
        (1-Real.exp (-c)) ≤ 1/2 →
      Real.exp (-2*(N+2:ℝ)*t*(g (N+3)-a (N+3))/B)/2*
        volume.real (prefixRegion (N+2) B 0 0) ≤
      volume.real (orderedSlackRegion (N+2) B t) := by
  obtain ⟨A,c,s,hA,hc,hs,hbound⟩ := translated_prefix_inversions
  refine ⟨A,c,s,hA,hc,hs,?_⟩
  intro N B t T hB ht hE hEB hT hTB hgap hsmall
  have hB' : 0 < B-t*(g (N+3)-a (N+3)) := by
    nlinarith only [hB,hEB,hE]
  have heq : N+2+1=N+3 := by omega
  have hbad := hbound N (B-t*(g (N+3)-a (N+3))) t T hB' hT hTB hgap
  have hbad' : volume.real {u : Fin (N+2) → ℝ |
      u ∈ prefixRegion (N+2) (B-t*(g (N+3)-a (N+3))) 0 0 ∧
        ¬StrictAnti (fun i => u i+renewalBackground (N+2) t i)} ≤
      volume.real (prefixRegion (N+2) (B-t*(g (N+3)-a (N+3))) 0 0)/2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ volume.real (prefixRegion (N+2) (B-t*(g (N+3)-a (N+3))) 0 0)
        from ENNReal.toReal_nonneg)
    exact hbad.trans (by nlinarith only [hh])
  have hhalf := ordered_translate_half_volume (by omega : 0 < N+2) ht
    (by simpa only [heq] using hbad')
  have hvol := prefix_budget_volume_lower (by omega : 0 < N+2) hB hE
    (by simpa only [mul_assoc] using hEB)
  have hh := div_le_div_of_nonneg_right hvol (by norm_num : (0:ℝ) ≤ 2)
  have harg : -2*((N+2:ℕ):ℝ)*(t*(g (N+3)-a (N+3)))/B=
      -2*(N+2:ℝ)*t*(g (N+3)-a (N+3))/B := by push_cast; ring
  rw [harg] at hh
  apply le_trans _ (by simpa only [heq] using hhalf)
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
