import OAI.NumberTheory.TotientAsymptotic.RenewalBackground
import OAI.NumberTheory.TotientAsymptotic.SimplexVolume

namespace OAI

/-! A renewal translate gives strict positive slack without losing dimension. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma renewal_translate_prefix {N : ℕ} {B t : ℝ} (ht : 0 ≤ t)
    {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0) :
    u+renewalBackground N t ∈ prefixRegion N B 0 0 ∧
      ∀ i,t*a (N-i.val) ≤ prefixLinear N (u+renewalBackground N t) i := by
  have hslack (i : Fin N) : t*a (N-i.val) ≤
      prefixLinear N (u+renewalBackground N t) i := by
    rw [map_add,Pi.add_apply,renewalBackground_slack]
    have hh := hu.1 i
    change 0 ≤ prefixLinear N u i at hh
    linarith only [hh]
  refine ⟨⟨?_,?_⟩,hslack⟩
  · intro i
    exact (mul_nonneg ht (a_pos (by have := i.isLt; omega)).le).trans (hslack i)
  · change (∑ i : Fin N,a (i.val+1)*(u i+renewalBackground N t i)) ≤ B-0
    simp only [mul_add,Finset.sum_add_distrib,renewalBackground_top,sub_zero]
    have hh := hu.2
    simp only [sub_zero] at hh
    linarith only [hh]

lemma renewal_translated_volume (N : ℕ) (hN : 0 < N) (B t : ℝ) :
    volume {v : Fin N → ℝ |
      v-renewalBackground N t ∈
        prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0} =
      ENNReal.ofReal ((max (B-t*(g (N+1)-a (N+1))) 0)^N/
        ((N.factorial:ℝ)*∏ i : Fin N,g (i.val+1))) := by
  have hh := measure_preimage_add_right (volume : Measure (Fin N → ℝ))
    (-renewalBackground N t) (prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0)
  change volume ((fun v => v-renewalBackground N t) ⁻¹'
    prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0)=_ 
  rw [show (fun v : Fin N → ℝ => v-renewalBackground N t)=
    (fun v => v+(-renewalBackground N t)) by rfl,hh]
  rw [volume_prefixRegion_explicit N hN]
  simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,sub_zero]

end TotientAsymptotic

end

end OAI
