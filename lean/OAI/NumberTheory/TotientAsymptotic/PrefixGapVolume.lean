import OAI.NumberTheory.TotientAsymptotic.PrefixGapWeights
import OAI.NumberTheory.TotientAsymptotic.SimplexExponential
import OAI.NumberTheory.TotientAsymptotic.PrefixConcentration

namespace OAI

/-! Exponential control of inversions in ordered prime-coordinate regions. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

theorem prefix_gap_cap_volume : ∃ A c s : ℝ,0 < A ∧ 0 < c ∧ 0 < s ∧
    ∀ (N : ℕ) (i : Fin (N+1)) (B T : ℝ),0 < B → 0 ≤ T → s*T ≤ B →
      volume.real (standardSimplex (N+2) B ∩
        {v | (∑ j,prefixGapWeight N i j*v j) ≤ -T}) ≤
      Real.exp (A-c*(N+2-i.val:ℕ)-s*(N+2:ℝ)*T/B)*
        volume.real (standardSimplex (N+2) B) := by
  obtain ⟨M,K,hM,hK,hw⟩ := prefix_gap_weight_bounds
  let d := 1-rho
  let s := d/(32*M)
  have hd : 0 < d := sub_pos.mpr rho_lt_one
  have hd1 : d ≤ 1 := by dsimp [d]; linarith only [rho_pos]
  have hs : 0 < s := div_pos hd (by positivity)
  have hsM : s*M=d/32 := by dsimp [s]; field_simp
  have hsM2 : s*M ≤ 1/2 := by rw [hsM]; linarith only [hd1]
  let A := 2*s*K+8*s^2*M*K
  let c := s*d/2
  have hA : 0 < A := by dsimp [A]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨A,c,s,hA,hc,hs,?_⟩
  intro N i B T hB _hT hTB
  obtain ⟨hpoint,hmean,hsq⟩ := hw N i
  have hweight (j) : -(1/2:ℝ) ≤ s*prefixGapWeight N i j := by
    have hh := mul_le_mul_of_nonneg_left (hpoint j).1 hs.le
    nlinarith only [hh,hsM2]
  have hbudget : 0 ≤ B+s*(-T) := by linarith only [hTB]
  have hv := volume_simplex_lower_cap_exp (N+2) hB (-T) s
    (prefixGapWeight N i) hs.le hweight hbudget
  apply hv.trans
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply Real.exp_le_exp.mpr
  have hq := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2*s^2 by positivity)
  have hcancel : 8*s^2*M=s*d/4 := by
    calc
      _ = 8*s*(s*M) := by ring
      _ = _ := by rw [hsM]; ring
  have hn : 0 ≤ ((N+2-i.val:ℕ):ℝ) := Nat.cast_nonneg _
  dsimp only [A,c]
  change d*((N+2-i.val:ℕ):ℝ)-2*K ≤ _ at hmean
  have hmean' := mul_le_mul_of_nonneg_left hmean hs.le
  simp only [mul_add] at hq
  have hqe : 2*s^2*(4*M*((N+2-i.val:ℕ):ℝ))+2*s^2*(4*M*K)=
      (s*d/4)*((N+2-i.val:ℕ):ℝ)+8*s^2*M*K := by
    calc
      _ = (8*s^2*M)*((N+2-i.val:ℕ):ℝ)+8*s^2*M*K := by ring
      _ = _ := by rw [hcancel]
  rw [hqe] at hq
  have hnon := mul_nonneg (mul_nonneg hs.le hd.le) hn
  have he : ((N+2:ℕ):ℝ)*(s*(-T)/B)= -(s*(N+2:ℝ)*T/B) := by
    push_cast
    ring
  rw [he]
  nlinarith only [hmean',hq,hnon]

lemma prefix_gap_bad_preimage (N : ℕ) (i : Fin (N+1)) (B T : ℝ) :
    prefixRegion (N+2) B 0 0 ∩
      {u | u i.castSucc-u i.succ ≤ -rho^(i.val+1)*T} =
      prefixSimplexMap (N+2) ⁻¹'
        (standardSimplex (N+2) B ∩
          {v | (∑ j,prefixGapWeight N i j*v j) ≤ -T}) := by
  rw [prefixSimplexMap_preimage]
  ext u
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq]
  rw [← prefix_gap_coordinate]
  have hr := pow_pos rho_pos (i.val+1)
  rw [div_le_iff₀ hr]
  have he : -T*rho^(i.val+1)= -rho^(i.val+1)*T := by ring
  rw [he]

theorem prefix_gap_volume : ∃ A c s : ℝ,0 < A ∧ 0 < c ∧ 0 < s ∧
    ∀ (N : ℕ) (i : Fin (N+1)) (B T : ℝ),0 < B → 0 ≤ T → s*T ≤ B →
      volume.real (prefixRegion (N+2) B 0 0 ∩
        {u | u i.castSucc-u i.succ ≤ -rho^(i.val+1)*T}) ≤
      Real.exp (A-c*(N+2-i.val:ℕ)-s*(N+2:ℝ)*T/B)*
        volume.real (prefixRegion (N+2) B 0 0) := by
  obtain ⟨A,c,s,hA,hc,hs,hbound⟩ := prefix_gap_cap_volume
  refine ⟨A,c,s,hA,hc,hs,?_⟩
  intro N i B T hB hT hTB
  rw [prefix_gap_bad_preimage]
  apply prefixSimplexMap_transfer
  · apply (measurableSet_standardSimplex _ _).inter
    exact measurableSet_le (by fun_prop) measurable_const
  · exact hbound N i B T hB hT hTB

end TotientAsymptotic

end

end OAI
