import OAI.NumberTheory.TotientAsymptotic.TranslatedPrefix
import OAI.NumberTheory.TotientAsymptotic.PrefixGapVolume

namespace OAI

/-! Summing adjacent inversions in the translated prime-coordinate region. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma finite_gap_exponential_sum {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (∑ i : Fin (N+1),Real.exp (-c*((N+2-i.val:ℕ):ℝ))) ≤
      1/(1-Real.exp (-c)) := by
  classical
  let q := Real.exp (-c)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hinj : Set.InjOn (fun i : Fin (N+1) => N+2-i.val)
      ↑(Finset.univ : Finset (Fin (N+1))) := by
    intro i _ j _ he
    apply Fin.ext
    change N+2-i.val=N+2-j.val at he
    have := i.isLt
    have := j.isLt
    omega
  have he (i : Fin (N+1)) : Real.exp (-c*((N+2-i.val:ℕ):ℝ))=q^(N+2-i.val) := by
    dsimp [q]
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [he]
  rw [←Finset.sum_image hinj]
  have hs := hasSum_geometric_of_lt_one hq hq1
  simpa only [one_div,q] using
    (hs.summable.sum_le_tsum _ (fun k _ => pow_nonneg hq k)).trans_eq hs.tsum_eq

theorem translated_prefix_inversions : ∃ A c s : ℝ,0 < A ∧ 0 < c ∧ 0 < s ∧
    ∀ (N : ℕ) (B t T : ℝ),0 < B → 0 ≤ T → s*T ≤ B →
      (∀ i : Fin (N+1),rho^(i.val+1)*T ≤
        renewalBackground (N+2) t i.castSucc-renewalBackground (N+2) t i.succ) →
      volume.real {u : Fin (N+2) → ℝ | u ∈ prefixRegion (N+2) B 0 0 ∧
        ¬StrictAnti (fun i => u i+renewalBackground (N+2) t i)} ≤
      (Real.exp (A-s*(N+2:ℝ)*T/B)/(1-Real.exp (-c)))*
        volume.real (prefixRegion (N+2) B 0 0) := by
  classical
  obtain ⟨A,c,s,hA,hc,hs,hbound⟩ := prefix_gap_volume
  refine ⟨A,c,s,hA,hc,hs,?_⟩
  intro N B t T hB hT hTB hgap
  let S := prefixRegion (N+2) B 0 0
  let E (i : Fin (N+1)) := S ∩
    {u | u i.castSucc-u i.succ ≤ -rho^(i.val+1)*T}
  have hsub : {u : Fin (N+2) → ℝ | u ∈ S ∧
      ¬StrictAnti (fun i => u i+renewalBackground (N+2) t i)} ⊆ ⋃ i,E i := by
    intro u hu
    have hn := hu.2
    rw [Fin.strictAnti_iff_succ_lt] at hn
    push Not at hn
    obtain ⟨i,hi⟩ := hn
    apply Set.mem_iUnion.mpr
    refine ⟨i,hu.1,?_⟩
    have hg := hgap i
    change u i.castSucc-u i.succ ≤ -rho^(i.val+1)*T
    nlinarith only [hi,hg]
  have hfinite : volume (⋃ i,E i) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume S ≠ ⊤ from ?_)
      (measure_mono (by intro u hu; obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu; exact hi.1))
    dsimp [S]
    rw [volume_prefixRegion_explicit (N+2) (by omega)]
    exact ENNReal.ofReal_ne_top
  have hmeasure := ENNReal.toReal_mono hfinite (measure_mono hsub)
  apply hmeasure.trans
  apply (measureReal_iUnion_fintype_le E).trans
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbound N i B T hB hT hTB)
  apply hsum.trans
  have he (i : Fin (N+1)) :
      Real.exp (A-c*((N+2-i.val:ℕ):ℝ)-s*(N+2:ℝ)*T/B)=
        Real.exp (A-s*(N+2:ℝ)*T/B)*Real.exp (-c*((N+2-i.val:ℕ):ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [←Finset.sum_mul,←Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (finite_gap_exponential_sum hc N)
    (Real.exp_pos (A-s*(N+2:ℝ)*T/B)).le
  simpa only [div_eq_mul_inv,mul_assoc,one_mul,S] using
    mul_le_mul_of_nonneg_right hh (show 0 ≤ volume.real S from ENNReal.toReal_nonneg)

end TotientAsymptotic

end

end OAI
