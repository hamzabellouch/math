import OAI.Analysis.AncientFlat.Evolution.LocalExtensionAlgebra

namespace OAI
noncomputable section
open Set Filter
namespace LocalSemigroupExtension
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (U : ℝ → (X →L[ℂ] X)) (h0 : U 0=1)
  (hadd : ∀ s t : ℝ, 0  ≤  s → 0 ≤ t → s+t ≤ 1 → U (s+t)=U s*U t)
  (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ t ∈ Icc (0:ℝ) 1, ‖U t‖ ≤ K)
include hbound in
lemma extend_bounded (T : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0:ℝ) T, ‖extend U t‖ ≤ M := by
  let B : ℝ := max 1 K
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hu1 : ‖U 1‖ ≤ B := (hbound 1 ⟨zero_le_one,le_rfl⟩).trans (le_max_right _ _)
  have hp (n : ℕ) : ‖U 1^n‖ ≤ B^n := by
    induction n with
    | zero =>
        rw [pow_zero,pow_zero]
        exact ContinuousLinearMap.norm_id_le
    | succ n ih =>
        rw [pow_succ,pow_succ]
        exact (norm_mul_le _ _).trans (mul_le_mul ih hu1 (norm_nonneg _) (pow_nonneg hB0 n))
  refine ⟨B^(⌊T⌋₊+1),by positivity,fun t ht => ?_⟩
  have hr : t-(⌊t⌋₊:ℝ) ∈ Icc (0:ℝ) 1 :=
    ⟨sub_nonneg.mpr (Nat.floor_le ht.1),by linarith [Nat.lt_floor_add_one t]⟩
  calc
    ‖extend U t‖ ≤ ‖U (t-(⌊t⌋₊:ℝ))‖*‖U 1^⌊t⌋₊‖ := norm_mul_le _ _
    _ ≤ B*B^⌊t⌋₊ := mul_le_mul ((hbound _ hr).trans (le_max_right _ _)) (hp _)
      (norm_nonneg _) hB0
    _=B^(⌊t⌋₊+1) := (pow_succ' _ _).symm
    _ ≤ B^(⌊T⌋₊+1) := pow_le_pow_right₀ hB (Nat.add_le_add_right (Nat.floor_mono ht.2) 1)
include h0 hadd in
lemma extend_sub_bound (M : ℝ) (s t : ℝ) (hs : 0  ≤  s) (ht : 0 ≤ t)
    (hMs : ‖extend U s‖ ≤ M) (hMt : ‖extend U t‖ ≤ M) (d : X) :
    ‖extend U s d-extend U t d‖ ≤ M*‖extend U |s-t| d-d‖ := by
  by_cases hst : t ≤ s
  · have hi := extend_add U h0 hadd t (s-t) ht (sub_nonneg.mpr hst)
    have he : t+(s-t)=s := by ring
    rw [he] at hi
    rw [abs_of_nonneg (sub_nonneg.mpr hst),hi,mul_apply_eq_comp,←map_sub]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hMt (norm_nonneg _))
  · have hts : s ≤ t := le_of_not_ge hst
    have hi := extend_add U h0 hadd s (t-s) hs (sub_nonneg.mpr hts)
    have he : s+(t-s)=t := by ring
    rw [he] at hi
    rw [abs_of_nonpos (sub_nonpos.mpr hts),neg_sub,norm_sub_rev,hi,
      mul_apply_eq_comp,←map_sub]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hMs (norm_nonneg _))
include h0 hadd hbound in
lemma extend_continuous (hcont : ∀ d : X, ContinuousOn (fun t => U t d) (Icc (0:ℝ) 1)) (d : X) :
    ContinuousOn (fun t => extend U t d) (Ici (0:ℝ)) := by
  intro t ht
  obtain ⟨M,hM,hMb⟩ := extend_bounded U K hbound (t+1)
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  have heps : 0 < ε/(M+1) := div_pos hε (by linarith)
  obtain ⟨η,hη,Hη⟩ := Metric.continuousWithinAt_iff.mp
    ((hcont d).continuousWithinAt ⟨le_rfl,zero_le_one⟩) (ε/(M+1)) heps
  refine ⟨min 1 η,lt_min zero_lt_one hη,fun s hs hst => ?_⟩
  have habs : |s-t| < min 1 η := by simpa only [Real.dist_eq] using hst
  have hsT : s ∈ Icc (0:ℝ) (t+1) := ⟨hs,by have := (abs_lt.mp (habs.trans_le (min_le_left _ _))).2; linarith⟩
  have htT : t ∈ Icc (0:ℝ) (t+1) := ⟨ht,by linarith⟩
  have hδ : |s-t| ∈ Icc (0:ℝ) 1 := ⟨abs_nonneg _,(habs.trans_le (min_le_left _ _)).le⟩
  have hsmall : ‖U |s-t| d-d‖ < ε/(M+1) := by
    have hh := Hη hδ (by simpa only [Real.dist_eq,sub_zero,abs_abs] using habs.trans_le (min_le_right (1:ℝ) η))
    simpa only [h0,one_apply_eq_self,dist_eq_norm] using hh
  rw [dist_eq_norm]
  calc
    _ ≤ M*‖extend U |s-t| d-d‖ := extend_sub_bound U h0 hadd M s t hs ht (hMb s hsT) (hMb t htT) d
    _=M*‖U |s-t| d-d‖ := by rw [extend_unit U h0 _ hδ]
    _ ≤ (M+1)*‖U |s-t| d-d‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (M+1)*(ε/(M+1)) := mul_lt_mul_of_pos_left hsmall (by linarith)
    _=ε := by field_simp
end LocalSemigroupExtension

end

end OAI
