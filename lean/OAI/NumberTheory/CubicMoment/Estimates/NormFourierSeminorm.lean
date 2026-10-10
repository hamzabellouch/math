import OAI.NumberTheory.CubicMoment.Estimates.WideGramSeminormControl
import OAI.NumberTheory.CubicMoment.Estimates.NormDenominatorMellin

namespace OAI

/-! Finite seminorm control survives the norm-denominator multiplier
and Fourier transform, uniformly before choosing a shrinking profile. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem normDenominatorFourier_seminorm_control (M : ℝ) (hM : 0 < M) (k n K : ℕ) :
    ∃ (I : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ (F : 𝓢(ℂ,ℂ)) (c : ℝ), 0 ≤ c →
      (1+c)^K*SchwartzMap.seminorm ℝ k n
        (𝓕 (SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
          (wideAnnularLogSchwartz M hM F c))) ≤
        C*(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F := by
  let A : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.fourierTransformCLM ℝ (V := ℝ) (E := ℂ)).comp
      ((SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)).restrictScalars ℝ)
  let p := schwartzSeminormFamily ℝ ℝ ℂ
  let q := (SchwartzMap.seminorm ℝ k n).comp A.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (k,n)).comp A.continuous
  obtain ⟨s,C,hC,hA⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  choose D hD hwide using fun i : ℕ × ℕ =>
    wideAnnularLogSchwartz_seminorm_control M hM i.1 i.2 K
  let I := s.biUnion (fun i => Finset.Iic (i.2+K,i.2))
  let E := 1+∑ i ∈ s, D i
  have hE : 0 < E := by
    have hs : 0 ≤ ∑ i ∈ s, D i := Finset.sum_nonneg (fun i _ => (hD i).le)
    dsimp [E]
    linarith
  refine ⟨I,(C:ℝ)*E,mul_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC)) hE,?_⟩
  intro F c hc
  let B := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) F
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp : 0 < (1+c)^K := by positivity
  have hi (i : ℕ × ℕ) (his : i ∈ s) :
      (1+c)^K*(p i) (wideAnnularLogSchwartz M hM F c) ≤ E*B := by
    have hsub : Finset.Iic (i.2+K,i.2) ⊆ I := by
      intro m hm
      exact Finset.mem_biUnion.mpr ⟨i,his,hm⟩
    have hb := Seminorm.le_def.mp (show
        (Finset.Iic (i.2+K,i.2)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ≤
          I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) from Finset.sup_mono hsub) F
    have hd : D i ≤ E := by
      have hh := Finset.single_le_sum (fun j _ => (hD j).le) his
      dsimp [E]
      linarith
    exact (hwide i F c hc).trans ((mul_le_mul_of_nonneg_left hb (hD i).le).trans
      (mul_le_mul_of_nonneg_right hd hB))
  have hsup : (1+c)^K*(s.sup p) (wideAnnularLogSchwartz M hM F c) ≤ E*B := by
    rw [←le_div_iff₀' hp]
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i his
    exact (le_div_iff₀' hp).mpr (hi i his)
  have ht := Seminorm.le_def.mp hA (wideAnnularLogSchwartz M hM F c)
  change SchwartzMap.seminorm ℝ k n (A (wideAnnularLogSchwartz M hM F c)) ≤
    (C:ℝ)*(s.sup p) (wideAnnularLogSchwartz M hM F c) at ht
  calc
    _ ≤ (1+c)^K*((C:ℝ)*(s.sup p) (wideAnnularLogSchwartz M hM F c)) :=
      mul_le_mul_of_nonneg_left ht hp.le
    _ = (C:ℝ)*((1+c)^K*(s.sup p) (wideAnnularLogSchwartz M hM F c)) := by ring
    _ ≤ (C:ℝ)*(E*B) := mul_le_mul_of_nonneg_left hsup C.coe_nonneg
    _ = _ := by dsimp [B]; ring

end CubicFirstMoment

end

end OAI
