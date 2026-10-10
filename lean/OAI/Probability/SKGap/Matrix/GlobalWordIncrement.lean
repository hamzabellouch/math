import Mathlib
import OAI.Probability.SKGap.Matrix.WordIncrement

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def globalWordHolder (f : 𝓢(ℝ,ℂ)) (R j A D : ℝ) : ℝ :=
  wordHolderScale f R j A+2*actualWordBound f R j A D+1
lemma globalWordHolder_nonneg (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    0 ≤ globalWordHolder f R j A D := by
  have hh := wordHolderScale_ge_one f R A hj
  have hb := actualWordBound_pos f hR hj hA hD
  dsimp [globalWordHolder]
  linarith

lemma WordLetter.eval_pair_global [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D δ : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    {a b : ι→ℝ} (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i) (haA : ∀ i,a i ≤ A) (hbA : ∀ i,b i ≤ A)
    (hab : ∀ i,|a i-b i| ≤ δ) (l m : WordLetter ι) (hl : l.bounded D) (hm : m.bounded D)
    (hlm : l.close δ m) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨globalWordHolder f R j A D*sqrt δ,mul_nonneg (globalWordHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)⟩
    MatrixFactorPairBounds B Δ (l.eval f R hR j a 1) (m.eval f R hR j b 1) := by
  intro B Δ
  have hG : wordHolderScale f R j A ≤ globalWordHolder f R j A D := by
    have hh := actualWordBound_pos f hR hj hA hD
    dsimp [globalWordHolder]
    linarith
  by_cases hs : δ ≤ 1
  · have hh := l.eval_pair f hR hj hA hD hδ hs ha hb haA hbA hab m hl hm hlm
    have hΔ : (⟨wordHolderScale f R j A*sqrt δ,mul_nonneg (zero_le_one.trans (wordHolderScale_ge_one f R A hj)) (sqrt_nonneg _)⟩:NNReal) ≤ Δ :=
      mul_le_mul_of_nonneg_right hG (sqrt_nonneg _)
    exact ⟨hh.leftBound,hh.rightBound,hh.leftLip,hh.rightLip,
      fun M=>(hh.parameter M).trans hΔ,hh.increment.weaken hΔ⟩
  · have hδ1 : 1 ≤ sqrt δ := by simpa only [sqrt_one] using sqrt_le_sqrt (le_of_not_ge hs)
    have hGB : 2*(B:ℝ) ≤ globalWordHolder f R j A D := by
      have hh := wordHolderScale_ge_one f R A hj
      change 2*actualWordBound f R j A D ≤ wordHolderScale f R j A+2*actualWordBound f R j A D+1
      linarith
    have hBΔ : 2*(B:ℝ) ≤ (Δ:ℝ) := by
      change 2*(B:ℝ) ≤ globalWordHolder f R j A D*sqrt δ
      exact (le_mul_of_one_le_right (by positivity : 0 ≤ 2*(B:ℝ)) hδ1).trans
        (mul_le_mul_of_nonneg_right hGB (sqrt_nonneg _))
    obtain ⟨h1,h2⟩ := l.eval_bounds f hR hj hA hD ha haA ⟨zero_le_one,le_rfl⟩ hl
    obtain ⟨h3,h4⟩ := m.eval_bounds f hR hj hA hD hb hbA ⟨zero_le_one,le_rfl⟩ hm
    refine ⟨h1,h3,h2,h4,?_,?_⟩
    · intro M
      exact (opNorm_sub _ _).trans ((add_le_add (h1 M) (h3 M)).trans (by
        change actualWordBound f R j A D + actualWordBound f R j A D ≤ (Δ:ℝ)
        change 2*actualWordBound f R j A D ≤ (Δ:ℝ) at hBΔ
        linarith))
    · apply LipschitzWith.of_dist_le_mul
      intro M N
      rw [dist_eq_norm]
      have he : (l.eval f R hR j a 1 M-m.eval f R hR j b 1 M)-
          (l.eval f R hR j a 1 N-m.eval f R hR j b 1 N)=
          (l.eval f R hR j a 1 M-l.eval f R hR j a 1 N)-
          (m.eval f R hR j b 1 M-m.eval f R hR j b 1 N) := by abel
      rw [he]
      apply (norm_sub_le _ _).trans
      have h2' := h2.dist_le_mul M N
      have h4' := h4.dist_le_mul M N
      rw [dist_eq_norm] at h2' h4'
      calc
        _ ≤ (B:ℝ)*dist M N+(B:ℝ)*dist M N := add_le_add h2' h4'
        _ = (2*(B:ℝ))*dist M N := by ring
        _ ≤ (Δ:ℝ)*dist M N := mul_le_mul_of_nonneg_right hBΔ dist_nonneg

theorem actualWord_pair_global [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D δ : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    {a b : ι→ℝ} (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i) (haA : ∀ i,a i ≤ A) (hbA : ∀ i,b i ≤ A)
    (hab : ∀ i,|a i-b i| ≤ δ) (F : List (WordLetter ι×WordLetter ι))
    (hF : ∀ p∈F,p.1.bounded D ∧ p.2.bounded D ∧ p.1.close δ p.2) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨globalWordHolder f R j A D*sqrt δ,mul_nonneg (globalWordHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)⟩
    (∀ M,opNorm (actualWord f R hR j a 1 (F.map Prod.fst) M-actualWord f R hR j b 1 (F.map Prod.snd) M) ≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ)
      (fun M=>actualWord f R hR j a 1 (F.map Prod.fst) M-actualWord f R hR j b 1 (F.map Prod.snd) M) := by
  intro B Δ
  let G := F.map (fun p=>(p.1.eval f R hR j a 1,p.2.eval f R hR j b 1))
  have hG : ∀ p∈G,MatrixFactorPairBounds B Δ p.1 p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1,h2,h3⟩ := hF q hq
    exact WordLetter.eval_pair_global f hR hj hA hD hδ ha hb haA hbA hab q.1 q.2 h1 h2 h3
  simpa only [G,List.length_map,List.map_map,Function.comp_def,actualWord] using! matrixWord_pair_increments G hG
end SKGap
end
end

end OAI
