import Mathlib
import OAI.Probability.SKGap.Matrix.WordLoopLeading
import OAI.Probability.SKGap.Localization.MarkedErrorRate

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

def wordMarkedCost (B : NNReal) (j R A c z : ℝ) (p q : ℕ) : ℝ :=
  markedRateConstant j R c ((p:NNReal)*B^p) ((q:NNReal)*B^q) (B^p) (B^q)
    (wordDifferentialBound B A z p) (wordDifferentialBound B A z q)

theorem actualWord_expected_recursion {n : ℕ} (hn : 0<n) (f : 𝓢(ℝ,ℂ))
    {j A D z : ℝ} (hj : 0<j) (hA : 0<A) (hD : 0≤D) (hs : sqrt j*A<1)
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(n:ℝ)))≤(1-sqrt j*A)^2/4)
    {a : Fin n→ℝ} (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (haD : ∀ i,|a i|≤D)
    (hz : z∈Icc (0:ℝ) 1) (P Q : List (WordLetter (Fin n)))
    (hP : ∀ l∈P,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : Fin n) :
    let R := 2*sqrt j+1+1
    let hR : 0≤R := by dsimp [R];positivity
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj.le hA.le hD).le⟩
    |wordExpected f hR j a z (P++(.noise::Q)) i-wordRecursionAtExpected f hR j a z P Q i|≤
      (wordMarkedCost B j R A (pathRate j A) z P.length Q.length+
        wordRecursionAtCost j B z a P Q)/(n:ℝ) := by
  intro R hR B
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hr : 0≤j/(n:ℝ) := by positivity
  have hh := actualWord_loop f (path_interval hj.le hA.le hs).1 hf hR hj.le hA.le hD hr ha haA hz P Q hP hQ i
  have hg := path_goodSet_exponential hj hA ha haA hs (by simpa only [Fintype.card_fin] using herr) hz
  have hd (k : ℕ) : 0≤wordDifferentialBound B A z k := by
    unfold wordDifferentialBound
    positivity
  have hb := markedError_absorption hn hj.le hR (pathRate_pos hj hA hs)
    (measureReal_nonneg) (by simpa only [Fintype.card_fin] using hg)
    ((P.length:NNReal)*B^P.length) ((Q.length:NNReal)*B^Q.length)
    (B^P.length) (B^Q.length) (hd P.length) (hd Q.length)
  have hl := actualWord_loop_leading hn f hR hj hA.le hD ha haA haD hz P Q hP hQ i
  simp only [Fintype.card_fin] at hh
  have he := hh.trans hb
  have he' : |wordExpected f hR j a z (P++(.noise::Q)) i-
      (j/(n:ℝ))*(∫ g : MatrixCoordinates (Fin n)→ℝ,
      actualWordLoop f hR j a z P Q (goeMatrix (j/n) g) i
        ∂Measure.pi (fun _=>gaussianReal 0 1))|≤
      wordMarkedCost B j R A (pathRate j A) z P.length Q.length/(n:ℝ) := by
    simpa only [wordExpected,Fintype.card_fin,wordMarkedCost] using he
  have ht := (abs_sub_le (wordExpected f hR j a z (P++(.noise::Q)) i)
    ((j/(n:ℝ))*(∫ g : MatrixCoordinates (Fin n)→ℝ,
      actualWordLoop f hR j a z P Q (goeMatrix (j/n) g) i
        ∂Measure.pi (fun _=>gaussianReal 0 1)))
      (wordRecursionAtExpected f hR j a z P Q i)).trans (add_le_add he' hl)
  simpa only [wordExpected,Fintype.card_fin,wordMarkedCost,add_div,B,NNReal.coe_mk] using! ht
end SKGap
end
end

end OAI
