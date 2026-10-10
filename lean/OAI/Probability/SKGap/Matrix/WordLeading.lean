import Mathlib
import OAI.Probability.SKGap.Matrix.WordBaseBias

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actualWord_entry_integrable [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z r : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (i b : ι) :
    Integrable (fun g : MatrixCoordinates ι→ℝ=>actualWord f R hR j a z F (goeMatrix r g) i b)
      (Measure.pi (fun _=>gaussianReal 0 1)) := by
  have hw := actualWord_bounds f hR hj hA hD ha haA hz F hF
  have hc := hw.2.continuous.comp (goeMatrix_pi_lipschitz (ι:=ι) r).continuous
  have he : Continuous (fun g : MatrixCoordinates ι→ℝ=>actualWord f R hR j a z F (goeMatrix r g) i b) :=
    (continuous_apply b).comp ((continuous_apply i).comp hc)
  exact (integrable_const ((actualWordBound f R j A D)^F.length)).mono' he.aestronglyMeasurable
    (ae_of_all _ (fun g=>(matrix_entry_le_opNorm _ i b).trans (hw.1 _)))

def wordAverageExpected (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) : ℝ :=
  (∑ i,wordExpected f hR j a z F i)/(Fintype.card ι:ℝ)

lemma wordAverageExpected_integral [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) :
    (∫ g : MatrixCoordinates ι→ℝ,trace (actualWord f R hR j a z F
      (goeMatrix (j/(Fintype.card ι:ℝ)) g))/(Fintype.card ι:ℝ)
        ∂Measure.pi (fun _=>gaussianReal 0 1))=wordAverageExpected f hR j a z F := by
  rw [integral_div]
  unfold trace
  simp only [Matrix.diag]
  rw [integral_finsetSum _ (fun i _=>actualWord_entry_integrable f hR hj hA hD ha haA hz F hF i i)]
  rfl

def wordLeadingCost (j B : ℝ) (u v q : ℕ) : ℝ :=
  j*(B^u*B^q*((2*exp (π^2/8))*((v:ℝ)*B^v)*sqrt (2*j))+B^u*B^v*B^q)

theorem actualWord_leading {n : ℕ} (hn : 0<n) (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0<j) (hA : 0≤A) (hD : 0≤D) {a : Fin n→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (U V Q : List (WordLetter (Fin n))) (hU : ∀ l∈U,l.bounded D)
    (hV : ∀ l∈V,l.bounded D) (hQ : ∀ l∈Q,l.bounded D) (i : Fin n) :
    let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
    |(j/(n:ℝ))*(∫ g,markedContraction
      (actualWord f R hR j a z U (goeMatrix (j/n) g))
      (actualWord f R hR j a z V (goeMatrix (j/n) g))
      (actualWord f R hR j a z Q (goeMatrix (j/n) g)) i ∂μ)-
        j*wordAverageExpected f hR j a z V*wordExpected f hR j a z (U++Q) i|≤
      wordLeadingCost j (actualWordBound f R j A D) U.length V.length Q.length/(n:ℝ) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  dsimp only
  let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj.le hA hD).le⟩
  let G := V.map (WordLetter.eval f R hR j a z)
  have hGb : ∀ p∈G,∀ M,opNorm (p M)≤B := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj.le hA hD ha haA hz (hV l hl)).1
  have hGl : ∀ p∈G,LipschitzWith B p := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj.le hA hD ha haA hz (hV l hl)).2
  have hu := actualWord_bounds f hR hj.le hA hD ha haA hz U hU
  have hq := actualWord_bounds f hR hj.le hA hD ha haA hz Q hQ
  have hh := goe_word_leading_contraction hn hj G
    (show 0<B from actualWordBound_pos f hR hj.le hA hD) hGb hGl
    (actualWord f R hR j a z U) (actualWord f R hR j a z Q) hu.2.continuous hq.2.continuous
    (pow_nonneg B.coe_nonneg U.length) (pow_nonneg B.coe_nonneg Q.length) hu.1 hq.1 i
  have he := wordAverageExpected_integral f hR hj.le hA hD ha haA hz V hV
  simp only [G,List.length_map,matrix_word_contraction,B] at hh
  simp only [Fintype.card_fin,actualWord] at he
  rw [he] at hh
  have heq : wordExpected f hR j a z (U++Q) i=
      ∫ g : MatrixCoordinates (Fin n)→ℝ,(actualWord f R hR j a z U (goeMatrix (j/n) g)*
        actualWord f R hR j a z Q (goeMatrix (j/n) g)) i i
          ∂Measure.pi (fun _=>gaussianReal 0 1) := by
    simp only [wordExpected,Fintype.card_fin,actualWord_append]
  rw [← heq] at hh
  simpa only [actualWord,wordLeadingCost,markedContraction] using! hh
end SKGap
end
end

end OAI
