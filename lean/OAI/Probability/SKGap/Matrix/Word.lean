import Mathlib
import OAI.Probability.SKGap.Brownian.PathCutoff
import OAI.Probability.SKGap.Matrix.MatrixWordRegularity

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

inductive WordLetter (ι : Type*)
  | diag : (ι→ℝ)→WordLetter ι
  | noise : WordLetter ι
  | inverse : WordLetter ι

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def WordLetter.bounded (D : ℝ) : WordLetter ι→Prop
  | .diag d => ∀ i,|d i| ≤ D
  | .noise => True
  | .inverse => True

def WordLetter.eval (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ) :
    WordLetter ι→Matrix ι ι ℝ→Matrix ι ι ℝ
  | .diag d,_ => diagonal d
  | .noise,M => realProject R hR M
  | .inverse,M => pathK f R hR j a z M

def actualWord (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (F : List (WordLetter ι)) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  matrixFactorProduct (F.map (WordLetter.eval f R hR j a z)) M

def actualWordBound (f : 𝓢(ℝ,ℂ)) (R j A D : ℝ) : ℝ :=
  1+R+D+pathBound f R j A+pathLip f R j A

lemma actualWordBound_pos (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) : 0<actualWordBound f R j A D := by
  have hh := path_constants_nonneg f hR hj hA
  unfold actualWordBound
  linarith

lemma WordLetter.eval_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (l : WordLetter ι) (hl : l.bounded D) :
    (∀ M,opNorm (l.eval f R hR j a z M) ≤ actualWordBound f R j A D) ∧
    LipschitzWith ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
      (l.eval f R hR j a z) := by
  have hconst := path_constants_nonneg f hR hj hA
  have hD' : D ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hR' : R ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have h1 : 1 ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hB : pathBound f R j A ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  have hL : pathLip f R j A ≤ actualWordBound f R j A D := by unfold actualWordBound;linarith
  cases l with
  | diag d =>
    constructor
    · intro M;exact (opNorm_diagonal_le hD hl).trans hD'
    · exact (LipschitzWith.const (diagonal d)).weaken (show (0:NNReal) ≤ _ from zero_le)
  | noise =>
    constructor
    · intro M;exact (realProject_opNorm hR M).trans hR'
    · exact (realProject_lipschitz hR).weaken h1
  | inverse =>
    have hh := pathK_bounds f hR hj hA ha haA hz
    constructor
    · intro M;exact (hh.1 M).trans hB
    · apply LipschitzWith.of_dist_le_mul
      intro M N
      change ‖pathK f R hR j a z M-pathK f R hR j a z N‖ ≤ actualWordBound f R j A D*‖M-N‖
      exact (hh.2 M N).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

theorem actualWord_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) :
    (∀ M,opNorm (actualWord f R hR j a z F M) ≤ (actualWordBound f R j A D)^F.length) ∧
    LipschitzWith ((F.length:NNReal)*⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩^F.length)
      (actualWord f R hR j a z F) := by
  let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
  let G := F.map (WordLetter.eval f R hR j a z)
  have hGb : ∀ p∈G,∀ M,opNorm (p M) ≤ B := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj hA hD ha haA hz (hF l hl)).1
  have hGl : ∀ p∈G,LipschitzWith B p := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact (l.eval_bounds f hR hj hA hD ha haA hz (hF l hl)).2
  constructor
  · intro M
    simpa only [G,B,actualWord,List.length_map,NNReal.coe_mk] using! matrixFactorProduct_opNorm G hGb M
  · simpa only [G,B,actualWord,List.length_map] using! (@matrixFactorProduct_lipschitz ι (Matrix ι ι ℝ) _ _ (inferInstance : MetricSpace (Matrix ι ι ℝ)).toPseudoMetricSpace G B hGb hGl)
end SKGap
end
end

end OAI
