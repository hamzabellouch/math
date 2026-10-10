import Mathlib
import OAI.Probability.SKGap.Localization.AffineBilinear
import OAI.Probability.SKGap.Localization.TemplatePatterns

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*}

def inverseChart {A : ℝ} (hA : 0<A) (a : ℝ) (ha : a∈Icc 0 A) : Icc (0:ℝ) 1 :=
  ⟨a/A,div_nonneg ha.1 hA.le,(div_le_one hA).mpr ha.2⟩

def diagonalChart {D : ℝ} (hD : 0<D) (d : ℝ) (hd : |d|≤D) : Icc (0:ℝ) 1 := by
  refine ⟨(d/D+1)/2,?_,?_⟩
  · have hh : -1≤d/D := (le_div_iff₀ hD).mpr (by linarith [(abs_le.mp hd).1])
    linarith
  · have hh : d/D≤1 := (div_le_one hD).mpr (abs_le.mp hd).2
    linarith

lemma inverseChart_exact {A : ℝ} (hA : 0<A) (a : ℝ) (ha : a∈Icc 0 A) :
    A*(inverseChart hA a ha:ℝ)=a := by
  dsimp [inverseChart]
  field_simp
lemma diagonalChart_exact {D : ℝ} (hD : 0<D) (d : ℝ) (hd : |d|≤D) :
    D*(2*(diagonalChart hD d hd:ℝ)-1)=d := by
  dsimp [diagonalChart]
  field_simp
  ring

def WordLetter.diagonalValue (i : ι) : WordLetter ι→ℝ
  | .diag d => d i
  | _ => 0
lemma WordLetter.diagonalValue_bound {D : ℝ} (hD : 0≤D) (l : WordLetter ι)
    (hl : l.bounded D) (i : ι) : |l.diagonalValue i|≤D := by
  cases l with
  | diag d => exact hl i
  | noise => simpa [diagonalValue] using hD
  | inverse => simpa [diagonalValue] using hD

theorem templateWord_surjective {A D : ℝ} (hA : 0<A) (hD : 0<D)
    {a : ι→ℝ} (ha : ∀ i,a i∈Icc 0 A) (F : List (WordLetter ι))
    (hF : ∀ l∈F,l.bounded D) {L : ℕ} (hL : F.length≤L) :
    ∃ (G : List (WordTemplateLetter L)) (θ : WordParameter L ι),
      G.length=F.length ∧ templateInverse A θ=a ∧ templateWord D θ G=F := by
  classical
  let θ : WordParameter L ι := fun s=>match s.1 with
    | none => inverseChart hA (a s.2) (ha s.2)
    | some k => if hk : k.val<F.length then
        diagonalChart hD ((F[k.val]).diagonalValue s.2)
          (WordLetter.diagonalValue_bound hD.le _ (hF _ (List.getElem_mem hk)) _)
      else ⟨0,le_rfl,zero_le_one⟩
  let pattern : Fin F.length→WordTemplateLetter L := fun k=>match F[k.val] with
    | .diag _ => .diag ⟨k.val,lt_of_lt_of_le k.isLt hL⟩
    | .noise => .noise
    | .inverse => .inverse
  let G := List.ofFn pattern
  refine ⟨G,θ,by simp [G],?_,?_⟩
  · funext i
    exact inverseChart_exact hA (a i) (ha i)
  · have hp (k : Fin F.length) : (pattern k).realize D θ=F[k.val] := by
      cases hl : F[k.val] with
      | diag d =>
        dsimp [pattern]
        rw [hl]
        apply congrArg WordLetter.diag
        funext i
        simp only [templateDiagonal,θ,dite_eq_left k.isLt,hl,WordLetter.diagonalValue]
        exact diagonalChart_exact hD (d i) _
      | noise => simp [pattern,hl,WordTemplateLetter.realize]
      | inverse => simp [pattern,hl,WordTemplateLetter.realize]
    change (List.ofFn pattern).map (WordTemplateLetter.realize D θ)=F
    rw [List.map_ofFn]
    calc
      _ = List.ofFn (fun k : Fin F.length=>F[k.val]) := congrArg List.ofFn (funext hp)
      _ = F := List.ofFn_getElem
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem all_actualWords_gaussian_chaining (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0<A) (hD : 0<D) (L : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,1 ≤ n→∀ p : Bool,
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
        (∀ i,a i∈Icc 0 A) ∧ F.length ≤ L ∧ (∀ l∈F,l.bounded D) ∧
        C< matrixWordSeminorm p
        (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
          actualWord f R hR j a 1 F (goeMatrix (j/n) x)) (WithLp.toLp 2 g))} ≤
      (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  obtain ⟨C,hC,ht⟩ := all_generalTemplateWords_gaussian_chaining (m:=L) f hR hj hA.le hD.le L
  refine ⟨C,hC,?_⟩
  intro n hn p
  apply (measure_mono ?_).trans (ht n hn p)
  intro g hg
  obtain ⟨a,F,ha,hFL,hF,hg⟩ := hg
  obtain ⟨G,θ,hG,haθ,hFθ⟩ := templateWord_surjective hA hD ha F hF hFL
  refine ⟨G,by omega,θ,?_⟩
  simpa only [generalTemplateMatrix,haθ,hFθ] using hg
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory
open scoped BigOperators SchwartzMap Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma WordLetter.sign (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (s : ι→ℝ) (hs : ∀ i,s i^2=1) (M : Matrix ι ι ℝ) (l : WordLetter ι) :
    l.eval f R hR j a z (signConjugate s M)=signConjugate s (l.eval f R hR j a z M) := by
  cases l with
  | diag d => exact (signConjugate_diagonal s hs d).symm
  | noise => exact realProject_sign hR s hs M
  | inverse => exact pathK_sign f hR j a z s hs M

lemma actualWord_sign (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (s : ι→ℝ) (hs : ∀ i,s i^2=1) (M : Matrix ι ι ℝ) (F : List (WordLetter ι)) :
    actualWord f R hR j a z F (signConjugate s M)=signConjugate s (actualWord f R hR j a z F M) := by
  induction F with
  | nil =>
    change (1:Matrix ι ι ℝ)=signConjugate s 1
    simpa only [diagonal_one] using (signConjugate_diagonal s hs (fun _=>1)).symm
  | cons l F ih =>
    change l.eval f R hR j a z (signConjugate s M)*actualWord f R hR j a z F (signConjugate s M)=
      signConjugate s (l.eval f R hR j a z M*actualWord f R hR j a z F M)
    rw [l.sign f hR j a z s hs M,ih,signConjugate_mul s hs]

theorem actualWord_offdiag_mean (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j r : ℝ) (a : ι→ℝ) (z : ℝ)
    (F : List (WordLetter ι)) (i k : ι) (hik : i≠k) :
    (∫ g,actualWord f R hR j a z F (goeMatrix r g) i k
      ∂Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1))=0 :=
  goe_equivariant_offdiag r (actualWord f R hR j a z F)
    (fun s hs M=>actualWord_sign f hR j a z s hs M F) i k hik
end SKGap
end
end

end OAI
