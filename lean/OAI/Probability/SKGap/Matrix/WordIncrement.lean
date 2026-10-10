import Mathlib
import OAI.Probability.SKGap.Matrix.Word
import OAI.Probability.SKGap.Matrix.MatrixWordIncrement
import OAI.Probability.SKGap.Brownian.PathParameter

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
def WordLetter.close (δ : ℝ) : WordLetter ι→WordLetter ι→Prop
  | .diag d,.diag e => ∀ i,|d i-e i|≤δ
  | .noise,.noise => True
  | .inverse,.inverse => True
  | _,_ => False

def wordHolderScale (f : 𝓢(ℝ,ℂ)) (R j A : ℝ) : ℝ :=
  (1+j)*(1+|ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)|+
    |ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)|)

lemma wordHolderScale_ge_one (f : 𝓢(ℝ,ℂ)) (R A : ℝ) {j : ℝ} (hj : 0≤j) :
    1≤wordHolderScale f R j A := by
  unfold wordHolderScale
  nlinarith [abs_nonneg (ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)),
    abs_nonneg (ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))]

lemma wordHolderScale_constants (f : 𝓢(ℝ,ℂ)) (R A : ℝ) {j : ℝ} (hj : 0≤j) :
    ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)*(1+j)≤wordHolderScale f R j A ∧
    ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)*(1+j)≤wordHolderScale f R j A := by
  have hc := le_abs_self (ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have hm := le_abs_self (ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have hc0 := abs_nonneg (ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have hm0 := abs_nonneg (ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))
  have h1 : 0≤1+j := by linarith
  unfold wordHolderScale
  constructor
  · have h := mul_le_mul_of_nonneg_right hc h1
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hm h1
    nlinarith

lemma WordLetter.eval_pair [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D δ : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) (hδ : 0≤δ) (hδ1 : δ≤1)
    {a b : ι→ℝ} (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) (haA : ∀ i,a i≤A) (hbA : ∀ i,b i≤A)
    (hab : ∀ i,|a i-b i|≤δ) (l m : WordLetter ι) (hl : l.bounded D) (hm : m.bounded D)
    (hlm : l.close δ m) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨wordHolderScale f R j A*sqrt δ,mul_nonneg (zero_le_one.trans (wordHolderScale_ge_one f R A hj)) (sqrt_nonneg _)⟩
    MatrixFactorPairBounds B Δ (l.eval f R hR j a 1) (m.eval f R hR j b 1) := by
  intro B Δ
  obtain ⟨hlb,hll⟩ := l.eval_bounds f hR hj hA hD ha haA ⟨zero_le_one,le_rfl⟩ hl
  obtain ⟨hmb,hml⟩ := m.eval_bounds f hR hj hA hD hb hbA ⟨zero_le_one,le_rfl⟩ hm
  refine ⟨hlb,hmb,hll,hml,?_,?_⟩
  · intro M
    cases l <;> cases m <;> try contradiction
    · rename_i d e
      change opNorm (diagonal d-diagonal e)≤wordHolderScale f R j A*sqrt δ
      rw [Matrix.diagonal_sub]
      exact (opNorm_diagonal_le hδ hlm).trans ((parameter_sqrt_small hδ hδ1).trans
        (by nlinarith [wordHolderScale_ge_one f R A hj,sqrt_nonneg δ]))
    · simp [WordLetter.eval,opNorm]
    · exact ((pathK_parameter_holder f hR hj hA hδ hδ1 ha hb haA hbA hab M M).1).trans
        (by have hh := mul_le_mul_of_nonneg_right (wordHolderScale_constants f R A hj).1 (sqrt_nonneg δ)
            simpa only [mul_assoc,Δ,NNReal.coe_mk] using! hh)
  · cases l <;> cases m <;> try contradiction
    · rename_i d e
      exact (LipschitzWith.const (diagonal d-diagonal e)).weaken (show (0:NNReal)≤Δ from zero_le)
    · simpa only [WordLetter.eval,sub_self] using (LipschitzWith.const (0:Matrix ι ι ℝ)).weaken (show (0:NNReal)≤Δ from zero_le)
    · apply LipschitzWith.of_dist_le_mul
      intro M N
      change ‖(pathK f R hR j a 1 M-pathK f R hR j b 1 M)-
        (pathK f R hR j a 1 N-pathK f R hR j b 1 N)‖≤wordHolderScale f R j A*sqrt δ*‖M-N‖
      have he : (pathK f R hR j a 1 M-pathK f R hR j b 1 M)-
          (pathK f R hR j a 1 N-pathK f R hR j b 1 N)=
          (pathK f R hR j a 1 M-pathK f R hR j a 1 N)-
          (pathK f R hR j b 1 M-pathK f R hR j b 1 N) := by abel
      rw [he]
      apply ((pathK_parameter_holder f hR hj hA hδ hδ1 ha hb haA hbA hab M N).2).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hh := mul_le_mul_of_nonneg_right (wordHolderScale_constants f R A hj).2 (sqrt_nonneg δ)
      simpa only [mul_assoc,Δ,NNReal.coe_mk] using! hh

theorem actualWord_pair_increments [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D δ : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) (hδ : 0≤δ) (hδ1 : δ≤1)
    {a b : ι→ℝ} (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) (haA : ∀ i,a i≤A) (hbA : ∀ i,b i≤A)
    (hab : ∀ i,|a i-b i|≤δ) (F : List (WordLetter ι×WordLetter ι))
    (hF : ∀ p∈F,p.1.bounded D ∧ p.2.bounded D ∧ p.1.close δ p.2) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨wordHolderScale f R j A*sqrt δ,mul_nonneg (zero_le_one.trans (wordHolderScale_ge_one f R A hj)) (sqrt_nonneg _)⟩
    (∀ M,opNorm (actualWord f R hR j a 1 (F.map Prod.fst) M-actualWord f R hR j b 1 (F.map Prod.snd) M)≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ)
      (fun M=>actualWord f R hR j a 1 (F.map Prod.fst) M-actualWord f R hR j b 1 (F.map Prod.snd) M) := by
  intro B Δ
  let G := F.map (fun p=>(p.1.eval f R hR j a 1,p.2.eval f R hR j b 1))
  have hG : ∀ p∈G,MatrixFactorPairBounds B Δ p.1 p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1,h2,h3⟩ := hF q hq
    exact WordLetter.eval_pair f hR hj hA hD hδ hδ1 ha hb haA hbA hab q.1 q.2 h1 h2 h3
  simpa only [G,List.length_map,List.map_map,Function.comp_def,actualWord] using! matrixWord_pair_increments G hG
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

inductive WordTemplateLetter (m : ℕ) where
  | diag : Fin m→WordTemplateLetter m
  | noise : WordTemplateLetter m
  | inverse : WordTemplateLetter m
  deriving DecidableEq, Fintype

abbrev WordParameter (m : ℕ) (ι : Type*) := (Option (Fin m)×ι)→Icc (0:ℝ) 1

def templateInverse (A : ℝ) (θ : WordParameter m ι) (i : ι) : ℝ := A*(θ (none,i):ℝ)
def templateDiagonal (D : ℝ) (θ : WordParameter m ι) (k : Fin m) (i : ι) : ℝ :=
  D*(2*(θ (some k,i):ℝ)-1)
def WordTemplateLetter.realize (D : ℝ) (θ : WordParameter m ι) : WordTemplateLetter m→WordLetter ι
  | .diag k => .diag (templateDiagonal D θ k)
  | .noise => .noise
  | .inverse => .inverse

def templateWord (D : ℝ) (θ : WordParameter m ι) (F : List (WordTemplateLetter m)) :=
  F.map (WordTemplateLetter.realize D θ)

def templateScale (A D : ℝ) : ℝ := 1+A+2*D

omit [Fintype ι] [DecidableEq ι] in
lemma templateInverse_bounds {A : ℝ} (hA : 0 ≤ A) (θ : WordParameter m ι) (i : ι) :
    0 ≤ templateInverse A θ i ∧ templateInverse A θ i ≤ A := by
  obtain ⟨h0,h1⟩ := (θ (none,i)).property
  dsimp [templateInverse]
  constructor
  · positivity
  · nlinarith only [mul_le_mul_of_nonneg_left h1 hA]

omit [Fintype ι] [DecidableEq ι] in
lemma templateDiagonal_bound {D : ℝ} (hD : 0 ≤ D) (θ : WordParameter m ι) (k : Fin m) (i : ι) :
    |templateDiagonal D θ k i| ≤ D := by
  obtain ⟨h0,h1⟩ := (θ (some k,i)).property
  rw [templateDiagonal,abs_mul,abs_of_nonneg hD]
  have hf : |2*(θ (some k,i):ℝ)-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hf hD

omit [Fintype ι] [DecidableEq ι] in
lemma templateWord_bounded {D : ℝ} (hD : 0 ≤ D) (θ : WordParameter m ι)
    (F : List (WordTemplateLetter m)) : ∀ l∈templateWord D θ F,l.bounded D := by
  intro l hl
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hl
  cases q with
  | diag k => exact templateDiagonal_bound hD θ k
  | noise => trivial
  | inverse => trivial

omit [DecidableEq ι] in
lemma template_coord_dist (θ η : WordParameter m ι) (s : Option (Fin m)×ι) :
    |(θ s:ℝ)-(η s:ℝ)| ≤ dist θ η := by
  simpa only [Subtype.dist_eq,Real.dist_eq] using dist_le_pi_dist θ η s

omit [DecidableEq ι] in
lemma templateInverse_dist {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (θ η : WordParameter m ι) (i : ι) :
    |templateInverse A θ i-templateInverse A η i| ≤ templateScale A D*dist θ η := by
  rw [templateInverse,templateInverse,←mul_sub,abs_mul,abs_of_nonneg hA]
  apply (mul_le_mul_of_nonneg_left (template_coord_dist θ η (none,i)) hA).trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  dsimp [templateScale]
  linarith

omit [DecidableEq ι] in
lemma templateLetter_close {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (θ η : WordParameter m ι) (l : WordTemplateLetter m) :
    (l.realize D θ).close (templateScale A D*dist θ η) (l.realize D η) := by
  cases l with
  | noise => trivial
  | inverse => trivial
  | diag k =>
    intro i
    change |D*(2*(θ (some k,i):ℝ)-1)-D*(2*(η (some k,i):ℝ)-1)| ≤ _
    have he : D*(2*(θ (some k,i):ℝ)-1)-D*(2*(η (some k,i):ℝ)-1)=
        (2*D)*((θ (some k,i):ℝ)-(η (some k,i):ℝ)) := by ring
    rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*D)]
    apply (mul_le_mul_of_nonneg_left (template_coord_dist θ η (some k,i)) (by positivity : 0 ≤ 2*D)).trans
    apply mul_le_mul_of_nonneg_right _ dist_nonneg
    dsimp [templateScale]
    linarith

omit [DecidableEq ι] in
lemma templateWord_paired {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (θ η : WordParameter m ι) (F : List (WordTemplateLetter m)) :
    ∀ p∈F.map (fun l=>(l.realize D θ,l.realize D η)),
      p.1.bounded D ∧ p.2.bounded D ∧ p.1.close (templateScale A D*dist θ η) p.2 := by
  intro p hp
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
  exact ⟨templateWord_bounded hD θ F _ (List.mem_map.mpr ⟨l,hl,rfl⟩),
    templateWord_bounded hD η F _ (List.mem_map.mpr ⟨l,hl,rfl⟩),templateLetter_close hA hD θ η l⟩
end SKGap
end
end

end OAI
