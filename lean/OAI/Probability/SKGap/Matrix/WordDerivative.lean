import Mathlib
import OAI.Probability.SKGap.Matrix.Word
import OAI.Probability.SKGap.Matrix.MatrixWordIncrement

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pathDiagonal_square_all {a : ι→ℝ} (ha : ∀ i,0≤a i) {z : ℝ} (hz : 0≤z) :
    pathDiagonal a z*pathDiagonal a z=z • diagonal a := by
  simp only [pathDiagonal,diagonal_mul_diagonal]
  ext i k
  by_cases h : i=k
  · subst k
    simp only [Matrix.smul_apply,diagonal_apply_eq,smul_eq_mul]
    calc
      (sqrt z*sqrt (a i))*(sqrt z*sqrt (a i)) = (sqrt z*sqrt z)*(sqrt (a i)*sqrt (a i)) := by ring
      _ = z*a i := by rw [mul_self_sqrt hz,mul_self_sqrt (ha i)]
  · simp [h]

lemma realProject_hasDerivAt {R : ℝ} (hR : 0≤R) (M E : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hE : Eᵀ=E) (hMR : opNorm M<R) :
    HasDerivAt (fun t : ℝ=>realProject R hR (M+t • E)) E 0 := by
  have hc : Continuous (fun t : ℝ=>opNorm (M+t • E)) :=
    continuous_realOpNorm.comp (continuous_const.add (continuous_id.smul continuous_const))
  have he : (fun t : ℝ=>realProject R hR (M+t • E)) =ᶠ[𝓝 (0:ℝ)] (fun t=>M+t • E) := by
    have hn : ∀ᶠ t in 𝓝 (0:ℝ),opNorm (M+t • E)<R := hc.continuousAt.eventually (gt_mem_nhds (by simpa using hMR))
    filter_upwards [hn] with t ht
    exact realProject_eq_self hR (M+t • E) (by simp [transpose_smul,hM,hE]) ht.le
  have hh : HasDerivAt (fun t : ℝ=>M+t • E) E 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0:ℝ)).smul_const E).const_add M
  exact hh.congr_of_eventuallyEq he

def WordLetter.direction (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0≤R) (j : ℝ) (a : ι→ℝ)
    (z : ℝ) (M E : Matrix ι ι ℝ) : WordLetter ι→Matrix ι ι ℝ
  | .diag _ => 0
  | .noise => E
  | .inverse => z • (pathK f R hR j a z M*diagonal a*E*pathK f R hR j a z M)

def actualWordDirection (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0≤R) (j : ℝ) (a : ι→ℝ)
    (z : ℝ) (M E : Matrix ι ι ℝ) : List (WordLetter ι)→Matrix ι ι ℝ
  | [] => 0
  | l::F => l.direction f R hR j a z M E*actualWord f R hR j a z F M +
      l.eval f R hR j a z M*actualWordDirection f R hR j a z M E F

lemma WordLetter.hasDerivAt [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0<lo)
    (hf : ∀ x∈Icc lo hi,f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0≤R) (j : ℝ)
    {a : ι→ℝ} (ha : ∀ i,0≤a i) {z : ℝ} (hz : 0≤z) (M E : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hE : Eᵀ=E) (hMR : opNorm M<R)
    (hl : lo<ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)))
    (hu : -hi<ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)))
    (l : WordLetter ι) : HasDerivAt (fun t : ℝ=>l.eval f R hR j a z (M+t • E))
      (l.direction f R hR j a z M E) 0 := by
  cases l with
  | diag d => exact hasDerivAt_const _ _
  | noise => exact realProject_hasDerivAt hR M E hM hE hMR
  | inverse =>
    have hh := realTruncatedK_derivative f hlo hf hR (pathDiagonal a z)
      (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b)) M E (diagonal_transpose _)
      (diagonal_transpose _) hM hE hMR hl hu
    simpa only [WordLetter.eval,WordLetter.direction,pathK,pathDiagonal_square_all ha hz,Matrix.mul_smul,Matrix.smul_mul] using! hh

theorem actualWord_hasDerivAt [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0<lo)
    (hf : ∀ x∈Icc lo hi,f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0≤R) (j : ℝ)
    {a : ι→ℝ} (ha : ∀ i,0≤a i) {z : ℝ} (hz : 0≤z) (M E : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hE : Eᵀ=E) (hMR : opNorm M<R)
    (hl : lo<ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)))
    (hu : -hi<ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)))
    (F : List (WordLetter ι)) : HasDerivAt
      (fun t : ℝ=>actualWord f R hR j a z F (M+t • E)) (actualWordDirection f R hR j a z M E F) 0 := by
  induction F with
  | nil => exact hasDerivAt_const _ _
  | cons l F ih =>
    have hh := (l.hasDerivAt f hlo hf hR j ha hz M E hM hE hMR hl hu).mul ih
    simpa only [actualWord,actualWordDirection,List.map_cons,matrixFactorProduct_cons,zero_smul,add_zero] using! hh
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma word_opNorm_smul (r : ℝ) (M : Matrix ι ι ℝ) : opNorm (r • M)=|r| *opNorm M := by
  unfold opNorm
  rw [map_smul,map_smul,norm_smul,Real.norm_eq_abs]

lemma WordLetter.direction_bound [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (M E : Matrix ι ι ℝ) (l : WordLetter ι) :
    opNorm (l.direction f R hR j a z M E) ≤
      (1+|z| *A*(actualWordBound f R j A D)^2)*opNorm E := by
  have hB := (actualWordBound_pos f hR hj hA hD).le
  have hn : 0≤opNorm E := norm_nonneg _
  have hh : 0≤|z| *A*(actualWordBound f R j A D)^2 := by positivity
  cases l with
  | diag d => simp only [WordLetter.direction,opNorm,map_zero,norm_zero];positivity
  | noise => change opNorm E ≤ _;nlinarith
  | inverse =>
    have hk : opNorm (pathK f R hR j a z M)≤actualWordBound f R j A D :=
      (WordLetter.eval_bounds f hR hj hA hD ha haA hz .inverse trivial).1 M
    have hd := opNorm_diagonal_le hA (fun i=>by rw [abs_of_nonneg (ha i)];exact haA i)
    rw [WordLetter.direction,word_opNorm_smul]
    have hprod : opNorm (pathK f R hR j a z M*diagonal a*E*pathK f R hR j a z M)≤
        actualWordBound f R j A D*A*opNorm E*actualWordBound f R j A D := by
      apply (opNorm_mul _ _).trans
      apply mul_le_mul _ hk (norm_nonneg _) (by positivity)
      apply (opNorm_mul _ _).trans
      apply mul_le_mul_of_nonneg_right _ hn
      exact (opNorm_mul _ _).trans (mul_le_mul hk hd (norm_nonneg _) hB)
    apply (mul_le_mul_of_nonneg_left hprod (abs_nonneg z)).trans
    nlinarith

theorem actualWordDirection_bound [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (M E : Matrix ι ι ℝ) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    opNorm (actualWordDirection f R hR j a z M E F) ≤
      (1+|z| *A*(B:ℝ)^2)*(wordParameterCoeff B F.length:ℝ)*opNorm E := by
  intro B
  have hB : 0≤(B:ℝ) := B.coe_nonneg
  have hC : 0≤1+|z| *A*(B:ℝ)^2 := by positivity
  have hE : 0≤opNorm E := norm_nonneg _
  induction F with
  | nil => simp [actualWordDirection,wordParameterCoeff,opNorm]
  | cons l F ih =>
    have hFt : ∀ p∈F,p.bounded D := fun p hp=>hF p (List.mem_cons_of_mem l hp)
    have hd := l.direction_bound f hR hj hA hD ha haA hz M E
    have ht := (actualWord_bounds f hR hj hA hD ha haA hz F hFt).1 M
    have hl := (l.eval_bounds f hR hj hA hD ha haA hz (hF l List.mem_cons_self)).1 M
    have hi := ih hFt
    change opNorm (l.direction f R hR j a z M E)≤(1+|z| *A*(B:ℝ)^2)*opNorm E at hd
    change opNorm (actualWord f R hR j a z F M)≤(B:ℝ)^F.length at ht
    change opNorm (l.eval f R hR j a z M)≤(B:ℝ) at hl
    rw [actualWordDirection]
    apply (word_opNorm_add _ _).trans
    apply (add_le_add (opNorm_mul _ _) (opNorm_mul _ _)).trans
    have h1 := mul_le_mul hd ht (norm_nonneg _) (mul_nonneg hC hE)
    have h2 := mul_le_mul hl hi (norm_nonneg _) hB
    apply (add_le_add h1 h2).trans_eq
    simp only [List.length_cons,wordParameterCoeff,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_pow]
    ring

lemma WordLetter.direction_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (E : Matrix ι ι ℝ) (l : WordLetter ι) : Continuous (fun M=>l.direction f R hR j a z M E) := by
  cases l with
  | diag d => exact continuous_const
  | noise => exact continuous_const
  | inverse =>
    have hk := pathK_continuous f hR hj hA ha haA hz
    exact ((hk.matrix_mul continuous_const).matrix_mul continuous_const).matrix_mul hk |>.const_smul z

lemma actualWordDirection_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (E : Matrix ι ι ℝ) :
    Continuous (fun M=>actualWordDirection f R hR j a z M E F) := by
  induction F with
  | nil => exact continuous_const
  | cons l F ih =>
    have hFt : ∀ p∈F,p.bounded D := fun p hp=>hF p (List.mem_cons_of_mem l hp)
    have hl := (l.eval_bounds f hR hj hA hD ha haA hz (hF l List.mem_cons_self)).2.continuous
    have ht := (actualWord_bounds f hR hj hA hD ha haA hz F hFt).2.continuous
    exact ((l.direction_continuous f hR hj hA ha haA hz E).matrix_mul ht).add (hl.matrix_mul (ih hFt))
end SKGap
end
end

end OAI
