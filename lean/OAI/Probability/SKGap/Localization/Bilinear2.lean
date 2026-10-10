import Mathlib
import OAI.Probability.SKGap.Brownian.PathAgreement

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def exactG (j : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  pathDiagonal a 1*(1-pathDiagonal a 1*(M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1)*pathDiagonal a 1)⁻¹*pathDiagonal a 1

def bilinearDataD (k : Fin 3) (q : ℝ) (a : ι → ℝ) : ι → ℝ :=
  if k=0 then a else fun i => 1+q*a i

def bilinearDataE (k : Fin 3) : ι → ℝ := if k=1 then 1 else 0

def bilinearDataW (k : Fin 3) : ℝ := if k=2 then 1 else 0

def bilinearError (k : Fin 3) (j : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  let q := (j/(Fintype.card ι:ℝ))*∑ b,a b
  if k=0 then exactG j a M-diagonal a
  else if k=1 then exactG j a M*M-q • diagonal a
  else M*exactG j a M*M-q • (1:Matrix ι ι ℝ)-q^2 • diagonal a

omit [DecidableEq ι] in
lemma bilinearData_bound [Nonempty ι] {j A : ℝ} (hj : 0 ≤ j) (hA : 0 ≤ A) {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) (k : Fin 3) (i : ι) :
    |bilinearDataD k ((j/(Fintype.card ι:ℝ))*∑ b,a b) a i| ≤ A+1+j*A^2 := by
  have hq := diagonal_mean_bounds hj ha haA
  have hq0 := hq.1
  have hai := ha i
  have haAi := haA i
  unfold bilinearDataD
  split_ifs
  · rw [abs_of_nonneg hai]
    nlinarith [mul_nonneg hj (sq_nonneg A)]
  · rw [abs_of_nonneg (by positivity)]
    have hh := mul_le_mul hq.2 haAi hai (mul_nonneg hj hA)
    nlinarith

lemma bilinearDataW_bound (k : Fin 3) : |bilinearDataW k| ≤ 1 := by
  unfold bilinearDataW
  split_ifs <;> norm_num

lemma bilinearError_agrees [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (M : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hMR : opNorm M ≤ R)
    (hl : lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (hu : -hi ≤ ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (k : Fin 3) :
    let q := (j/(Fintype.card ι:ℝ))*∑ b,a b
    bilinearError k j a M=affineRight (pathFeature (decide (k=2)) f R hR j a)
      (bilinearDataD k q a) (bilinearDataE k) (bilinearDataW k) M-
        diagonal (fun i => (if k=2 then q else 1)*bilinearDataD k q a i-bilinearDataE k i) := by
  dsimp only
  have he := path_bilinear_agreement f hlo hf hR j ha M hM hMR hl hu
  dsimp only at he
  have hd (q : ℝ) : diagonal (fun i => q*a i)=q • diagonal a := by
    ext i k; by_cases h : i=k <;> simp [h]
  have hd₂ (q : ℝ) : diagonal (fun i => q*(1+q*a i))=q • (1:Matrix ι ι ℝ)+q^2 • diagonal a := by
    ext i k; by_cases h : i=k
    · subst k; simp only [diagonal_apply_eq,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul]; ring
    · simp [h]
  fin_cases k
  · change exactG j a M-diagonal a=affineRight (pathK f R hR j a 1) a 0 0 M-diagonal (fun i => 1*a i-0)
    simpa only [one_mul,sub_zero,exactG] using congrArg (fun Q => Q-diagonal a) he.1.symm
  · change exactG j a M*M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • diagonal a=
      affineRight (pathK f R hR j a 1) (fun i => 1+((j/(Fintype.card ι:ℝ))*∑ b,a b)*a i) 1 0 M-
        diagonal (fun i => 1*(1+((j/(Fintype.card ι:ℝ))*∑ b,a b)*a i)-1)
    rw [he.2.1]
    simp only [one_mul,add_sub_cancel_left,hd,exactG]
  · change M*exactG j a M*M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1-
      ((j/(Fintype.card ι:ℝ))*∑ b,a b)^2 • diagonal a=
      affineRight (fun Q => realProject R hR Q*pathK f R hR j a 1 Q)
        (fun i => 1+((j/(Fintype.card ι:ℝ))*∑ b,a b)*a i) 0 1 M-
        diagonal (fun i => ((j/(Fintype.card ι:ℝ))*∑ b,a b)*(1+((j/(Fintype.card ι:ℝ))*∑ b,a b)*a i)-0)
    rw [he.2.2]
    simp only [sub_zero,hd₂,exactG]
    abel

lemma path_all_good_exponential [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hs : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤ (1-sqrt j*A)^2/4) :
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      {g | ∃ z ∈ Icc (0:ℝ) 1, g ∉ truncationGoodSet (j/(Fintype.card ι:ℝ))
        (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
        (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))} ≤
      3*exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
  have hp := goe_path_spectral_tail hj hA0 (by norm_num : (0:ℝ)≤1) ha haA hs herr
  dsimp only at hp
  have he : {g | ∃ z ∈ Icc (0:ℝ) 1, g ∉ truncationGoodSet (j/(Fintype.card ι:ℝ))
        (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
        (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))} ⊆
      {g | ∃ z ∈ Icc (0:ℝ) 1, ¬(opNorm (goeMatrix (j/(Fintype.card ι:ℝ)) g)<2*sqrt j+1+1 ∧
        ((1-sqrt j*A)^2/2)/2 < ComplexSpectral.lowerRayleigh (liftMatrix
          (stabilityMatrix a z ((j/(Fintype.card ι:ℝ))*∑ b,a b) (goeMatrix (j/(Fintype.card ι:ℝ)) g))) ∧
        -(2+A*(2*sqrt j+1+j*A)) < ComplexSpectral.lowerRayleigh (-liftMatrix
          (stabilityMatrix a z ((j/(Fintype.card ι:ℝ))*∑ b,a b) (goeMatrix (j/(Fintype.card ι:ℝ)) g))))} := by
    rintro g ⟨z,hz,hg⟩
    refine ⟨z,hz,?_⟩
    intro hh
    apply hg
    rw [stabilityMatrix_path_rep a ha hz.1] at hh
    simpa only [truncationGoodSet,Set.mem_ofPred_eq,div_div,show (2:ℝ)*2=4 by norm_num] using hh
  apply ((measureReal_mono he).trans hp).trans
  have hn : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left (1/(π^2*j))
    (((1-sqrt j*A)^2)^2/(16*π^2*j*A^2))) hn
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right (1/(π^2*j))
    (((1-sqrt j*A)^2)^2/(16*π^2*j*A^2))) hn
  have he₁ : exp (-(1:ℝ)^2*(Fintype.card ι:ℝ)/(π^2*j)) ≤ exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
    apply exp_le_exp.mpr
    change _ ≤ -min _ _ * _
    convert neg_le_neg h₁ using 1 <;> first | rfl | ring
  have he₂ : exp (-((1-sqrt j*A)^2)^2*(Fintype.card ι:ℝ)/(16*π^2*j*A^2)) ≤ exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
    apply exp_le_exp.mpr
    change _ ≤ -min _ _ * _
    convert neg_le_neg h₂ using 1 <;> first | rfl | ring
  linarith
end SKGap
end
end

end OAI
