import OAI.Analysis.TriangularHilbert.NormBounds

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def heatCarrier (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) :=
  if w = v then rowStar (heatArray A h u p σ) v else (rowStar (heatArray A h u p σ) v)ᴴ

def heatMask (d : Three → ι → ℝ) : Matrix (BlockSpace ι) (BlockSpace ι) ℂ :=
  blockD (fun w => Matrix.diagonal (fun i => (d w i : ℂ)))

omit [Fintype ι] in
lemma heatMask_eq_diagonal (d : Three → ι → ℝ) :
    heatMask d = Matrix.diagonal (fun a : BlockSpace ι => (d a.1 a.2 : ℂ)) := by
  ext ⟨v,i⟩ ⟨w,j⟩
  by_cases hv : v = w <;> by_cases hi : i = j <;>
    simp [heatMask, blockD, blocks, Matrix.diagonal, hv, hi, Prod.mk.injEq]

omit [Fintype ι] in
lemma heatMask_isHermitian (d : Three → ι → ℝ) : (heatMask d).IsHermitian := by
  rw [heatMask_eq_diagonal]
  exact Matrix.isHermitian_diagonal_iff.mpr (fun a => by change star (d a.1 a.2 : ℂ) = _; exact Complex.conj_ofReal _)

lemma heatCarrier_norm (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) :
    ‖heatCarrier A h u p σ v w‖ = ‖rowStar (heatArray A h u p σ) v‖ := by
  unfold heatCarrier
  split_ifs
  · rfl
  · exact norm_star (rowStar (heatArray A h u p σ) v)

lemma localGram_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    localGram A h u p σ v w =
      (heatCarrier A h u p σ v w)ᴴ * heatCarrier A h u p σ v w := by
  unfold heatCarrier
  split_ifs with hw
  · subst w
    exact localGram_center A hh u p hσ v
  · rw [Matrix.conjTranspose_conjTranspose]
    exact localGram_other A hh u p hσ hw

lemma localInsert_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    (v w : Three) (d : Three → ι → ℝ) :
    weightedGram (fixedBase A (heatWeights h u p σ) v w)
      (fun a : BlockSpace ι => heatWeights h u p σ a.1 a.2 * d a.1 a.2) =
        (heatCarrier A h u p σ v w)ᴴ * heatMask d * heatCarrier A h u p σ v w := by
  simp only [fixedBase, heatCarrier]
  split_ifs
  · exact rowBare_insert A _ d (fun a j => (weight_pos hh (hσ a) (u j) (p a)).le) v
  · rw [Matrix.conjTranspose_conjTranspose]
    exact colBare_insert A _ d (fun a j => (weight_pos hh (hσ a) (u j) (p a)).le) v

lemma localFirst_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    localFirst A h u p σ v w = (heatCarrier A h u p σ v w)ᴴ *
      heatMask (fun a i => if a = w then score (u i) (p a) (σ a) else 0) *
        heatCarrier A h u p σ v w := by
  rw [localFirst, groupFirst_eq_insert]
  exact localInsert_eq_carrier A hh u p hσ v w
    (fun a i => if a = w then score (u i) (p a) (σ a) else 0)

omit [Fintype ι] [DecidableEq ι] in
lemma groupSecond_eq_insert (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (w : Three) :
    groupSecond h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w =
      fun a : BlockSpace ι => heatWeights h u p σ a.1 a.2 *
        (if a.1 = w then score (u a.2) (p a.1) (σ a.1)^2 - (σ a.1)⁻¹ else 0) := by
  funext a
  simp only [groupSecond, heatWeights]
  split_ifs with ha
  · rw [ha, mul_comm]
  · rw [mul_zero]

lemma localSecond_eq_carrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    localSecond A h u p σ v w = (heatCarrier A h u p σ v w)ᴴ *
      heatMask (fun a i => if a = w then score (u i) (p a) (σ a)^2 - (σ a)⁻¹ else 0) *
        heatCarrier A h u p σ v w := by
  rw [localSecond, groupSecond_eq_insert]
  exact localInsert_eq_carrier A hh u p hσ v w
    (fun a i => if a = w then score (u i) (p a) (σ a)^2 - (σ a)⁻¹ else 0)

end
end TriangularHilbert.Heat
end

end OAI
