import Mathlib
import OAI.Probability.SKGap.Localization.CoefficientRow
import OAI.Probability.SKGap.Stability.ImplicitPerturb
import OAI.Probability.SKGap.Stability.ImplicitUniform

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

def uniformControlBudget (j δ B : ℝ) : ℝ :=
  let L:=B+|j| *B^2+2*|j| *B
  let W:=(1+B^2*(δ/2)⁻¹*L)*B^2*(B+2*|j| *B)
  let C:=B*W+B
  let Y:=(B+|j| *B^2)*W+|j| *C
  let F:=(1+B^2*(δ/2)⁻¹*L)*(B*(B+Y+|j| *C)+B^2*B+
        |j| *B^2*W*B+|j| *B^2*C*B+|j| *B^2*2*(B*W+B))
  let G:=B*W+B+B*F
  let H:=(B+|j| *B^2)*F+|j| *W*B+|j| *C*B+|j| *G
  W+C+Y+F+G+H

lemma uniformControlBudget_nonneg {j δ B : ℝ} (hδ : 0<δ) (hB : 0≤B) :
    0≤uniformControlBudget j δ B := by unfold uniformControlBudget; positivity

theorem implicit_uniform_control (j χ b r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell q w y : E) (c : ℝ)
    (s χ' p' c' b' : ι→ℝ) (X' : ι→E→L[ℝ]E) (u' m' ell' w' y' q' : ι→E)
    {δ d B : ℝ} (hδ : 0<δ) (hd : 0<d) (hr : 0≤r) (hscale : r*d^2=1) (hB : 0≤B)
    (hX : ‖X‖≤B) (hX' : ∀i,‖X' i‖≤B) (hJ : ‖J‖≤B)
    (hχ : |χ|≤B^2) (hχ' : ∀i,|χ' i|≤B^2)
    (hu : ‖u‖≤B) (hm : ‖m‖≤d) (hm' : ∀i,‖m' i‖≤d) (ht : ‖t‖≤d)
    (hell : ‖ell‖≤B*d) (hell' : ∀i,‖ell' i‖≤B*d) (hp : d*|p|≤B)
    (hS : ∀v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j b r X J q v))
    (hS' : ∀i v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j (b' i) r (X' i) J (q' i) v))
    (hSmall : |j| *|χ-b| *‖X‖^2+|j*r| *‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2)
    (hSmall' : ∀i,|j| *|χ' i-b' i| *‖X' i‖^2+|j*r| *‖X' i‖^2*
      (‖m' i+t-(2:ℝ) • q' i‖*‖ell' i‖+2*‖q' i‖*‖ell' i+q' i‖)≤δ/2)
    (h : Equations j χ r p (X*X) J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (X' i*X' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    (hDA : ∀V,columnNorm (fun i=>(s i • (X*X-X' i*X' i)) V)≤B*‖V‖)
    (hDu : columnNorm (fun i=>s i • (u-u' i))≤B)
    (hDχ : columnNorm (fun i=>s i*(χ-χ' i))≤B)
    (hDm : columnNorm (fun i=>s i • (m-m' i))≤B*d)
    (hDell : columnNorm (fun i=>s i • (ell-ell' i))≤B*d)
    (hDp : d*columnNorm (fun i=>s i*(p-p' i))≤B) :
    ‖w‖+d*|c|+‖y‖+columnNorm (fun i=>s i • (w-w' i))+
      d*columnNorm (fun i=>s i*(c-c' i))+columnNorm (fun i=>s i • (y-y' i))≤
        uniformControlBudget j δ B := by
  let L:=B+|j| *B^2+2*|j| *B
  let W:=(1+B^2*(δ/2)⁻¹*L)*B^2*(B+2*|j| *B)
  let C:=B*W+B
  let Y:=(B+|j| *B^2)*W+|j| *C
  let F:=(1+B^2*(δ/2)⁻¹*L)*(B*(B+Y+|j| *C)+B^2*B+
        |j| *B^2*W*B+|j| *B^2*C*B+|j| *B^2*2*(B*W+B))
  let G:=B*W+B+B*F
  let H:=(B+|j| *B^2)*F+|j| *W*B+|j| *C*B+|j| *G
  have hW0 : 0≤W := by dsimp [W,L]; positivity
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hY0 : 0≤Y := by dsimp [Y]; positivity
  have hL0 : 0≤L := by dsimp [L]; positivity
  have hF0 : 0≤F := by dsimp [F]; positivity
  obtain ⟨hw,hc,hy⟩:=implicit_uniform_size j χ b r p X J u m t ell q w y c
    hδ hd hr hscale (sq_nonneg B) hB hB hB hB
    (pow_le_pow_left₀ (norm_nonneg X) hX 2) hJ hχ hu hm ht hell hp hS hSmall h
  change ‖w‖≤W at hw
  change d*|c|≤C at hc
  change ‖y‖≤Y at hy
  have hl : ∀i,‖L₂ j (χ' i) r J (m' i+t) (ell' i)‖≤L := by
    intro i
    have hv : ‖m' i+t‖≤2*d := (norm_add_le _ _).trans (by linarith [hm' i])
    convert L₂_normalized_bound j (χ' i) r J (m' i+t) (ell' i) hr hd.le hscale
      (by norm_num : (0:ℝ)≤2) hB hv (hell' i) (hχ' i) hJ using 1; dsimp [L]; ring
  have hb : ‖u+J w-(j*χ) • w-(j*c) • (m+t)‖≤B+Y+|j| *C := by
    have he : u+J w-(j*χ) • w-(j*c) • (m+t)=u+y-(j*c) • t := by
      rw [h.2.1]; module
    rw [he]
    apply (norm_sub_le _ _).trans
    have hct : ‖(j*c) • t‖≤|j| *C := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul]
      calc
        _ ≤ |j| *|c| *d := mul_le_mul_of_nonneg_left ht (by positivity)
        _ = |j| *(d*|c|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hc (abs_nonneg j)
    exact add_le_add ((norm_add_le _ _).trans (add_le_add hu hy)) hct
  have hf:=implicit_frobenius_estimate j χ r p X J u m t ell w y c
    s χ' p' c' X' u' m' ell' w' y' q' b' h h' hδ hB hL0 hd hr hscale
    hB hB hB hB hB hB hC0 (by norm_num : (0:ℝ)≤2) hX' hl hS' hSmall'
    hDA hDu hDχ hDm hDell hDp hc (fun i=>(norm_add_le _ _).trans (by linarith [hm' i]))
  have hf' : columnNorm (fun i=>s i • (w-w' i))≤F := by
    apply hf.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hb hB) le_rfl)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by positivity)) hB)) le_rfl)
      (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hw hB) le_rfl) (by positivity))
  have hg : d*columnNorm (fun i=>s i*(c-c' i))≤G := by
    exact (implicit_scalar_columns s r p ell w c p' c' ell' w' h.2.2 (fun i=>(h' i).2.2)
      hr hd hscale hB hDell hDp hB hell').trans (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hw hB) le_rfl) (mul_le_mul_of_nonneg_left hf' hB))
  have hh : columnNorm (fun i=>s i • (y-y' i))≤H := by
    have hh:=implicit_field_columns s j χ r p (X*X) J u m t ell w y c χ' p' c'
      (fun i=>X' i*X' i) u' m' ell' w' y' h h' hB (sq_nonneg B) hd hB hB hC0
      (by norm_num : (0:ℝ)≤1) hJ hχ' hDχ hDm hc (by simpa only [one_mul] using hm') hg
    apply hh.trans
    simp only [mul_one]
    exact add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hf' (by positivity))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (abs_nonneg j)) hB)) le_rfl) le_rfl
  change _≤W+C+Y+F+G+H
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hw hc) hy) hf') hg) hh
end SKGap.ImplicitSystem

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.ImplicitSystem
variable {n : ℕ}

lemma halfDiff_column (U : VectorFields n) (x : Spin n) (k : Fin n) :
    ((spin x k/2) • ((WithLp.toLp 2 (U x) : Euclid n)-WithLp.toLp 2 (U (flip x k))))=
      WithLp.toLp 2 (fun i=>derivativeMatrix U x i k) := by
  ext i
  change (spin x k/2)*(U x i-U (flip x k) i)=halfDiff k (fun y=>U y i) x
  rw [halfDiff_as_flip]; ring

lemma columnNorm_halfDiff (U : VectorFields n) (x : Spin n) :
    columnNorm (fun k=>(spin x k/2) •
      ((WithLp.toLp 2 (U x) : Euclid n)-WithLp.toLp 2 (U (flip x k))))=‖derivativeMatrix U x‖ := by
  simp only [halfDiff_column]
  exact columnNorm_matrix _

lemma columnNorm_scalar_halfDiff (f : Spin n→ℝ) (x : Spin n) :
    columnNorm (fun k=>(spin x k/2)*(f x-f (flip x k)))=‖derivativeVector f x‖ := by
  have he : (fun k=>(spin x k/2)*(f x-f (flip x k)))=fun k=>halfDiff k f x := by
    ext k; rw [halfDiff_as_flip]; ring
  rw [he]
  rfl

lemma diagonal_halfDiff_columns (a : VectorFields n) (x : Spin n) {R : ℝ}
    (hR : 0≤R) (ha : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2)
    (V : Euclid n) :
    columnNorm (fun k=>((spin x k/2) •
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (Matrix.diagonal (a x))-
       Matrix.toEuclideanCLM (𝕜:=ℝ) (Matrix.diagonal (a (flip x k))))) V)≤R*‖V‖ := by
  apply coefficient_diagonal_columns (fun _=>a x) (fun k=>a (flip x k)) (fun k=>spin x k/2) hR
  intro i
  convert ha i using 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [derivativeMatrix,halfDiff_as_flip]
  ring

lemma implicit_tuple_small (w y : VectorFields n) (c : Spin n→ℝ) (x : Spin n)
    {d C : ℝ} (hd : 0≤d) (hC : 0≤C)
    (h : vectorNorm (w x)+d*|c x|+vectorNorm (y x)+‖derivativeMatrix w x‖+
      d*‖derivativeVector c x‖+‖derivativeMatrix y x‖≤C) :
    SmallBound w x C ∧ SmallBound y x C ∧
      |d*c x|≤C ∧ ‖derivativeVector (fun z=>d*c z) x‖≤C := by
  have hw0:=vectorNorm_nonneg (w x)
  have hy0:=vectorNorm_nonneg (y x)
  have hc0:=mul_nonneg hd (abs_nonneg (c x))
  have hw1:=norm_nonneg (derivativeMatrix w x)
  have hy1:=norm_nonneg (derivativeMatrix y x)
  have hc1:=mul_nonneg hd (norm_nonneg (derivativeVector c x))
  refine ⟨⟨hC,by linarith,by linarith⟩,⟨hC,by linarith,by linarith⟩,?_,?_⟩
  · rw [abs_mul,abs_of_nonneg hd]; linarith
  · have he : derivativeVector (fun z=>d*c z) x=d • derivativeVector c x := by
      ext k
      change halfDiff k (fun z=>d*c z) x=d*halfDiff k c x
      simp [halfDiff]; ring
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
    linarith
end SKGapCutoff.Recipe

end
end

end OAI
