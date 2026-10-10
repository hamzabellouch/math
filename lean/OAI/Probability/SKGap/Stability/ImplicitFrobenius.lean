import Mathlib
import OAI.Probability.SKGap.Stability.ImplicitFlip

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ImplicitSystem
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ι : Type*} [Fintype ι]

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
lemma columnNorm_compare (U : ι→E) (V : ι→F) {C : ℝ} (hC : 0≤C)
    (h : ∀i,‖U i‖≤C*‖V i‖) : columnNorm U≤C*columnNorm V := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC (columnNorm_nonneg _))
  simp only [←sq,columnNorm_sq,mul_pow,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (U i)) (h i) 2

lemma columnNorm_inner_common (V : ι→E) (w : E) :
    columnNorm (fun i=>inner ℝ (V i) w)≤‖w‖*columnNorm V := by
  apply columnNorm_compare _ _ (norm_nonneg w)
  intro i
  simpa only [Real.norm_eq_abs,mul_comm] using abs_real_inner_le_norm (V i) w

lemma columnNorm_inner_variable (V W : ι→E) {C : ℝ}
    (hC : 0≤C) (hV : ∀i,‖V i‖≤C) :
    columnNorm (fun i=>inner ℝ (V i) (W i))≤C*columnNorm W := by
  apply columnNorm_compare _ _ hC
  intro i
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hV i) (norm_nonneg _))

lemma normalized_coefficient_difference (D : ι→E) (dp : ι→ℝ) (w : E)
    {r d R P : ℝ} (hr : 0≤r) (hd : 0<d) (hscale : r*d^2=1)
    (_hR : 0≤R) (hD : columnNorm D≤R*d) (hP : d*columnNorm dp≤P) :
    d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)≤R*‖w‖+P := by
  have he : (fun i=>r*inner ℝ (D i) w+dp i)=r • (fun i=>inner ℝ (D i) w)+dp := rfl
  rw [he]
  have hc:=columnNorm_add (r • (fun i=>inner ℝ (D i) w)) dp
  rw [columnNorm_smul,abs_of_nonneg hr] at hc
  have hi:=(columnNorm_inner_common D w).trans
    (mul_le_mul_of_nonneg_left hD (norm_nonneg w))
  calc
    _ ≤ d*(r*(‖w‖*(R*d))+columnNorm dp) := mul_le_mul_of_nonneg_left
      (hc.trans (add_le_add (mul_le_mul_of_nonneg_left hi hr) le_rfl)) hd.le
    _ = R*‖w‖*(r*d^2)+d*columnNorm dp := by ring
    _ = R*‖w‖+d*columnNorm dp := by rw [hscale]; ring
    _ ≤ _ := add_le_add le_rfl hP

lemma normalized_scalar_difference (D W L : ι→E) (dp : ι→ℝ) (w : E)
    {r d R P Q : ℝ} (hr : 0≤r) (hd : 0<d) (hscale : r*d^2=1)
    (hR : 0≤R) (hD : columnNorm D≤R*d) (hP : d*columnNorm dp≤P)
    (hQ : 0≤Q) (hL : ∀i,‖L i‖≤Q*d) :
    d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i+r*inner ℝ (L i) (W i))≤
      R*‖w‖+P+Q*columnNorm W := by
  have h₁:=normalized_coefficient_difference D dp w hr hd hscale hR hD hP
  have h₂:=columnNorm_inner_variable L W (mul_nonneg hQ hd.le) hL
  have he : (fun i=>r*inner ℝ (D i) w+dp i+r*inner ℝ (L i) (W i))=
      (fun i=>r*inner ℝ (D i) w+dp i)+r • (fun i=>inner ℝ (L i) (W i)) := rfl
  rw [he]
  have hh:=columnNorm_add (fun i=>r*inner ℝ (D i) w+dp i) (r • (fun i=>inner ℝ (L i) (W i)))
  rw [columnNorm_smul,abs_of_nonneg hr] at hh
  calc
    _ ≤ d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)+d*r*((Q*d)*columnNorm W) := by
      nlinarith only [mul_le_mul_of_nonneg_left hh hd.le,
        mul_le_mul_of_nonneg_left h₂ (mul_nonneg hd.le hr)]
    _ = d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)+Q*columnNorm W*(r*d^2) := by ring
    _ = d*columnNorm (fun i=>r*inner ℝ (D i) w+dp i)+Q*columnNorm W := by rw [hscale]; ring
    _ ≤ _ := add_le_add h₁ le_rfl

variable [FiniteDimensional ℝ E]

theorem implicit_frobenius_estimate (j χ r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell w y : E) (c : ℝ)
    (s χ' p' c' : ι→ℝ) (X' : ι→E→L[ℝ]E) (u' m' ell' w' y' q' : ι→E) (b' : ι→ℝ)
    (h : Equations j χ r p (X*X) J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (X' i*X' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    {δ X₀ L₀ d RA U Rχ Rm Rell P C V : ℝ}
    (hδ : 0<δ) (hX₀ : 0≤X₀) (hL₀ : 0≤L₀) (hd : 0<d) (hr : 0≤r) (hscale : r*d^2=1)
    (_hRA : 0≤RA) (_hU : 0≤U) (_hRχ : 0≤Rχ) (hRm : 0≤Rm) (hRell : 0≤Rell)
    (_hP : 0≤P) (_hC : 0≤C) (hV : 0≤V)
    (hX : ∀i,‖X' i‖≤X₀) (hL : ∀i,‖L₂ j (χ' i) r J (m' i+t) (ell' i)‖≤L₀)
    (hS : ∀i v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j (b' i) r (X' i) J (q' i) v))
    (hSmall : ∀i,|j| *|χ' i-b' i| *‖X' i‖^2+|j*r| *‖X' i‖^2*
      (‖m' i+t-(2:ℝ) • q' i‖*‖ell' i‖+2*‖q' i‖*‖ell' i+q' i‖)≤δ/2)
    (hDA : ∀B, columnNorm (fun i=>(s i • (X*X-X' i*X' i)) B)≤RA*‖B‖)
    (hDu : columnNorm (fun i=>s i • (u-u' i))≤U)
    (hDχ : columnNorm (fun i=>s i*(χ-χ' i))≤Rχ)
    (hDm : columnNorm (fun i=>s i • (m-m' i))≤Rm*d)
    (hDell : columnNorm (fun i=>s i • (ell-ell' i))≤Rell*d)
    (hDp : d*columnNorm (fun i=>s i*(p-p' i))≤P)
    (hc : d*|c|≤C) (hv : ∀i,‖m' i+t‖≤V*d) :
    columnNorm (fun i=>s i • (w-w' i))≤(1+X₀^2*(δ/2)⁻¹*L₀)*
      (RA*‖u+J w-(j*χ) • w-(j*c) • (m+t)‖+X₀^2*U+
        |j| *X₀^2*‖w‖*Rχ+|j| *X₀^2*C*Rm+
        |j| *X₀^2*V*(Rell*‖w‖+P)) := by
  let A':=fun i=>X' i*X' i
  have hA : ∀i,‖A' i‖≤X₀^2 := fun i=>(norm_mul_le _ _).trans
    (by simpa only [pow_two] using mul_le_mul (hX i) (hX i) (norm_nonneg _) hX₀)
  let z:=fun i=>r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i)
  have hz : d*columnNorm z≤Rell*‖w‖+P :=
    normalized_coefficient_difference _ _ w hr hd hscale hRell hDell hDp
  have h₂ : columnNorm (fun i=>A' i (s i • (u-u' i)))≤X₀^2*U :=
    (columnNorm_operator A' _ (sq_nonneg _) hA).trans (mul_le_mul_of_nonneg_left hDu (sq_nonneg _))
  have h₃ : columnNorm (fun i=>(j*(s i*(χ-χ' i))) • A' i w)≤|j| *X₀^2*‖w‖*Rχ := by
    have he : (fun i=>(j*(s i*(χ-χ' i))) • A' i w)=
        j • (fun i=>(s i*(χ-χ' i)) • A' i w) := by ext i; simp [mul_smul]
    rw [he,columnNorm_smul]
    have hb : ∀i,‖A' i w‖≤X₀^2*‖w‖ := fun i=>((A' i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
    have hh:=(columnNorm_vector_scalar _ _ (by positivity : 0≤X₀^2*‖w‖) hb).trans
      (mul_le_mul_of_nonneg_left hDχ (by positivity))
    nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg j)]
  have h₄ : columnNorm (fun i=>(j*c) • A' i (s i • (m-m' i)))≤|j| *X₀^2*C*Rm := by
    change columnNorm ((j*c) • (fun i=>A' i (s i • (m-m' i))))≤_
    rw [columnNorm_smul,abs_mul]
    have hh:=(columnNorm_operator A' _ (sq_nonneg _) hA).trans
      (mul_le_mul_of_nonneg_left hDm (sq_nonneg _))
    calc
      _ ≤ |j| *|c| *(X₀^2*(Rm*d)) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (|j| *X₀^2*Rm)*(d*|c|) := by ring
      _ ≤ (|j| *X₀^2*Rm)*C := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  have h₅ : columnNorm (fun i=>(j*z i) • A' i (m' i+t))≤|j| *X₀^2*V*(Rell*‖w‖+P) := by
    have he : (fun i=>(j*z i) • A' i (m' i+t))=j • (fun i=>z i • A' i (m' i+t)) := by
      ext i; simp [mul_smul]
    rw [he,columnNorm_smul]
    have hb : ∀i,‖A' i (m' i+t)‖≤X₀^2*(V*d) := fun i=>((A' i).le_opNorm _).trans
      (mul_le_mul (hA i) (hv i) (norm_nonneg _) (sq_nonneg _))
    have hh:=columnNorm_vector_scalar (fun i=>A' i (m' i+t)) z (by positivity : 0≤X₀^2*(V*d)) hb
    calc
      _ ≤ |j| *((X₀^2*(V*d))*columnNorm z) := mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      _ = (|j| *X₀^2*V)*(d*columnNorm z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)
  have H:=implicit_columns_bound j χ r p X J u m t ell w y c s χ' p' c' X' u' m' ell' w' y' q' b'
    h h' hδ hX₀ hL₀ hX hL hS hSmall
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (add_le_add (add_le_add (add_le_add (hDA _) h₂) h₃) h₄) h₅

end SKGap.ImplicitSystem
namespace SKGapCutoff.Recipe
open Matrix
variable {n : ℕ}
lemma frobenius_by_rows (D : Interaction n) {R : ℝ} (hR : 0≤R)
    (hD : ∀i,∑k,(D i k)^2≤R^2) : ‖D‖≤R*Real.sqrt n := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hR (Real.sqrt_nonneg _))
  simp only [←sq,SKGap.frobenius_sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ∑_i:Fin n,R^2 := Finset.sum_le_sum fun i _=>hD i
    _ = _ := by simp [mul_comm]

lemma coefficient_diagonal_columns (a a' : Fin n→Fin n→ℝ) (s : Fin n→ℝ)
    {R : ℝ} (hR : 0≤R) (ha : ∀i,∑k,(s k*(a k i-a' k i))^2≤R^2)
    (B : EuclideanSpace ℝ (Fin n)) :
    SKGap.ImplicitSystem.columnNorm (fun k=>(s k •
      (toEuclideanCLM (𝕜:=ℝ) (diagonal (a k))-toEuclideanCLM (𝕜:=ℝ) (diagonal (a' k)))) B)≤R*‖B‖ := by
  let D : Interaction n:=fun i k=>B i*(s k*(a k i-a' k i))
  have he : (fun k=>(s k •
      (toEuclideanCLM (𝕜:=ℝ) (diagonal (a k))-toEuclideanCLM (𝕜:=ℝ) (diagonal (a' k)))) B)=
      (fun k=>(WithLp.toLp 2 (fun i=>D i k) : EuclideanSpace ℝ (Fin n))) := by
    ext k i
    change s k*((toEuclideanCLM (𝕜:=ℝ) (diagonal (a k)) (WithLp.toLp 2 B.ofLp)) i-
      (toEuclideanCLM (𝕜:=ℝ) (diagonal (a' k)) (WithLp.toLp 2 B.ofLp)) i)=D i k
    simp only [toEuclideanCLM_toLp,WithLp.ofLp_toLp,mulVec_diagonal,D]
    ring
  rw [he,columnNorm_matrix]
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hR (norm_nonneg _))
  simp only [←sq,SKGap.frobenius_sq,mul_pow,EuclideanSpace.real_norm_sq_eq]
  calc
    _ = ∑i,(B i)^2*(∑k,(s k*(a k i-a' k i))^2) := by
      simp only [D,mul_pow,Finset.mul_sum]
    _ ≤ ∑i,(B i)^2*R^2 := Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (ha i) (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
end SKGapCutoff.Recipe

end
end

end OAI
