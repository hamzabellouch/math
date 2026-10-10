import Mathlib
import OAI.Probability.SKGap.Stability.ImplicitCoefficient

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem
variable {n : ℕ}

lemma vectorNorm_implicit_rank (z r m : Fin n→ℝ) {ρ : ℝ}
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt n)
    (hm : vectorNorm (m-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt n) :
    vectorNorm (m+(fun i=>Real.tanh (r i))-(2:ℝ) • (fun i=>Real.tanh (z i)))≤
      3*ρ*Real.sqrt n := by
  let q:=fun i=>Real.tanh (z i)
  let t:=fun i=>Real.tanh (r i)
  have ht:=vectorNorm_tanh_diff z r
  have ht' : vectorNorm (t-q)≤ρ*Real.sqrt n := by
    have he : t-q= -(q-t) := by ext i; dsimp; ring
    rw [he,vectorNorm_neg]
    exact ht.trans hz
  have hh:=vectorNorm_add (m-t) ((2:ℝ) • (t-q))
  rw [vectorNorm_smul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  have he : (m-t)+(2:ℝ) • (t-q)=m+t-(2:ℝ) • q := by ext i; dsimp; ring
  rw [he] at hh
  exact hh.trans (by nlinarith only [hm,ht'])

theorem implicit_normalized_perturbation (z r m : Fin n→ℝ) (a j : ℝ)
    (X : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hn : 0<n) {R ρ : ℝ} (hρ : 0≤ρ) (ha : |a|≤R) (haρ : |a|≤ρ)
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt n)
    (hm : vectorNorm (m-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt n)
    (hX : ‖X‖^2≤Real.exp (R/2)) :
    let χ:=(∑i,phi (z i) (r i) a)/(n:ℝ)
    let b:=(∑i,scalarVariance (z i))/(n:ℝ)
    let ell:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 (fun i=>logSlope (z i) (r i) a)
    let q:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 (fun i=>Real.tanh (z i))
    let t:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 (fun i=>Real.tanh (r i))
    let M:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 m
    |j| *|χ-b| *‖X‖^2+|j*(n:ℝ)⁻¹| *‖X‖^2*
      (‖M+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤
        |j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)*ρ := by
  dsimp only
  obtain ⟨hA,hAv,hχ,hEllq,hEll,hq⟩:=implicit_coefficient_bounds z r a hn hρ ha haρ hz
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0≤Real.sqrt n:=Real.sqrt_nonneg _
  have he:0≤Real.exp (R/2):=(Real.exp_pos _).le
  have hv:=vectorNorm_implicit_rank z r m hz hm
  have hbr : vectorNorm (m+(fun i=>Real.tanh (r i))-(2:ℝ) • (fun i=>Real.tanh (z i)))*
      vectorNorm (fun i=>logSlope (z i) (r i) a)+
      2*vectorNorm (fun i=>Real.tanh (z i))*
      vectorNorm ((fun i=>logSlope (z i) (r i) a)+(fun i=>Real.tanh (z i)))≤14*ρ*(n:ℝ) := by
    have h₁:=mul_le_mul hv hEll (vectorNorm_nonneg _) (by positivity : 0≤3*ρ*Real.sqrt n)
    have h₂:=mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤2)) hEllq
      (vectorNorm_nonneg _) (by positivity : 0≤2*Real.sqrt n)
    apply (add_le_add h₁ h₂).trans_eq
    calc
      _ = 14*ρ*(Real.sqrt n)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hnR.le]
  change |j| *|_| *‖X‖^2+|j*(n:ℝ)⁻¹| *‖X‖^2*
    (vectorNorm _*vectorNorm _+2*vectorNorm _*vectorNorm _)≤_
  calc
    _ ≤ |j| *((3*Real.exp (R/2)+2)*ρ)*Real.exp (R/2)+
        |j*(n:ℝ)⁻¹| *Real.exp (R/2)*(14*ρ*(n:ℝ)) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hχ (abs_nonneg _)) hX (sq_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hX (abs_nonneg _)) hbr
          (add_nonneg (mul_nonneg (vectorNorm_nonneg _) (vectorNorm_nonneg _))
            (mul_nonneg (mul_nonneg (by norm_num) (vectorNorm_nonneg _)) (vectorNorm_nonneg _))) (by positivity)
    _ = _ := by
      rw [abs_mul,abs_inv,abs_of_pos hnR]
      field_simp
      ring

lemma implicit_rho_threshold (j R δ ρ : ℝ) (hδ : 0<δ)
    (hρ : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    |j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)*ρ≤δ/2 := by
  let K:=|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)
  have hK : 0≤K := by dsimp [K]; positivity
  have hp : 0<2*(K+1) := by positivity
  apply (mul_le_mul_of_nonneg_left hρ hK).trans
  change K*(δ/(2*(K+1)))≤δ/2
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  rw [mul_assoc,div_mul_eq_mul_div,←mul_div_assoc]
  apply (div_le_iff₀ hp).mpr
  nlinarith

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}
abbrev Euclid (n : ℕ) := EuclideanSpace ℝ (Fin n)

def phiDiagonal (z r : Fin n→ℝ) (a : ℝ) : Euclid n→L[ℝ]Euclid n :=
  Matrix.toEuclideanCLM (𝕜:=ℝ) (diagonal (fun i=>phi (z i) (r i) a))
def phiSqrt (z r : Fin n→ℝ) (a : ℝ) : Euclid n→L[ℝ]Euclid n :=
  Matrix.toEuclideanCLM (𝕜:=ℝ) (diagonal (fun i=>Real.sqrt (phi (z i) (r i) a)))

lemma phiSqrt_square (z r : Fin n→ℝ) (a : ℝ) :
    phiSqrt z r a*phiSqrt z r a=phiDiagonal z r a := by
  rw [phiSqrt,phiDiagonal,←map_mul,diagonal_mul_diagonal]
  congr 2
  ext i
  exact Real.mul_self_sqrt (phi_pos _ _ _).le

lemma phiSqrt_bound (z r : Fin n→ℝ) (a : ℝ) {R : ℝ} (ha : |a|≤R) :
    ‖phiSqrt z r a‖^2≤Real.exp (R/2) := by
  have he : 0≤Real.exp (R/2):=(Real.exp_pos _).le
  have hh : ‖phiSqrt z r a‖≤Real.sqrt (Real.exp (R/2)) := by
    apply SKGap.opNorm_diagonal_le (Real.sqrt_nonneg _)
    intro i
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (Real.sq_sqrt he)

theorem literal_implicit_exists_unique (z r m : Fin n→ℝ) (a j p : ℝ)
    (J : Euclid n→L[ℝ]Euclid n) (u : Euclid n) (hn : 0<n)
    {R ρ δ : ℝ} (hδ : 0<δ) (hρ : 0≤ρ) (ha : |a|≤R) (haρ : |a|≤ρ)
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt n)
    (hm : vectorNorm (m-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt n)
    (hρsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (hStable : ∀v,δ*‖v‖^2 ≤ inner ℝ v
      (stableMatrix j ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹
        (phiSqrt z r a) J (WithLp.toLp 2 (fun i=>Real.tanh (z i))) v)) :
    ∃! sol : Euclid n×Euclid n×ℝ,
      Equations j ((∑i,phi (z i) (r i) a)/(n:ℝ)) (n:ℝ)⁻¹ p
        (phiDiagonal z r a) J u (WithLp.toLp 2 m)
        (WithLp.toLp 2 (fun i=>Real.tanh (r i)))
        (WithLp.toLp 2 (fun i=>logSlope (z i) (r i) a)) sol.1 sol.2.1 sol.2.2 := by
  have hSmall:=(implicit_normalized_perturbation z r m a j (phiSqrt z r a) hn hρ ha haρ hz hm
    (phiSqrt_bound z r a ha)).trans (implicit_rho_threshold j R δ ρ hδ hρsmall)
  have H:=unique_implicit_solution j ((∑i,phi (z i) (r i) a)/(n:ℝ))
    ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹ p (phiSqrt z r a) J u
    (WithLp.toLp 2 m) (WithLp.toLp 2 (fun i=>Real.tanh (r i)))
    (WithLp.toLp 2 (fun i=>logSlope (z i) (r i) a))
    (WithLp.toLp 2 (fun i=>Real.tanh (z i))) hδ hStable hSmall
  simpa only [phiSqrt_square] using H

end SKGapCutoff.Recipe

end
end

end OAI
