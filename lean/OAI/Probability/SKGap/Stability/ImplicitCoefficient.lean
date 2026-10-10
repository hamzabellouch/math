import Mathlib
import OAI.Probability.SKGap.Stability.StableFields
import OAI.Probability.SKGap.Localization.Operation
import OAI.Probability.SKGap.Localization.PhiCoefficient
import OAI.Probability.SKGap.Stability.ImplicitLinear

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

lemma vectorNorm_const (c : ℝ) : vectorNorm (fun _ : Fin n=>c)=|c| *Real.sqrt n := by
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (by positivity)).mp
  rw [vectorNorm_sq,mul_pow,sq_abs,Real.sq_sqrt (Nat.cast_nonneg n)]
  simp [mul_comm]

lemma vectorNorm_neg (v : Fin n→ℝ) : vectorNorm (-v)=vectorNorm v := by
  exact norm_neg (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
lemma vectorNorm_sub (u v : Fin n→ℝ) : vectorNorm (u-v)≤vectorNorm u+vectorNorm v := by
  simpa only [sub_eq_add_neg,vectorNorm_neg] using vectorNorm_add u (-v)
lemma vectorNorm_tanh (z : Fin n→ℝ) : vectorNorm (fun i=>Real.tanh (z i))≤Real.sqrt n := by
  simpa only [vectorNorm_const,abs_one,one_mul] using
    (vectorNorm_mono (u:=fun i=>Real.tanh (z i)) (v:=fun _=>1)
      (fun i=>by simpa using (Real.abs_tanh_lt_one (z i)).le))
lemma vectorNorm_tanh_diff (z r : Fin n→ℝ) :
    vectorNorm (fun i=>Real.tanh (z i)-Real.tanh (r i))≤vectorNorm (z-r) :=
  vectorNorm_mono fun i=>tanh_lipschitz (r i) (z i)

lemma abs_logSlope_le_two (z r a : ℝ) : |logSlope z r a|≤2 := by
  rw [logSlope,abs_div,abs_of_pos (phi_pos z r a),div_le_iff₀ (phi_pos z r a)]
  exact phiZ_relative_bound z r a

lemma vectorNorm_logSlope (z r : Fin n→ℝ) (a : ℝ) :
    vectorNorm (fun i=>logSlope (z i) (r i) a)≤2*Real.sqrt n := by
  simpa only [vectorNorm_const,abs_of_pos (by norm_num : (0:ℝ)<2)] using
    (vectorNorm_mono (u:=fun i=>logSlope (z i) (r i) a) (v:=fun _=>2)
      (fun i=>by simpa using abs_logSlope_le_two (z i) (r i) a))

lemma vectorNorm_logSlope_near (z r : Fin n→ℝ) (a : ℝ) :
    vectorNorm (fun i=>logSlope (z i) (r i) a+Real.tanh (r i))≤3*vectorNorm (z-r) := by
  have h:=vectorNorm_mono (u:=fun i=>logSlope (z i) (r i) a+Real.tanh (r i))
    (v:=fun i=>3*(z i-r i)) (fun i=>by simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)] using
      (logSlope_near_diagonal (z i) (r i) a))
  apply h.trans_eq
  convert! vectorNorm_smul 3 (z-r) using 1
  norm_num

lemma phi_near_current (z r a : ℝ) {R : ℝ} (ha : |a|≤R) :
    |phi z r a-scalarVariance z|≤
      (2*Real.exp (R/2)+2)*|z-r|+(Real.exp (R/2)/2)*|a| := by
  have he:=Real.exp_le_exp.mpr (show |a|/2≤R/2 by linarith)
  have h₁:=(phi_near_root z r a).trans (mul_le_mul_of_nonneg_right he (by positivity))
  have h₂:=scalarVariance_lipschitz r z
  have h₃:=abs_sub_le (phi z r a) (scalarVariance r) (scalarVariance z)
  rw [abs_sub_comm (scalarVariance r)] at h₃
  linarith

lemma vectorNorm_phi_near_current (z r : Fin n→ℝ) (a : ℝ) {R : ℝ} (ha : |a|≤R) :
    vectorNorm (fun i=>phi (z i) (r i) a-scalarVariance (z i))≤
      (2*Real.exp (R/2)+2)*vectorNorm (z-r)+(Real.exp (R/2)/2)*|a| *Real.sqrt n := by
  let E:=Real.exp (R/2)
  have he:0≤E := (Real.exp_pos _).le
  have hmono:=vectorNorm_mono (u:=fun i=>phi (z i) (r i) a-scalarVariance (z i))
    (v:=fun i=>(2*E+2)*|z i-r i|+(E/2)*|a|) (fun i=>by
      rw [abs_of_nonneg (show 0≤(2*E+2)*|z i-r i|+(E/2)*|a| from by positivity)]
      exact phi_near_current _ _ _ ha)
  apply hmono.trans
  have ht:=vectorNorm_add ((2*E+2) • (fun i=>|z i-r i|)) (fun _=>(E/2)*|a|)
  rw [vectorNorm_smul,abs_of_nonneg (by positivity : 0≤2*E+2),
    vectorNorm_abs,vectorNorm_const,abs_of_nonneg (by positivity : 0≤(E/2)*|a|)] at ht
  exact ht

lemma normalized_mean_bound (u : Fin n→ℝ) (hn : 0<n) :
    |(∑i,u i)/(n:ℝ)|≤vectorNorm u/Real.sqrt n := by
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0<Real.sqrt n:=Real.sqrt_pos.mpr hnR
  have hh:=siteMean_square (fun _=>u) (fun _=>false) hn
  change (n:ℝ)*((∑i,u i)/(n:ℝ))^2≤(vectorNorm u)^2 at hh
  apply (sq_le_sq₀ (abs_nonneg _) (div_nonneg (vectorNorm_nonneg _) hs.le)).mp
  rw [sq_abs, div_pow, div_pow, Real.sq_sqrt hnR.le]
  exact (le_div_iff₀ hnR).mpr (by simpa only [div_pow, mul_comm] using hh)

theorem implicit_coefficient_bounds (z r : Fin n→ℝ) (a : ℝ) (hn : 0<n)
    {R ρ : ℝ} (hρ : 0≤ρ) (ha : |a|≤R) (haρ : |a|≤ρ)
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt n) :
    let E:=Real.exp (R/2)
    let A:=fun i=>phi (z i) (r i) a
    let ell:=fun i=>logSlope (z i) (r i) a
    let q:=fun i=>Real.tanh (z i)
    (∀i,0<A i ∧ A i≤E) ∧
    vectorNorm (A-(fun i=>scalarVariance (z i)))≤(3*E+2)*ρ*Real.sqrt n ∧
    |(∑i,A i)/(n:ℝ)-(∑i,scalarVariance (z i))/(n:ℝ)|≤(3*E+2)*ρ ∧
    vectorNorm (ell+q)≤4*ρ*Real.sqrt n ∧
    vectorNorm ell≤2*Real.sqrt n ∧ vectorNorm q≤Real.sqrt n := by
  dsimp only
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0<Real.sqrt n:=Real.sqrt_pos.mpr hnR
  have he:0<Real.exp (R/2):=Real.exp_pos _
  have hA : vectorNorm (fun i=>phi (z i) (r i) a-scalarVariance (z i))≤
      (3*Real.exp (R/2)+2)*ρ*Real.sqrt n := by
    apply (vectorNorm_phi_near_current z r a ha).trans
    have h₁:=mul_le_mul_of_nonneg_left hz (by positivity : 0≤2*Real.exp (R/2)+2)
    have h₂:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haρ
      (by positivity : 0≤Real.exp (R/2)/2)) hs.le
    nlinarith only [h₁,h₂,mul_nonneg he.le (mul_nonneg hρ hs.le)]
  refine ⟨fun i=>⟨phi_pos _ _ _,(phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith))⟩,hA,?_,?_,
    vectorNorm_logSlope z r a,vectorNorm_tanh z⟩
  · rw [←sub_div,←Finset.sum_sub_distrib]
    exact (normalized_mean_bound _ hn).trans ((div_le_div_of_nonneg_right hA hs.le).trans_eq (by field_simp))
  · have h₁:=vectorNorm_logSlope_near z r a
    have h₂:=vectorNorm_tanh_diff z r
    have h₃:=vectorNorm_add (fun i=>logSlope (z i) (r i) a+Real.tanh (r i))
      (fun i=>Real.tanh (z i)-Real.tanh (r i))
    have heq : (fun i=>logSlope (z i) (r i) a+Real.tanh (r i))+
        (fun i=>Real.tanh (z i)-Real.tanh (r i))=
        (fun i=>logSlope (z i) (r i) a)+(fun i=>Real.tanh (z i)) := by ext i; dsimp; ring
    rw [heq] at h₃
    nlinarith only [h₁,h₂,h₃,hz]

end SKGapCutoff.Recipe

end
end

section

noncomputable section
namespace SKGap.ImplicitSystem
open SKGap.ImplicitLinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma eliminated_rhs_bound (A : E →L[ℝ] E) (j p : ℝ) (u m t : E) :
    ‖A (u-(j*p) • (m+t))‖≤‖A‖*(‖u‖+|j| *|p| *(‖m‖+‖t‖)) := by
  calc
    _ ≤ ‖A‖*‖u-(j*p) • (m+t)‖ := A.le_opNorm _
    _ ≤ ‖A‖*(‖u‖+‖(j*p) • (m+t)‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ _ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left (norm_add_le m t) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))) (norm_nonneg _)

lemma implicit_scalar_size (r p : ℝ) (ell w : E) :
    |r*inner ℝ ell w+p|≤|r| *‖ell‖*‖w‖+|p| := by
  calc
    _ ≤ |r*inner ℝ ell w|+|p| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      nlinarith only [mul_le_mul_of_nonneg_left (abs_real_inner_le_norm ell w) (abs_nonneg r)]

lemma implicit_field_size (J : E →L[ℝ] E) (j χ c : ℝ) (w m : E) :
    ‖J w-(j*χ) • w-(j*c) • m‖≤(‖J‖+|j*χ|)*‖w‖+|j| *|c| *‖m‖ := by
  calc
    _ ≤ ‖J w-(j*χ) • w‖+‖(j*c) • m‖ := norm_sub_le _ _
    _ ≤ ‖J w‖+‖(j*χ) • w‖+‖(j*c) • m‖ := add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ _ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul]
      nlinarith only [J.le_opNorm w]

variable [FiniteDimensional ℝ E]

theorem implicit_size_bounds (j χ b r p : ℝ) (X J : E →L[ℝ] E)
    (u m t ell q w y : E) (c : ℝ) {δ : ℝ} (hδ : 0<δ)
    (hStable : ∀v,δ*‖v‖^2 ≤ inner ℝ v (stableMatrix j b r X J q v))
    (hSmall : |j| *|χ-b| *‖X‖^2+|j*r| *‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2)
    (hEq : Equations j χ r p (X*X) J u m t ell w y c) :
    let W := (1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖)*
      ‖X‖^2*(‖u‖+|j| *|p| *(‖m‖+‖t‖))
    ‖w‖≤W ∧ |c|≤|r| *‖ell‖*W+|p| ∧
      ‖y‖≤(‖J‖+|j*χ|)*W+|j| *(|r| *‖ell‖*W+|p|)*‖m‖ := by
  dsimp only
  let W := (1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖)*
      ‖X‖^2*(‖u‖+|j| *|p| *(‖m‖+‖t‖))
  have hPert := (normalized_difference_bound j χ b r X J (m+t) ell q).trans hSmall
  obtain ⟨B,hMB,hBM,hB⟩ := unnormalized_inverse X (L₂ j χ r J (m+t) ell)
    (stableMatrix j b r X J q) (by linarith : δ/2<δ) hStable hPert
  have hw : (1+X*X*L₂ j χ r J (m+t) ell) w=(X*X) (u-(j*p) • (m+t)) := by
    apply (eliminated_equation j χ r p (X*X) J u m t ell w).mp
    rcases hEq with ⟨hw,hy,hc⟩
    refine ⟨?_,rfl,rfl⟩
    simpa only [←hc,←hy] using hw
  have hform : w=B ((X*X) (u-(j*p) • (m+t))) := by
    rw [←hw]
    change w=(B*(1+X*X*L₂ j χ r J (m+t) ell)) w
    rw [hBM]; rfl
  have hBB : ‖B‖≤1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖ := by
    convert hB using 2
    congr 2
    ring
  have hwB : ‖w‖≤W := by
    calc
      ‖w‖=‖B ((X*X) (u-(j*p) • (m+t)))‖ := congrArg norm hform
      _ ≤ ‖B‖*‖(X*X) (u-(j*p) • (m+t))‖ := B.le_opNorm _
      _ ≤ ‖B‖*(‖X*X‖*(‖u‖+|j| *|p| *(‖m‖+‖t‖))) :=
        mul_le_mul_of_nonneg_left (eliminated_rhs_bound (X*X) j p u m t) (norm_nonneg _)
      _ ≤ W := by
        dsimp [W]
        have hX : ‖X*X‖≤‖X‖^2 := by simpa only [pow_two] using norm_mul_le X X
        have h0 : 0≤‖u‖+|j| *|p| *(‖m‖+‖t‖) := by positivity
        have hK : 0≤1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖ := by positivity
        calc
          _ ≤ (1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖)*
              (‖X‖^2*(‖u‖+|j| *|p| *(‖m‖+‖t‖))) :=
            mul_le_mul hBB (mul_le_mul_of_nonneg_right hX h0) (by positivity) hK
          _ = _ := by ring
  have hcB : |c|≤|r| *‖ell‖*W+|p| := by
    rw [hEq.2.2]
    exact (implicit_scalar_size r p ell w).trans
      (add_le_add (mul_le_mul_of_nonneg_left hwB (mul_nonneg (abs_nonneg _) (norm_nonneg _))) (le_refl _))
  refine ⟨hwB,hcB,?_⟩
  rw [hEq.2.1]
  apply (implicit_field_size J j χ c w m).trans
  exact add_le_add (mul_le_mul_of_nonneg_left hwB (by positivity))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcB (abs_nonneg j)) (norm_nonneg m))

end SKGap.ImplicitSystem

end
end

end OAI
