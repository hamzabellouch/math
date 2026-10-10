import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySparseNumerics

theorem compress_energy (E A G b ε x y w δ : ℝ)
    (hG : 0<G) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxG : x ≤ G⁻¹) (hyG : y ≤ G⁻¹) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hA : 0 ≤ A) (hAδ : A ≤ δ)
    (hb : E  ≤  2*b^2*ε^2*((264*G⁻¹+x)*(44*G⁻¹+y)/4) + 2*(264+w)*A) :
    E  ≤  6000*(b/G)^2*ε^2 + 530*δ := by
  have hi : 0 ≤ G⁻¹ := inv_nonneg.mpr hG.le
  have hmul : (264*G⁻¹+x)*(44*G⁻¹+y)  ≤  (265*G⁻¹)*(45*G⁻¹) := by
    apply mul_le_mul <;> nlinarith
  have hm := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 2*b^2*ε^2/4 by positivity)
  have ht : 2*(264+w)*A  ≤  530*δ := by
    calc
      _ ≤ 2*(264+w)*δ :=
        mul_le_mul_of_nonneg_left hAδ
          (mul_nonneg (by norm_num) (add_nonneg (by norm_num) hw))
      _ ≤ 530*δ := by nlinarith
  have he : 2*b^2*ε^2*((264*G⁻¹+x)*(44*G⁻¹+y)/4)  ≤ 
      6000*(b/G)^2*ε^2 := by
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm, sq_nonneg (b*G⁻¹*ε)]
  linarith

lemma log_two_lower : (1/2:ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h ⊢
  exact h

theorem middle_density (G d s q n A B C : ℝ)
    (hd : 0<d) (hs : 0<s) (hq : 0<q) (hn : 0<n)
    (hG : d*n*Real.log 2/2 ≤ G)
    (hsmall : 1+Real.log q ≤ n*Real.log 2)
    (hA : A ≤ G⁻¹*(1+Real.log q+n*Real.log 2))
    (hB : B ≤ 2*Real.log 4*(d*n)/(Real.log q+s*n*Real.log 2))
    (hlogq : 0 ≤ Real.log q)
    (hC : C ≤ (3/2)*G⁻¹*(s*n)/q) :
    A+B+C  ≤  4/d + 4*d/s + 6*s/(q*d) := by
  have hln : 0<Real.log 2 := lt_of_lt_of_le (by norm_num) log_two_lower
  have hGpos : 0<G := lt_of_lt_of_le (by positivity) hG
  have hi : G⁻¹  ≤  2/(d*n*Real.log 2) := by
    calc
      _  ≤  (d*n*Real.log 2/2)⁻¹ := inv_anti₀ (by positivity) hG
      _ = _ := by field_simp
  have ha : A ≤ 4/d := by
    apply hA.trans
    calc
      _  ≤  (2/(d*n*Real.log 2))*(2*(n*Real.log 2)) := by
        apply mul_le_mul hi (by linarith) (by positivity) (by positivity)
      _ = _ := by field_simp; ring
  have hden : 0<s*n*Real.log 2 := by positivity
  have hb : B ≤ 4*d/s := by
    apply hB.trans
    calc
      _  ≤  2*Real.log 4*(d*n)/(s*n*Real.log 2) := by
        apply div_le_div_of_nonneg_left (by positivity) hden
        linarith
      _ = _ := by
        rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
        field_simp
        ring
  have hc : C ≤ 6*s/(q*d) := by
    apply hC.trans
    calc
      _  ≤  (3/2)*(2/(d*n*Real.log 2))*(s*n)/q := by gcongr
      _ = 3*s/(q*d*Real.log 2) := by field_simp
      _  ≤  6*s/(q*d) := by
        apply (div_le_iff₀ (by positivity : 0<q*d*Real.log 2)).mpr
        have heq : 6*s/(q*d)*(q*d*Real.log 2) = 6*s*Real.log 2 := by
          field_simp
        rw [heq]
        nlinarith [log_two_lower]
  linarith

theorem compress_scaled_energy (E A A₀ G b B n g ε x y w : ℝ)
    (hn : 0<n) (hg : 0<g) (hG : g*n ≤ G)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hbB : b ≤ B*n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxn : x ≤ 1/n) (hyn : y ≤ 1/n)
    (hw : w ≤ 1) (hA : 0 ≤ A) (hA₀ : A ≤ A₀)
    (he : E ≤ 2*b^2*ε^2*((264*G⁻¹+x)*(44*G⁻¹+y)/4)+2*(264+w)*A) :
    E ≤ (B^2/2*(264/g+1)*(44/g+1))*ε^2+530*A₀ := by
  have hGp : 0<G := lt_of_lt_of_le (mul_pos hg hn) hG
  have hi : G⁻¹ ≤ (g*n)⁻¹ := inv_anti₀ (mul_pos hg hn) hG
  have ha : 264*G⁻¹+x ≤ (264/g+1)/n := by
    calc
      _  ≤  264*(g*n)⁻¹+1/n := by linarith
      _ = _ := by field_simp
  have hc : 44*G⁻¹+y ≤ (44/g+1)/n := by
    calc
      _  ≤  44*(g*n)⁻¹+1/n := by linarith
      _ = _ := by field_simp
  have hprod := mul_le_mul ha hc (by positivity : 0 ≤ 44*G⁻¹+y)
    (by positivity : 0 ≤ (264/g+1)/n)
  have hbp := (sq_le_sq₀ hb (mul_nonneg hB hn.le)).mpr hbB
  have hmid : 2*b^2*ε^2*((264*G⁻¹+x)*(44*G⁻¹+y)/4)  ≤ 
      (B^2/2*(264/g+1)*(44/g+1))*ε^2 := by
    calc
      _  ≤  2*(B*n)^2*ε^2*(((264/g+1)/n)*((44/g+1)/n)/4) := by
        apply mul_le_mul
        · gcongr
        · exact div_le_div_of_nonneg_right hprod (by norm_num)
        · positivity
        · positivity
      _ = _ := by field_simp; ring
  have ht : 2*(264+w)*A ≤ 530*A₀ := by nlinarith
  linarith

lemma exists_density_parameters {η : ℝ} (hη : 0<η) :
    ∃ d s q : ℕ, 0<d ∧ 1 ≤ s ∧ 0<q ∧
      4/(d:ℝ)+4*(d:ℝ)/s+6*(s:ℝ)/((q:ℝ)*d)<η := by
  obtain ⟨d,hd⟩ := exists_nat_gt (max 1 (12/η))
  have hd1 : (1:ℝ)<d := (le_max_left _ _).trans_lt hd
  have hd0 : (0:ℝ)<d := by linarith
  have hdη : 12/η < (d:ℝ) := (le_max_right _ _).trans_lt hd
  obtain ⟨s,hs⟩ := exists_nat_gt (max 1 (12*(d:ℝ)/η))
  have hs1 : (1:ℝ)<s := (le_max_left _ _).trans_lt hs
  have hs0 : (0:ℝ)<s := by linarith
  have hsη : 12*(d:ℝ)/η < (s:ℝ) := (le_max_right _ _).trans_lt hs
  obtain ⟨q,hq⟩ := exists_nat_gt (max 1 (18*(s:ℝ)/((d:ℝ)*η)))
  have hq1 : (1:ℝ)<q := (le_max_left _ _).trans_lt hq
  have hq0 : (0:ℝ)<q := by linarith
  have hqη : 18*(s:ℝ)/((d:ℝ)*η)<q := (le_max_right _ _).trans_lt hq
  refine ⟨d,s,q,by exact_mod_cast hd0,by exact_mod_cast hs1.le,
    by exact_mod_cast hq0,?_⟩
  have ha : 4/(d:ℝ)<η/3 := by
    apply (div_lt_iff₀ hd0).mpr
    have hh := (div_lt_iff₀ hη).mp hdη
    nlinarith
  have hb : 4*(d:ℝ)/(s:ℝ)<η/3 := by
    apply (div_lt_iff₀ hs0).mpr
    have hh := (div_lt_iff₀ hη).mp hsη
    nlinarith
  have hc : 6*(s:ℝ)/((q:ℝ)*d)<η/3 := by
    apply (div_lt_iff₀ (mul_pos hq0 hd0)).mpr
    have hh := (div_lt_iff₀ (mul_pos hd0 hη)).mp hqη
    nlinarith
  linarith

end OrdinarySparseNumerics

end

end OAI
