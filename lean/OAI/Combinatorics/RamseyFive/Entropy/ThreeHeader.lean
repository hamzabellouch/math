import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ThreePublicDefs

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization

private lemma log_three_sum {x y z : ℝ} (hx : 1≤x) (hy : 1≤y) (hz : 0≤z) (hzy : z≤y) :
    Real.log (1+(x+z))≤Real.log 3+Real.log x+Real.log y := by
  have hxy : x≤x*y := le_mul_of_one_le_right (by linarith) hy
  have hyx : y≤x*y := le_mul_of_one_le_left (by linarith) hx
  have h1 : 1≤x*y := hx.trans hxy
  have hh := Real.log_le_log (by positivity : 0<1+(x+z))
    (show 1+(x+z)≤3*x*y by linarith)
  rw [Real.log_mul (by positivity) (by linarith),Real.log_mul (by norm_num) (by linarith)] at hh
  exact hh

theorem threePublic_header {K : Type} [Field K] [Finite K] [Fintype K]
    [Fintype (ℙ K (Fin 4→K))] (σ : ℝ) (hσ : 100000≤σ)
    (hq : Real.exp σ=Nat.card K) :
    Real.log (Fintype.card (ThreePublicIndex K σ):ℝ)≤35*(Nat.card K:ℝ) := by
  have hd : finrank K (Fin 4→K)≤5 := by simp
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hσq : σ≤Nat.card K := by rw [←hq];linarith only [Real.add_one_le_exp σ]
  have hh := projective_header_le (K:=K) (V:=Fin 4→K) σ (by linarith) hq hd
  have ht := log_card_training_le (V:=Fin 4→K) σ hσ (vector_card_le_exp σ hq hd)
  rw [hq,Nat.card_eq_fintype_card] at ht
  let a : ℕ := (Fintype.card (ℙ K (Fin 4→K))+1)*
    Fintype.card (TrainingCode (Fin 4→K) (listCap σ) (productCap σ) (Nat.card (Fin 4→K)))
  let c : ℕ := Fintype.card (Submodule K (Fin 4→K))
  let l : ℕ := Nat.log 2 (Nat.card K)+1
  have ha1 : (1:ℝ)≤a := by
    have h : 0<a := Nat.mul_pos (Nat.succ_pos _) Fintype.card_pos
    exact_mod_cast h
  have hc1 : (1:ℝ)≤c := by exact_mod_cast Fintype.card_pos (α:=Submodule K (Fin 4→K))
  have hl1 : (1:ℝ)≤l := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (Nat.log 2 (Nat.card K)))
  have ha : Real.log (a:ℝ)≤7*(Nat.card K:ℝ) := by
    dsimp only [a]
    rw [Nat.cast_mul,Real.log_mul (by positivity) (by exact_mod_cast (Fintype.card_pos (α:=TrainingCode (Fin 4→K) (listCap σ) (productCap σ) (Nat.card (Fin 4→K)))).ne')]
    push_cast at hh ⊢
    linarith
  have hvc := vector_card_le_exp (K:=K) (V:=Fin 4→K) σ hq hd
  have hc : Real.log (c:ℝ)≤25*(Nat.card K:ℝ) := by
    have hsc := FlatAtlas.card_submodules_le (K:=K) (V:=Fin 4→K) 5 hd
    rw [Nat.card_eq_fintype_card] at hsc
    have hsc' : (c:ℝ)≤(Nat.card (Fin 4→K):ℝ)^5 := by exact_mod_cast hsc
    have he : (Real.exp (5*σ))^5=Real.exp (25*σ) := by
      rw [←Real.exp_nat_mul];congr 1;ring
    have hle := hsc'.trans ((pow_le_pow_left₀ (by positivity) hvc 5).trans_eq he)
    have hh' := Real.log_le_log (by linarith : (0:ℝ)<c) hle
    rw [Real.log_exp] at hh'
    linarith
  have hl : Real.log (l:ℝ)≤Nat.card K := by
    have hlq : (l:ℝ)≤(Nat.card K:ℝ)+1 := by
      dsimp only [l];rw [Nat.cast_add,Nat.cast_one]
      have hx : (Nat.log 2 (Nat.card K):ℝ)≤Nat.card K := by exact_mod_cast Nat.log_le_self 2 (Nat.card K)
      linarith only [hx]
    have hh' := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ)<l)
    linarith
  let z : ℕ := (flatIndices (K:=K) (V:=Fin 4→K) 3).card*l
  have hz : (z:ℝ)≤(c:ℝ)*l := by
    have hf : (flatIndices (K:=K) (V:=Fin 4→K) 3).card≤c := by
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    have hz' : z≤c*l := Nat.mul_le_mul_right l hf
    exact_mod_cast hz'
  have hs := log_three_sum ha1 (one_le_mul_of_one_le_of_one_le hc1 hl1) (Nat.cast_nonneg z) hz
  have hcl : Real.log ((c:ℝ)*l)≤26*(Nat.card K:ℝ) := by
    rw [Real.log_mul (by linarith) (by linarith)];linarith
  have h3 : Real.log 3≤2 := by
    have hh' := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  have he : (Fintype.card (ThreePublicIndex K σ):ℝ)=1+((a:ℝ)+z) := by
    simp only [ThreePublicIndex,ThreeBranch,Fintype.card_sum,Fintype.card_prod,Fintype.card_unit,
      Fintype.card_fin,Fintype.card_coe,Nat.cast_add,Nat.cast_one,Nat.cast_mul,a,z,l]
  rw [he]
  linarith
end SharpRamseyFive.ScoreGeometry

end OAI
