import Mathlib
import OAI.MathematicalPhysics.BFSS.NormalPotential
import OAI.MathematicalPhysics.BFSS.SpinCoupling

namespace OAI

/-! The exact skew normal fermion frequency and absence of zero frequencies. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open scoped Matrix Kronecker
variable {N : ℕ} (M : AlgebraData N)

def spinHalf (a : Fin 3) : GammaMatrix :=
  (-1/2 : ℝ) • (BFSSGamma.massT M.gamma * M.gamma (Fin.castLE (by decide) a))

lemma spinHalf_skew (a : Fin 3) : (M.spinHalf a).transpose = -M.spinHalf a := by
  have hc := BFSSGamma.gamma_massT_comm M.gamma M.gamma_clifford
    (Fin.castLE (by decide) a)
  have ha : (Fin.castLE (by decide) a : Fin 9) < 3 := a.isLt
  simp only [ite_eq_left ha,one_smul] at hc
  have hs (i : SpaceIndex) : (M.gamma i).transpose = M.gamma i := M.gamma_symmetric i
  simp only [spinHalf,Matrix.transpose_smul,Matrix.transpose_mul,hs,
    BFSSGamma.massT_transpose M.gamma M.gamma_clifford M.gamma_symmetric,mul_neg,hc,
    smul_neg]

lemma spinHalf_sq (a : Fin 3) : M.spinHalf a * M.spinHalf a = (-1/4 : ℝ) • (1 : GammaMatrix) := by
  have hc := BFSSGamma.gamma_massT_comm M.gamma M.gamma_clifford
    (Fin.castLE (by decide) a)
  have ha : (Fin.castLE (by decide) a : Fin 9) < 3 := a.isLt
  simp only [ite_eq_left ha,one_smul] at hc
  have he : (BFSSGamma.massT M.gamma * M.gamma (Fin.castLE (by decide) a)) *
      (BFSSGamma.massT M.gamma * M.gamma (Fin.castLE (by decide) a)) = -(1 : GammaMatrix) := by
    calc
      _ = BFSSGamma.massT M.gamma *
          (M.gamma (Fin.castLE (by decide) a) * BFSSGamma.massT M.gamma) *
          M.gamma (Fin.castLE (by decide) a) := by noncomm_ring
      _ = _ := by rw [hc,←mul_assoc,Matrix.mul_assoc,
        BFSSGamma.gamma_sq M.gamma M.gamma_clifford,mul_one,
        BFSSGamma.massT_sq M.gamma M.gamma_clifford M.gamma_symmetric]
  simp only [spinHalf,smul_mul_assoc,mul_smul_comm,smul_smul,he,smul_neg]
  module

lemma spinHalf_product (a b : Fin 3) : M.spinHalf a * M.spinHalf b =
    (-1/4 : ℝ) • (M.gamma (Fin.castLE (by decide) a) * M.gamma (Fin.castLE (by decide) b)) := by
  have hc := BFSSGamma.gamma_massT_comm M.gamma M.gamma_clifford (Fin.castLE (by decide) a)
  have ha : (Fin.castLE (by decide) a : Fin 9) < 3 := a.isLt
  simp only [ite_eq_left ha,one_smul] at hc
  simp only [spinHalf,smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [mul_assoc,←mul_assoc (M.gamma _) _ _,hc,←mul_assoc,←mul_assoc,
    BFSSGamma.massT_sq M.gamma M.gamma_clifford M.gamma_symmetric]
  simp only [neg_mul,one_mul,smul_neg]
  module

lemma spinHalf_cyclic :
    M.spinHalf 0*M.spinHalf 1 = (1/2 : ℝ) • M.spinHalf 2 ∧
    M.spinHalf 1*M.spinHalf 2 = (1/2 : ℝ) • M.spinHalf 0 ∧
    M.spinHalf 2*M.spinHalf 0 = (1/2 : ℝ) • M.spinHalf 1 := by
  have hc (i : SpaceIndex) (hi : i < 3) : BFSSGamma.massT M.gamma * M.gamma i =
      M.gamma i * BFSSGamma.massT M.gamma := by
    simpa only [ite_eq_left hi,one_smul] using BFSSGamma.massT_gamma_comm M.gamma M.gamma_clifford i
  rw [M.spinHalf_product,M.spinHalf_product,M.spinHalf_product]
  change (-1/4:ℝ) • (M.gamma 0*M.gamma 1) = (1/2:ℝ) • ((-1/2:ℝ) • (BFSSGamma.massT M.gamma*M.gamma 2)) ∧
    (-1/4:ℝ) • (M.gamma 1*M.gamma 2) = (1/2:ℝ) • ((-1/2:ℝ) • (BFSSGamma.massT M.gamma*M.gamma 0)) ∧
    (-1/4:ℝ) • (M.gamma 2*M.gamma 0) = (1/2:ℝ) • ((-1/2:ℝ) • (BFSSGamma.massT M.gamma*M.gamma 1))
  rw [hc 2 (by decide),hc 0 (by decide),hc 1 (by decide),
    BFSSGamma.gamma2_massT M.gamma M.gamma_clifford M.gamma_symmetric,
    BFSSGamma.gamma0_massT M.gamma M.gamma_clifford M.gamma_symmetric,
    BFSSGamma.gamma1_massT M.gamma M.gamma_clifford M.gamma_symmetric,
    BFSSGamma.gamma_anti M.gamma M.gamma_clifford (show (2:SpaceIndex) ≠ 0 by decide)]
  constructor
  · module
  constructor <;> module

lemma spinHalf_reverse (a b : Fin 3) (hab : a ≠ b) :
    M.spinHalf b * M.spinHalf a = -(M.spinHalf a * M.spinHalf b) := by
  have hn : (Fin.castLE (by decide) b : Fin 9) ≠ Fin.castLE (by decide) a := by
    intro h
    exact hab (Fin.ext (congrArg (fun x : Fin 9 => x.val) h.symm))
  rw [M.spinHalf_product,M.spinHalf_product,
    BFSSGamma.gamma_anti M.gamma M.gamma_clifford hn,smul_neg]

def colorJ (q : Boson N) (a : Fin 3) : Module.End ℝ (ColorVector N) :=
  (1/2 : ℝ) • M.colorAd (spatialColor q (Fin.castLE (by decide) a))

lemma colorJ_skew (q : Boson N) (a : Fin 3) (x y : ColorVector N) :
    inner ℝ (M.colorJ q a x) y = -inner ℝ x (M.colorJ q a y) := by
  simp only [colorJ,LinearMap.smul_apply,real_inner_smul_left,real_inner_smul_right,
    M.colorAd_skew,mul_neg]

lemma colorJ_commutators (q : Boson N) (hq : M.ZeroRelations q) :
    M.colorJ q 0*M.colorJ q 1-M.colorJ q 1*M.colorJ q 0 = M.colorJ q 2 ∧
    M.colorJ q 1*M.colorJ q 2-M.colorJ q 2*M.colorJ q 1 = M.colorJ q 0 ∧
    M.colorJ q 2*M.colorJ q 0-M.colorJ q 0*M.colorJ q 2 = M.colorJ q 1 := by
  have one (a b c : Fin 3) (h : M.colorLie (spatialColor q (Fin.castLE (by decide) a))
      (spatialColor q (Fin.castLE (by decide) b)) =
        (2:ℝ) • spatialColor q (Fin.castLE (by decide) c)) :
      M.colorJ q a*M.colorJ q b-M.colorJ q b*M.colorJ q a = M.colorJ q c := by
    apply LinearMap.ext
    intro x
    simp only [colorJ,LinearMap.sub_apply,Module.End.mul_apply,LinearMap.smul_apply,map_smul,
      smul_smul]
    rw [←smul_sub,M.colorAd_commutator,h]
    change (1/2*(1/2):ℝ) • M.colorLie ((2:ℝ) • spatialColor q (Fin.castLE (by decide) c)) x = _
    rw [M.colorLie_smul_left,smul_smul]
    norm_num
    rfl
  exact ⟨one 0 1 2 hq.1,one 1 2 0 hq.2.1,one 2 0 1 hq.2.2.1⟩
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open BFSSSpinHalf
open scoped Kronecker
variable {N : ℕ} (M : AlgebraData N)

abbrev FrequencyIndex (N : ℕ) := SpinIndex × ColorIndex N
abbrev FrequencyMatrix (N : ℕ) := Matrix (FrequencyIndex N) (FrequencyIndex N) ℝ

def colorJTensor (q : Boson N) (a : Fin 3) : FrequencyMatrix N :=
  rightLift (eucAlg.symm (M.colorJ q a))

def spinHalfTensor (a : Fin 3) : FrequencyMatrix N := leftLift (M.spinHalf a)

def spinHalfCoupling (q : Boson N) : FrequencyMatrix N :=
  M.colorJTensor q 0*M.spinHalfTensor 0+M.colorJTensor q 1*M.spinHalfTensor 1+
    M.colorJTensor q 2*M.spinHalfTensor 2

lemma colorJTensor_skew (q : Boson N) (a : Fin 3) :
    (M.colorJTensor q a).transpose = -M.colorJTensor q a := by
  have hj : (eucAlg.symm (M.colorJ q a)).transpose = -eucAlg.symm (M.colorJ q a) := by
    apply skew_matrix_of_inner
    simpa only [AlgEquiv.apply_symm_apply] using M.colorJ_skew q a
  simp only [colorJTensor,rightLift_transpose,hj,map_neg]

lemma spinHalfTensor_skew (a : Fin 3) :
    (M.spinHalfTensor (N := N) a).transpose = -M.spinHalfTensor a := by
  simp only [spinHalfTensor,leftLift_transpose,M.spinHalf_skew,map_neg]

lemma tensor_commute (q : Boson N) (a b : Fin 3) :
    Commute (M.spinHalfTensor a) (M.colorJTensor q b) :=
  lifts_commute _ _

lemma spinHalfCoupling_symmetric (q : Boson N) :
    (M.spinHalfCoupling q).transpose = M.spinHalfCoupling q := by
  simp only [spinHalfCoupling,Matrix.transpose_add,Matrix.transpose_mul,
    M.colorJTensor_skew,M.spinHalfTensor_skew,neg_mul_neg]
  rw [(M.tensor_commute q 0 0).eq,(M.tensor_commute q 1 1).eq,(M.tensor_commute q 2 2).eq]

lemma spinHalfCoupling_polynomial (q : Boson N) (hq : M.ZeroRelations q) :
    M.spinHalfCoupling q*M.spinHalfCoupling q =
      (-1/4 : ℝ) • (M.colorJTensor q 0*M.colorJTensor q 0+
        M.colorJTensor q 1*M.colorJTensor q 1+M.colorJTensor q 2*M.colorJTensor q 2)+
      (1/2 : ℝ) • M.spinHalfCoupling q := by
  obtain ⟨hj01,hj12,hj20⟩ := M.colorJ_commutators q hq
  have jc (a b c : Fin 3) (hh : M.colorJ q a*M.colorJ q b-M.colorJ q b*M.colorJ q a = M.colorJ q c) :
      M.colorJTensor q a*M.colorJTensor q b-M.colorJTensor q b*M.colorJTensor q a = M.colorJTensor q c := by
    have h := congrArg (fun T : Module.End ℝ (ColorVector N) =>
      (rightLift (ι := SpinIndex) (eucAlg.symm T))) hh
    simpa only [map_sub,map_mul,colorJTensor] using h
  have ls (a : Fin 3) : M.spinHalfTensor a*M.spinHalfTensor a =
      (-1/4 : ℝ) • (1 : FrequencyMatrix N) := by
    simp only [spinHalfTensor,←map_mul,M.spinHalf_sq,map_smul,map_one]
  have lp (a b c : Fin 3) (hh : M.spinHalf a*M.spinHalf b = (1/2 : ℝ) • M.spinHalf c) :
      M.spinHalfTensor (N := N) a*M.spinHalfTensor b = (1/2 : ℝ) • M.spinHalfTensor c := by
    simpa only [spinHalfTensor,←map_mul,map_smul] using congrArg (leftLift (κ := ColorIndex N)) hh
  have ln (a b c : Fin 3) (hab : a ≠ b)
      (hh : M.spinHalf a*M.spinHalf b = (1/2 : ℝ) • M.spinHalf c) :
      M.spinHalfTensor (N := N) b*M.spinHalfTensor a = (-1/2 : ℝ) • M.spinHalfTensor c := by
    rw [spinHalfTensor,spinHalfTensor,←map_mul,M.spinHalf_reverse a b hab,hh,map_neg,map_smul]
    change -((1/2:ℝ) • M.spinHalfTensor c) = (-1/2:ℝ) • M.spinHalfTensor c
    module
  obtain ⟨hl01,hl12,hl20⟩ := M.spinHalf_cyclic
  exact casimir_identity (M.colorJTensor q) M.spinHalfTensor (M.tensor_commute q)
    (jc 0 1 2 hj01) (jc 1 2 0 hj12) (jc 2 0 1 hj20) ls
    (lp 0 1 2 hl01) (ln 0 1 2 (by decide) hl01)
    (lp 1 2 0 hl12) (ln 1 2 0 (by decide) hl12)
    (lp 2 0 1 hl20) (ln 2 0 1 (by decide) hl20)

def normalFermionFrequency (q : Boson N) : FrequencyMatrix N :=
  (3/2 : ℝ) • leftLift (κ := ColorIndex N) (BFSSGamma.massT M.gamma)-
    (2 : ℝ) • (leftLift (M.gamma 0)*M.colorJTensor q 0+
      leftLift (M.gamma 1)*M.colorJTensor q 1+leftLift (M.gamma 2)*M.colorJTensor q 2)

lemma massT_spinHalf (a : Fin 3) : BFSSGamma.massT M.gamma*M.spinHalf a =
    (1/2 : ℝ) • M.gamma (Fin.castLE (by decide) a) := by
  simp only [spinHalf,mul_smul_comm,←mul_assoc,
    BFSSGamma.massT_sq M.gamma M.gamma_clifford M.gamma_symmetric,neg_mul,one_mul,smul_neg]
  module

lemma normalFermionFrequency_factor (q : Boson N) :
    M.normalFermionFrequency q =
      leftLift (κ := ColorIndex N) (BFSSGamma.massT M.gamma)*
        ((3/2 : ℝ) • (1 : FrequencyMatrix N)-(4 : ℝ) • M.spinHalfCoupling q) := by
  let T : FrequencyMatrix N := leftLift (BFSSGamma.massT M.gamma)
  have tl (a : Fin 3) : T*M.spinHalfTensor a =
      (1/2 : ℝ) • leftLift (M.gamma (Fin.castLE (by decide) a)) := by
    change leftLift (BFSSGamma.massT M.gamma)*leftLift (M.spinHalf a) = _
    rw [←map_mul,M.massT_spinHalf,map_smul]
  have tp (a : Fin 3) : T*(M.colorJTensor q a*M.spinHalfTensor a) =
      (1/2 : ℝ) • (leftLift (M.gamma (Fin.castLE (by decide) a))*M.colorJTensor q a) := by
    have hc : Commute T (M.colorJTensor q a) := lifts_commute _ _
    calc
      _ = M.colorJTensor q a*(T*M.spinHalfTensor a) := by rw [←mul_assoc,hc.eq,mul_assoc]
      _ = _ := by
        have hg : Commute (leftLift (M.gamma (Fin.castLE (by decide) a))) (M.colorJTensor q a) :=
          lifts_commute _ _
        rw [tl,mul_smul_comm,hg.eq.symm]
  change _ = T*((3/2 : ℝ) • (1 : FrequencyMatrix N)-(4 : ℝ) • M.spinHalfCoupling q)
  rw [mul_sub,mul_smul_comm,mul_one,mul_smul_comm,spinHalfCoupling,mul_add,mul_add,tp 0,tp 1,tp 2]
  change (3/2:ℝ) • T-(2:ℝ) • (leftLift (M.gamma 0)*M.colorJTensor q 0+
      leftLift (M.gamma 1)*M.colorJTensor q 1+leftLift (M.gamma 2)*M.colorJTensor q 2) =
    (3/2:ℝ) • T-(4:ℝ) • ((1/2:ℝ) • (leftLift (M.gamma 0)*M.colorJTensor q 0)+
      (1/2:ℝ) • (leftLift (M.gamma 1)*M.colorJTensor q 1)+
      (1/2:ℝ) • (leftLift (M.gamma 2)*M.colorJTensor q 2))
  module

theorem normalFermionFrequency_trivial_kernel (q : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0)
    (x : EuclideanSpace ℝ (FrequencyIndex N))
    (hx : eucAlg (M.normalFermionFrequency q) x = 0) : x = 0 := by
  let T : FrequencyMatrix N := leftLift (BFSSGamma.massT M.gamma)
  let A : FrequencyMatrix N := (3/2:ℝ) • 1-(4:ℝ) • M.spinHalfCoupling q
  have ht : T*T = -(1 : FrequencyMatrix N) := by
    change leftLift (BFSSGamma.massT M.gamma)*leftLift (BFSSGamma.massT M.gamma) = _
    rw [←map_mul,BFSSGamma.massT_sq M.gamma M.gamma_clifford M.gamma_symmetric,map_neg,map_one]
  rw [M.normalFermionFrequency_factor] at hx
  change eucAlg (T*A) x = 0 at hx
  rw [map_mul,Module.End.mul_apply] at hx
  have hh := congrArg (fun y => eucAlg T y) hx
  rw [map_zero] at hh
  change (eucAlg T*eucAlg T) (eucAlg A x) = 0 at hh
  rw [←map_mul,ht,map_neg,map_one,LinearMap.neg_apply,Module.End.one_apply,neg_eq_zero] at hh
  exact matrix_shift_trivial_kernel (M.colorJTensor q) (M.spinHalfCoupling q)
    (M.colorJTensor_skew q) (M.spinHalfCoupling_symmetric q)
    (M.spinHalfCoupling_polynomial q (M.potential_zero_relations q hq)) x hh
end
end BFSSQuantum.AlgebraData
namespace BFSSPairSum
open Finset
lemma endpoints {W : Type*} [AddCommGroup W] (F : Fin 9 → W) :
    (∑ p : {p : Fin 9 × Fin 9 // p.1 < p.2}, (F p.1.1 + F p.1.2)) =
      8 • ∑ i : Fin 9, F i := by
  have hh (f : Fin 9 × Fin 9 → W) :
      (∑ p : {p : Fin 9 × Fin 9 // p.1 < p.2}, f p.1) =
        ∑ i : Fin 9, ∑ j : Fin 9, if i < j then f (i,j) else 0 := by
    rw [←Finset.sum_subtype (univ.filter (fun p : Fin 9 × Fin 9 => p.1 < p.2))
      (by simp) f,Finset.sum_filter,Fintype.sum_prod_type]
  rw [Finset.sum_add_distrib,hh (fun p => F p.1),hh (fun p => F p.2)]
  conv_lhs =>
    arg 2
    rw [Finset.sum_comm]
  rw [←Finset.sum_add_distrib]
  have hs (i : Fin 9) :
      (∑ j : Fin 9, if i < j then F i else 0) +
        (∑ j : Fin 9, if j < i then F i else 0) = 8 • F i := by
    rw [←Finset.sum_add_distrib]
    have he (j : Fin 9) : (if i < j then F i else 0) +
        (if j < i then F i else 0) = if j = i then 0 else F i := by
      rcases lt_trichotomy i j with h|h|h
      · simp [h,not_lt_of_ge h.le,ne_of_gt h]
      · subst j; simp
      · simp [h,not_lt_of_ge h.le,ne_of_lt h]
    simp_rw [he]
    conv_lhs =>
      arg 2
      intro j
      rw [←ite_not]
    rw [←Finset.sum_filter]
    simp only [Finset.filter_ne',Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ,Fintype.card_fin]
  simp_rw [hs]
  exact Finset.smul_sum.symm
end BFSSPairSum

end OAI
