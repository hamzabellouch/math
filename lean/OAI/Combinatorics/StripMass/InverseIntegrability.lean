import Mathlib
import OAI.Combinatorics.StripMass.LaguerreScaling

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators Pointwise
open Set MeasureTheory Filter
lemma integrableOn_scaledLaguerre_inverse_coordinate {N : ℕ} {a p β : ℝ}
    (ha : 0 < a) (i : Fin N) (hp : p < a + i.val) (hb : 1 ≤ β) :
    IntegrableOn (fun r => (r i) ^ (-p) * scaledLaguerreDensity N a β r) (laguerreDomain N) := by
  apply (integrableOn_laguerre_inverse_coordinate ha i hp).mono'
    (((measurable_pi_apply i).pow_const _).mul
      (measurable_scaledLaguerreDensity N a β)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos (hr.2 i) _).le
    (scaledLaguerreDensity_pos a β hr).le)]
  exact mul_le_mul_of_nonneg_left (scaledLaguerreDensity_le a hb hr)
    (Real.rpow_pos_of_pos (hr.2 i) _).le

abbrev mobiusInverseQuarter {N : ℕ} (i : Fin N) (z : Fin N → ℝ) : ℝ :=
  (mobiusCoordinate (z i)) ^ (-(1/4:ℝ))

lemma continuousOn_mobiusInverseQuarter {N : ℕ} (i : Fin N) :
    ContinuousOn (mobiusInverseQuarter i) (coordinateBox (Fin N) (Ioo 0 1)) := by
  exact (continuousOn_mobiusCoordinate.comp (continuous_apply i).continuousOn
    (fun z hz => (hz i).1)).rpow_const (fun z hz => Or.inl (mobiusCoordinate_mem (hz i)).1.ne')

lemma antitoneOn_mobiusInverseQuarter {N : ℕ} (i : Fin N) :
    AntitoneOn (mobiusInverseQuarter i) (coordinateBox (Fin N) (Ioo 0 1)) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (mobiusCoordinate_mem (hx i)).1
    (mobiusCoordinate_strictMonoOn.monotoneOn (hx i).1 (hy i).1 (hxy i)) (by norm_num)

lemma integrableOn_scaledLaguerre_mobiusInverseQuarter {N : ℕ} {β : ℝ} (i : Fin N) (hb : 1 ≤ β) :
    IntegrableOn (fun z => mobiusInverseQuarter i z * scaledLaguerreDensity N 1 β z)
      (orderedDomain N) := by
  have hs : orderedDomain N ⊆ laguerreDomain N := fun _ hz => ⟨hz.1, fun i => (hz.2 i).1⟩
  have hm : Measurable (fun z => mobiusInverseQuarter i z * scaledLaguerreDensity N 1 β z) := by
    unfold mobiusInverseQuarter mobiusCoordinate
    apply Measurable.mul
    · fun_prop
    · exact measurable_scaledLaguerreDensity N 1 β
  apply ((integrableOn_scaledLaguerre_inverse_coordinate (by norm_num : (0:ℝ)<1)
    i (by linarith [Nat.cast_nonneg (α:=ℝ) i.val] : (1/4:ℝ) < 1 + i.val) hb).mono_set hs).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_pos_of_pos (mobiusCoordinate_mem (hz.2 i)).1 _).le
    (scaledLaguerreDensity_pos 1 β (hs hz)).le)]
  exact mul_le_mul_of_nonneg_right (mobius_inverseQuarter_bounds (hz.2 i)).2
    (scaledLaguerreDensity_pos 1 β (hs hz)).le

lemma positiveLaw_mobius_expectation {N : ℕ} (β : ℝ) (g : (Fin N → ℝ) → ℝ) :
    (∫ y, g y ∂positiveLaw N) =
      (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z *
        (g (mobiusMap N z) * lowerLikelihood N β z)) /
      (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * lowerLikelihood N β z) := by
  rw [integral_positiveLaw]
  unfold expectation
  rw [integral_density_mobius_likelihood N β g, mobiusLikelihood_Normalizer N β,
    mul_div_mul_left _ _ (mobiusDensityConstant_pos N).ne']

 

theorem positiveLaw_inverseQuarter_ge_scaled_reference {N : ℕ} (i : Fin N) {β : ℝ}
    (hb : 1 ≤ β) (hb' : β ≤ (N + 1 : ℝ) / 2) :
    (2 : ℝ) ^ (-(1/4:ℝ)) *
      ((∫ z in orderedDomain N, (z i) ^ (-(1/4:ℝ)) * scaledLaguerreDensity N 1 β z) /
        (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z)) ≤
      ∫ y, (y i) ^ (-(1/4:ℝ)) ∂positiveLaw N := by
  have hS : orderedDomain N ⊆ laguerreDomain N := fun _ hz => ⟨hz.1, fun j => (hz.2 j).1⟩
  have hiB : IntegrableOn (scaledLaguerreDensity N 1 β) (orderedDomain N) :=
    (integrableOn_scaledLaguerreDensity (by norm_num : (0:ℝ)<1) hb).mono_set hS
  have hiBF : IntegrableOn (fun z => scaledLaguerreDensity N 1 β z * mobiusInverseQuarter i z)
      (orderedDomain N) := by
    simpa only [mul_comm] using integrableOn_scaledLaguerre_mobiusInverseQuarter i hb
  have hiBL := integrableOn_mobiusLikelihood N β
  have hiBFL : IntegrableOn (fun z => scaledLaguerreDensity N 1 β z *
      (mobiusInverseQuarter i z * lowerLikelihood N β z)) (orderedDomain N) :=
    (integrableOn_density_mobius_likelihood_iff N β (fun y => (y i) ^ (-(1/4:ℝ)))).1
      (integrableOn_inverseQuarterCoordinate_density N i)
  have hiBcoord := (integrableOn_scaledLaguerre_inverse_coordinate (by norm_num : (0:ℝ)<1)
    i (by linarith [Nat.cast_nonneg (α:=ℝ) i.val] : (1/4:ℝ) < 1 + i.val) hb).mono_set hS
  have hcov := ordered_density_covariance_Ioo (by norm_num : (0:ℝ)<1)
    (fun _ : Fin N => scaledLaguerreWeight 1 β)
    (fun _ => (continuousOn_scaledLaguerreWeight 1 β).mono (fun _ hx => hx.1))
    (fun _ _ hx => (scaledLaguerreWeight_pos 1 β hx.1).le)
    (fun z => -mobiusInverseQuarter i z) (fun z => -lowerLikelihood N β z)
    (continuousOn_mobiusInverseQuarter i).neg (continuousOn_lowerLikelihood N β).neg
    (fun _ hx _ hy hxy => neg_le_neg (antitoneOn_mobiusInverseQuarter i hx hy hxy))
    (fun _ hx _ hy hxy => neg_le_neg (lowerLikelihood_antitone N hb' hx hy hxy))
    hiB (by simpa only [orderedDomain, orderedChamber, scaledLaguerreDensity, mul_neg, Pi.neg_def] using hiBF.neg)
    (by simpa only [orderedDomain, orderedChamber, scaledLaguerreDensity, mul_neg, Pi.neg_def] using hiBL.neg)
    (by simpa only [orderedDomain, orderedChamber, scaledLaguerreDensity, neg_mul_neg] using hiBFL)
  have hZ : 0 < ∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z :=
    scaledLaguerre_cutoffNormalizer_pos N (by norm_num) hb (by norm_num)
  have hL := mobiusLikelihood_Normalizer_pos N β
  have hcomp :
      (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * mobiusInverseQuarter i z) /
        (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z) ≤
      (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z *
        (mobiusInverseQuarter i z * lowerLikelihood N β z)) /
        (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * lowerLikelihood N β z) := by
    apply (div_le_div_iff₀ hZ hL).2
    simp only [mul_neg, neg_mul, neg_neg, integral_neg] at hcov
    simpa only [orderedDomain, orderedChamber, scaledLaguerreDensity, mul_comm] using hcov
  calc
    _ ≤ (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z * mobiusInverseQuarter i z) /
        (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z) := by
      rw [← mul_div_assoc, ← integral_const_mul]
      apply div_le_div_of_nonneg_right _ hZ.le
      apply setIntegral_mono_on (hiBcoord.const_mul _) hiBF (isOpen_orderedDomain N).measurableSet
      intro z hz
      have h := mul_le_mul_of_nonneg_right (mobius_inverseQuarter_bounds (hz.2 i)).1
        (scaledLaguerreDensity_pos 1 β (hS hz)).le
      simpa only [mobiusInverseQuarter, _root_.mul_assoc] using
        h.trans_eq (_root_.mul_comm _ _)
    _ ≤ _ := hcomp
    _ = _ := (positiveLaw_mobius_expectation β (fun y => (y i) ^ (-(1/4:ℝ)))).symm

lemma integral_scaledLaguerre_cutoff_inverse_coordinate {N : ℕ} (a p R : ℝ) (i : Fin N)
    {β : ℝ} (hb : 0 < β) :
    (laguerreDensityScale N a β * (β ^ p)⁻¹) *
      (∫ y in orderedChamber N (Ioo 0 R), (y i) ^ (-p) * scaledLaguerreDensity N a β y) =
      (β ^ N)⁻¹ * (∫ r in orderedChamber N (Ioo 0 (β * R)), (r i) ^ (-p) * laguerreDensity N a r) := by
  rw [← integral_const_mul]
  calc
    (∫ y in orderedChamber N (Ioo 0 R), (laguerreDensityScale N a β * (β ^ p)⁻¹) *
        ((y i) ^ (-p) * scaledLaguerreDensity N a β y)) =
        ∫ y in orderedChamber N (Ioo 0 R), ((β • y) i) ^ (-p) * laguerreDensity N a (β • y) := by
      apply setIntegral_congr_fun (measurableSet_orderedChamber_Ioo N R)
      intro y hy
      dsimp only
      rw [laguerreDensity_scaled a hb (fun j => (hy.2 j).1)]
      simp only [Pi.smul_apply, smul_eq_mul, Real.mul_rpow hb.le (hy.2 i).1.le, Real.rpow_neg hb.le]
      ring
    _ = _ := integral_orderedChamber_scaled R hb (fun r => (r i) ^ (-p) * laguerreDensity N a r)

lemma scaled_reference_cutoff_inverse_coordinate {N : ℕ} (a p R : ℝ) (i : Fin N)
    {β : ℝ} (hb : 0 < β) :
    (∫ y in orderedChamber N (Ioo 0 R), (y i) ^ (-p) * scaledLaguerreDensity N a β y) /
      (∫ y in orderedChamber N (Ioo 0 R), scaledLaguerreDensity N a β y) =
      β ^ p *
        ((∫ r in orderedChamber N (Ioo 0 (β * R)), (r i) ^ (-p) * laguerreDensity N a r) /
          (∫ r in orderedChamber N (Ioo 0 (β * R)), laguerreDensity N a r)) := by
  exact scaled_quotient (laguerreDensityScale_pos N a hb).ne'
    (inv_ne_zero (pow_ne_zero _ hb.ne')) (Real.rpow_pos_of_pos hb _).ne'
    (integral_scaledLaguerre_cutoff N a R hb) (integral_scaledLaguerre_cutoff_inverse_coordinate a p R i hb)

 

theorem positiveLaw_inverseQuarter_ge_reference {N : ℕ} (i : Fin N) {β : ℝ}
    (hb : 1 ≤ β) (hb' : β ≤ (N + 1 : ℝ) / 2) :
    (2 : ℝ) ^ (-(1/4:ℝ)) * β ^ (1/4:ℝ) *
      (∫ r, (r i) ^ (-(1/4:ℝ)) ∂laguerreLaw N 1) ≤
        ∫ y, (y i) ^ (-(1/4:ℝ)) ∂positiveLaw N := by
  have hb0 : 0 < β := by linarith
  have hpD : (1/4:ℝ) < laguerreDimension 1 (i.val + 1) := by
    unfold laguerreDimension
    have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith [sq_nonneg (i.val : ℝ)]
  have hcut := laguerreLaw_cutoff_inverse_coordinate (by norm_num : (0:ℝ)<1) hb0 i
    (by norm_num : (0:ℝ)≤1/4) hpD
  have hscale := scaled_reference_cutoff_inverse_coordinate 1 (1/4) 1 i hb0
  simp only [mul_one] at hscale
  calc
    _ ≤ (2 : ℝ) ^ (-(1/4:ℝ)) * (β ^ (1/4:ℝ) *
        ((∫ r in cutoffEvent N β, (r i) ^ (-(1/4:ℝ)) ∂laguerreLaw N 1) /
          (laguerreLaw N 1).real (cutoffEvent N β))) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hcut
        (mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).le
          (Real.rpow_pos_of_pos hb0 _).le)
    _ = (2 : ℝ) ^ (-(1/4:ℝ)) *
        ((∫ z in orderedDomain N, (z i) ^ (-(1/4:ℝ)) * scaledLaguerreDensity N 1 β z) /
          (∫ z in orderedDomain N, scaledLaguerreDensity N 1 β z)) := by
      rw [laguerreLaw_conditioned_eq N (by norm_num), ← hscale]
      rfl
    _ ≤ _ := positiveLaw_inverseQuarter_ge_scaled_reference i hb hb'

end
end CriticalStrip

 

namespace StripPfaffian
noncomputable section
open scoped BigOperators Matrix

lemma congruence_skew {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    ∀ i j, (M * A * M.transpose) j i = -(M * A * M.transpose) i j := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [hA l k]
  ring

lemma toLin_basis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    Matrix.toLin' M (standardBasis n i) = ∑ j, M j i • standardBasis n j := by
  ext k
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, standardBasis,
    Pi.basisFun_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]

lemma sum_four_reverse {ι E : Type*} [Fintype ι] [AddCommMonoid E]
    (F : ι → ι → ι → ι → E) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ l, ∑ k, ∑ j, ∑ i, F i j k l := by
  let e : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) :=
    ⟨(fun p => (p.2.2.2, p.2.2.1, p.2.1, p.1)),
     (fun p => (p.2.2.2, p.2.2.1, p.2.1, p.1)), by intro p; rfl, by intro p; rfl⟩
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv e (fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p => F p.2.2.2 p.2.2.1 p.2.1 p.1) (fun _ => rfl))

lemma twoForm_congruence {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    ExteriorAlgebra.map (Matrix.toLin' M) (twoForm A) = twoForm (M * A * M.transpose) := by
  rw [twoForm_full A hA, twoForm_full _ (congruence_skew M A hA)]
  simp only [map_smul, map_sum, map_mul]
  congr 1
  simp only [generator, ExteriorAlgebra.map_apply_ι,
    toLin_basis, Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_smul,
    Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, Finset.sum_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [sum_four_reverse]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

lemma pfaffian_congruence {n : ℕ} (hn : Even n) (M A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    pfaffian n (M * A * M.transpose) = M.det * pfaffian n A := by
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) :=
    by simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  change topCoord n (twoForm _ ^ (n / 2)) / _ =
    M.det * (topCoord n (twoForm A ^ (n / 2)) / _)
  rw [← twoForm_congruence M A hA, ← map_pow, topCoord_map n _ _ hhom]
  have hd : (Matrix.toLin' M).det = M.det := by
    rw [← LinearMap.det_toMatrix (standardBasis n)]
    congr 1
    ext i j
    simp [standardBasis, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hd]
  ring

lemma pfaffian_scale_coordinates {n : ℕ} (hn : Even n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j) (s : Fin n → ℂ) :
    pfaffian n (fun i j => s i * A i j * s j) = (∏ i, s i) * pfaffian n A := by
  have hM : Matrix.diagonal s * A * (Matrix.diagonal s).transpose =
      fun i j => s i * A i j * s j := by
    ext i j
    simp only [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simpa only [hM, Matrix.det_diagonal] using
    pfaffian_congruence hn (Matrix.diagonal s) A hA

def schurComplement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u v : Vec n) (t : ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => A i j - (u i * v j - v i * u j) / t

lemma schurComplement_skew {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u v : Vec n) (t : ℂ) :
    ∀ i j, schurComplement A u v t j i = -schurComplement A u v t i j := by
  intro i j
  simp only [schurComplement, hA i j]
  ring

def eliminatingShear {n : ℕ} (u v : Vec n) (t : ℂ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
  Fin.snoc
    (Fin.snoc
      (fun i : Fin n => Fin.snoc (Fin.snoc (fun j => if i = j then (1 : ℂ) else 0) (-v i / t)) (u i / t))
      (Fin.snoc (Fin.snoc (fun _ : Fin n => (0 : ℂ)) 1) 0))
    (Fin.snoc (Fin.snoc (fun _ : Fin n => (0 : ℂ)) 0) 1)

lemma eliminatingShear_upper {n : ℕ} (u v : Vec n) (t : ℂ) :
    (eliminatingShear u v t).IsUpperTriangular := by
  intro i j
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun i => ?_) i) i
  all_goals
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) j
  all_goals
    intro hji
    simp only [id_eq] at hji
    simp_all [eliminatingShear]
  all_goals
    simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at hji
    try omega

lemma eliminatingShear_det {n : ℕ} (u v : Vec n) (t : ℂ) :
    (eliminatingShear u v t).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (eliminatingShear_upper u v t),
    Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp [eliminatingShear]

lemma eliminatingShear_congruence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (_hA : ∀ i j, A j i = -A i j) (u v : Vec n) {t : ℂ} (ht : t ≠ 0) :
    eliminatingShear u v t * border (border A u) (Fin.snoc v t) * (eliminatingShear u v t).transpose =
      border (border (schurComplement A u v t) 0) (Fin.snoc 0 t) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun i => ?_) i) i
  all_goals
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) j
  all_goals
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp only [Fin.sum_univ_castSucc]
    simp [eliminatingShear, schurComplement, ht]
  all_goals field_simp [ht]
  all_goals ring

lemma pfaffian_schur_complement {n : ℕ} (hn : Even n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j)
    (u v : Vec n) {t : ℂ} (ht : t ≠ 0) :
    pfaffian (n + 2) (border (border A u) (Fin.snoc v t)) =
      t * pfaffian n (schurComplement A u v t) := by
  have h := pfaffian_congruence (hn.add (by decide : Even 2))
    (eliminatingShear u v t) (border (border A u) (Fin.snoc v t))
    (border_skew _ (border_skew A hA u) _)
  rw [eliminatingShear_det, one_mul, eliminatingShear_congruence A hA u v ht,
    pfaffian_block_extra hn _ (schurComplement_skew A hA u v t)] at h
  exact h.symm

end

noncomputable section
open scoped BigOperators

def schurEntry (x y : ℂ) : ℂ := (y - x) / (x + y)
def schurMatrix {n : ℕ} (x : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => schurEntry (x i) (x j)
def schurProduct {n : ℕ} (x : Fin n → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, schurEntry (x i) (x j)

lemma schurEntry_self (x : ℂ) : schurEntry x x = 0 := by simp [schurEntry]
lemma schurEntry_swap (x y : ℂ) : schurEntry y x = -schurEntry x y := by
  simp only [schurEntry, add_comm y x]
  ring
lemma schurMatrix_skew {n : ℕ} (x : Fin n → ℂ) :
    ∀ i j, schurMatrix x j i = -schurMatrix x i j :=
  fun i j => schurEntry_swap (x i) (x j)
lemma schurEntry_ne_zero {x y : ℂ} (hne : y ≠ x) (hd : x + y ≠ 0) :
    schurEntry x y ≠ 0 := div_ne_zero (sub_ne_zero.mpr hne) hd

lemma schurEntry_elimination {x y a b : ℂ}
    (hxy : x + y ≠ 0) (hxa : x + a ≠ 0) (hxb : x + b ≠ 0)
    (hya : y + a ≠ 0) (hyb : y + b ≠ 0) (_hab : a + b ≠ 0) (hne : b ≠ a) :
    schurEntry x y -
        (schurEntry x a * schurEntry y b - schurEntry x b * schurEntry y a) /
          schurEntry a b =
      (schurEntry x a * schurEntry x b) * schurEntry x y *
        (schurEntry y a * schurEntry y b) := by
  have hba := sub_ne_zero.mpr hne
  unfold schurEntry
  field_simp
  ring

lemma schurEntry_border_elimination {x y a : ℂ}
    (hxy : x + y ≠ 0) (hxa : x + a ≠ 0) (hya : y + a ≠ 0) :
    schurEntry x y - (schurEntry x a - schurEntry y a) =
      schurEntry x a * schurEntry x y * schurEntry y a := by
  unfold schurEntry
  field_simp
  ring

lemma schurMatrix_snoc {n : ℕ} (x : Fin n → ℂ) (a : ℂ) :
    schurMatrix (Fin.snoc x a) = border (schurMatrix x) (fun i => schurEntry (x i) a) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [schurMatrix, Fin.snoc_last, Fin.snoc_castSucc, border_last_last,
      border_last_old, border_old_last, border_old_old, schurEntry_self]
  exact schurEntry_swap _ _

lemma schurColumn_snoc {n : ℕ} (x : Fin n → ℂ) (a b : ℂ) :
    (fun i : Fin (n + 1) => schurEntry (Fin.snoc (α := fun _ => ℂ) x a i) b) =
      Fin.snoc (fun i => schurEntry (x i) b) (schurEntry a b) := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

lemma schurProduct_snoc {n : ℕ} (x : Fin n → ℂ) (a : ℂ) :
    schurProduct (Fin.snoc x a) = schurProduct x * ∏ i, schurEntry (x i) a := by
  unfold schurProduct
  rw [Fin.prod_univ_castSucc, prod_Ioi_last, mul_one]
  simp_rw [prod_Ioi_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  exact Finset.prod_mul_distrib

@[simp] lemma pfaffian_empty (A : Matrix (Fin 0) (Fin 0) ℂ) : pfaffian 0 A = 1 := by
  have h := topCoord_topWedge 0
  simpa [topCoord, topWedge, ExteriorAlgebra.ιMulti_zero_apply, pfaffian,
    Module.Basis.coord_apply] using h

lemma pfaffian_schur_snoc_snoc {n : ℕ} (hn : Even n) (x : Fin n → ℂ) (a b : ℂ)
    (hbase : pfaffian n (schurMatrix x) = schurProduct x)
    (hxx : ∀ i j, x i + x j ≠ 0) (hxa : ∀ i, x i + a ≠ 0)
    (hxb : ∀ i, x i + b ≠ 0) (hab : a + b ≠ 0) (hne : b ≠ a) :
    pfaffian (n + 2) (schurMatrix (Fin.snoc (Fin.snoc x a) b)) =
      schurProduct (Fin.snoc (Fin.snoc x a) b) := by
  have hc : schurComplement (schurMatrix x) (fun i => schurEntry (x i) a)
      (fun i => schurEntry (x i) b) (schurEntry a b) =
      fun i j => (schurEntry (x i) a * schurEntry (x i) b) * schurMatrix x i j *
        (schurEntry (x j) a * schurEntry (x j) b) := by
    ext i j
    exact schurEntry_elimination (hxx i j) (hxa i) (hxb i) (hxa j) (hxb j) hab hne
  rw [schurMatrix_snoc, schurMatrix_snoc, schurColumn_snoc,
    pfaffian_schur_complement hn _ (schurMatrix_skew x) _ _ (schurEntry_ne_zero hne hab),
    hc, pfaffian_scale_coordinates hn _ (schurMatrix_skew x), hbase]
  simp only [schurProduct_snoc, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Finset.prod_mul_distrib]
  ring

 
end
end StripPfaffian

end OAI
