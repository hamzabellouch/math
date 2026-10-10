import OAI.NumberTheory.DirichletL.Detector.LowGaussEnergy

namespace OAI

noncomputable section
open scoped Classical
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGaussColumns (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    Finset {I : Id // Supported I} :=
  ((idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn).toFinset

lemma lowGaussColumns_mem (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) :
    s∈lowGaussColumns W1 hW1 Y hY ↔ W1 ((Ideal.absNorm s.val:ℝ)/Y)≠0 := by
  simp only [lowGaussColumns,Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support]

lemma lowRayAmplitude_source_columns (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (m : O) :
    lowRayAmplitude C W1 Y σ m v=
      CenteredMomentGaussEnergy.gaussPolynomial (lowGaussColumns W1 hW1 Y hY)
        (fun s=>primaryGenerator s.val)
        (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
        (lowGaussColumn C W1 Y σ v) (-m) := by
  unfold lowRayAmplitude
  rw [tsum_eq_sum (s:=lowGaussColumns W1 hW1 Y hY) (fun s hs=>by
    have hz : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0 := by
      simpa only [lowGaussColumns_mem,not_not] using hs
    simp only [lowAdditiveCoefficient_outer_zero C W1 Y s m v hz,ite_self])]
  unfold CenteredMomentGaussEnergy.gaussPolynomial
  exact Finset.sum_congr rfl (fun s _=>lowGaussColumn_row C W1 Y σ v s m)

lemma lowGaussColumns_card (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 1≤Y)
    (a b : ℝ) (hW : Function.support W1⊆Set.Icc a b) :
    ((lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY)).card:ℝ)≤128*max 1 b*Y := by
  let F := lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY)
  have hH : 1≤max 1 b*Y := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hY
  have hh := DescentFiberCost.finite_ideal_count_real (F.image Subtype.val) (max 1 b*Y) hH
    (by intro I hI;obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hI;exact s.property.1)
    (by
      intro I hI
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hI
      have hw := (hW ((lowGaussColumns_mem W1 hW1 Y _ s).mp hs)).2
      have hn : (Ideal.absNorm s.val:ℝ)≤b*Y := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hY)).mp hw
      exact hn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_trans zero_le_one hY)))
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  simpa only [mul_assoc,F] using hh

lemma lowGaussColumn_norm_bound (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (W1 : ℝ→ℂ) (a b B : ℝ) (ha : 0<a) (hB : 0≤B)
    (hW : Function.support W1⊆Set.Icc a b) (hWB : ∀x,‖W1 x‖≤B)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) :
    ‖lowGaussColumn (calibrationForSet S hS) W1 Y σ v s‖≤
      B*a^(-(1/2:ℝ))/Y := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  by_cases hzero : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0
  · simp only [lowGaussColumn,hzero,mul_zero,zero_mul,ite_self,norm_zero]
    positivity
  have hqa := (hW hzero).1
  have hp : ‖(((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)‖=
      ((Ideal.absNorm s.val:ℝ)/Y)^(-(1/2:ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hq hY)]
    congr 1
    simp
  have hr : ((Ideal.absNorm s.val:ℝ)/Y)^(-(1/2:ℝ))≤a^(-(1/2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha hqa (by norm_num)
  unfold lowGaussColumn
  split_ifs
  · rw [norm_mul,norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,hp]
    calc
      _ ≤ Y⁻¹*B*1*a^(-(1/2:ℝ)) := by
        gcongr
        · exact hWB _
        · exact lowArithmeticCoefficient_source_norm S hS s
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem lowGaussColumn_l2_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W1 : ℝ→ℂ,∀hW1 : HasCompactSupport W1,
      Function.support W1⊆Set.Icc a b → (∀x,‖W1 x‖≤B) →
      ∀Y : ℝ,∀hY : 1≤Y,∀σ : RayRing,∀v : ℝ,
      (∑s∈lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY),
        ‖lowGaussColumn (calibrationForSet S hS) W1 Y σ v s‖^2)≤C/Y := by
  let C := 128*max 1 b*(B*a^(-(1/2:ℝ)))^2+1
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro S hS W1 hW1 hW hWB Y hY σ v
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  have hcoef (s : {I : Id // Supported I}) := lowGaussColumn_norm_bound S hS W1 a b B ha hB hW hWB Y hy σ v s
  calc
    _ ≤ ∑_s∈lowGaussColumns W1 hW1 Y hy,(B*a^(-(1/2:ℝ))/Y)^2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoef s) 2
    _ = ((lowGaussColumns W1 hW1 Y hy).card:ℝ)*(B*a^(-(1/2:ℝ))/Y)^2 := by simp
    _ ≤ (128*max 1 b*Y)*(B*a^(-(1/2:ℝ))/Y)^2 :=
      mul_le_mul_of_nonneg_right (lowGaussColumns_card W1 hW1 Y hY a b hW) (sq_nonneg _)
    _ = (128*max 1 b*(B*a^(-(1/2:ℝ)))^2)/Y := by field_simp
    _ ≤ C/Y := div_le_div_of_nonneg_right (by dsimp only [C];linarith) hy.le

end SevenEighths.ProbePhysical
end

end OAI
