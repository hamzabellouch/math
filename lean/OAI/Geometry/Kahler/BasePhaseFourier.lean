import OAI.Geometry.Kahler.BaseHopf

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def phaseChar (n : ℤ) (z : Circle) : ℂ := (z^n : Circle)

@[simp] lemma phaseChar_mul (n : ℤ) (z w : Circle) : phaseChar n (z*w)=phaseChar n z*phaseChar n w := by
  simp [phaseChar,mul_zpow]
@[simp] lemma phaseChar_zero (z : Circle) : phaseChar 0 z=1 := by simp [phaseChar]
@[simp] lemma phaseChar_one (n : ℤ) : phaseChar n 1=1 := by simp [phaseChar]
lemma phaseChar_add (n m : ℤ) (z : Circle) : phaseChar (n+m) z=phaseChar n z*phaseChar m z := by
  simp [phaseChar,zpow_add]
lemma phaseChar_exp (n : ℤ) (t : ℝ) : phaseChar n (Circle.exp t)=Complex.exp ((n:ℂ)*t*Complex.I) := by
  simp only [phaseChar,Circle.coe_zpow,Circle.coe_exp,← Complex.exp_int_mul]
  congr 1
  ring
lemma phaseChar_continuous (n : ℤ) : Continuous (phaseChar n) := by
  exact continuous_subtype_val.comp (continuous_id.zpow n)
@[simp] lemma phaseChar_norm (n : ℤ) (z : Circle) : ‖phaseChar n z‖=1 := (z^n).norm_coe

lemma circle_char_mean (n : ℤ) : (∫ z, phaseChar n z ∂circleMeasure) = if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · subst n; simp
  rw [ite_eq_right hn]
  let w := Circle.exp (Real.pi/(n:ℝ))
  have hw : phaseChar n w = -1 := by
    rw [phaseChar_exp]
    have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    have hh : (n:ℂ)*(Real.pi/(n:ℝ):ℝ)*Complex.I = Real.pi*Complex.I := by push_cast; field_simp
    rw [hh,Complex.exp_pi_mul_I]
  apply integral_eq_zero_of_mul_left_eq_neg (g := w)
  intro z
  rw [phaseChar_mul,hw,neg_one_mul]

lemma circle_char_prod_mean (n m : ℤ) :
    (∫ z, phaseChar n z*phaseChar m z ∂circleMeasure) = if n+m=0 then 1 else 0 := by
  simp_rw [← phaseChar_add]
  exact circle_char_mean (n+m)

def phaseSum (s : Finset ℤ) (a : ℤ → ℂ) (z : Circle) : ℂ := ∑ n ∈ s, a n*phaseChar n z

lemma phaseSum_continuous (s : Finset ℤ) (a : ℤ → ℂ) : Continuous (phaseSum s a) :=
  continuous_finsetSum _ (fun n _ => continuous_const.mul (phaseChar_continuous n))

lemma phaseSum_mean (s : Finset ℤ) (a : ℤ → ℂ) :
    (∫ z, phaseSum s a z ∂circleMeasure) = if 0 ∈ s then a 0 else 0 := by
  classical
  unfold phaseSum
  rw [MeasureTheory.integral_finsetSum s (fun n _ => (compact_continuous_integrable (phaseChar_continuous n)).const_mul (a n))]
  simp_rw [integral_const_mul,circle_char_mean]
  simp

def PhaseBandwidth (W : Base → ℝ) (ℓ : ℕ) : Prop :=
  ∀ p : Sphere, ∃ s : Finset ℤ, ∃ a : ℤ → ℂ,
    (∀ n ∈ s, |n| ≤ (ℓ:ℤ)) ∧ ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ) = phaseSum s a z

def OrbitMeanOne (W : Base → ℝ) : Prop :=
  ∀ p : Sphere, (∫ z : Circle, W ((z:ℂ) • (p:Base)) ∂circleMeasure) = 1

lemma phaseBandwidth_one : PhaseBandwidth (fun _ => 1) 0 := by
  intro p
  refine ⟨{0},fun _ => 1,?_,?_⟩
  · intro n hn; have hn0 : n=0 := Finset.mem_singleton.mp hn; simp [hn0]
  · intro z; simp [phaseSum]

lemma orbitMean_one : OrbitMeanOne (fun _ => 1) := by intro p; simp

end PinchedHartogs.BaseConstruction

end

end OAI
