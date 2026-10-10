import Mathlib
import OAI.Probability.GaussianInformation.Kernel.NoisyProjection

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential

namespace Geometry
lemma truncated_inverseMoment {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (D : E → ℝ) (hD : Measurable D) (hD0 : ∀ x,0 ≤ D x)
    (k : ℕ) (hk : 0 < k) (A : ℝ≥0∞) (hA : A ≠ ∞)
    (htail : ∀ j : ℕ, μ {x | D x ≤ (1/2:ℝ)^j} ≤
      A * ENNReal.ofReal ((1/2:ℝ)^((k+1)*j))) (L : ℕ) :
    (∫⁻ x,(ENNReal.ofReal (D x))⁻¹^k ∂μ) ≤ μ univ +
      (∑ j ∈ Finset.range L, ENNReal.ofReal ((2:ℝ)^((j+1)*k))*μ {x|D x ≤ (1/2:ℝ)^j}) +
      A*ENNReal.ofReal ((2:ℝ)^(k+1))*ENNReal.ofReal ((1/2:ℝ)^L) := by
  let S : ℕ → Set E := fun j => {x|D x ≤ (1/2:ℝ)^j}
  let w : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((2:ℝ)^((j+1)*k))
  have hS (j : ℕ) : MeasurableSet (S j) := measurableSet_le hD measurable_const
  have hz : ∀ᵐ x ∂μ,D x ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using zeroSet_null_of_dyadic_tails μ D k A hA htail
  have heq : (fun x => (ENNReal.ofReal (D x))⁻¹^k) =ᵐ[μ]
      (fun x => ENNReal.ofReal ((D x)⁻¹^k)) := by
    filter_upwards [hz] with x hx
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr (hD0 x)),
      ENNReal.ofReal_inv_of_pos (lt_of_le_of_ne (hD0 x) hx.symm)]
  rw [lintegral_congr_ae heq]
  calc
    _ ≤ ∫⁻ x, 1+∑' j,(S j).indicator (fun _ => w j) x ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [S,w,Set.indicator,Set.mem_ofPred_eq] using
        inv_pow_dyadic_majorant (D x) (hD0 x) k hk
    _ = μ univ+∑' j,w j*μ (S j) := by
      rw [lintegral_add_left measurable_const,lintegral_tsum (fun j =>
        (measurable_const.indicator (hS j)).aemeasurable)]
      simp only [lintegral_const,one_mul,lintegral_indicator (hS _),Measure.restrict_apply_univ]
    _ = μ univ + (∑ j ∈ Finset.range L,w j*μ (S j)) + ∑' j,w (j+L)*μ (S (j+L)) := by
      have hh : (∑ j ∈ Finset.range L,w j*μ (S j)) + (∑' j,w (j+L)*μ (S (j+L))) =
          ∑' j,w j*μ (S j) :=
        Summable.sum_add_tsum_nat_add' (f := fun j => w j*μ (S j)) (k := L) ENNReal.summable
      exact (congrArg (fun x => μ univ+x) hh.symm).trans (add_assoc _ _ _).symm
    _ ≤ μ univ+(∑ j ∈ Finset.range L,w j*μ (S j))+
        ∑' j,A*ENNReal.ofReal ((2:ℝ)^k)*ENNReal.ofReal ((1/2:ℝ)^(j+L)) := by
      refine add_le_add_right ?_ _
      apply ENNReal.tsum_le_tsum
      intro j
      calc
        w (j+L)*μ (S (j+L)) ≤ w (j+L)*(A*ENNReal.ofReal ((1/2:ℝ)^((k+1)*(j+L)))) := by
          exact mul_le_mul_right (htail (j+L)) _
        _ = _ := by
          dsimp [w]
          rw [mul_left_comm,← ENNReal.ofReal_mul (by positivity),dyadic_weight_product,
            ENNReal.ofReal_mul (by positivity)]
          ac_rfl
    _ = _ := by
      have hs : (∑' j,A*ENNReal.ofReal ((2:ℝ)^k)*ENNReal.ofReal ((1/2:ℝ)^(j+L))) =
          A*ENNReal.ofReal ((2:ℝ)^(k+1))*ENNReal.ofReal ((1/2:ℝ)^L) := by
        simp_rw [pow_add,ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (1/2:ℝ)^_),
          ← mul_assoc,ENNReal.tsum_mul_right,ENNReal.tsum_mul_left,
          ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),ENNReal.tsum_geometric]
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
        simp only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat,one_div,ENNReal.one_sub_inv_two,
          inv_inv,pow_succ,ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k),mul_assoc]
        norm_num
      rw [hs]
lemma exists_good_dyadic_scale {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (D : E → ℝ) (hD : Measurable D)
    (hD0 : ∀ x,0 ≤ D x) (hD1 : ∀ᵐ x ∂μ,D x ≤ 1)
    (k : ℕ) (hk : 0 < k) (A : ℝ≥0∞) (hA : A ≠ ∞)
    (htail : ∀ j : ℕ, μ {x|D x ≤ (1/2:ℝ)^j} ≤
      A*ENNReal.ofReal ((1/2:ℝ)^((k+1)*j))) (L : ℕ) (hL : 0 < L)
    (hcut : A*ENNReal.ofReal ((2:ℝ)^(k+1))*ENNReal.ofReal ((1/2:ℝ)^L) ≤ 1) :
    ∃ j : ℕ,j<L ∧ 0 < μ {x|D x ≤ (1/2:ℝ)^j} ∧
      (∫⁻ x,(ENNReal.ofReal (D x))⁻¹^k ∂μ) ≤
        ENNReal.ofReal ((2:ℝ)^k*((L:ℝ)+2))*
          (ENNReal.ofReal ((2:ℝ)^(j*k))*μ {x|D x ≤ (1/2:ℝ)^j}) := by
  classical
  let S : ℕ → Set E := fun j => {x|D x ≤ (1/2:ℝ)^j}
  let f : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((2:ℝ)^(j*k))*μ (S j)
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range L) f
    ⟨0,Finset.mem_range.mpr hL⟩
  have hS0 : μ (S 0)=1 := by
    have he : S 0 =ᵐ[μ] univ := by
      filter_upwards [hD1] with x hx
      apply propext
      change (D x ≤ (1/2:ℝ)^0) ↔ True
      simpa using hx
    rw [measure_congr he,measure_univ]
  have hf0 : f 0=1 := by simp [f,hS0]
  have hfj : 1 ≤ f j := by rw [← hf0]; exact hmax 0 (Finset.mem_range.mpr hL)
  have hjpos : 0 < μ (S j) := by
    by_contra hn
    have hz : μ (S j)=0 := le_antisymm (not_lt.mp hn) bot_le
    simp only [f,hz,mul_zero] at hfj
    exact absurd hfj (by norm_num)
  refine ⟨j,Finset.mem_range.mp hj,hjpos,?_⟩
  have hsum : (∑ i ∈ Finset.range L,ENNReal.ofReal ((2:ℝ)^((i+1)*k))*μ (S i)) ≤
      (L:ℝ≥0∞)*(ENNReal.ofReal ((2:ℝ)^k)*f j) := by
    calc
      _ = ∑ i ∈ Finset.range L,ENNReal.ofReal ((2:ℝ)^k)*f i := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [f]
        rw [Nat.add_mul,one_mul,pow_add,ENNReal.ofReal_mul (by positivity)]
        ac_rfl
      _ ≤ ∑ _i ∈ Finset.range L,ENNReal.ofReal ((2:ℝ)^k)*f j := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_right (hmax i hi) _
      _ = _ := by simp
  have hk1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal ((2:ℝ)^k) := by
    exact_mod_cast (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ 2^k)
  have h1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal ((2:ℝ)^k)*f j := by
    calc (1:ℝ≥0∞)=1*1 := by simp
         _ ≤ _ := mul_le_mul hk1 hfj (by positivity) (by positivity)
  have h := truncated_inverseMoment μ D hD hD0 k hk A hA htail L
  change _ ≤ μ univ+(∑ i ∈ Finset.range L,ENNReal.ofReal ((2:ℝ)^((i+1)*k))*μ (S i))+_ at h
  rw [measure_univ] at h
  calc
    _ ≤ 1+(L:ℝ≥0∞)*(ENNReal.ofReal ((2:ℝ)^k)*f j)+1 :=
      h.trans (add_le_add (add_le_add_right hsum 1) hcut)
    _ ≤ ENNReal.ofReal ((2:ℝ)^k)*f j+(L:ℝ≥0∞)*(ENNReal.ofReal ((2:ℝ)^k)*f j)+
        ENNReal.ofReal ((2:ℝ)^k)*f j := add_le_add (add_le_add_left h1 _) h1
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add (by positivity) (by positivity)]
      simp only [ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
      change _ = _*f j
      ring
end Geometry

namespace Scale
open KernelPotential.Geometry Sphere Coercivity

noncomputable def radius (j : ℕ) : ℝ := 2*(1/2:ℝ)^j
lemma radius_pos (j : ℕ) : 0 < radius j := by unfold radius; positivity

lemma closed_cap {d : ℕ} (hd : 2 ≤ d) (ν : Measure (Ambient d))
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (s : Ambient d) {r : ℝ} (hr : 0 < r) :
    ν (closedBall s r) ≤ ENNReal.ofReal (H*(9*3^d)*(2*r)^(d-1)) := by
  calc
    _ ≤ ν (ball s (2*r)) := measure_mono (closedBall_subset_ball (by linarith))
    _ ≤ ENNReal.ofReal H*sphereProbability d (ball s (2*r)) := by
      simpa only [Measure.smul_apply,smul_eq_mul] using hν (ball s (2*r))
    _ ≤ ENNReal.ofReal H*ENNReal.ofReal ((9*3^d:ℝ)*(2*r)^(d-1)) :=
      mul_le_mul_right (cap_bound hd s (by linarith)) _
    _ = _ := by rw [← ENNReal.ofReal_mul hH.le]; congr 1; ring

lemma norm_half_tail {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (s : Ambient d) (j : ℕ) :
    ν {u | ‖u-s‖/2 ≤ (1/2:ℝ)^j} ≤
      ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
        ENNReal.ofReal ((1/2:ℝ)^((2*(d/16)+1)*j)) := by
  have he : {u : Ambient d|‖u-s‖/2 ≤ (1/2:ℝ)^j}=closedBall s (radius j) := by
    ext u
    rw [mem_closedBall,dist_eq_norm]
    change ‖u-s‖/2 ≤ (1/2:ℝ)^j ↔ ‖u-s‖ ≤ 2*(1/2:ℝ)^j
    constructor <;> intro h <;> linarith
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (H*(9*3^d)*(2*radius j)^(d-1)) := closed_cap (by omega) ν hH hν s (radius_pos j)
    _ ≤ ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1)*((1/2:ℝ)^j)^(2*(d/16)+1)) := by
      apply ENNReal.ofReal_le_ofReal
      have heq : 2*radius j=4*((1/2:ℝ)^j) := by unfold radius; ring
      rw [heq,mul_pow]
      simp only [← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hj0 : (0:ℝ) ≤ (1/2:ℝ)^j := by positivity
      have hj1 : (1/2:ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      exact pow_le_pow_of_le_one hj0 hj1 (by have hh := Nat.div_mul_le_self d 16; omega)
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity),← pow_mul, Nat.mul_comm j]

lemma exists_J_scale {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (s : Ambient d) (hs : ‖s‖=1) (L : ℕ) (hL : 0 < L)
    (hcut : ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
      ENNReal.ofReal ((2:ℝ)^(2*(d/16)+1))*ENNReal.ofReal ((1/2:ℝ)^L) ≤ 1) :
    ∃ j : ℕ,j<L ∧ 0 < ν (closedBall s (radius j)) ∧
      J ν s ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*((L:ℝ)+2))*
        (ENNReal.ofReal ((2:ℝ)^(j*(2*(d/16))))*ν (closedBall s (radius j))) := by
  have hsupport : ∀ᵐ u ∂ν,‖u‖=1 :=
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega))
  have hD1 : ∀ᵐ u ∂ν,‖u-s‖/2 ≤ 1 := by
    filter_upwards [hsupport] with u hu
    have hh := norm_sub_le u s
    rw [hu,hs] at hh
    linarith
  obtain ⟨j,hj,hjm,hjb⟩ := exists_good_dyadic_scale ν (fun u => ‖u-s‖/2)
    (by fun_prop) (fun _ => by positivity) hD1 (2*(d/16)) (by omega)
    (ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))) ENNReal.ofReal_ne_top
    (norm_half_tail hd ν hH hν s) L hL hcut
  have he : {u : Ambient d|‖u-s‖/2 ≤ (1/2:ℝ)^j}=closedBall s (radius j) := by
    ext u
    rw [mem_closedBall,dist_eq_norm]
    change ‖u-s‖/2 ≤ (1/2:ℝ)^j ↔ ‖u-s‖ ≤ 2*(1/2:ℝ)^j
    constructor <;> intro h <;> linarith
  rw [he] at hjm hjb
  refine ⟨j,hj,hjm,le_trans ?_ hjb⟩
  apply lintegral_mono
  intro u
  apply pow_le_pow_left₀ zero_le
  apply ENNReal.inv_le_inv.mpr
  apply ENNReal.ofReal_le_ofReal
  have hh := norm_nonneg (u-s)
  linarith

end Scale

end KernelPotential

end OAI
