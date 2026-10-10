import OAI.NumberTheory.SiegelZeros.EntireFunctions.DeletedProduct
import OAI.NumberTheory.SiegelZeros.Structure.AffineFactor

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W03

open Filter Complex Real
open scoped Topology

theorem exp_le_norm_tprod_of_finite_log_lower {ι : Type*} (f : ι → ℂ)
    (hf : Multipliable f) (hne : ∀ i, f i ≠ 0) {b : ℝ}
    (hb : ∀ t : Finset ι, b ≤ Real.log ‖∏ i ∈ t, f i‖) :
    Real.exp b ≤ ‖∏' i, f i‖ := by
  have ht : Tendsto (fun t : Finset ι => ‖∏ i ∈ t, f i‖) atTop
      (𝓝 ‖∏' i, f i‖) := continuous_norm.continuousAt.tendsto.comp hf.hasProd
  apply ge_of_tendsto' ht
  intro t
  exact (Real.le_log_iff_exp_le
    (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)))).mp (hb t)

theorem infinite_far_product_log_lower {ι : Type*} (ρ : ι → ℂ) (z : ℂ)
    (hρ : ∀ i, ρ i ≠ 0) (hfar : ∀ i, 3 * ‖z‖ ≤ ‖ρ i‖)
    (hsquare : Summable (fun i => 1 / ‖ρ i‖ ^ 2))
    (hprod : Multipliable (fun i => genusOneFactor (ρ i) z)) :
    -(6 * ∑' i, (‖z‖ / ‖ρ i‖) ^ 2) ≤
      Real.log ‖∏' i, genusOneFactor (ρ i) z‖ ∧
    (∏' i, genusOneFactor (ρ i) z) ≠ 0 := by
  have hzne : ∀ i, z ≠ ρ i := by
    intro i hi
    have hp : 0 < ‖ρ i‖ := norm_pos_iff.mpr (hρ i)
    have hh := hfar i
    rw [hi] at hh
    linarith
  have hrat : Summable (fun i => (‖z‖ / ‖ρ i‖) ^ 2) := by
    convert hsquare.mul_left (‖z‖ ^ 2) using 1
    funext i
    ring
  have hbound : ∀ t : Finset ι,
      -(6 * ∑' i, (‖z‖ / ‖ρ i‖) ^ 2) ≤
        Real.log ‖∏ i ∈ t, genusOneFactor (ρ i) z‖ := by
    intro t
    have hfinite := SiegelZerosAwei.Workers.W01.finite_far_product_log_lower t ρ z
      (fun i _ => hρ i) (fun i _ => hfar i)
    have hsum := hrat.sum_le_tsum t (fun i _ => sq_nonneg (‖z‖ / ‖ρ i‖))
    linarith
  have he := exp_le_norm_tprod_of_finite_log_lower
    (fun i => genusOneFactor (ρ i) z) hprod
    (fun i => genusOneFactor_ne_zero (hρ i) (hzne i)) hbound
  have hn : 0 < ‖∏' i, genusOneFactor (ρ i) z‖ := (Real.exp_pos _).trans_le he
  exact ⟨(Real.le_log_iff_exp_le hn).mpr he, norm_pos_iff.mp hn⟩

theorem finite_near_product_log_lower {ι : Type*} (S : Finset ι) (ρ : ι → ℂ)
    {z : ℂ} {r d B : ℝ} (hd : 0 < d) (hz : ‖z‖ = r)
    (hρ : ∀ i ∈ S, ρ i ≠ 0) (hupper : ∀ i ∈ S, ‖ρ i‖ ≤ B)
    (hsep : ∀ i ∈ S, d ≤ |r - ‖ρ i‖|) :
    (S.card : ℝ) * (Real.log d - Real.log B) - r * (∑ i ∈ S, 1 / ‖ρ i‖) ≤
      Real.log ‖∏ i ∈ S, genusOneFactor (ρ i) z‖ ∧
    (∏ i ∈ S, genusOneFactor (ρ i) z) ≠ 0 := by
  have hzne : ∀ i ∈ S, z ≠ ρ i := by
    intro i hi he
    have hh := hsep i hi
    rw [← he, hz, sub_self, abs_zero] at hh
    linarith
  have hnonzero : (∏ i ∈ S, genusOneFactor (ρ i) z) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => genusOneFactor_ne_zero (hρ i hi) (hzne i hi))
  refine ⟨?_, hnonzero⟩
  rw [norm_prod, Real.log_prod (fun i hi => norm_ne_zero_iff.mpr
    (genusOneFactor_ne_zero (hρ i hi) (hzne i hi)))]
  have hs := Finset.sum_le_sum (fun i hi =>
    show Real.log d - Real.log B - r / ‖ρ i‖ ≤
      Real.log ‖genusOneFactor (ρ i) z‖ from by
      have hlog := Real.log_le_log (norm_pos_iff.mpr (hρ i hi)) (hupper i hi)
      have hh := SiegelZerosAwei.Workers.W01.log_norm_genusOneFactor_lower
        (hρ i hi) hd hz (hsep i hi)
      linarith)
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv, one_mul, Finset.mul_sum, mul_sub] using hs

variable {q : ℕ} [NeZero q]

theorem actual_canonicalProduct_near_far_lower (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    {R r d : ℝ} (hR : 0 < R) (hr : R ≤ r ∧ r ≤ 2 * R) (hd : 0 < d)
    {z : ℂ} (hz : ‖z‖ = r)
    (hsep : ∀ i ∈ zeroIndexFinset χ hχ (6 * R),
      d ≤ |r - ‖W51.zeroValue χ i‖|) :
    let S := zeroIndexFinset χ hχ (6 * R)
    (S.card : ℝ) * (Real.log d - Real.log (6 * R)) -
        r * (∑ i ∈ S, 1 / ‖W51.zeroValue χ i‖) -
        6 * r ^ 2 * (∑' i : {i : W51.ZeroIndex χ // i ∉ S},
          1 / ‖W51.zeroValue χ i.val‖ ^ 2) ≤
      Real.log ‖W51.canonicalProduct χ z‖ ∧
    W51.canonicalProduct χ z ≠ 0 := by
  classical
  let S := zeroIndexFinset χ hχ (6 * R)
  change (S.card : ℝ) * (Real.log d - Real.log (6 * R)) -
      r * (∑ i ∈ S, 1 / ‖W51.zeroValue χ i‖) -
      6 * r ^ 2 * (∑' i : {i : W51.ZeroIndex χ // i ∉ S},
        1 / ‖W51.zeroValue χ i.val‖ ^ 2) ≤
      Real.log ‖W51.canonicalProduct χ z‖ ∧ W51.canonicalProduct χ z ≠ 0
  have hnear := finite_near_product_log_lower S (W51.zeroValue χ)
    (z := z) (r := r) (d := d) (B := 6 * R) hd hz
    (fun i _ => actual_zeroValue_ne_zero χ hχ hprimitive i)
    (fun i hi => (mem_zeroIndexFinset χ hχ (6 * R) i).mp hi) hsep
  have hfar : ∀ i : {i : W51.ZeroIndex χ // i ∉ S},
      3 * ‖z‖ ≤ ‖W51.zeroValue χ i.val‖ := by
    intro i
    have hh : ¬ ‖W51.zeroValue χ i.val‖ ≤ 6 * R := by
      intro hb
      exact i.property ((mem_zeroIndexFinset χ hχ (6 * R) i.val).mpr hb)
    rw [hz]
    calc
      3 * r ≤ 3 * (2 * R) :=
        mul_le_mul le_rfl hr.2 (hR.le.trans hr.1) (by norm_num)
      _ = 6 * R := by ring
      _ ≤ ‖W51.zeroValue χ i.val‖ := (lt_of_not_ge hh).le
  have htail := infinite_far_product_log_lower
    (fun i : {i : W51.ZeroIndex χ // i ∉ S} => W51.zeroValue χ i.val) z
    (fun i => actual_zeroValue_ne_zero χ hχ hprimitive i.val) hfar
    (zeroSubfamily_inverse_square_summable χ hχ hprimitive (S : Set (W51.ZeroIndex χ))ᶜ)
    (multipliable_zeroSubproduct χ hχ hprimitive (S : Set (W51.ZeroIndex χ))ᶜ z)
  have hhead : Multipliable
      (fun i : (S : Set (W51.ZeroIndex χ)) => genusOneFactor (W51.zeroValue χ i.val) z) :=
    multipliable_zeroSubproduct χ hχ hprimitive (S : Set (W51.ZeroIndex χ)) z
  have hsplit := Multipliable.tprod_mul_tprod_compl
    (f := fun i : W51.ZeroIndex χ => genusOneFactor (W51.zeroValue χ i) z)
    (s := (S : Set (W51.ZeroIndex χ))) hhead
    (multipliable_zeroSubproduct χ hχ hprimitive (S : Set (W51.ZeroIndex χ))ᶜ z)
  rw [Finset.tprod_subtype' S
    (fun i : W51.ZeroIndex χ => genusOneFactor (W51.zeroValue χ i) z)] at hsplit
  change (∏ i ∈ S, genusOneFactor (W51.zeroValue χ i) z) *
    (∏' i : {i : W51.ZeroIndex χ // i ∉ S}, genusOneFactor (W51.zeroValue χ i.val) z) =
      W51.canonicalProduct χ z at hsplit
  have hratio : (∑' i : {i : W51.ZeroIndex χ // i ∉ S},
      (‖z‖ / ‖W51.zeroValue χ i.val‖) ^ 2) =
      r ^ 2 * ∑' i : {i : W51.ZeroIndex χ // i ∉ S}, 1 / ‖W51.zeroValue χ i.val‖ ^ 2 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    rw [hz]
    ring
  rw [hratio] at htail
  have hlog : Real.log ‖W51.canonicalProduct χ z‖ =
      Real.log ‖∏ i ∈ S, genusOneFactor (W51.zeroValue χ i) z‖ +
      Real.log ‖∏' i : {i : W51.ZeroIndex χ // i ∉ S},
        genusOneFactor (W51.zeroValue χ i.val) z‖ := by
    rw [← hsplit, norm_mul, Real.log_mul
      (norm_ne_zero_iff.mpr hnear.2) (norm_ne_zero_iff.mpr htail.2)]
  refine ⟨?_, ?_⟩
  · rw [hlog]
    nlinarith only [hnear.1, htail.1]
  · rw [← hsplit]
    exact mul_ne_zero hnear.2 htail.2

end SiegelZerosAwei.W03

end

end SiegelZeros

end OAI
