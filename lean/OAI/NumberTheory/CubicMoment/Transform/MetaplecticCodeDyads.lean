import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedSupport

namespace OAI

/-! The exact norm dyad of each free variable after fixing the supported
parameters in the retained Voronoi sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev MetaplecticDyadPrefix (r : Eisenstein) := PrimaryArgument × MetaplecticSupportPrefix r

def metaplecticCodePrefix {r : Eisenstein} (z : MetaplecticRetainedCode r) :
    MetaplecticDyadPrefix r := (z.1,z.2.1)

def metaplecticFreeScale {r : Eisenstein} (p : MetaplecticDyadPrefix r) : ℝ :=
  norm p.1^3*((3:ℝ)^((p.2.1:ℝ)-1)*norm p.2.2.2.1.val*norm p.2.2.2.2^3)

lemma metaplecticFreeScale_pos {r : Eisenstein} (p : MetaplecticDyadPrefix r) :
    0 < metaplecticFreeScale p := by
  have hd := norm_pos_of_ne_zero (primary_ne_zero p.1.property)
  have hh := norm_pos_of_ne_zero (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
  have hp := norm_pos_of_ne_zero (primary_ne_zero p.2.2.2.2.property)
  change 0 < norm p.1^3*((3:ℝ)^((p.2.1:ℝ)-1)*
    norm (metaplecticDivisorPrimary r p.2.2.2.1)*norm p.2.2.2.2^3)
  positivity

lemma metaplectic_prefix_frequency {r : Eisenstein} (p : MetaplecticDyadPrefix r)
    {w : Eisenstein} (hw : w ≠ 0) :
    metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1) =
      metaplecticFreeScale p*norm w := by
  have he := metaplecticFreeArgument_frequency p.2.1 p.2.2.1
    (metaplecticDivisorPrimary r p.2.2.2.1) p.2.2.2.2 hw
  have hk : -1 ≤ (p.2.1:ℤ)-1 := by omega
  have hn := metaplectic_block_frequency p.1 _ ((p.2.1:ℤ)-1) hk p.2.2.1
    (metaplecticDivisorPrimary r p.2.2.2.1) p.2.2.2.2 w he
  have hnat : (((p.2.1:ℤ)-1+1).toNat) = p.2.1 := by omega
  simpa only [metaplecticPrefixArgument,metaplecticFreeScale,hnat,metaplecticDivisorPrimary] using hn

lemma metaplectic_code_frequency {r : Eisenstein} (z : MetaplecticRetainedCode r) :
    metaplecticDualNorm (metaplecticRetainedDecode r z) =
      metaplecticFreeScale (metaplecticCodePrefix z)*norm z.2.2 := by
  simpa only [metaplecticRetainedDecode,metaplecticCodePrefix] using
    (metaplectic_prefix_frequency (r := r) (z.1,z.2.1)
      (primary_ne_zero z.2.2.property))

lemma metaplectic_free_dyad {r : Eisenstein} (p : MetaplecticDyadPrefix r)
    {w : Eisenstein} (hw : w ≠ 0) {I : ℝ}
    (hI : I/2 ≤ metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1) ∧
      metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1) ≤ I) :
    (I/metaplecticFreeScale p)/2 ≤ norm w ∧ norm w ≤ I/metaplecticFreeScale p := by
  have hq := metaplecticFreeScale_pos p
  rw [metaplectic_prefix_frequency p hw] at hI
  constructor
  · rw [show (I/metaplecticFreeScale p)/2 = (I/2)/metaplecticFreeScale p by ring]
    apply (div_le_iff₀ hq).mpr
    nlinarith [hI.1]
  · exact (le_div_iff₀ hq).mpr (by nlinarith [hI.2])

lemma metaplectic_free_length_one {r : Eisenstein} (p : MetaplecticDyadPrefix r)
    {w : Eisenstein} (hw : primary w) {I : ℝ}
    (hI : metaplecticDualNorm (metaplecticPrefixArgument r p.2 w,p.1) ≤ I) :
    1 ≤ I/metaplecticFreeScale p := by
  have hq := metaplecticFreeScale_pos p
  rw [metaplectic_prefix_frequency p (primary_ne_zero hw)] at hI
  apply (le_div_iff₀ hq).mpr
  have h := mul_le_mul_of_nonneg_left (one_le_norm (primary_ne_zero hw)) hq.le
  nlinarith

lemma metaplecticFreeScale_lower {r : Eisenstein} (p : MetaplecticDyadPrefix r) :
    (1/3:ℝ) ≤ metaplecticFreeScale p := by
  have hd := one_le_norm (primary_ne_zero p.1.property)
  have hh := one_le_norm (primary_ne_zero (metaplecticDivisorPrimary r p.2.2.2.1).property)
  have hp := one_le_norm (primary_ne_zero p.2.2.2.2.property)
  have hb : (1/3:ℝ) ≤ (3:ℝ)^((p.2.1:ℝ)-1) := by
    rw [Real.rpow_sub (by norm_num),Real.rpow_one]
    exact div_le_div_of_nonneg_right
      (Real.one_le_rpow (by norm_num) (Nat.cast_nonneg p.2.1)) (by norm_num)
  change (1/3:ℝ) ≤ norm p.1^3*((3:ℝ)^((p.2.1:ℝ)-1)*
    norm (metaplecticDivisorPrimary r p.2.2.2.1)*norm p.2.2.2.2^3)
  calc
    (1/3:ℝ) = 1*((1/3)*1*1) := by ring
    _ ≤ _ := by
      gcongr
      · exact one_le_pow₀ hd
      · exact one_le_pow₀ hp

lemma metaplectic_free_length_upper {r : Eisenstein} (p : MetaplecticDyadPrefix r)
    {I : ℝ} (hI : 0 ≤ I) : I/metaplecticFreeScale p ≤ 3*I := by
  apply (div_le_iff₀ (metaplecticFreeScale_pos p)).mpr
  have h := mul_nonneg hI (sub_nonneg.mpr (metaplecticFreeScale_lower p))
  nlinarith

end CubicFirstMoment

end

end OAI
