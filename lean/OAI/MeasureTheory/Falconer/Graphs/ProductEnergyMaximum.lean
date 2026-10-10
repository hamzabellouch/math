import OAI.MeasureTheory.Falconer.Estimates.ProductOccupiedCount
import OAI.MeasureTheory.Falconer.Graphs.ProductEnergyTransfer

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal NNReal

noncomputable def finiteEnergyMaximum {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞) : ℝ :=
  ((S.sup (fun i => (E i).toNNReal) : ℝ≥0) : ℝ)

theorem finiteEnergyMaximum_nonneg {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞) :
    0 ≤ finiteEnergyMaximum S E := NNReal.coe_nonneg _

theorem le_finiteEnergyMaximum {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞) {i : ι} (hi : i ∈ S) :
    (E i).toReal ≤ finiteEnergyMaximum S E := by
  exact_mod_cast (Finset.le_sup (f := fun i => (E i).toNNReal) hi)

theorem sum_energy_le_maximum {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞) :
    (∑ i ∈ S, (E i).toReal) ≤ (S.card:ℝ)*finiteEnergyMaximum S E := by
  simpa only [Finset.sum_const,nsmul_eq_mul] using
    Finset.sum_le_sum (fun i hi => le_finiteEnergyMaximum S E hi)

theorem two_rpow_as_scale (N : ℕ) (hN : 0 < N) (t : ℝ) :
    (2:ℝ)^t = ((2:ℝ)^N)^(t/N) := by
  rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem product_profile_factor (N : ℕ) (hN : 0 < N) (m₁ m₂ : ℝ → ℝ) (a p k : ℝ) (lam : ℝ) :
    (2:ℝ)^(2*(p-a))*graphProfileCoefficient N ![m₁,m₁,m₂,m₂] a p *
      (144*((2:ℝ)^N)^k) * (4096*((2:ℝ)^N)^(m₁ p-m₁ a+(m₂ p-m₂ a)+12*lam)) =
    589824*((2:ℝ)^N)^(-(m₁ p-p/N-(m₁ a-a/N))-(m₂ p-p/N-(m₂ a-a/N))+k+12*lam) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  rw [two_rpow_as_scale N hN]
  simp only [graphProfileCoefficient,Fin.prod_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,← Real.rpow_sub hR]
  have he (x y z w t : ℝ) : x*(y*y*z*z)*(144*w)*(4096*t) = 589824*(x*y*y*z*z*w*t) := by ring
  rw [he]
  simp only [← Real.rpow_add hR]
  congr 2
  ring

theorem product_profile_sum_bound {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞)
    (N : ℕ) (hN : 0 < N) (m₁ m₂ : ℝ → ℝ) (a p k lam : ℝ)
    (hcard : (S.card:ℝ) ≤ 4096*((2:ℝ)^N)^(m₁ p-m₁ a+(m₂ p-m₂ a)+12*lam)) :
    (2:ℝ)^(2*(p-a))*graphProfileCoefficient N ![m₁,m₁,m₂,m₂] a p *
      (144*((2:ℝ)^N)^k) * (∑ i ∈ S, (E i).toReal) ≤
    589824*((2:ℝ)^N)^(-(m₁ p-p/N-(m₁ a-a/N))-(m₂ p-p/N-(m₂ a-a/N))+k+12*lam) *
      finiteEnergyMaximum S E := by
  have hs := (sum_energy_le_maximum S E).trans
    (mul_le_mul_of_nonneg_right hcard (finiteEnergyMaximum_nonneg S E))
  have hc : 0 ≤ graphProfileCoefficient N ![m₁,m₁,m₂,m₂] a p :=
    Finset.prod_nonneg (fun _ _ => by positivity)
  apply (mul_le_mul_of_nonneg_left hs (by positivity :
    0 ≤ (2:ℝ)^(2*(p-a))*graphProfileCoefficient N ![m₁,m₁,m₂,m₂] a p * (144*((2:ℝ)^N)^k))).trans_eq
  rw [← mul_assoc,product_profile_factor N hN]

end PlanarFalconer

end OAI
