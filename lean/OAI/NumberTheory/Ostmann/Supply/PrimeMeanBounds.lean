import OAI.NumberTheory.Ostmann.Supply.FiniteCoverage
import OAI.NumberTheory.Ostmann.Supply.PrimeMeanIdentity

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Set
open scoped BigOperators

theorem weightedPrimeSum_eq_interval (φ : ℝ→ℝ) (W : ℕ→ℝ)
    (hs : tsupport φ ⊆ Ioo (1/2:ℝ) 1) (X : ℕ) (hX : 0<X) :
    weightedPrimeSum φ (X:ℝ) W = ∑n∈primesInInterval (X/2) X,
      Real.log n*W n*φ ((n:ℝ)/X) := by
  classical
  have hXr : (0:ℝ)<X := Nat.cast_pos.mpr hX
  have hsub : primesInInterval (X/2) X⊆Finset.Ioc 0 X := by
    intro n hn
    obtain ⟨hn,hp⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Ioc.mpr ⟨hp.pos,(Finset.mem_Icc.mp hn).2⟩
  unfold weightedPrimeSum
  rw [Nat.floor_natCast]
  have he := Finset.sum_subset hsub (f:=fun n => if n.Prime then
    Real.log n*W n*φ ((n:ℝ)/X) else 0) (by
      intro n hn hnP
      by_cases hp : n.Prime
      · rw [ite_eq_left hp]
        have hz : φ ((n:ℝ)/X)=0 := by
          by_contra hφ
          have hw := Ostmann.ZeroDensity.principal_weight_nonzero_interval hs hXr hφ
          have hlo : X/2≤n := by
            have hx : (X/2:ℕ)≤(X:ℝ)/2 := by simpa using (Nat.cast_div_le (α:=ℝ) (m:=X) (n:=2))
            exact_mod_cast hx.trans hw.1.le
          apply hnP
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo,(Finset.mem_Ioc.mp hn).2⟩,hp⟩
        rw [hz,mul_zero]
      · rw [ite_eq_right hp])
  rw [←he]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ite_eq_left (Finset.mem_filter.mp hn).2]

theorem weightedPrimeSum_le_log_mul (φ : ℝ→ℝ) (W : ℕ→ℝ)
    (hs : tsupport φ ⊆ Ioo (1/2:ℝ) 1) (_hφ0 : ∀x,0≤φ x) (hφ1 : ∀x,φ x≤1)
    (hW : ∀n,0≤W n) (X : ℕ) (hX : 0<X) :
    weightedPrimeSum φ (X:ℝ) W≤Real.log (X:ℝ)*∑n∈primesInInterval (X/2) X,W n := by
  rw [weightedPrimeSum_eq_interval φ W hs X hX,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨hn,hp⟩ := Finset.mem_filter.mp hn
  have hnX : (n:ℝ)≤X := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr hp.pos
  have hlogn : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  calc
    _ ≤ Real.log (n:ℝ)*W n := mul_le_of_le_one_right (mul_nonneg hlogn (hW n)) (hφ1 _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.log_le_log hn0 hnX) (hW n)

end Ostmann.Supply

end

end OAI
