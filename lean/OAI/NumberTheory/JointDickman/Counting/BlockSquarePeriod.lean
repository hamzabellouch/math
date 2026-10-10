import OAI.NumberTheory.JointDickman.Counting.BlockSquareHits
import OAI.NumberTheory.JointDickman.Counting.RealPeriodicMoments

namespace OAI

/-! # Ordinary long means of square-hit blocks -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem blockSquareHit_modEq {B M u v : ℕ} (h : u ≡ v [MOD auxiliarySquarePeriod B]) :
    BlockSquareHit B M u ↔ BlockSquareHit B M v := by
  have hd (i : Fin M) (p : ℕ) (hp : p ∈ auxiliaryPrimes B) :
      p^2 ∣ u+(i.val+1) ↔ p^2 ∣ v+(i.val+1) :=
    ((h.of_dvd (auxiliarySquare_dvd_period hp)).add_right (i.val+1)).dvd_iff (dvd_refl _)
  constructor
  · rintro ⟨i,p,hp,hpu⟩
    exact ⟨i,p,hp,(hd i p hp).mp hpu⟩
  · rintro ⟨i,p,hp,hpv⟩
    exact ⟨i,p,hp,(hd i p hp).mpr hpv⟩

noncomputable def blockSquareWeight (B M u : ℕ) : ℝ :=
  (B : ℝ)^10*(if BlockSquareHit B M u then 1 else 0)

noncomputable def residueBlockSquareWeight (B M : ℕ) (r : ZMod (auxiliarySquarePeriod B)) : ℝ :=
  blockSquareWeight B M r.val

theorem residueBlockSquareWeight_natCast (B M u : ℕ) :
    residueBlockSquareWeight B M u = blockSquareWeight B M u := by
  unfold residueBlockSquareWeight blockSquareWeight
  rw [ZMod.val_natCast]
  simp only [blockSquareHit_modEq (Nat.mod_modEq u (auxiliarySquarePeriod B))]

theorem blockSquareWeight_long_mean {B M : ℕ} (hB : 1 < B) (hM : M ≤ B^2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop, (∑ u ∈ range K, blockSquareWeight B M u)/(K : ℝ) < 1/(B : ℝ)+ε := by
  let f := residueBlockSquareWeight B M
  have ht := real_periodic_moment_tendsto f 1
  have hf (u : ℕ) : f u = blockSquareWeight B M u := residueBlockSquareWeight_natCast B M u
  simp only [pow_one,hf] at ht
  have hmean : (∑ r, f r)/(auxiliarySquarePeriod B : ℝ) ≤ 1/(B : ℝ) := by
    simpa only [f,residueBlockSquareWeight,blockSquareWeight,← mul_sum,mul_div_assoc]
      using block_squareHit_polynomial_bound hB hM
  exact ht.eventually (Iio_mem_nhds (lt_add_of_le_of_pos hmean hε))

end JointDickman

end OAI
