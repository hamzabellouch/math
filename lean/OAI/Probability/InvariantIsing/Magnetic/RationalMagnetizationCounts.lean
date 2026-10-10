import OAI.Probability.InvariantIsing.Cavity.ConsecutiveGroupProfile
import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupInterior

namespace OAI

/-! A common denominator makes any finite rational interior magnetization
attainable after repeating the original group block. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma rational_magnetization_counts {A : Type*} [Fintype A] [DecidableEq A]
    (size : A → ℕ) (mag : RationalMagnetization A) :
    ∃ d : ℕ, 0 < d ∧ ∃ k : A → ℕ, (∀ a, k a ≤ d*size a) ∧
      ∀ a, (k a : ℝ)=(d*size a : ℕ)*((1+(mag.val a : ℝ))/2) := by
  let p := fun a => (1+mag.val a)/2
  have hp a : 0 ≤ p a := by
    have hh := (abs_lt.mp (mag.property a)).1
    have hh' : 0 ≤ (1+(mag.val a : ℝ))/2 := by linarith
    exact_mod_cast hh'
  have hp1 a : (p a : ℝ) ≤ 1 := by
    have hh := (abs_lt.mp (mag.property a)).2
    dsimp only [p]
    push_cast
    linarith
  let d := ∏ a, (p a).den
  have hd : 0 < d := Finset.prod_pos (fun a _ => (p a).den_pos)
  have hdiv a : (p a).den ∣ d := Finset.dvd_prod_of_mem (fun a => (p a).den) (Finset.mem_univ a)
  let k := fun a => (d/(p a).den)*(p a).num.toNat*size a
  have he a : (k a : ℝ)=(d*size a : ℕ)*(p a : ℝ) := by
    have hnum : ((p a).num.toNat : ℝ)=(p a : ℝ)*(p a).den := by
      have hnat : ((p a).num.toNat : ℤ)=(p a).num :=
        Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hp a))
      have hreal : ((p a).num.toNat : ℝ)=((p a).num : ℝ) := by exact_mod_cast hnat
      rw [hreal,Rat.cast_def]
      exact (div_mul_cancel₀ ((p a).num : ℝ)
        (Nat.cast_ne_zero.mpr (p a).den_pos.ne')).symm
    have hprod : ((d/(p a).den : ℕ) : ℝ)*(p a).den=d := by
      exact_mod_cast Nat.div_mul_cancel (hdiv a)
    dsimp only [k]
    rw [Nat.cast_mul,Nat.cast_mul,hnum,Nat.cast_mul]
    calc
      _ = (((d/(p a).den : ℕ) : ℝ)*(p a).den)*size a*(p a : ℝ) := by ring
      _ = _ := by rw [hprod]
  refine ⟨d,hd,k,?_,?_⟩
  · intro a
    have hh : (k a : ℝ) ≤ (d*size a : ℕ) := by
      rw [he]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (hp1 a)
    exact_mod_cast hh
  · intro a
    simpa only [p,Rat.cast_div,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat] using he a

end InvariantIsing

end

end OAI
