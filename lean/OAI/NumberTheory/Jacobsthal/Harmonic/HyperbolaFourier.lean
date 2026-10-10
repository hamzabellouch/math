import OAI.NumberTheory.Jacobsthal.Partitions.PairFibreEnumeration

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaIdentities

attribute [local instance] Classical.decEq

theorem integerWeight_orthogonality (N : ℕ) [NeZero N] (I : Finset ℤ) (u : ZMod N) :
    (∑ h : ZMod N, integerWeight N I h * ZMod.stdAddChar (h*u)) =
      (N : ℂ) * (integerFibre N I u).card := by
  unfold integerWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (h : ZMod N) (x : ℤ) :
      ZMod.stdAddChar (-h*(x : ZMod N)) * ZMod.stdAddChar (h*u) =
        ZMod.stdAddChar (h*(u-(x : ZMod N))) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hterm, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  have he (x : ℤ) : u-(x : ZMod N) = 0 ↔ (x : ZMod N) = u := by
    rw [sub_eq_zero, eq_comm]
  simp_rw [he]
  simp only [ZMod.card, apply_ite, Nat.cast_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, integerFibre]
  ring

theorem integerWeight_zero (N : ℕ) [NeZero N] (I : Finset ℤ) :
    integerWeight N I 0 = I.card := by simp [integerWeight]

end ErdosHyperbolaIdentities

end

section

open scoped BigOperators
namespace ErdosHyperbolaIdentities

attribute [local instance] Classical.decEq

theorem double_weighted_kernel (N : ℕ) [NeZero N] (I J : Finset ℤ) (u v : ZMod N) :
    (∑ h : ZMod N, ∑ k : ZMod N,
      integerWeight N I h * integerWeight N J k * ZMod.stdAddChar (h*u+k*v)) =
      (N : ℂ)^2 * (integerFibre N I u).card * (integerFibre N J v).card := by
  have he (h k : ZMod N) :
      integerWeight N I h * integerWeight N J k * ZMod.stdAddChar (h*u+k*v) =
        (integerWeight N I h * ZMod.stdAddChar (h*u)) *
          (integerWeight N J k * ZMod.stdAddChar (k*v)) := by
    rw [AddChar.map_add_eq_mul]
    ring
  simp_rw [he]
  calc
    _ = (∑ h : ZMod N, integerWeight N I h * ZMod.stdAddChar (h*u)) *
        (∑ k : ZMod N, integerWeight N J k * ZMod.stdAddChar (k*v)) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ = _ := by rw [integerWeight_orthogonality, integerWeight_orthogonality]; ring

theorem double_fourier_scaled (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (I J : Finset ℤ) :
    (∑ h : ZMod N, ∑ k : ZMod N,
      integerWeight N I h * integerWeight N J k * restrictedSum N T hT a c h k) =
      (N : ℂ)^2 * (hyperbolaPairs N T a c I J).card := by
  unfold restrictedSum
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext h
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have hphase (h k : ZMod N) (u : (ZMod N)ˣ) :
      ZMod.stdAddChar (h*(u : ZMod N)+k*(c : ZMod N)*(↑u⁻¹ : ZMod N)) =
        ZMod.stdAddChar (h*(u : ZMod N)+k*((c : ZMod N)*(↑u⁻¹ : ZMod N))) := by
    congr 1
    ring
  simp_rw [hphase, double_weighted_kernel]
  have hc : ((hyperbolaPairs N T a c I J).card : ℂ) =
      (∑ u ∈ unitClass N T hT a,
        (integerFibre N I (u : ZMod N)).card *
          (integerFibre N J ((c : ZMod N)*(↑u⁻¹ : ZMod N))).card : ℂ) := by
    exact_mod_cast hyperbolaPairs_card_eq_fibre_sum N T hT a c I J
  rw [hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem count_eq_fourier (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (I J : Finset ℤ) :
    ((hyperbolaPairs N T a c I J).card : ℂ) =
      (∑ h : ZMod N, ∑ k : ZMod N,
        integerWeight N I h * integerWeight N J k * restrictedSum N T hT a c h k)/(N : ℂ)^2 := by
  have hN : (N : ℂ)^2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast NeZero.ne N)
  apply (eq_div_iff hN).mpr
  simpa only [mul_comm] using (double_fourier_scaled N T hT a c I J).symm

end ErdosHyperbolaIdentities

end

end Erdos970

end OAI
