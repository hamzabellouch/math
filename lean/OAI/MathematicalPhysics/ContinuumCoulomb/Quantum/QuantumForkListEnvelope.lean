import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListGraph

namespace OAI

/-! Polynomial coefficient envelopes for the parallel fork used by the literal
compiler. Both retained bonds and active pairs fit the same size bound. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

def forkBudget (M L : ℝ) : ℝ :=
  3*M*L+L+3*M*(1+4*L)+12*M*(1+2*L)^2+1

def forkRadius (M L T : ℝ) : ℝ :=
  L+16*(forkBudget M L)^3*T+4*forkBudget M L+1

def forkCoefficient (M L T : ℝ) : ℝ :=
  1+L+(10*M+2)*(forkRadius M L T)^2

theorem graphScale_abs_bound {m r : ℕ} (w : Fin m → ℚ) (J K : Fin r → ℚ)
    (c N : ℚ) (hN : 0 ≤ N) {M L T : ℝ} (hm : (m:ℝ) ≤ M) (hr : (r:ℝ) ≤ M)
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : |(c:ℝ)| ≤ L)
    (hw : ∀ e, |(w e:ℝ)| ≤ L) (hJ : ∀ e, |(J e:ℝ)| ≤ L)
    (hK : ∀ e, |(K e:ℝ)| ≤ L) :
    |(graphScale w J K c N:ℝ)| ≤ forkRadius M L T := by
  have hM : 0 ≤ M := (Nat.cast_nonneg m).trans hm
  have hL0 : 0 ≤ L := by linarith
  have hn0 : 0 ≤ (N:ℝ) := by exact_mod_cast hN
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hret : (∑ e, |(w e:ℝ)|) ≤ M*L := by
    calc
      _ ≤ ∑ _e : Fin m, L := Finset.sum_le_sum (fun e _ => hw e)
      _ = (m:ℝ)*L := by simp
      _ ≤ M*L := mul_le_mul_of_nonneg_right hm hL0
  have hlin : (∑ e, (1+2*|(J e:ℝ)|+2*|(K e:ℝ)|)) ≤ M*(1+4*L) := by
    calc
      _ ≤ ∑ _e : Fin r, (1+4*L) := Finset.sum_le_sum (fun e _ => by linarith [hJ e,hK e])
      _ = (r:ℝ)*(1+4*L) := by simp [mul_add]
      _ ≤ M*(1+4*L) := mul_le_mul_of_nonneg_right hr (by positivity)
  have hsq : (∑ e, (1+|(J e:ℝ)|+|(K e:ℝ)|)^2) ≤ M*(1+2*L)^2 := by
    calc
      _ ≤ ∑ _e : Fin r, (1+2*L)^2 := Finset.sum_le_sum (fun e _ =>
        pow_le_pow_left₀ (by positivity) (by linarith [hJ e,hK e]) 2)
      _ = (r:ℝ)*(1+2*L)^2 := by simp
      _ ≤ M*(1+2*L)^2 := mul_le_mul_of_nonneg_right hr (sq_nonneg _)
  let A : ℝ := 3*∑ e, (1+2*|(J e:ℝ)|+2*|(K e:ℝ)|)
  let D : ℝ := 3*(∑ e, |(w e:ℝ)|)+|(c:ℝ)|+12*∑ e, (1+|(J e:ℝ)|+|(K e:ℝ)|)^2
  have hAD0 : 0 ≤ A+D+1 := by dsimp [A,D]; positivity
  have hAD : A+D+1 ≤ forkBudget M L := by dsimp [A,D,forkBudget]; linarith
  have hcube := pow_le_pow_left₀ hAD0 hAD 3
  rw [graphScale_cast]
  change |16*(A+D+1)^3*(N:ℝ)+4*(A+D+1)+1| ≤ _
  rw [abs_of_nonneg (by positivity)]
  have hnT : (N:ℝ) ≤ T := by simpa only [abs_of_nonneg hn0] using hT
  have hprod := mul_le_mul hcube hnT hn0 (pow_nonneg (hAD0.trans hAD) 3)
  dsimp only [forkRadius]
  nlinarith

end ContinuumCoulomb.QuantumForkList

end

end OAI
