import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesLift

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPriorGrid
open Construction PrimeProgression PrimeCellReplacement HistorySignedResidues

theorem giantPrimeSupport_modulus_lt (G : ℝ) (M : ℕ)
    (hsize : (M : ℝ) < Real.exp (G-1)) {p : ℕ} (hp : p ∈ giantPrimeSupport G) : M < p := by
  obtain ⟨_, hprime, hlo, _⟩ := (mem_logPrimeSupport _ _ _ _).mp hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
  have he : Real.exp (G-1) ≤ (p : ℝ) := by
    simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hlo
  exact_mod_cast hsize.trans_le he

theorem giantPrimeSupport_coprime (G : ℝ) (M : ℕ) (hM : 0 < M)
    (hsize : (M : ℝ) < Real.exp (G-1)) {p : ℕ} (hp : p ∈ giantPrimeSupport G) :
    Nat.Coprime p M := by
  exact Nat.coprime_of_lt_prime (Nat.ne_of_gt hM)
    (giantPrimeSupport_modulus_lt G M hsize hp) ((mem_logPrimeSupport _ _ _ _).mp hp).2.1

theorem giantPrimeSupport_isUnit (G : ℝ) (M : ℕ) (hM : 0 < M)
    (hsize : (M : ℝ) < Real.exp (G-1)) {p : ℕ} (hp : p ∈ giantPrimeSupport G) :
    IsUnit (p : ZMod M) :=
  (ZMod.isUnit_iff_coprime p M).mpr (giantPrimeSupport_coprime G M hM hsize hp)

def giantPrimeUnit (G : ℝ) (M : ℕ) (hM : 0 < M)
    (hsize : (M : ℝ) < Real.exp (G-1)) (p : ℕ) (hp : p ∈ giantPrimeSupport G) :
    (ZMod M)ˣ := (giantPrimeSupport_isUnit G M hM hsize hp).unit

@[simp] theorem giantPrimeUnit_coe (G : ℝ) (M : ℕ) (hM : 0 < M)
    (hsize : (M : ℝ) < Real.exp (G-1)) (p : ℕ) (hp : p ∈ giantPrimeSupport G) :
    (giantPrimeUnit G M hM hsize p hp : ZMod M) = p :=
  (giantPrimeSupport_isUnit G M hM hsize hp).unit_spec

theorem jointUnitTest_primeResidueTest {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (G : ℝ)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M)
    (hsize : (M : ℝ) < Real.exp (G-1)) (p q : ℕ)
    (hp : p ∈ giantPrimeSupport G) (hq : q ∈ giantPrimeSupport G) :
    jointUnitTest (primeResidueTest g V outside h k M hd)
      (fun t : Bool => if t then (q : ZMod M) else (p : ZMod M)) =
      liftedResidueTest g V outside h k M hd ((p : ZMod M), (q : ZMod M)) := by
  let u : Bool → (ZMod M)ˣ := fun t => if t then
    giantPrimeUnit G M (NeZero.pos M) hsize q hq else
    giantPrimeUnit G M (NeZero.pos M) hsize p hp
  have hu : (fun t => (u t : ZMod M)) =
      (fun t : Bool => if t then (q : ZMod M) else (p : ZMod M)) := by
    funext t
    cases t <;> simp [u]
  rw [← hu, jointUnitTest_units]
  simp only [primeResidueTest, u, Bool.false_eq_true, ite_false, ite_true, giantPrimeUnit_coe]

theorem jointUnitTest_mixedResidueTest {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l) (G : ℝ)
    (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M)
    (hsize : (M : ℝ) < Real.exp (G-1)) (n : ℤ) (p : ℕ)
    (hp : p ∈ giantPrimeSupport G) :
    jointUnitTest (mixedResidueTest g V outside h k M hd (n : ZMod M))
      (fun _ : Unit => (p : ZMod M)) =
      liftedResidueTest g V outside h k M hd ((n : ZMod M), (p : ZMod M)) := by
  let u : Unit → (ZMod M)ˣ := fun _ => giantPrimeUnit G M (NeZero.pos M) hsize p hp
  have hu : (fun i => (u i : ZMod M)) = (fun _ : Unit => (p : ZMod M)) := by
    funext i
    exact giantPrimeUnit_coe G M (NeZero.pos M) hsize p hp
  rw [← hu, jointUnitTest_units]
  simp only [mixedResidueTest, u, giantPrimeUnit_coe]

end Ostmann.Arithmetic.HistoryGiantPriorGrid

end

end OAI
