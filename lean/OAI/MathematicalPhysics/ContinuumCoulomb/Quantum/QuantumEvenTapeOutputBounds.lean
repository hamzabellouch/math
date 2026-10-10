import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenTapeWeights
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteOutputBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCoefficientPrograms

namespace OAI

/-! A uniform source promise for the literal even tape followed by the
fixed final routing rounds, with a common numerical envelope for the
spatial compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenTapeGeometry
open QuantumListSchedule QuantumCoefficientPrograms
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)
    {r : ℕ} (labels : G.Edge ≃ Fin r) {N : ℚ}

theorem output_polynomialPromise (hN : 0 < N) (hpath : ∀ e, P.length e ≤ 20)
    {X Y m L T n k : ℕ} (hbox : P.Bounded X Y) (hn : 0 < G.n)
    (hm : Fintype.card G.Edge ≤ m) (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T)
    (hc : G.CoefficientBound L) (hsize : n ≤ G.n)
    (a b : ℚ) (hab : a < b)
    (hx : (8*X:ℕ) ≤ (n+1:ℝ)^k) (hy : (8*Y:ℕ) ≤ (n+1:ℝ)^k)
    (hw : ((3^81*m+1)*iterated (3*m) (pathCoefficient m L T) T 80:ℕ) ≤ (n+1:ℝ)^k)
    (hgap : ((n+1:ℝ)^k)⁻¹ ≤ (b:ℝ)-a) :
    (QuantumListRouteProgram.latticeOutput
      (QuantumListRouteProgram.iterate N QuantumFinalRoutingProgram.rounds
        (QuantumEvenTapeProgram.value (input P labels N))) a b).PolynomialPromise k := by
  have hr : r ≤ m := by
    have he : Fintype.card G.Edge=r := (Fintype.card_congr labels).trans (Fintype.card_fin r)
    omega
  have hm' : (Fintype.card G.Edge:ℝ) ≤ m := by exact_mod_cast hm
  have hc' := coefficientBound P labels N hN.le hm' (by exact_mod_cast hL) hT hc
  have hn' : G.n ≤ (QuantumEvenTapeProgram.value (input P labels N)).1.1 := by
    rw [count_eq]
    exact Nat.le_add_right _ _
  have hcount : ((QuantumEvenTapeProgram.value (input P labels N)).1.2.2.length:ℝ) ≤ 3*(m:ℝ) := by
    have he := entry_count P labels N
    have hh : (QuantumEvenTapeProgram.value (input P labels N)).1.2.2.length ≤ 3*m := by
      change (QuantumEvenTapeProgram.entries (input P labels N)).length ≤ _
      rw [he]
      omega
    exact_mod_cast hh
  have hC1 : (1:ℝ) ≤ qmaPathCoefficientBound m L T :=
    qmaPathCoefficientBound_one (Nat.cast_nonneg _) (by exact_mod_cast hL)
  apply QuantumListRouteProgram.compiled_polynomialPromise hN
    (QuantumEvenTapeProgram.value (input P labels N)) (input_valid P labels N)
    (embedding P labels N) (represents P labels N)
    (by rw [QuantumFinalRoutingProgram.rounds_eq]; exact work_le P labels N hpath)
    (embedding_bounded P labels N hbox) (hn.trans_le hn') a b hab n k (hsize.trans hn')
    hx hy hcount hC1 hT hc' ?_ hgap
  have hC0 : (0:ℝ) ≤ iterated (3*m) (pathCoefficient m L T) T 80 := Nat.cast_nonneg _
  calc
    (3^QuantumFinalRoutingProgram.rounds*(3*(m:ℝ)))*
        qmaPathIteratedBound (3*(m:ℝ)) (qmaPathCoefficientBound m L T) T
          QuantumFinalRoutingProgram.rounds =
      (3^81*(m:ℝ))*(iterated (3*m) (pathCoefficient m L T) T 80:ℝ) := by
        rw [QuantumFinalRoutingProgram.rounds_eq]
        rw [← pathCoefficient_cast]
        have he := iterated_cast (3*m) (pathCoefficient m L T) T 80
        simp only [Nat.cast_mul,Nat.cast_ofNat] at he
        rw [← he]
        ring
    _ ≤ ((3^81*m+1)*iterated (3*m) (pathCoefficient m L T) T 80:ℕ) := by
      push_cast
      nlinarith
    _ ≤ _ := hw

end ContinuumCoulomb.QuantumEvenTapeGeometry

end

end OAI
