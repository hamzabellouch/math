import Mathlib
import OAI.Analysis.FreeWords.PartialWords

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

local instance : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

variable {I : Type*} {l : Filter I}

theorem unitary_norm_le (u : unitary (ConcreteAlgebra M)) : ‖u.val‖≤1 := by
  have hh := CStarRing.norm_coe_unitary_mul u (1:ConcreteAlgebra M)
  simpa only [mul_one] using hh.le.trans (PatchingWord.concrete_norm_one_le (M := M))

theorem tendsto_gns_unitary_pow {f : I → unitary (ConcreteAlgebra M)}
    {u : unitary (ConcreteAlgebra M)}
    (hf : Tendsto (fun i => gnsVector (tracePositive τ) (f i).val) l
      (𝓝 (gnsVector (tracePositive τ) u.val))) (n : ℕ) :
    Tendsto (fun i => gnsVector (tracePositive τ) ((f i)^n).val) l
      (𝓝 (gnsVector (tracePositive τ) (u^n).val)) := by
  induction n with
  | zero => simpa only [pow_zero, Submonoid.coe_one] using (tendsto_const_nhds (x := gnsVector (tracePositive τ) (1:ConcreteAlgebra M)))
  | succ n ih =>
    simpa only [pow_succ,Submonoid.coe_mul] using
      tendsto_gns_mul τ 1 zero_le_one (fun i => unitary_norm_le ((f i)^n)) ih hf

theorem tendsto_gns_unitary_zpow {f : I → unitary (ConcreteAlgebra M)}
    {u : unitary (ConcreteAlgebra M)}
    (hf : Tendsto (fun i => gnsVector (tracePositive τ) (f i).val) l
      (𝓝 (gnsVector (tracePositive τ) u.val))) (k : ℤ) :
    Tendsto (fun i => gnsVector (tracePositive τ) ((f i)^k).val) l
      (𝓝 (gnsVector (tracePositive τ) (u^k).val)) := by
  cases k with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using tendsto_gns_unitary_pow τ hf n
  | negSucc n =>
    simpa only [zpow_negSucc, ← Unitary.star_eq_inv, Unitary.coe_star] using
      tendsto_gns_star τ (tendsto_gns_unitary_pow τ hf (n+1))

theorem tendsto_gns_unitary_word {f : I → unitary (ConcreteAlgebra M)}
    {u : unitary (ConcreteAlgebra M)}
    (hf : Tendsto (fun i => gnsVector (tracePositive τ) (f i).val) l
      (𝓝 (gnsVector (tracePositive τ) u.val))) (w : List (ℤ × ConcreteAlgebra M)) :
    Tendsto (fun i => gnsVector (tracePositive τ)
      ((w.map fun z => ((f i)^z.1).val*z.2).prod)) l
      (𝓝 (gnsVector (tracePositive τ) ((w.map fun z => (u^z.1).val*z.2).prod))) := by
  induction w with
  | nil => exact tendsto_const_nhds
  | cons z s ih =>
    simp only [List.map_cons,List.prod_cons]
    have hb (i:I) : ‖((f i)^z.1).val*z.2‖ ≤ ‖z.2‖ := by
      calc
        ‖((f i)^z.1).val*z.2‖ ≤ ‖((f i)^z.1).val‖ * ‖z.2‖ := norm_mul_le _ _
        _ ≤ 1 * ‖z.2‖ := mul_le_mul_of_nonneg_right (unitary_norm_le ((f i)^z.1)) (norm_nonneg z.2)
        _ = ‖z.2‖ := one_mul _
    exact tendsto_gns_mul τ ‖z.2‖ (norm_nonneg _) hb
      (tendsto_gns_mul τ 1 zero_le_one (fun i => unitary_norm_le ((f i)^z.1))
        (tendsto_gns_unitary_zpow τ hf z.1) tendsto_const_nhds) ih

end

end KKLocalPatching
end

end OAI
