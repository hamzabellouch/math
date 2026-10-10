import OAI.Combinatorics.ContingencyTables.Transport.IntegerRootTransport

namespace OAI

/-! # The hard-zero limit of the actual integer transport

The final bound contains only finite marginal and auxiliary defect sums,
minimum-endpoint graph energies, and the two positive endpoint masses.
Thus no limit of recursively defined coefficients is needed.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Topology
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal Filter

universe u

variable {K : Type*} {l : Filter K}

lemma auxiliaryKernel_tendsto {I : Type u} (Ms : List ℕ)
    (F : K → (Coordinates I Ms → ℕ) → ℝ) (f : (Coordinates I Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x))) (z : I → ℕ) :
    Tendsto (fun t => auxiliaryKernel Ms (F t) z) l (nhds (auxiliaryKernel Ms f z)) := by
  induction Ms with
  | nil => exact tendsto_const_nhds
  | cons U Ms ih =>
    apply Tendsto.add
    · unfold marginal
      apply tendsto_finsetSum
      intro j _
      exact eliminate_tendsto Ms _ _ (fun x => hlim _) _
    · apply ih
      intro x
      unfold marginal
      apply tendsto_finsetSum
      intro j _
      exact hlim _

lemma removal_tendsto {C : Type*} [DecidableEq C]
    (F : K → (C → ℕ) → ℝ) (f : (C → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x))) (z : C → ℕ) (i j : C) :
    Tendsto (fun t => integerRemovalMatrix (F t) z i j) l
      (nhds (integerRemovalMatrix f z i j)) := by
  by_cases hv : ValidPair z i j
  · simpa only [integerRemovalMatrix,hv,↓reduceIte] using hlim (removeTwo z i j)
  · simpa only [integerRemovalMatrix,hv,↓reduceIte] using
      (tendsto_const_nhds : Tendsto (fun _ : K => (0:ℝ)) l (nhds 0))

lemma oneHole_tendsto {C : Type*} [DecidableEq C]
    (F : K → (C → ℕ) → ℝ) (f : (C → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x))) (z : C → ℕ) (i : C) :
    Tendsto (fun t => oneHole (F t) z i) l (nhds (oneHole f z i)) := by
  by_cases hi : 0 < z i
  · simpa only [oneHole,hi,↓reduceIte] using hlim (removeOne z i)
  · simpa only [oneHole,hi,↓reduceIte] using
      (tendsto_const_nhds : Tendsto (fun _ : K => (0:ℝ)) l (nhds 0))

lemma integerGraphEnergy_tendsto {C : Type*} [DecidableEq C]
    (V : Finset (C → ℕ)) (F : K → (C → ℕ) → ℝ) (f H : (C → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x))) :
    Tendsto (fun t => integerGraphEnergy V (F t) H) l (nhds (integerGraphEnergy V f H)) := by
  unfold integerGraphEnergy
  apply Tendsto.div_const
  apply tendsto_finsetSum
  intro e _
  exact ((hlim e.1).min (hlim e.2)).mul_const _

lemma root_linear_eq (g : (Bool → ℕ) → ℝ) (z : Bool → ℕ) (s t : ℝ) :
    holeLinear g z (rootCoefficients s t) = oneHole g z false/s-oneHole g z true/t := by
  simp only [holeLinear,Fintype.sum_bool,rootCoefficients,Bool.false_eq_true,↓reduceIte]
  ring

/-- The original raw integer transport survives arbitrary hard zeros.
Only its two endpoint marginal masses must remain positive. -/
theorem integer_root_graph_transport_limit [l.NeBot] (Ms : List ℕ)
    (F : K → (Coordinates Bool Ms → ℕ) → ℝ) (f H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x)))
    (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hsoft : ∀ᶠ t in l, (∀ x, 0 ≤ F t x) ∧
      BalancedBox.PositiveSlice (F t) (bounds m Ms) (R+Ms.sum) ∧
      BalancedBox.RemovalSlice (F t) (bounds m Ms) (R+Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms f) z false)
    (ht : 0 < oneHole (eliminate Ms f) z true)
    (V : Finset (Coordinates Bool Ms → ℕ)) (hV : leafVertices Ms z ⊆ V) :
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms f) z false true
    (oneHole (eliminate Ms (fun p => f p*H p)) z false/s -
      oneHole (eliminate Ms (fun p => f p*H p)) z true/t)^2 ≤
      (1/s+1/t+2*((W:ℝ)+1)^2*c/(s*t)) * integerGraphEnergy V f H := by
  dsimp only
  have hmarg := eliminate_tendsto Ms F f hlim
  have hnum := eliminate_tendsto Ms (fun t p => F t p*H p) (fun p => f p*H p)
    (fun p => (hlim p).mul_const (H p))
  have hsm := oneHole_tendsto _ _ hmarg z false
  have htm := oneHole_tendsto _ _ hmarg z true
  have hsn := oneHole_tendsto _ _ hnum z false
  have htn := oneHole_tendsto _ _ hnum z true
  have hc := removal_tendsto _ _ (auxiliaryKernel_tendsto Ms F f hlim) z false true
  have he := integerGraphEnergy_tendsto V F f H hlim
  have hleft := ((hsn.div hsm (ne_of_gt hs)).sub (htn.div htm (ne_of_gt ht))).pow 2
  have h1 : Tendsto (fun _ : K => (1:ℝ)) l (nhds 1) := tendsto_const_nhds
  have hright := (((h1.div hsm (ne_of_gt hs)).add
    (h1.div htm (ne_of_gt ht))).add
    ((hc.const_mul (2*((W:ℝ)+1)^2)).div (hsm.mul htm) (mul_ne_zero (ne_of_gt hs) (ne_of_gt ht)))).mul he
  apply le_of_tendsto_of_tendsto hleft hright
  have hspos : ∀ᶠ t in l, 0 < oneHole (eliminate Ms (F t)) z false :=
    hsm.eventually (lt_mem_nhds hs)
  have htpos : ∀ᶠ t in l, 0 < oneHole (eliminate Ms (F t)) z true :=
    htm.eventually (lt_mem_nhds ht)
  filter_upwards [hsoft,hspos,htpos] with t hf hsp htp
  have hb := integer_root_graph_transport Ms (F t) H m z R W hlower hupper
    hf.1 hf.2.1 hf.2.2 hz htotal hsp htp V hV
  simpa only [root_linear_eq, Pi.div_apply] using hb

end ContingencyTables.IntegerWeightedTransport

end OAI
