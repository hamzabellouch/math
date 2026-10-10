import OAI.Combinatorics.ContingencyTables.Transport.ContextGraphEnergy

namespace OAI

/-! # Actual physical context variance, including zero-mass contexts -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles
open FirstPaperContextTransport FirstPaperPhysicalMarginal FiniteExposureVariance
open PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physicalContextEnergy_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (f H : SmallProfile small → ℝ) (hf : ∀ z,0 ≤ f z) :
    0 ≤ physicalContextEnergy small B s σ f H := by
  unfold physicalContextEnergy
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (le_min (hf _) (hf _)) (sq_nonneg _))

/-- No positivity assumption is needed on the whole context. Its child
variance is bounded by its actual physical prefix exchange energy. -/
theorem physical_context_variance (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hU : 2 ≤ U) (hB : ∀ i j,small i j=true → B i j=U)
    (hlarge : ∀ i j,small i j=false → 2 ≤ B i j)
    (hσ : ∀ a : Earlier small s,σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L),∀ i j,T.val.val i j ≤ B i j)
    (H : SmallProfile small → ℝ) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let z := fun j : Fin (U+1) => eliminate Ms f (childProfile U j.val)
    let μ := fun j : Fin (U+1) =>
      eliminate Ms (fun p => f p*H (assemble small s hs σ U e p)) (childProfile U j.val)/z j
    variance z μ ≤ ((U:ℝ)+1)^4*(2+2*n*((U:ℝ)+1)^2)*
      physicalContextEnergy small B s σ (hardMarginal small B r c L) H := by
  dsimp only
  let Ms := widths (fun _ : Fin n => U)
  let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
  let z := fun j : Fin (U+1) => eliminate Ms f (childProfile U j.val)
  have hz : ∀ j,0 ≤ z j := fun j => eliminate_nonnegative Ms f
    (contextHard_nonnegative small B r c L Ms _ _) (childProfile U j.val)
  have hc : 0 ≤ ((U:ℝ)+1)^4*(2+2*n*((U:ℝ)+1)^2) := by positivity
  by_cases hZ : 0 < ∑ j,z j
  · have hv := physical_child_variance small B r c L s hs σ U hU hB hlarge hσ e hcap
      (fun p => H (assemble small s hs σ U e p)) hZ
    have he := context_graphEnergy_le small B r c L s hs σ U (by omega) hB hσ e H
    dsimp only at hv he
    exact hv.trans (mul_le_mul_of_nonneg_left he hc)
  · have hzero : (∑ j,z j)=0 := le_antisymm (le_of_not_gt hZ) (Finset.sum_nonneg (fun j _ => hz j))
    have hzw := zero_mass_weights z hz hzero
    change variance z _ ≤ _
    unfold variance
    simp only [hzw,zero_mul,Finset.sum_const_zero]
    exact mul_nonneg hc (physicalContextEnergy_nonnegative small B s σ _ H
      (hardMarginal_nonnegative small B r c L))

end ContingencyTables.SmallGraphProfiles

end OAI
