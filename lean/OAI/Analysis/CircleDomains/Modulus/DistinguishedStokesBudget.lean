import OAI.Analysis.CircleDomains.Modulus.StokesBudget

namespace OAI

/-! The singular terminal is absent from the Stokes boundary sum. Restrict
both the finite terminal norm and the original countable band budget to
its complement before applying Cauchy--Schwarz. -/

open Set Function
open scoped BigOperators

noncomputable section
namespace CircleDomainRigidity

 theorem sum_off_distinguished {I : Type*} [Fintype I] [DecidableEq I]
    (b : I) (f : I → ℝ) :
    (∑ i : {i : I // i ≠ b}, f i) = ∑ i ∈ Finset.univ.erase b, f i :=
  (Finset.sum_subtype (Finset.univ.erase b) (by simp) f).symm

 theorem sum_off_distinguished_le {I : Type*} [Fintype I] [DecidableEq I]
    (b : I) (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i : {i : I // i ≠ b}, f i) ≤ ∑ i, f i := by
  rw [sum_off_distinguished]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun i _ _ => hf i)

 theorem circle_stokes_bound_off_distinguished
    {I S : Type*} [Fintype I] [DecidableEq I] (label : I → S) (hinj : Injective label) (b : I)
    (band : S → ℝ) (hband : Summable (fun s => band s ^ 2))
    (r A : I → ℝ) (hA : ∀ i ≠ b, 0 ≤ A i) (hb : ∀ s, 0 ≤ band s)
    {L e η outer : ℝ} (hL : 0 ≤ L)
    (hr : ∑ i, r i ^ 2 ≤ L ^ 2)
    (hexcess : Real.sqrt (∑ i, max (A i - band (label i)) 0 ^ 2) ≤ η)
    (hstokes : |outer| ≤ Real.sqrt Real.pi * L * e +
      ∑ i ∈ Finset.univ.erase b, 2 * Real.pi * r i * A i) :
    |outer| ≤ Real.sqrt Real.pi * L * e +
      2 * Real.pi * L *
        (Real.sqrt (∑' s : {s : S // s ≠ label b}, band s ^ 2) + η) := by
  classical
  let label' : {i : I // i ≠ b} → {s : S // s ≠ label b} :=
    fun i => ⟨label i, fun h => i.property (hinj h)⟩
  have hi : Injective label' := by
    intro i j h
    exact Subtype.ext (hinj (congrArg Subtype.val h))
  have hr' : (∑ i : {i : I // i ≠ b}, r i ^ 2) ≤ L ^ 2 :=
    (sum_off_distinguished_le b (fun i => r i ^ 2) (fun i => sq_nonneg _)).trans hr
  have he' : Real.sqrt (∑ i : {i : I // i ≠ b}, max (A i - band (label i)) 0 ^ 2) ≤ η :=
    (Real.sqrt_le_sqrt (sum_off_distinguished_le b _ (fun i => sq_nonneg _))).trans hexcess
  have hs' : |outer| ≤ Real.sqrt Real.pi * L * e +
      ∑ i : {i : I // i ≠ b}, 2 * Real.pi * r i * A i := by
    rwa [sum_off_distinguished b (fun i => 2 * Real.pi * r i * A i)]
  exact circle_stokes_bound_of_excess label' hi (fun s => band s)
    (hband.subtype _) (fun i => r i) (fun i => A i)
    (fun i => hA i i.property) (fun i => hb _) hL hr' he' hs'

end CircleDomainRigidity

end

end OAI
