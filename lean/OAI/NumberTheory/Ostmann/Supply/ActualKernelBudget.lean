import OAI.NumberTheory.Ostmann.Supply.ActualCenteredBudget
import OAI.NumberTheory.Ostmann.Supply.KernelEmpirical
import OAI.NumberTheory.Ostmann.Supply.RetainedBandProducts

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter TensorModes TensorOperators Ostmann.Preliminaries
open scoped BigOperators

theorem actualKernelOutput_norm_sq (d : Decomposition) (A : Finset ℕ)
    (p : ℕ→ℕ) [∀i,NeZero (p i)] (n K : ℕ)
    (hp : ∀i<n,(p i).Prime) (hinj : Set.InjOn p (Finset.range n:Set ℕ)) :
    ‖lowModes (kernelCenteredCodomain p (fun i => actualSupport d (p i))) n K
      (kernelOutputEmpirical p (fun i => actualSupport d (p i)) A
        (fun a i => (a:ZMod (p i))) n)‖^2 =
      ∑t∈retainedProducts p n K,centeredEnergy A (actualSupport d) t := by
  exact norm_residue_lowModes_sq_eq_product_sum A p (actualSupport d) n K hp hinj

theorem actualKernelInput_norm_sq (d : Decomposition) (B : Finset ℕ)
    (p : ℕ→ℕ) [∀i,NeZero (p i)] (n K : ℕ)
    (hp : ∀i<n,(p i).Prime) (hinj : Set.InjOn p (Finset.range n:Set ℕ))
    (hB : ∀b∈B,∀i<n,-(b:ZMod (p i))∈(actualSupport d (p i))ᶜ) :
    ‖lowModes (kernelCenteredDomain p (fun i => actualSupport d (p i))) n K
      (kernelInputEmpirical p (fun i => actualSupport d (p i)) B
        (fun b i => -(b:ZMod (p i))) n)‖^2 =
      ∑t∈retainedProducts p n K,centeredEnergy B (actualSecondSupport d) t := by
  have h := norm_negResidue_lowModes_sq B p (actualComplementSupport d) n K hp hinj
    (by simpa only [actualComplementSupport_eq] using hB)
  let normFn (T : ∀i,Finset (ZMod (p i))) : ℝ :=
    ‖lowModes (fun i => FiniteHilbertSpace.of (centeredSpace (T i))) n K
      (empiricalTensor B (fun b i => (centeredSpace (T i)).orthogonalProjectionOnto
        (EuclideanSpace.single (-(b:ZMod (p i))) 1)) n)‖^2
  change normFn (fun i => actualComplementSupport d (p i)) = _ at h
  change normFn (fun i => (actualSupport d (p i))ᶜ) = _
  have he : normFn (fun i => actualComplementSupport d (p i)) =
      normFn (fun i => (actualSupport d (p i))ᶜ) :=
    congrArg normFn (funext (fun i => actualComplementSupport_eq d (p i)))
  exact he.symm.trans h

theorem prime_mem_retainedProducts (p : ℕ→ℕ) {n K i : ℕ} (hi : i<n) (hK : 1≤K) :
    p i∈retainedProducts p n K := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨{i},?_,by simp⟩
  simp only [retainedModes,Finset.mem_filter,Finset.mem_powerset,Finset.singleton_subset_iff,
    Finset.mem_range,Finset.card_singleton]
  exact ⟨hi,hK⟩

theorem eventually_actualKernel_budgets (d : Decomposition) :
    ∃ C:ℝ,0<C ∧ ∀ᶠL:ℝ in atTop, ∀p:ℕ→ℕ,∀n:ℕ,
      ∀ _hzero:∀i,NeZero (p i),
      (∀i<n,(p i).Prime) → Set.InjOn p (Finset.range n:Set ℕ) →
      (∀i<n,(1/20:ℝ)*L<Real.log (Real.log (p i:ℝ)) ∧
        Real.log (Real.log (p i:ℝ))≤(9/10:ℝ)*L) →
      let A := upperWindow d.A ((supplyRadius L)^2)
      let B := upperWindow d.B ((supplyRadius L)^2)
      let S := fun i => actualSupport d (p i)
      A.Nonempty ∧ B.Nonempty ∧
      (∀a∈A,∀i<n,(a:ZMod (p i))∈S i) ∧
      (∀b∈B,∀i<n,-(b:ZMod (p i))∈(S i)ᶜ) ∧
      ‖lowModes (kernelCenteredCodomain p S) n (2*supplyTruncation L)
        (kernelOutputEmpirical p S A (fun a i => (a:ZMod (p i))) n)‖^2 ≤
        1536*(supplyRadius L:ℝ)/(A.card:ℝ)*
          Real.exp (C*Real.sqrt (Real.log (Real.log (supplyRadius L:ℝ)))) ∧
      ‖lowModes (kernelCenteredDomain p S) n (2*supplyTruncation L)
        (kernelInputEmpirical p S B (fun b i => -(b:ZMod (p i))) n)‖^2 ≤
        1536*(supplyRadius L:ℝ)/(B.card:ℝ)*
          Real.exp (C*Real.sqrt (Real.log (Real.log (supplyRadius L:ℝ)))) := by
  obtain ⟨C,hC,hbudget⟩ := eventually_actual_centered_energy_budgets d
  refine ⟨C,hC,?_⟩
  filter_upwards [supplyRadius_tendsto.eventually hbudget,
    supplyRadius_tendsto.eventually (eventually_actualWindow_supports d),
    eventually_retainedBandProducts,eventually_ge_atTop (1:ℝ)] with L hbudget hs hret hL
  intro p n hzero hp hinj hband
  let : ∀i,NeZero (p i) := hzero
  have hK : 1≤2*supplyTruncation L := by
    have hpos : 0<supplyTruncation L := Nat.ceil_pos.mpr (by linarith : 0<10000*L)
    omega
  have ht := hret p n hp hinj hband
  have hpR : ∀i<n,p i≤ supplyRadius L := fun i hi =>
    (ht (p i) (prime_mem_retainedProducts p hi hK)).2.1
  have hA := fun a ha i hi => hs.2.2.1 a ha (p i) (hp i hi) (hpR i hi)
  have hB : ∀b∈upperWindow d.B ((supplyRadius L)^2),∀i<n,
      -(b:ZMod (p i))∈(actualSupport d (p i))ᶜ := by
    intro b hb i hi
    have h := hs.2.2.2 b hb (p i) (hp i hi) (hpR i hi)
    simpa only [actualSecondSupport,mem_reflectedSupport,actualComplementSupport_eq] using h
  obtain ⟨hba,hbb⟩ := hbudget (retainedProducts p n (2*supplyTruncation L))
    (fun t ht' => ⟨(ht t ht').1,(ht t ht').2.1⟩) (fun t ht' => (ht t ht').2.2)
  refine ⟨hs.1,hs.2.1,hA,hB,?_,?_⟩
  · rw [actualKernelOutput_norm_sq d _ p n _ hp hinj]
    exact hba
  · rw [actualKernelInput_norm_sq d _ p n _ hp hinj hB]
    exact hbb

end Ostmann.Supply

end

end OAI
