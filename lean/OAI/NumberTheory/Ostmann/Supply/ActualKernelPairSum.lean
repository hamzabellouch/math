import OAI.NumberTheory.Ostmann.Supply.ActualKernelAverage
import OAI.NumberTheory.Ostmann.Supply.ActualWindowSizes
import OAI.NumberTheory.Ostmann.Supply.NaturalWeight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Ostmann.Preliminaries
open scoped BigOperators

theorem sqrt_product_le_common {a b T : ℝ} (_ha : 0≤a) (hb : 0≤b) (hT : 0≤T)
    (haT : a≤T) (hbT : b≤T) : Real.sqrt (a*b)≤T := by
  have h := Real.sqrt_le_sqrt (mul_le_mul haT hbT hb hT)
  simpa only [←pow_two,Real.sqrt_sq hT] using h

theorem multiply_average_bound {a b v D E : ℝ} (ha : 0<a) (hb : 0<b)
    (h : v≤D/Real.sqrt (a*b)*E) : a*b*v≤D*Real.sqrt (a*b)*E := by
  have hp : 0<a*b := mul_pos ha hb
  have hs : Real.sqrt (a*b)≠0 := (Real.sqrt_pos.mpr hp).ne'
  have he : (a*b)*(D/Real.sqrt (a*b)*E)=D*Real.sqrt (a*b)*E := by
    field_simp
    rw [Real.sq_sqrt hp.le]
    ring
  exact (mul_le_mul_of_nonneg_left h hp.le).trans_eq he

theorem eventually_actualKernel_pair_sum_bound (d : Decomposition) :
    ∃ C:ℝ,0<C ∧ ∀ᶠL:ℝ in atTop, ∀p:ℕ→ℕ,∀n:ℕ,
      ∀ _hzero:∀i,NeZero (p i),
      (∀i<n,(p i).Prime) → Set.InjOn p (Finset.range n:Set ℕ) →
      (∀i<n,(1/20:ℝ)*L<Real.log (Real.log (p i:ℝ)) ∧
        Real.log (Real.log (p i:ℝ))≤(9/10:ℝ)*L) →
      (∀i<n,(1/3:ℝ)≤density (actualSupport d (p i))) →
      (∀i<n,density (actualSupport d (p i))≤2/3) →
      (∀i<n,gamma (actualSupport d (p i))≤ supplyEpsilon^2) →
      reciprocalMass (Finset.range n) p≤L →
      let A := upperWindow d.A ((supplyRadius L)^2)
      let B := upperWindow d.B ((supplyRadius L)^2)
      let S := fun i => actualSupport d (p i)
      (∑a∈A,∑b∈B,naturalKernelWeight p S n (supplyTruncation L) (a+b)) ≤
        4718592*kernelUnitProduct (Finset.range n) p S*(supplyRadius L:ℝ)^2*
          Real.exp (-(8/5:ℝ)*reciprocalMass (Finset.range n) p+C*Real.sqrt L) := by
  obtain ⟨C,hC,haverage⟩ := eventually_actualKernel_average_bound d
  obtain ⟨D,hD,hsize⟩ := eventually_actualWindow_card_bound d
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [haverage,hsize,eventually_supplyBand_primes_large] with L hav hs hlarge
  intro p n hzero hp hinj hband hlo hhi hg hH
  let : ∀i,NeZero (p i) := hzero
  let A := upperWindow d.A ((supplyRadius L)^2)
  let B := upperWindow d.B ((supplyRadius L)^2)
  let S := fun i => actualSupport d (p i)
  have ha : (0:ℝ)<A.card := Nat.cast_pos.mpr hs.1.card_pos
  have hb : (0:ℝ)<B.card := Nat.cast_pos.mpr hs.2.1.card_pos
  have hU : 0≤kernelUnitProduct (Finset.range n) p S :=
    (kernelUnitProduct_pos (Finset.range n) p S
      (fun i hi => hlarge _ (hp i (Finset.mem_range.mp hi)) (hband i (Finset.mem_range.mp hi)).1)
      (fun i hi => hlo i (Finset.mem_range.mp hi))
      (fun i hi => hhi i (Finset.mem_range.mp hi))
      (fun i hi => hg i (Finset.mem_range.mp hi))).le
  have ht := multiply_average_bound ha hb (hav p n hzero hp hinj hband hlo hhi hg hH)
  have hsz := sqrt_product_le_common ha.le hb.le
    (by positivity : 0≤1536*(supplyRadius L:ℝ)*Real.exp (D*Real.sqrt L)) hs.2.2.1 hs.2.2.2
  change (∑a∈A,∑b∈B,naturalKernelWeight p S n (supplyTruncation L) (a+b)) ≤
    4718592*kernelUnitProduct (Finset.range n) p S*(supplyRadius L:ℝ)^2*
      Real.exp (-(8/5:ℝ)*reciprocalMass (Finset.range n) p+(C+D)*Real.sqrt L)
  rw [naturalKernelWeight_pair_sum p S A B n (supplyTruncation L) hs.1 hs.2.1]
  calc
    _ ≤ (3072*kernelUnitProduct (Finset.range n) p S*(supplyRadius L:ℝ))*
      Real.sqrt ((A.card:ℝ)*(B.card:ℝ))*
      Real.exp (-(8/5:ℝ)*reciprocalMass (Finset.range n) p+C*Real.sqrt L) := ht
    _ ≤ (3072*kernelUnitProduct (Finset.range n) p S*(supplyRadius L:ℝ))*
      (1536*(supplyRadius L:ℝ)*Real.exp (D*Real.sqrt L))*
      Real.exp (-(8/5:ℝ)*reciprocalMass (Finset.range n) p+C*Real.sqrt L) := by
        gcongr
    _ = _ := by rw [show -(8/5:ℝ)*reciprocalMass (Finset.range n) p+(C+D)*Real.sqrt L =
        D*Real.sqrt L+(-(8/5:ℝ)*reciprocalMass (Finset.range n) p+C*Real.sqrt L) by ring]; simp only [Real.exp_add]; ring

end Ostmann.Supply

end

end OAI
