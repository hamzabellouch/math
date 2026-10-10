import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSelector

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialEnergyCallerSelector
namespace SevenEighths.InverseInitialEnergyCallerPool
local notation "Eis" => ActualEisensteinCubic.O

theorem residual_factors_in_pool (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hne : (columns S P j).Nonempty)
    {Q : Ideal Eis} (hQ : Q∈normalizedFactors (residual P j)) :
    Q∈primePool (columns S P j) := by
  obtain ⟨c,hc⟩ := hne
  obtain ⟨hcs,_,hPc,_⟩ := (mem_columns hP hj).mp hc
  apply mem_primePool_iff.mpr
  refine ⟨c,hc,?_⟩
  exact Multiset.mem_of_le
    ((dvd_iff_normalizedFactors_le_normalizedFactors
      (residual_squarefree hP hj).ne_zero hcs.ne_zero).mp hPc) hQ

def forcedSlots (S : Finset (Ideal Eis)) (P j : Ideal Eis) :
    Finset (primePool (columns S P j)) := idealSupport (columns S P j) (residual P j)

theorem forcedSlots_image (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hne : (columns S P j).Nonempty) :
    (forcedSlots S P j).image Subtype.val = IdealMobiusDivisorSum.primeSupport (residual P j) := by
  ext Q
  constructor
  · rintro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    exact Multiset.mem_toFinset.mpr ((mem_idealSupport_iff _ _ i).mp hi)
  · intro hQ
    have hf : Q∈normalizedFactors (residual P j) := Multiset.mem_toFinset.mp hQ
    let i : primePool (columns S P j) := ⟨Q,residual_factors_in_pool S hP hj hne hf⟩
    exact Finset.mem_image.mpr ⟨i,(mem_idealSupport_iff _ _ i).mpr hf,rfl⟩

theorem forcedSlots_product (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hne : (columns S P j).Nonempty) :
    (∏ i∈forcedSlots S P j,i.val)=residual P j := by
  calc
    _ = ∏ Q∈(forcedSlots S P j).image Subtype.val,Q := by
      rw [Finset.prod_image]
      exact fun a _ b _ h=>Subtype.val_injective h
    _ = _ := by rw [forcedSlots_image S hP hj hne]
                exact squarefree_support_product_self (residual_squarefree hP hj)

theorem original_selector_forced_slots
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hne : (columns S P j).Nonempty) (a : Ideal Eis→ℂ) (W : Ideal Eis→ℂ)
    (A : Finset (primePool (columns S P j)))
    (hA : Squarefree (∏ i∈A,i.val))
    (hcover : residual P j∣(∏ i∈A,i.val) → W (∏ i∈A,i.val)≠0 →
      IsCoprime (∏ i∈A,i.val) j → reconstruct P j (∏ i∈A,i.val)∈S) :
    reconstructedSelector S P j a A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) =
    a (reconstruct P j (∏ i∈A,i.val)) *
      SevenEighths.InverseMoment.primeMark (forcedSlots S P j) (fun i=>{i})
        (fun _ _=>(1:ℂ)) A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) :=
  reconstructedSelector_forced_mark S hP hj a W (forcedSlots S P j) A
    (forcedSlots_product S hP.2.1 hj hne) hA hcover

end SevenEighths.InverseInitialEnergyCallerPool

end

end OAI
