import OAI.NumberTheory.TotientAsymptotic.SquarefreeIntervalMass
import OAI.NumberTheory.TotientAsymptotic.CommonLargestPrime

namespace OAI

/-! The common-largest-prime bound for the globally squarefree application. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem common_prime_squarefree_mass_bound : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (k a b : ℕ) (i : Fin k) (y T U V I : ℝ),
    Real.exp 2 ≤ y → 1 ≤ B y → 1 < T → 1 ≤ k → 2 ≤ U →
    U ≤ V → (k:ℝ)*(B V-B U+D) ≤ I →
    ∀ E : Finset (PairedFactors k × ℕ),
    (∀ f ∈ E,CommonPrimeWitness a b i y T f) →
    (∀ f ∈ E,Squarefree (pairedProduct f.1)) →
    (∀ f ∈ E,0 < pairedProduct f.1 ∧ pairedProduct f.1=(∏ j,f.1.2 j) ∧
      ((pairedProduct f.1).primeFactorsList.length:ℝ) ≤ I ∧
      ∀ p ∈ (pairedProduct f.1).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) →
    (∑ f ∈ E,((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹) ≤
      (C*(B y)^2/(Real.log T)^2)*Real.exp (I*(Real.log k+1)) := by
  classical
  obtain ⟨C,hC,htail⟩ := collision_triple_reciprocal_tail_ne
  obtain ⟨D,hD,halloc⟩ := squarefree_interval_allocation_bound
  refine ⟨C,D,hC,hD,?_⟩
  intro k a b i y T U V I hy hBy hT hk hU hUV hI E hE hsq hQ
  let R := E.image Prod.fst
  let M := C*(B y)^2/(Real.log T)^2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmass : (∑ r ∈ R,(pairedProduct r:ℝ)⁻¹) ≤ Real.exp (I*(Real.log k+1)) := by
    have hR : ∀ r ∈ R,0 < pairedProduct r ∧ pairedProduct r=(∏ j,r.2 j) ∧
        ((pairedProduct r).primeFactorsList.length:ℝ) ≤ I ∧
        ∀ p ∈ (pairedProduct r).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
      intro r hr
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hr
      exact hQ f hf
    apply halloc k U V I hk hU hUV hI R
    · exact fun r hr => ⟨(hR r hr).1,(hR r hr).2.1⟩
    · intro r hr
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hr
      exact hsq f hf
    · exact fun r hr => (hR r hr).2.2.1
    · exact fun r hr => (hR r hr).2.2.2
  have hmap : ∀ f ∈ E,f.1 ∈ R := fun f hf => Finset.mem_image.mpr ⟨f,hf,rfl⟩
  have hfiber (r : PairedFactors k) (hr : r ∈ R) :
      (∑ f ∈ E.filter (fun f => f.1=r),((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹) ≤
        M*(pairedProduct r:ℝ)⁻¹ := by
    apply common_prime_fiber_bound i y T C _ E hE r hr
    intro a b ha hb hab hay hby Q hQ
    exact htail y hy hBy a b ha hb hab hay hby Q T hT hQ
  calc
    _ = ∑ r ∈ R,∑ f ∈ E.filter (fun f => f.1=r),((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹ :=
      (Finset.sum_fiberwise_of_maps_to hmap
        (fun f => ((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹)).symm
    _ ≤ ∑ r ∈ R,M*(pairedProduct r:ℝ)⁻¹ := Finset.sum_le_sum hfiber
    _ = M*(∑ r ∈ R,(pairedProduct r:ℝ)⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass hM

/-- The equal-largest-prime branch, for the original finite family of pairs. -/
theorem common_largest_prime_squarefree_mass_bound : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (k a b : ℕ) (i : Fin k) (y T U V I : ℝ),0 < a → 0 < b →
    Real.exp 2 ≤ y → 1 ≤ B y → 1 < T → 1 ≤ k → 2 ≤ U →
    U ≤ V → (k:ℝ)*(B V-B U+D) ≤ I →
    ∀ Q : Finset (PairedFactors k),
    (∀ f ∈ Q,CommonLargestConditions a b i y T U V I f) →
    (∀ f ∈ Q,Squarefree (pairedProduct f)) →
    (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤
      (C*(B y)^2/(Real.log T)^2)*Real.exp (I*(Real.log k+1)) := by
  classical
  obtain ⟨C,D,hC,hD,hbound⟩ := common_prime_squarefree_mass_bound
  refine ⟨C,D,hC,hD,?_⟩
  intro k a b i y T U V I ha hb hy hBy hT hk hU hUV hI Q hQ hsq
  let E := Q.image (commonLargestEncoding i)
  have hE : ∀ e ∈ E,CommonPrimeWitness a b i y T e := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact commonLargest_witness ha hb (hQ f hf)
  have hres : ∀ e ∈ E,0 < pairedProduct e.1 ∧ pairedProduct e.1=(∏ j,e.1.2 j) ∧
      ((pairedProduct e.1).primeFactorsList.length:ℝ) ≤ I ∧
      ∀ p ∈ (pairedProduct e.1).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact commonLargest_residual (hQ f hf)
  have hi : ∀ f ∈ Q,∀ g ∈ Q,commonLargestEncoding i f=commonLargestEncoding i g → f=g := by
    intro f hf g hg he
    have hh := congrArg (commonPrimeDecode i) he
    rwa [commonLargest_decode (hQ f hf),commonLargest_decode (hQ g hg)] at hh
  have hsum : (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹)=
      ∑ e ∈ E,((pairedProduct e.1*e.2:ℕ):ℝ)⁻¹ := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro f hf
    rw [commonLargest_product (hQ f hf)]
  rw [hsum]
  apply hbound k a b i y T U V I hy hBy hT hk hU hUV hI E hE _ hres
  intro e he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  exact Squarefree.squarefree_of_dvd
    (divideFactor_prod_dvd i _ _ (commonLargest_divisors (hQ f hf)).2.1) (hsq f hf)

end TotientAsymptotic

end

end OAI
