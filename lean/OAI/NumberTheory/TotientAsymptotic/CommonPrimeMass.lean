import OAI.NumberTheory.TotientAsymptotic.CollisionSieveTails
import OAI.NumberTheory.TotientAsymptotic.PairedFactorizationMass

namespace OAI

/-! The reciprocal mass after one common largest prime has been extracted. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

abbrev PairedFactors (k : ℕ) := (Fin k → ℕ) × (Fin k → ℕ)

def pairedProduct {k : ℕ} (f : PairedFactors k) : ℕ := ∏ j,f.1 j

structure CommonPrimeWitness {k : ℕ} (a b : ℕ) (i : Fin k) (y T : ℝ)
    (f : PairedFactors k × ℕ) : Prop where
  left_pos : 0 < a*f.1.1 i
  right_pos : 0 < b*f.1.2 i
  left_le : (a*f.1.1 i:ℕ) ≤ y
  right_le : (b*f.1.2 i:ℕ) ≤ y
  prime_lower : T ≤ f.2
  prime : f.2.Prime
  left_prime : (a*f.1.1 i*f.2+1).Prime
  right_prime : (b*f.1.2 i*f.2+1).Prime
  different : a*f.1.1 i*f.2+1 ≠ b*f.1.2 i*f.2+1

lemma common_prime_fiber_sum {k : ℕ} (E : Finset (PairedFactors k × ℕ))
    (r : PairedFactors k) :
    (∑ f ∈ E.filter (fun f => f.1=r),((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹)=
      (pairedProduct r:ℝ)⁻¹*
        (∑ q ∈ (E.filter (fun f => f.1=r)).image Prod.snd,(q:ℝ)⁻¹) := by
  classical
  rw [Finset.mul_sum,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro f hf
    have he := (Finset.mem_filter.mp hf).2
    rw [he,Nat.cast_mul,mul_inv_rev]
    ring
  · intro f hf g hg he
    exact Prod.ext ((Finset.mem_filter.mp hf).2.trans (Finset.mem_filter.mp hg).2.symm) he

lemma common_prime_fiber_bound {k a b : ℕ} (i : Fin k) (y T C : ℝ)
    (htail : ∀ a b : ℕ,0 < a → 0 < b → a ≠ b → (a:ℝ) ≤ y → (b:ℝ) ≤ y →
      ∀ Q : Finset ℕ,(∀ q ∈ Q,T ≤ q ∧ q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) →
        (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ C*(B y)^2/(Real.log T)^2)
    (E : Finset (PairedFactors k × ℕ))
    (hE : ∀ f ∈ E,CommonPrimeWitness a b i y T f)
    (r : PairedFactors k) (hr : r ∈ E.image Prod.fst) :
    (∑ f ∈ E.filter (fun f => f.1=r),((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹) ≤
      (C*(B y)^2/(Real.log T)^2)*(pairedProduct r:ℝ)⁻¹ := by
  classical
  obtain ⟨f,hf,he⟩ := Finset.mem_image.mp hr
  have hw := hE f hf
  have hlpos : 0 < a*r.1 i := by simpa only [he] using hw.left_pos
  have hrpos : 0 < b*r.2 i := by simpa only [he] using hw.right_pos
  have hlle : ((a*r.1 i:ℕ):ℝ) ≤ y := by simpa only [he] using hw.left_le
  have hrle : ((b*r.2 i:ℕ):ℝ) ≤ y := by simpa only [he] using hw.right_le
  have hne : a*r.1 i ≠ b*r.2 i := by
    intro h
    apply hw.different
    simp only [he,h]
  have ht := htail (a*r.1 i) (b*r.2 i) hlpos hrpos hne hlle hrle
    ((E.filter (fun f => f.1=r)).image Prod.snd) (by
      intro q hq
      obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hg,her⟩ := Finset.mem_filter.mp hg
      have hwg := hE g hg
      exact ⟨hwg.prime_lower,hwg.prime,by simpa only [her] using hwg.left_prime,
        by simpa only [her] using hwg.right_prime⟩)
  rw [common_prime_fiber_sum]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left ht
    (inv_nonneg.mpr (Nat.cast_nonneg (pairedProduct r)))

 theorem common_prime_mass_bound : ∃ C U₀ : ℝ,0 < C ∧ 2 ≤ U₀ ∧
    ∀ (k a b : ℕ) (i : Fin k) (y T U V I : ℝ),
    Real.exp 2 ≤ y → 1 ≤ B y → 1 < T → 1 ≤ k → U₀ ≤ U →
    4*(k:ℝ)^2 ≤ U → U ≤ V → (k:ℝ)*(B V-B U+1) ≤ I →
    ∀ E : Finset (PairedFactors k × ℕ),
    (∀ f ∈ E,CommonPrimeWitness a b i y T f) →
    (∀ f ∈ E,0 < pairedProduct f.1 ∧ pairedProduct f.1=(∏ j,f.1.2 j) ∧
      ((pairedProduct f.1).primeFactorsList.length:ℝ) ≤ I ∧
      ∀ p ∈ (pairedProduct f.1).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) →
    (∑ f ∈ E,((pairedProduct f.1*f.2:ℕ):ℝ)⁻¹) ≤
      (C*(B y)^2/(Real.log T)^2)*Real.exp (I*(Real.log k+1)+1) := by
  classical
  obtain ⟨C,hC,htail⟩ := collision_triple_reciprocal_tail_ne
  obtain ⟨U₀,hU₀,halloc⟩ := paired_interval_allocation_bound
  refine ⟨C,U₀,hC,hU₀,?_⟩
  intro k a b i y T U V I hy hBy hT hk hU hquad hUV hI E hE hQ
  let R := E.image Prod.fst
  let M := C*(B y)^2/(Real.log T)^2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmass : (∑ r ∈ R,(pairedProduct r:ℝ)⁻¹) ≤ Real.exp (I*(Real.log k+1)+1) := by
    have hR : ∀ r ∈ R,0 < pairedProduct r ∧ pairedProduct r=(∏ j,r.2 j) ∧
        ((pairedProduct r).primeFactorsList.length:ℝ) ≤ I ∧
        ∀ p ∈ (pairedProduct r).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
      intro r hr
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hr
      exact hQ f hf
    simpa only [pairedProduct,Nat.cast_prod] using halloc k U V I hk hU hquad hUV hI R hR
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

end TotientAsymptotic

end

end OAI
