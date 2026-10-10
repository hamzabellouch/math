import OAI.NumberTheory.TotientAsymptotic.DistinctLargestWitness

namespace OAI

/-! The unequal-largest-prime branch, including the finite choice of cross slots. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem distinct_largest_fixed_slots_mass_bound : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (k a b : ℕ) (i j l : Fin k) (y T U V I : ℝ),0 < a → 0 < b →
    Real.exp 2 ≤ y → 1 < T → 1 ≤ k → 2 ≤ U → U ≤ V →
    (k:ℝ)*(B V-B U+D) ≤ I → ∀ Q : Finset (PairedFactors k),
    (∀ f ∈ Q,DistinctLargestConditions a b i y T U V I f) →
    (∀ f ∈ Q,CrossRemoval i j l f) →
    (∀ f ∈ Q,Squarefree (pairedProduct f)) →
    (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤
      (C*(B y)^2/(Real.log T)^2)*Real.exp (I*(Real.log k+1)) := by
  classical
  obtain ⟨C,D,hC,hD,hbound⟩ := distinct_prime_squarefree_mass_bound
  refine ⟨C,D,hC,hD,?_⟩
  intro k a b i j l y T U V I ha hb hy hT hk hU hUV hI Q hQ hs hsq
  let E := Q.image (distinctLargestEncoding i j l)
  have hE : ∀ e ∈ E,DistinctPrimeWitness a b i j y T e := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact distinctLargest_witness ha hb (hQ f hf) (hs f hf)
  have hres : ∀ e ∈ E,0 < pairedProduct e.1 ∧ pairedProduct e.1=(∏ t,e.1.2 t) ∧
      ((pairedProduct e.1).primeFactorsList.length:ℝ) ≤ I ∧
      ∀ p ∈ (pairedProduct e.1).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact distinctLargest_residual (hQ f hf) (hs f hf)
  have hsqE : ∀ e ∈ E,Squarefree (pairedProduct e.1) := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact distinctLargest_residual_squarefree (hQ f hf) (hs f hf) (hsq f hf)
  have hi : ∀ f ∈ Q,∀ g ∈ Q,distinctLargestEncoding i j l f=distinctLargestEncoding i j l g → f=g := by
    intro f hf g hg he
    have hh := congrArg (distinctPrimeDecode i j l) he
    rwa [distinctLargest_decode (hQ f hf) (hs f hf),
      distinctLargest_decode (hQ g hg) (hs g hg)] at hh
  have hsum : (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹)=∑ e ∈ E,twoPrimeWeight e := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro f hf
    unfold twoPrimeWeight
    rw [distinctLargest_product (hQ f hf) (hs f hf)]
  rw [hsum]
  exact hbound k a b i j y T U V I hy hT hk hU hUV hI E hE hsqE hres

/-- Summing over the two recorded cross slots costs at most `k^2`. -/
theorem distinct_largest_prime_mass_bound : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (k a b : ℕ) (i : Fin k) (y T U V I : ℝ),0 < a → 0 < b →
    Real.exp 2 ≤ y → 1 < T → 1 ≤ k → 2 ≤ U → U ≤ V →
    (k:ℝ)*(B V-B U+D) ≤ I → ∀ Q : Finset (PairedFactors k),
    (∀ f ∈ Q,DistinctLargestConditions a b i y T U V I f) →
    (∀ f ∈ Q,Squarefree (pairedProduct f)) →
    (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤
      (k:ℝ)^2*(C*(B y)^2/(Real.log T)^2)*Real.exp (I*(Real.log k+1)) := by
  classical
  obtain ⟨C,D,hC,hD,hbound⟩ := distinct_largest_fixed_slots_mass_bound
  refine ⟨C,D,hC,hD,?_⟩
  intro k a b i y T U V I ha hb hy hT hk hU hUV hI Q hQ hsq
  let M := (C*(B y)^2/(Real.log T)^2)*Real.exp (I*(Real.log k+1))
  have hcover : (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤
      ∑ j : Fin k,∑ l : Fin k,∑ f ∈ Q.filter (CrossRemoval i j l),(pairedProduct f:ℝ)⁻¹ := by
    calc
      _ ≤ ∑ f ∈ Q,∑ j : Fin k,∑ l : Fin k,
          if CrossRemoval i j l f then (pairedProduct f:ℝ)⁻¹ else 0 := by
        apply Finset.sum_le_sum
        intro f hf
        obtain ⟨j,l,hjl⟩ := distinctLargest_slots (hQ f hf)
        have hl := Finset.single_le_sum (s:=Finset.univ)
          (f:=fun l' => if CrossRemoval i j l' f then (pairedProduct f:ℝ)⁻¹ else 0)
          (fun _ _ => by positivity) (Finset.mem_univ l)
        have hj := Finset.single_le_sum (s:=Finset.univ)
          (f:=fun j' => ∑ l' : Fin k,if CrossRemoval i j' l' f then (pairedProduct f:ℝ)⁻¹ else 0)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (Finset.mem_univ j)
        have hl' : (pairedProduct f:ℝ)⁻¹ ≤
            ∑ l' : Fin k,if CrossRemoval i j l' f then (pairedProduct f:ℝ)⁻¹ else 0 := by
          simpa only [hjl,ite_true] using hl
        exact hl'.trans hj
      _ = ∑ j : Fin k,∑ l : Fin k,∑ f ∈ Q,
          if CrossRemoval i j l f then (pairedProduct f:ℝ)⁻¹ else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
      _ = _ := by simp only [Finset.sum_filter]
  have hfixed (j l : Fin k) :
      (∑ f ∈ Q.filter (CrossRemoval i j l),(pairedProduct f:ℝ)⁻¹) ≤ M := by
    apply hbound k a b i j l y T U V I ha hb hy hT hk hU hUV hI
    · exact fun f hf => hQ f (Finset.mem_filter.mp hf).1
    · exact fun f hf => (Finset.mem_filter.mp hf).2
    · exact fun f hf => hsq f (Finset.mem_filter.mp hf).1
  calc
    _ ≤ ∑ j : Fin k,∑ l : Fin k,∑ f ∈ Q.filter (CrossRemoval i j l),(pairedProduct f:ℝ)⁻¹ := hcover
    _ ≤ ∑ _j : Fin k,∑ _l : Fin k,M :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ => hfixed j l))
    _ = _ := by simp [M,pow_two]; ring

end TotientAsymptotic

end

end OAI
