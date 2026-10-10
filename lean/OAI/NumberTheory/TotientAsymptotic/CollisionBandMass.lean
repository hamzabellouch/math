import OAI.NumberTheory.TotientAsymptotic.CollisionBandData

namespace OAI

/-! The complete one-band reciprocal collision estimate. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem collision_band_mass_bound : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (k a b : ℕ) (i : Fin k) (y T U V I : ℝ),0 < a → 0 < b →
    Real.exp 2 ≤ y → 1 ≤ B y → 1 < T → 1 ≤ k → 2 ≤ U → U ≤ V →
    (k:ℝ)*(B V-B U+D) ≤ I → ∀ Q : Finset (PairedFactors k),
    (∀ f ∈ Q,CollisionBandConditions a b i y T U V I f) →
    (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤
      (C*(k:ℝ)^2*(B y)^2/(Real.log T)^2)*Real.exp (I*(Real.log k+1)) := by
  classical
  obtain ⟨C₀,D₀,hC₀,hD₀,hcommon⟩ := common_largest_prime_squarefree_mass_bound
  obtain ⟨C₁,D₁,hC₁,hD₁,hdistinct⟩ := distinct_largest_prime_mass_bound
  refine ⟨C₀+2*C₁,max D₀ D₁,by positivity,lt_max_of_lt_left hD₀,?_⟩
  intro k a b i y T U V I ha hb hy hBy hT hk hU hUV hI Q hQ
  let Q₀ := Q.filter (fun f => largestPrimeFactor (f.1 i)=largestPrimeFactor (f.2 i))
  let Q₁ := Q.filter (fun f => largestPrimeFactor (f.2 i)<largestPrimeFactor (f.1 i))
  let Q₂ := Q.filter (fun f => largestPrimeFactor (f.1 i)<largestPrimeFactor (f.2 i))
  let M := (B y)^2/(Real.log T)^2*Real.exp (I*(Real.log k+1))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hI₀ : (k:ℝ)*(B V-B U+D₀) ≤ I :=
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (le_max_left D₀ D₁)) hk0).trans hI
  have hI₁ : (k:ℝ)*(B V-B U+D₁) ≤ I :=
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (le_max_right D₀ D₁)) hk0).trans hI
  have h₀ : (∑ f ∈ Q₀,(pairedProduct f:ℝ)⁻¹) ≤ C₀*M := by
    have hh := hcommon k a b i y T U V I ha hb hy hBy hT hk hU hUV hI₀ Q₀
      (fun f hf => (hQ f (Finset.mem_filter.mp hf).1).common (Finset.mem_filter.mp hf).2)
      (fun f hf => (hQ f (Finset.mem_filter.mp hf).1).squarefree)
    convert hh using 1; dsimp [M]; ring
  have h₁ : (∑ f ∈ Q₁,(pairedProduct f:ℝ)⁻¹) ≤ (k:ℝ)^2*C₁*M := by
    have hh := hdistinct k a b i y T U V I ha hb hy hT hk hU hUV hI₁ Q₁
      (fun f hf => (hQ f (Finset.mem_filter.mp hf).1).distinct (Finset.mem_filter.mp hf).2)
      (fun f hf => (hQ f (Finset.mem_filter.mp hf).1).squarefree)
    convert hh using 1; dsimp [M]; ring
  have h₂ : (∑ f ∈ Q₂,(pairedProduct f:ℝ)⁻¹) ≤ (k:ℝ)^2*C₁*M := by
    rw [← collision_swap_sum Q₂ (fun f hf => (hQ f (Finset.mem_filter.mp hf).1).product_eq)]
    have hh := hdistinct k b a i y T U V I hb ha hy hT hk hU hUV hI₁
      (Q₂.image Prod.swap) (by
        intro f hf
        obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
        exact (hQ g (Finset.mem_filter.mp hg).1).swap.distinct (Finset.mem_filter.mp hg).2)
      (by
        intro f hf
        obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
        exact (hQ g (Finset.mem_filter.mp hg).1).swap.squarefree)
    convert hh using 1; dsimp [M]; ring
  have he : (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹)=
      (∑ f ∈ Q₀,(pairedProduct f:ℝ)⁻¹)+(∑ f ∈ Q₁,(pairedProduct f:ℝ)⁻¹)+
        (∑ f ∈ Q₂,(pairedProduct f:ℝ)⁻¹) := by
    simp only [Q₀,Q₁,Q₂,Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro f hf
    rcases lt_trichotomy (largestPrimeFactor (f.1 i)) (largestPrimeFactor (f.2 i)) with h|h|h
    · simp [h,ne_of_lt h,not_lt_of_gt h]
    · simp [h]
    · simp [h,(ne_of_lt h).symm,not_lt_of_gt h]
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1:ℝ) ≤ (k:ℝ)^2 := by nlinarith
  calc
    _ = (∑ f ∈ Q₀,(pairedProduct f:ℝ)⁻¹)+(∑ f ∈ Q₁,(pairedProduct f:ℝ)⁻¹)+
        (∑ f ∈ Q₂,(pairedProduct f:ℝ)⁻¹) := he
    _ ≤ C₀*M+(k:ℝ)^2*C₁*M+(k:ℝ)^2*C₁*M := add_le_add (add_le_add h₀ h₁) h₂
    _ ≤ (C₀+2*C₁)*(k:ℝ)^2*M := by nlinarith [mul_nonneg hC₀.le hM]
    _ = _ := by dsimp [M]; ring

end TotientAsymptotic

end

end OAI
