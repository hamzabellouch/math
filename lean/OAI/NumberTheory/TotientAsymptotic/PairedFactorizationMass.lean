import OAI.NumberTheory.TotientAsymptotic.OrderedFactorizations
import OAI.NumberTheory.TotientAsymptotic.RoughPrimeMass

namespace OAI

/-! Weighted counts of actual ordered left and right interval factorizations. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma paired_factorization_mass_le (k : ℕ)
    (Q : Finset ((Fin k → ℕ) × (Fin k → ℕ)))
    (hQ : ∀ f ∈ Q,0 < (∏ j,f.1 j) ∧ (∏ j,f.1 j)=(∏ j,f.2 j)) :
    (∑ f ∈ Q,((∏ j,f.1 j):ℝ)⁻¹) ≤
      ∑ n ∈ Q.image (fun f => ∏ j,f.1 j),(k:ℝ)^(2*n.primeFactorsList.length)/(n:ℝ) := by
  classical
  let F := fun f : (Fin k → ℕ) × (Fin k → ℕ) => ∏ j,f.1 j
  rw [← Finset.sum_fiberwise_of_maps_to (fun f hf => Finset.mem_image.mpr ⟨f,hf,rfl⟩ :
    ∀ f ∈ Q,F f ∈ Q.image F)]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
  have hn0 := (hQ f hf).1
  let T := Q.filter (fun g => F g=F f)
  have hc := paired_factorizations_card_le k (F f) hn0 T (by
    intro g hg
    obtain ⟨hg,he⟩ := Finset.mem_filter.mp hg
    exact ⟨he,by rw [← (hQ g hg).2]; exact he⟩)
  have hcr : (T.card:ℝ) ≤ (k:ℝ)^(2*(F f).primeFactorsList.length) := by exact_mod_cast hc
  have he : (∑ g ∈ T,((F g):ℝ)⁻¹)=(T.card:ℝ)/(F f:ℝ) := by
    calc
      _ = ∑ _g ∈ T,(F f:ℝ)⁻¹ := Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.mp hg).2])
      _ = _ := by simp [div_eq_mul_inv]
  calc
    _ = (T.card:ℝ)/(F f:ℝ) := by simpa only [T,F,Nat.cast_prod] using he
    _ ≤ _ := div_le_div_of_nonneg_right hcr (Nat.cast_nonneg _)

/-- After fixing the extracted large prime(s), the remaining two allocations
have the bound used at each step of Ford's iteration. -/
theorem paired_interval_allocation_bound : ∃ U₀ : ℝ,2 ≤ U₀ ∧
    ∀ (k : ℕ) (U V I : ℝ),1 ≤ k → U₀ ≤ U → 4*(k:ℝ)^2 ≤ U → U ≤ V →
    (k:ℝ)*(B V-B U+1) ≤ I →
    ∀ Q : Finset ((Fin k → ℕ) × (Fin k → ℕ)),
    (∀ f ∈ Q,0 < (∏ j,f.1 j) ∧ (∏ j,f.1 j)=(∏ j,f.2 j) ∧
      (((∏ j,f.1 j).primeFactorsList.length):ℝ) ≤ I ∧
      ∀ p ∈ (∏ j,f.1 j).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) →
    (∑ f ∈ Q,((∏ j,f.1 j):ℝ)⁻¹) ≤ Real.exp (I*(Real.log k+1)+1) := by
  obtain ⟨U₀,hU₀,hbound⟩ := rough_interval_allocation_bound
  refine ⟨U₀,hU₀,?_⟩
  intro k U V I hk hU hquad hUV hI Q hQ
  apply (paired_factorization_mass_le k Q (fun f hf => ⟨(hQ f hf).1,(hQ f hf).2.1⟩)).trans
  apply hbound (k:ℝ) U V I (by exact_mod_cast hk) hU hquad hUV hI
  intro n hn
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hn
  exact ⟨(hQ f hf).1,(hQ f hf).2.2⟩

end TotientAsymptotic

end

end OAI
