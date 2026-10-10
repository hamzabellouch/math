import OAI.NumberTheory.TotientAsymptotic.FordBandWitness
import OAI.NumberTheory.TotientAsymptotic.CollisionBandMass

namespace OAI

/-! The one-band sieve bound for actual Ford tuples with a fixed lower state. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem ford_band_fiber_mass : ∃ C D₀ : ℝ,0 < C ∧ 0 < D₀ ∧
    ∀ (b k D r : ℕ) (hk : k ≤ b) (i : Fin k),i.val+1=k →
    ∀ (y S : ℝ) (Y U : ℕ → ℝ),Real.exp 2 ≤ y → 1 ≤ B y →
    FordComparisonParameters b y S D r Y U →
    2 ≤ Y k → 1 < U (k-1) → D₀ ≤ Real.sqrt (B S*B y) →
    ∀ T : Finset (ShiftedPair b),
    (∀ t ∈ T,FordComparisonConditions b y S D r Y U t) →
    ∀ s ∈ T.image (fun t => fordFactorState t (Y k)),
    (∑ f ∈ (T.filter (fun t => fordFactorState t (Y k)=s)).image (fun t => fordBand hk t Y),
      (pairedProduct f:ℝ)⁻¹) ≤
    (C*(k:ℝ)^2*(B y)^2/(Real.log (U (k-1)))^2)*
      Real.exp (fordBandCap k y S Y*(Real.log k+1)) := by
  classical
  obtain ⟨C,D₀,hC,hD₀,hbound⟩ := collision_band_mass_bound
  refine ⟨C,D₀,hC,hD₀,?_⟩
  intro b k D r hk i hi y S Y U hy hBy hp hYk hUi hD T hT s hs
  let j := Fin.castLE hk i
  obtain ⟨t₀,ht₀,he₀⟩ := Finset.mem_image.mp hs
  have ha : 0 < s.left j := by
    have he := congrArg (fun z : ShiftedPair b => z.left j) he₀
    rw [← he]
    exact partBelow_pos _ _
  have hb : 0 < s.right j := by
    have he := congrArg (fun z : ShiftedPair b => z.right j) he₀
    rw [← he]
    exact partBelow_pos _ _
  have hgap := hp.2.2.2.2.1 (k-1) (Finset.mem_range.mpr (by have := i.isLt; omega : k-1 < b))
  have hkm : k-1+1=k := by have := i.isLt; omega
  rw [hkm] at hgap
  have hcap : (k:ℝ)*(B (Y (k-1))-B (Y k)+D₀) ≤ fordBandCap k y S Y := by
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hD) (Nat.cast_nonneg k)
  apply hbound k (s.left j) (s.right j) i y (U (k-1)) (Y k) (Y (k-1))
    (fordBandCap k y S Y) ha hb hy hBy hUi (by have := i.isLt; omega) hYk
    (hgap.1.trans hgap.2).le hcap
  intro f hf
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
  have hl := congrArg (fun z : ShiftedPair b => z.left j) he
  have hr := congrArg (fun z : ShiftedPair b => z.right j) he
  change partBelow (t.left j-1) (Y k)=s.left j at hl
  change partBelow (t.right j-1) (Y k)=s.right j at hr
  have hw := ford_band_conditions hk i hi ((Real.exp_pos 2).le.trans hy) hp (hT t ht)
  change CollisionBandConditions (partBelow (t.left j-1) (Y k))
    (partBelow (t.right j-1) (Y k)) i y (U (k-1)) (Y k) (Y (k-1))
    (fordBandCap k y S Y) (fordBand hk t Y) at hw
  rwa [hl,hr] at hw

end TotientAsymptotic

end

end OAI
