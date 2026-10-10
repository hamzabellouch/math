import OAI.NumberTheory.TotientAsymptotic.HeadLimitedFamily
import OAI.NumberTheory.TotientAsymptotic.GeometricPrimeRegion

namespace OAI

/-! Positive prime mass with the leading tail separated from the new head. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def headLimitedPrimeGrid (x c : ℝ) (n : ℕ) : Finset (Fin n → ℕ) :=
  gridOuter (prefixBoxGrid n (B x/(1+rowContractionError (m x))))
    (headLimitedFamily (m x) n (B x) c)

lemma headLimitedPrimeGrid_subset {x c : ℝ} {n : ℕ} :
    headLimitedPrimeGrid x c n ⊆ geometricPrimeGrid x c n := by
  intro b hb
  obtain ⟨hb,u,hu,hs⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hb,u,hu,hs.1⟩

theorem head_limited_prime_mass_lower : ∃ c : ℝ,0 < c ∧
    ∀ᶠ H : ℕ in atTop,∃ δ : ℝ,0 < δ ∧ ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x →
        δ*G x (m x) ≤ gridPrimeMass (headLimitedPrimeGrid x c (N+2)) := by
  obtain ⟨c,δ,hc,hδ,hvolume⟩ := head_limited_volume_lower
  obtain ⟨c₀,hc₀,hprime⟩ := positive_prefix_grid_mass
  refine ⟨c,hc,?_⟩
  filter_upwards [geometric_dominates_polynomial hc c₀ 1,eventually_ge_atTop 1]
    with H hH hH1
  obtain ⟨d,hd,hprefix⟩ := fixed_prefix_volume_lower H
  refine ⟨δ*d/2,by positivity,?_⟩
  filter_upwards [hvolume H hH1,hprefix] with x hx hp
  intro N hN
  have hn : N+2 ≤ m x := by omega
  have he : m x-H=N+2 := by omega
  rw [he] at hp
  let S := headLimitedFamily (m x) (N+2) (B x) c
  have hS : S ⊆ prefixRegion (N+2) (B x/(1+rowContractionError (m x))) 0 0 := by
    intro u hu
    exact contractedPrefix_subset_prefixRegion
      (fun i => by linarith only [rowContractionError_nonneg (m x-(i.val+1))]) hu.1.1
  have hlinear (u) (hu : u ∈ S) (i : Fin (N+2)) : c₀*(N+2-i.val:ℕ) ≤ u i := by
    have hdist : H ≤ m x-i.val := by have := i.isLt; omega
    have hdim : ((N+2-i.val:ℕ):ℝ) ≤ (m x-i.val:ℕ) := by
      exact_mod_cast Nat.sub_le_sub_right hn i.val
    calc
      _ ≤ c₀*(m x-i.val:ℕ) := mul_le_mul_of_nonneg_left hdim hc₀.le
      _ ≤ c*(rho^(m x-i.val))⁻¹ := by simpa only [pow_one] using hH _ hdist
      _ ≤ u i := hu.1.2.1 i
  have hmass := hprime (B x/(1+rowContractionError (m x))) S hS hlinear
  have hvol := hx N hN
  have hh := div_le_div_of_nonneg_right hvol (by norm_num : (0:ℝ) ≤ 2)
  calc
    _ = (δ*(d*G x (m x)))/2 := by ring
    _ ≤ (δ*G x (N+2))/2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hδ.le) (by norm_num)
    _ ≤ volume.real S/2 := hh
    _ ≤ _ := hmass

lemma head_limited_prime_coordinates {c : ℝ} (hc : 0 < c) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ p ∈ gridPrimeTuples (headLimitedPrimeGrid x c n),
        (∀ i,(p i).Prime) ∧
        primePrefixCoord p ∈ relaxedGeometricFamily (m x) n (B x) (c/2) ∧
        ∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x := by
  filter_upwards [geometric_grid_coordinates hc] with H hH
  filter_upwards [hH,B_tendsto.eventually (eventually_ge_atTop (100:ℝ))] with x hx hB
  intro n hn p hp
  obtain ⟨b,hb,hpb⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hp,hcell⟩ := mem_primeBoxTuples_iff.mp hpb
  refine ⟨hp,hx n hn b (headLimitedPrimeGrid_subset hb) _ hcell,?_⟩
  obtain ⟨_,u,hu,hfamily⟩ := Finset.mem_filter.mp hb
  have hdist := unitGridCell_coordinate_distance hu hcell
  intro i
  have hi := (neg_le_abs _).trans (hdist i)
  have hu := hfamily.2 i
  nlinarith only [hi,hu,hB]

end TotientAsymptotic

end

end OAI
