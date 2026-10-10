import OAI.NumberTheory.TotientAsymptotic.LocalCoordinateBounds
import OAI.NumberTheory.TotientAsymptotic.HeadLimitedPrimeMass

namespace OAI

/-! Positive prime mass with geometric upper bounds at every local index. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localPrimeGrid (x c : ℝ) (L n : ℕ) : Finset (Fin n → ℕ) :=
  gridOuter (prefixBoxGrid n (B x/(1+rowContractionError (m x))))
    (locallyConcentratedFamily (m x) n (B x) c L)

lemma localPrimeGrid_subset {x c : ℝ} {L n : ℕ} :
    localPrimeGrid x c L n ⊆ headLimitedPrimeGrid x c n := by
  intro b hb
  obtain ⟨hb,u,hu,hs⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hb,u,hu,hs.1⟩

theorem local_prime_mass_lower : ∃ c : ℝ,∃ L : ℕ,0 < c ∧ 1 ≤ L ∧
    ∀ᶠ H : ℕ in atTop,∃ δ : ℝ,0 < δ ∧ ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x →
        δ*G x (m x) ≤ gridPrimeMass (localPrimeGrid x c L (N+2)) := by
  obtain ⟨c,δ,L,hc,hδ,hL,hvolume⟩ := locally_concentrated_volume_lower
  obtain ⟨c₀,hc₀,hprime⟩ := positive_prefix_grid_mass
  refine ⟨c,L,hc,hL,?_⟩
  filter_upwards [geometric_dominates_polynomial hc c₀ 1,eventually_ge_atTop 1]
    with H hH hH1
  obtain ⟨d,hd,hprefix⟩ := fixed_prefix_volume_lower H
  refine ⟨δ*d/2,by positivity,?_⟩
  filter_upwards [hvolume H hH1,hprefix] with x hx hp
  intro N hN
  have hn : N+2 ≤ m x := by omega
  have he : m x-H=N+2 := by omega
  rw [he] at hp
  let S := locallyConcentratedFamily (m x) (N+2) (B x) c L
  have hS : S ⊆ prefixRegion (N+2) (B x/(1+rowContractionError (m x))) 0 0 := by
    intro u hu
    exact contractedPrefix_subset_prefixRegion
      (fun i => by linarith only [rowContractionError_nonneg (m x-(i.val+1))]) hu.1.1.1
  have hlinear (u) (hu : u ∈ S) (i : Fin (N+2)) : c₀*(N+2-i.val:ℕ) ≤ u i := by
    have hdist : H ≤ m x-i.val := by have := i.isLt; omega
    have hdim : ((N+2-i.val:ℕ):ℝ) ≤ (m x-i.val:ℕ) := by
      exact_mod_cast Nat.sub_le_sub_right hn i.val
    calc
      _ ≤ c₀*(m x-i.val:ℕ) := mul_le_mul_of_nonneg_left hdim hc₀.le
      _ ≤ c*(rho^(m x-i.val))⁻¹ := by simpa only [pow_one] using hH _ hdist
      _ ≤ u i := hu.1.1.2.1 i
  have hmass := hprime (B x/(1+rowContractionError (m x))) S hS hlinear
  have hvol := hx N hN
  calc
    _ = (δ*(d*G x (m x)))/2 := by ring
    _ ≤ (δ*G x (N+2))/2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hδ.le) (by norm_num)
    _ ≤ volume.real S/2 := div_le_div_of_nonneg_right hvol (by norm_num)
    _ ≤ _ := hmass

theorem local_prime_mass_lower_base : ∃ c δ : ℝ,∃ L : ℕ,
    0 < c ∧ 0 < δ ∧ 1 ≤ L ∧
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x →
        δ*G x (N+2) ≤ gridPrimeMass (localPrimeGrid x c L (N+2)) := by
  obtain ⟨c,δ,L,hc,hδ,hL,hvolume⟩ := locally_concentrated_volume_lower
  obtain ⟨c₀,hc₀,hprime⟩ := positive_prefix_grid_mass
  refine ⟨c,δ/2,L,hc,half_pos hδ,hL,?_⟩
  filter_upwards [geometric_dominates_polynomial hc c₀ 1,eventually_ge_atTop 1]
    with H hH hH1
  filter_upwards [hvolume H hH1] with x hx
  intro N hN
  have hn : N+2 ≤ m x := by omega
  let S := locallyConcentratedFamily (m x) (N+2) (B x) c L
  have hS : S ⊆ prefixRegion (N+2) (B x/(1+rowContractionError (m x))) 0 0 := by
    intro u hu
    exact contractedPrefix_subset_prefixRegion
      (fun i => by linarith only [rowContractionError_nonneg (m x-(i.val+1))]) hu.1.1.1
  have hlinear (u) (hu : u ∈ S) (i : Fin (N+2)) : c₀*(N+2-i.val:ℕ) ≤ u i := by
    have hdist : H ≤ m x-i.val := by have := i.isLt; omega
    have hdim : ((N+2-i.val:ℕ):ℝ) ≤ (m x-i.val:ℕ) := by
      exact_mod_cast Nat.sub_le_sub_right hn i.val
    calc
      _ ≤ c₀*(m x-i.val:ℕ) := mul_le_mul_of_nonneg_left hdim hc₀.le
      _ ≤ c*(rho^(m x-i.val))⁻¹ := by simpa only [pow_one] using hH _ hdist
      _ ≤ u i := hu.1.1.2.1 i
  have hmass := hprime (B x/(1+rowContractionError (m x))) S hS hlinear
  calc
    _ = (δ*G x (N+2))/2 := by ring
    _ ≤ volume.real S/2 := div_le_div_of_nonneg_right (hx N hN) (by norm_num)
    _ ≤ _ := hmass

theorem local_prime_coordinates {c : ℝ} (hc : 0 < c) :
    ∃ A : ℝ,0 < A ∧ ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ p ∈ gridPrimeTuples (localPrimeGrid x c L n),
        (∀ i,(p i).Prime) ∧
        primePrefixCoord p ∈ relaxedGeometricFamily (m x) n (B x) (c/2) ∧
        (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) ∧
        ∀ i,primePrefixCoord p i ≤
          A*(m x-i.val+L+2:ℕ)*(rho^(m x-i.val+L+2))⁻¹+1 := by
  obtain ⟨A,hA,hupper⟩ := local_candidate_coordinate_envelope
  refine ⟨A,hA,?_⟩
  intro L
  filter_upwards [head_limited_prime_coordinates hc] with H hH
  filter_upwards [hH,hupper H L] with x hx hu
  intro n hn p hp
  have hpn : p ∈ gridPrimeTuples (headLimitedPrimeGrid x c n) := by
    obtain ⟨b,hb,hpb⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨b,localPrimeGrid_subset hb,hpb⟩
  obtain ⟨hpr,hr,hcap⟩ := hx n hn p hpn
  refine ⟨hpr,hr,hcap,?_⟩
  obtain ⟨b,hb,hpb⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨_,u,hucell,hfamily⟩ := Finset.mem_filter.mp hb
  have hpcell := (mem_primeBoxTuples_iff.mp hpb).2
  have hdist := unitGridCell_coordinate_distance hucell hpcell
  have hdim : n=m x-H := by omega
  subst n
  intro i
  have hupp := hu c u hfamily i
  have hclose := (neg_le_abs _).trans (hdist i)
  linarith only [hupp,hclose]

end TotientAsymptotic

end

end OAI
