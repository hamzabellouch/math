import OAI.MeasureTheory.Falconer.Recursion.MinimalDescriptorLength
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks

namespace OAI

namespace PlanarFalconer

theorem prefix_policy_geometry (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (htN : t ≤ N) (hw : a+100*q < t)
    (hpref : 2*policyDepth A N q a t ≤ a+t) :
    let p := policyDepth A N q a t
    a < p ∧ p ≤ t ∧ q ≤ p-a ∧ 2*(p-a) ≤ t-a ∧
      PolicyDescriptor.parallel a p ∈ policyDescriptorList A N q a t := by
  classical
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq htN hw)
  dsimp only
  refine ⟨by omega,by omega,by omega,by omega,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,t),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      le_rfl,le_rfl,hw⟩
  · change PolicyDescriptor.parallel a (policyDepth A N q a t) ∈ originDescriptors A N q a t
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨a,Finset.mem_Ico.mpr ⟨?_,by omega⟩,rfl⟩
    have he : min (policyDepth A N q a t-a) (t-policyDepth A N q a t) =
        policyDepth A N q a t-a := min_eq_left (by omega)
    rw [he]
    omega

theorem source_policy_block_lower (N : ℕ) (kap : ℝ) :
    kap*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) := Nat.le_ceil _

theorem prefix_policy_scales (A : ℕ → ℝ) {N q a t : ℕ}
    {sig kap v : ℝ} (hsig : 0 < sig) (hgap : 10*sig < kap)
    (hq : 0 < q) (hblock : kap*(N:ℝ) ≤ (q:ℝ))
    (htN : t ≤ N) (hw : a+100*q < t)
    (hpref : 2*policyDepth A N q a t ≤ a+t)
    (hv : (t:ℝ)-sig*N ≤ v) (hvt : v ≤ t) :
    let p := policyDepth A N q a t
    let n := p-a
    a+n = p ∧ a+n ≤ N ∧ kap*N ≤ (n:ℝ) ∧
      10*sig*N ≤ v-(a+n) ∧ (n:ℝ) ≤ v-(a+n)+2*sig*N ∧
      ((t-a)/2:ℕ) ≤ v-(a+n)+2*sig*N ∧ v-a ≤ N := by
  have hg := prefix_policy_geometry A hq htN hw hpref
  let p := policyDepth A N q a t
  have hap : a ≤ p := hg.1.le
  have he : a+(p-a) = p := Nat.add_sub_of_le hap
  have hn : ((p-a:ℕ):ℝ) = (p:ℝ)-a := Nat.cast_sub hap
  have hpR : 2*(p:ℝ) ≤ (a:ℝ)+t := by exact_mod_cast hpref
  have hwR : (a:ℝ)+100*(q:ℝ) < (t:ℝ) := by exact_mod_cast hw
  have hqR : (q:ℝ) ≤ ((p-a:ℕ):ℝ) := by exact_mod_cast hg.2.2.1
  have htR : (t:ℝ) ≤ N := by exact_mod_cast htN
  have hsigN : 0 ≤ sig*(N:ℝ) := mul_nonneg hsig.le (Nat.cast_nonneg _)
  have hgapN : 10*sig*(N:ℝ) ≤ kap*N :=
    mul_le_mul_of_nonneg_right hgap.le (Nat.cast_nonneg _)
  have hhalf : 2*(((t-a)/2:ℕ):ℝ) ≤ (t:ℝ)-(a:ℝ) := by
    have hh : a+2*((t-a)/2) ≤ t := by omega
    have hhR : (a:ℝ)+2*(((t-a)/2:ℕ):ℝ) ≤ t := by exact_mod_cast hh
    linarith
  dsimp only
  refine ⟨he,by omega,hblock.trans hqR,?_,?_,?_,?_⟩
  · change 10*sig*N ≤ v-((a:ℝ)+((p-a:ℕ):ℝ))
    rw [hn]
    nlinarith
  · change ((p-a:ℕ):ℝ) ≤ v-((a:ℝ)+((p-a:ℕ):ℝ))+2*sig*N
    rw [hn]
    linarith
  · change (((t-a)/2:ℕ):ℝ) ≤ v-((a:ℝ)+((p-a:ℕ):ℝ))+2*sig*N
    rw [hn]
    linarith
  · linarith [show (0:ℝ) ≤ (a:ℝ) from Nat.cast_nonneg a]

end PlanarFalconer

end OAI
