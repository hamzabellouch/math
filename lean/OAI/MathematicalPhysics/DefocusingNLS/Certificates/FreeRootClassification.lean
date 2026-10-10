import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeSymmetryZeros
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeOutgoingNonvanishing

namespace OAI

/-! The counted free zeros are exactly the three symmetry values. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

theorem free_spectral_zero_card_bound (hR : RectangleRouche) (ell : ℕ) (b Z : ℝ)
    (hD : (b,Z)∈freeMatchingDisk)
    (S : Finset {z : ℂ | -(1/32 : ℝ)≤z.re})
    (hz : ∀ z ∈ S, spectralSlowDeterminant ell b Z z.val=0) :
    (S.card : ℕ∞)≤(freeOutgoingCount ell : ℕ∞) := by
  classical
  let f := fun z : {z : ℂ | -(1/32 : ℝ)≤z.re} =>
    analyticOrderAt (spectralSlowDeterminant ell b Z) z.val
  have hs : Summable f := ⟨_,hasSum_of_isLUB _ (isLUB_sSup (Set.range
    (fun s : Finset {z : ℂ | -(1/32 : ℝ)≤z.re} => ∑ z ∈ s, f z)))⟩
  have hZ : Z≠0 := by
    have hh := (abs_le.mp (freeMatchingDisk_subset_certificate_box hD).2).1
    intro he
    norm_num [he] at hh
  calc
    (S.card : ℕ∞) = ∑ _z ∈ S, (1 : ℕ∞) := by simp
    _ ≤ ∑ z ∈ S, f z := by
      apply Finset.sum_le_sum
      intro z hzs
      apply Order.one_le_iff_ne_zero.mpr
      exact (analyticAt_spectralSlowDeterminant ell b Z z hZ z.property).analyticOrderAt_ne_zero.mpr
        (hz z hzs)
    _ ≤ ∑' z, f z := hs.sum_le_tsum S (fun _ _ => zero_le)
    _ = (freeOutgoingCount ell : ℕ∞) := free_outgoing_count hR ell b Z hD

theorem radialFree_phase_scaling_zeros (hR : RectangleRouche) (w : RadialShootingDisk)
    (hw : diskProfile w=0) (lam : ℂ) (hhalf : -(1/32 : ℝ)≤lam.re) :
    spectralSlowDeterminant 0 (radialShootingB w) ((radialShootingR w)^2/4) lam=0 ↔
      lam=0 ∨ lam=1 := by
  classical
  obtain ⟨h0,_ht,h1⟩ := radialFree_spectral_symmetry_zeros w hw
  constructor
  · intro hz
    by_contra h
    push Not at h
    let a : {z : ℂ | -(1/32 : ℝ)≤z.re} := ⟨0,by norm_num⟩
    let b : {z : ℂ | -(1/32 : ℝ)≤z.re} := ⟨1,by norm_num⟩
    let c : {z : ℂ | -(1/32 : ℝ)≤z.re} := ⟨lam,hhalf⟩
    have hc := free_spectral_zero_card_bound hR 0 _ _ (radialShooting_freeMatchingDisk w)
      {a,b,c} (by
        intro z hzS
        simp only [Finset.mem_insert,Finset.mem_singleton] at hzS
        rcases hzS with rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact hz)
    have hab : a≠b := by intro he; have := congrArg Subtype.val he; norm_num [a,b] at this
    have hac : a≠c := by intro he; exact h.1 (congrArg Subtype.val he).symm
    have hbc : b≠c := by intro he; exact h.2 (congrArg Subtype.val he).symm
    norm_num [Finset.card_insert_of_notMem,hab,hac,hbc,freeOutgoingCount] at hc
  · rintro (rfl | rfl)
    · exact h0
    · exact h1

theorem radialFree_translation_zero (hR : RectangleRouche) (w : RadialShootingDisk)
    (hw : diskProfile w=0) (lam : ℂ) (hhalf : -(1/32 : ℝ)≤lam.re) :
    spectralSlowDeterminant 1 (radialShootingB w) ((radialShootingR w)^2/4) lam=0 ↔
      lam=1/2 := by
  classical
  have ht := (radialFree_spectral_symmetry_zeros w hw).2.1
  constructor
  · intro hz
    by_contra h
    let a : {z : ℂ | -(1/32 : ℝ)≤z.re} := ⟨1/2,by norm_num⟩
    let b : {z : ℂ | -(1/32 : ℝ)≤z.re} := ⟨lam,hhalf⟩
    have hc := free_spectral_zero_card_bound hR 1 _ _ (radialShooting_freeMatchingDisk w)
      {a,b} (by
        intro z hzS
        simp only [Finset.mem_insert,Finset.mem_singleton] at hzS
        rcases hzS with rfl | rfl
        · exact ht
        · exact hz)
    have hab : a≠b := by intro he; exact h (congrArg Subtype.val he).symm
    norm_num [Finset.card_insert_of_notMem,hab,freeOutgoingCount] at hc
  · rintro rfl
    exact ht

end DefocusingNLS

end OAI
