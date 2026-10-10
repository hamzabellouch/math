import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeRootClassification

namespace OAI

/-! The three free symmetry zeros have analytic multiplicity one. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

private theorem free_order_sum_le (hR : RectangleRouche) (ell : ℕ) (b Z : ℝ)
    (hD : (b,Z)∈freeMatchingDisk) (S : Finset {z : ℂ | -(1/32 : ℝ)≤z.re}) :
    (∑ z ∈ S, analyticOrderAt (spectralSlowDeterminant ell b Z) z.val)≤
      (freeOutgoingCount ell : ℕ∞) := by
  let f := fun z : {z : ℂ | -(1/32 : ℝ)≤z.re} =>
    analyticOrderAt (spectralSlowDeterminant ell b Z) z.val
  have hs : Summable f := ⟨_,hasSum_of_isLUB _ (isLUB_sSup (Set.range
    (fun s : Finset {z : ℂ | -(1/32 : ℝ)≤z.re} => ∑ z ∈ s, f z)))⟩
  exact (hs.sum_le_tsum S (fun _ _ => zero_le)).trans_eq (free_outgoing_count hR ell b Z hD)

theorem radialFree_symmetry_zeros_simple (hR : RectangleRouche) (w : RadialShootingDisk)
    (hw : diskProfile w=0) :
    analyticOrderAt (spectralSlowDeterminant 0 (radialShootingB w) ((radialShootingR w)^2/4)) 0=1 ∧
    analyticOrderAt (spectralSlowDeterminant 1 (radialShootingB w) ((radialShootingR w)^2/4)) (1/2)=1 ∧
    analyticOrderAt (spectralSlowDeterminant 0 (radialShootingB w) ((radialShootingR w)^2/4)) 1=1 := by
  classical
  let b := radialShootingB w
  let Z := (radialShootingR w)^2/4
  have hD : (b,Z)∈freeMatchingDisk := radialShooting_freeMatchingDisk w
  have hZ : Z≠0 := by
    have hh := (abs_le.mp (freeMatchingDisk_subset_certificate_box hD).2).1
    intro he
    norm_num [he] at hh
  obtain ⟨h0,ht,h1⟩ := radialFree_spectral_symmetry_zeros w hw
  have ho0 : 1≤analyticOrderAt (spectralSlowDeterminant 0 b Z) 0 :=
    Order.one_le_iff_ne_zero.mpr
      ((analyticAt_spectralSlowDeterminant 0 b Z 0 hZ (by norm_num)).analyticOrderAt_ne_zero.mpr h0)
  have hot : 1≤analyticOrderAt (spectralSlowDeterminant 1 b Z) (1/2) :=
    Order.one_le_iff_ne_zero.mpr
      ((analyticAt_spectralSlowDeterminant 1 b Z (1/2) hZ (by norm_num)).analyticOrderAt_ne_zero.mpr ht)
  have ho1 : 1≤analyticOrderAt (spectralSlowDeterminant 0 b Z) 1 :=
    Order.one_le_iff_ne_zero.mpr
      ((analyticAt_spectralSlowDeterminant 0 b Z 1 hZ (by norm_num)).analyticOrderAt_ne_zero.mpr h1)
  let a : {z : ℂ | -(1/32 : ℝ)≤z.re} := ⟨0,by norm_num⟩
  let c : {z : ℂ | -(1/32 : ℝ)≤z.re} := ⟨1,by norm_num⟩
  let t : {z : ℂ | -(1/32 : ℝ)≤z.re} := ⟨1/2,by norm_num⟩
  have hsum : analyticOrderAt (spectralSlowDeterminant 0 b Z) 0+
      analyticOrderAt (spectralSlowDeterminant 0 b Z) 1≤(1 : ℕ∞)+1 := by
    simpa [a,c,freeOutgoingCount,show (1 : ℕ∞)+1=2 by norm_num] using
      free_order_sum_le hR 0 b Z hD {a,c}
  have htup : analyticOrderAt (spectralSlowDeterminant 1 b Z) (1/2)≤1 := by
    simpa [t,freeOutgoingCount] using free_order_sum_le hR 1 b Z hD {t}
  have h0up : analyticOrderAt (spectralSlowDeterminant 0 b Z) 0≤1 := by
    apply (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞)≠⊤)).mp
    exact (add_le_add le_rfl ho1).trans hsum
  have h1up : analyticOrderAt (spectralSlowDeterminant 0 b Z) 1≤1 := by
    apply (ENat.add_le_add_iff_left (by simp : (1 : ℕ∞)≠⊤)).mp
    exact (add_le_add ho0 le_rfl).trans hsum
  exact ⟨le_antisymm h0up ho0,le_antisymm htup hot,le_antisymm h1up ho1⟩

end DefocusingNLS

end OAI
