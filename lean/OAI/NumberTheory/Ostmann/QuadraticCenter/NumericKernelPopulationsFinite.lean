import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelFiberSelection
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisionRootSets

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def canonicalSmallKernelPoints (S : Finset ℤ) (m : ℕ) (h : ℤ) (Y : ℝ) : Finset ℤ :=
  S.filter (fun x => |(canonicalSignedKernel ((m : ℤ)*x-h) : ℝ)| < Y)

theorem exists_large_small_canonicalKernelRoots {S : Finset ℤ} {m : ℕ}
    (hm : 0 < m) {h : ℤ} (hcop : IsCoprime h (m : ℤ))
    (hnonzero : ∀ x ∈ S, (m : ℤ)*x-h ≠ 0)
    {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 < Y)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |(x : ℝ)-(y : ℝ)| ≤ X)
    (hsurvive : ((canonicalKernelImage S m h).card : ℝ)*
      (4*Real.sqrt (X/Y)+8*Real.sqrt (m : ℝ)) < S.card) :
    ∃ u ∈ canonicalKernelImage S m h,
      0 < |(u : ℝ)| ∧ |(u : ℝ)| < Y ∧ Squarefree u ∧
      (canonicalKernelRoots S m h u).Nonempty ∧
      (S.card : ℝ)-((canonicalKernelImage S m h).card : ℝ)*
        (4*Real.sqrt (X/Y)+8*Real.sqrt (m : ℝ)) ≤
          ((canonicalKernelImage S m h).card : ℝ)*(canonicalKernelRoots S m h u).card := by
  classical
  let A := canonicalSmallKernelPoints S m h Y
  let B := S.filter (fun x => Y ≤ |(canonicalSignedKernel ((m : ℤ)*x-h) : ℝ)|)
  have hpart : A.card+B.card = S.card := by
    simpa only [A, B, canonicalSmallKernelPoints, not_lt] using
      Finset.card_filter_add_card_filter_not (s := S) (fun x => |(canonicalSignedKernel ((m : ℤ)*x-h) : ℝ)| < Y)
  have htail := canonical_large_kernel_tail_bound hm hcop hX hY hdiam
  change (B.card : ℝ) ≤ _ at htail
  have hA : A.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < A.card := by
      have hh : (A.card : ℝ)+B.card = S.card := by exact_mod_cast hpart
      linarith
    exact_mod_cast hp
  obtain ⟨u,hu,hcard,hroot⟩ := exists_large_canonicalKernelRoots hA hm h
  have hAS : A ⊆ S := Finset.filter_subset _ _
  have hKI : canonicalKernelImage A m h ⊆ canonicalKernelImage S m h :=
    Finset.image_subset_image hAS
  have hRI : canonicalKernelRoots A m h u ⊆ canonicalKernelRoots S m h u := by
    apply Finset.image_subset_image
    exact Finset.filter_subset_filter _ hAS
  obtain ⟨x,hx,hxu⟩ := Finset.mem_image.mp hu
  have hxS := hAS hx
  have hxsmall := (Finset.mem_filter.mp hx).2
  have huz : u ≠ 0 := by
    rw [←hxu]
    exact canonicalSignedKernel_ne_zero (hnonzero x hxS)
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast huz
  refine ⟨u,hKI hu,abs_pos.mpr huR,?_,?_,hroot.mono hRI,?_⟩
  · simpa only [hxu] using hxsmall
  · rw [←hxu]
    exact canonicalSignedKernel_squarefree (hnonzero x hxS)
  · have hcount := hcard.trans (Nat.mul_le_mul (Finset.card_le_card hKI) (Finset.card_le_card hRI))
    have hcountR : (A.card : ℝ) ≤ ((canonicalKernelImage S m h).card : ℝ)*
        (canonicalKernelRoots S m h u).card := by exact_mod_cast hcount
    have hh : (A.card : ℝ)+B.card = S.card := by exact_mod_cast hpart
    linarith

end Ostmann.QuadraticCenter

end

end OAI
