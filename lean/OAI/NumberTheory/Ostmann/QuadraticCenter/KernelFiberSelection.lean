import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelFunctions
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelLargePopulation

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def canonicalKernelImage (S : Finset ℤ) (m : ℕ) (h : ℤ) : Finset ℤ :=
  S.image (fun x => canonicalSignedKernel ((m:ℤ)*x-h))

theorem canonicalKernelFiber_sum (S : Finset ℤ) (m : ℕ) (h : ℤ) :
    S.card=∑u∈canonicalKernelImage S m h,(canonicalKernelFiber S m h u).card := by
  exact Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)

theorem exists_large_canonicalKernelRoots {S : Finset ℤ} (hS : S.Nonempty)
    {m : ℕ} (hm : 0 < m) (h : ℤ) :
    ∃u∈canonicalKernelImage S m h,
      S.card ≤ (canonicalKernelImage S m h).card*(canonicalKernelRoots S m h u).card ∧
      (canonicalKernelRoots S m h u).Nonempty := by
  classical
  have hK : (canonicalKernelImage S m h).Nonempty := hS.image _
  obtain ⟨u,hu,hmax⟩ := (canonicalKernelImage S m h).exists_mem_eq_sup' hK
    (fun u => (canonicalKernelFiber S m h u).card)
  have hcnt : S.card ≤ (canonicalKernelImage S m h).card*(canonicalKernelFiber S m h u).card := by
    rw [canonicalKernelFiber_sum]
    calc
      _ ≤ ∑ _v∈canonicalKernelImage S m h,(canonicalKernelFiber S m h u).card := by
        apply Finset.sum_le_sum
        intro v hv
        rw [←hmax]
        exact Finset.le_sup' (fun v => (canonicalKernelFiber S m h v).card) hv
      _ = _ := by simp
  refine ⟨u,hu,?_,?_⟩
  · rwa [canonicalKernelRoots_card hm]
  · apply Finset.card_pos.mp
    rw [canonicalKernelRoots_card hm]
    by_contra hn
    have hz : (canonicalKernelFiber S m h u).card=0 := by omega
    rw [hz,mul_zero] at hcnt
    exact (not_le_of_gt hS.card_pos) hcnt

theorem canonical_large_kernel_tail_bound {S : Finset ℤ} {m : ℕ}
    (hm : 0 < m) {h : ℤ} (hcop : IsCoprime h (m:ℤ))
    {X Y : ℝ} (hX : 0≤X) (hY : 0<Y)
    (hdiam : ∀x∈S,∀y∈S,|(x:ℝ)-(y:ℝ)|≤X) :
    ((S.filter (fun x => Y≤|(canonicalSignedKernel ((m:ℤ)*x-h):ℝ)|)).card:ℝ) ≤
      ((canonicalKernelImage S m h).card:ℝ)*
        (4*Real.sqrt (X/Y)+8*Real.sqrt (m:ℝ)) := by
  classical
  let B := S.filter (fun x => Y≤|(canonicalSignedKernel ((m:ℤ)*x-h):ℝ)|)
  have hb := large_kernel_tail_bound S hm hcop
    (fun x => canonicalSignedKernel ((m:ℤ)*x-h))
    (fun x => canonicalSquareFactor ((m:ℤ)*x-h)) hX hY
    (fun x hx => canonical_kernel_factorization ((m:ℤ)*x-h)) hdiam
  change (B.card:ℝ) ≤ _ at hb ⊢
  have hsub : B.image (fun x => canonicalSignedKernel ((m:ℤ)*x-h)) ⊆
      canonicalKernelImage S m h := Finset.image_subset_image (Finset.filter_subset _ _)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Nat.cast_le.mpr (Finset.card_le_card hsub)

end Ostmann.QuadraticCenter

end

end OAI
