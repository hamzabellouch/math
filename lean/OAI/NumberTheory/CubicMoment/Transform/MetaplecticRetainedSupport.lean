import OAI.NumberTheory.CubicMoment.Transform.MetaplecticFreeFrequency
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCoefficientMass

namespace OAI

/-! Choose the literal published support representation once for each
nonzero retained coefficient. The resulting finite code set decodes
injectively to the original frequency set. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev MetaplecticSupportPrefix (r : Eisenstein) :=
  ℕ × (Eisensteinˣ × ((metaplecticPrimaryDivisors r) × PrimaryArgument))

abbrev MetaplecticRetainedCode (r : Eisenstein) :=
  PrimaryArgument × (MetaplecticSupportPrefix r × PrimaryArgument)

def metaplecticDivisorPrimary (r : Eisenstein) (h : metaplecticPrimaryDivisors r) : PrimaryArgument :=
  ⟨h.val,(mem_primaryElementBall.mp (Finset.mem_filter.mp h.property).1).1⟩

def metaplecticPrefixArgument (r : Eisenstein) (p : MetaplecticSupportPrefix r)
    (w : Eisenstein) : MetaplecticDualArgument :=
  metaplecticFreeArgument p.1 p.2.1 (metaplecticDivisorPrimary r p.2.2.1) p.2.2.2 w

def metaplecticRetainedDecode (r : Eisenstein) (z : MetaplecticRetainedCode r) :
    MetaplecticDualArgument × PrimaryArgument :=
  (metaplecticPrefixArgument r z.2.1 z.2.2.val,z.1)

lemma metaplecticNormalizedDualCoefficient_zero
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument)
    (hz : a r nd.1*metaplecticLocalCoefficient r nd.1 = 0) :
    metaplecticNormalizedDualCoefficient a r ℓ nd = 0 := by
  unfold metaplecticNormalizedDualCoefficient
  split_ifs <;> simp only [hz,zero_div,zero_mul]

/-- The index stores only genuine supported factors. Neither a free
coefficient bound nor a moment estimate is included in this reindexing. -/
theorem metaplectic_retained_support_partition
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ S : Finset (MetaplecticDualArgument × PrimaryArgument),
      ∃ T : Finset (MetaplecticRetainedCode r),
        (∀ z ∈ T, metaplecticRetainedDecode r z ∈ S ∧
          (∃ k : ℕ, z.2.1.2.2.2.val ∣ r^k) ∧ IsCoprime z.2.2.val r ∧
          Squarefree (z.2.1.2.2.1.val*z.2.2.val) ∧
          ‖a r (metaplecticRetainedDecode r z).1‖ ≤
            C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2)) ∧
        ∀ (ℓ : ℤ) (t : ℝ),
          (∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
            mellinPhase t (metaplecticDualNorm nd)) =
          ∑ z ∈ T, metaplecticNormalizedDualCoefficient a r ℓ (metaplecticRetainedDecode r z)*
            mellinPhase t (metaplecticDualNorm (metaplecticRetainedDecode r z)) := by
  obtain ⟨C,hC,hcoef⟩ := ha
  refine ⟨C,hC,?_⟩
  intro r hr hsr S
  let U := S.filter (fun nd => a r nd.1*metaplecticLocalCoefficient r nd.1 ≠ 0)
  have hcode (nd : U) : ∃ z : MetaplecticRetainedCode r,
      metaplecticRetainedDecode r z = nd.val ∧
      (∃ k : ℕ, z.2.1.2.2.2.val ∣ r^k) ∧ IsCoprime z.2.2.val r ∧
      Squarefree (z.2.1.2.2.1.val*z.2.2.val) ∧
      ‖a r (metaplecticRetainedDecode r z).1‖ ≤
        C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2) := by
    have hnd := (Finset.mem_filter.mp nd.property).2
    obtain ⟨j,ζ,h,h',w,hj,hh,hh',hw,hdiv,h'div,hwr,hs,he,hb⟩ :=
      hcoef r hr hsr nd.val.1 hnd
    let z : MetaplecticRetainedCode r :=
      (nd.val.2,((j+1).toNat,ζ,⟨h,metaplectic_supported_divisor_mem hr hh hs hdiv⟩,⟨h',hh'⟩),⟨w,hw⟩)
    have hd : metaplecticRetainedDecode r z = nd.val := by
      apply Prod.ext
      · apply Subtype.ext
        change (metaplecticFreeArgument (j+1).toNat ζ _ _ w).val = nd.val.1.val
        rw [metaplecticFreeArgument_val _ _ _ _ (primary_ne_zero hw)]
        exact (metaplectic_numerator_of_frequency nd.val.1 hj ζ h h' w he).symm
      · rfl
    refine ⟨z,hd,h'div,hwr,hs,?_⟩
    rw [hd]
    have hjk : (((j+1).toNat:ℕ):ℤ)-1 = j := by omega
    simpa only [z,hjk] using hb
  choose code hdecode hsupport hcop hsquare hbound using hcode
  let T : Finset (MetaplecticRetainedCode r) := Finset.univ.image code
  have hinj : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    exact (hdecode x).symm.trans ((congrArg (metaplecticRetainedDecode r) hxy).trans (hdecode y))
  refine ⟨T,?_,?_⟩
  · intro z hz
    obtain ⟨nd,_,rfl⟩ := Finset.mem_image.mp hz
    refine ⟨?_,hsupport nd,hcop nd,hsquare nd,hbound nd⟩
    rw [hdecode nd]
    exact (Finset.mem_filter.mp nd.property).1
  · intro ℓ t
    let F := fun nd : MetaplecticDualArgument × PrimaryArgument =>
      metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase t (metaplecticDualNorm nd)
    have hU : (∑ nd ∈ S, F nd) = ∑ nd ∈ U, F nd := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro nd hnd hnU
      have hz : a r nd.1*metaplecticLocalCoefficient r nd.1 = 0 := by
        by_contra h
        exact hnU (Finset.mem_filter.mpr ⟨hnd,h⟩)
      simp only [F,metaplecticNormalizedDualCoefficient_zero a r ℓ nd hz,zero_mul]
    change (∑ nd ∈ S, F nd) = ∑ z ∈ T, F (metaplecticRetainedDecode r z)
    rw [hU]
    change (∑ nd ∈ U, F nd) = ∑ z ∈ Finset.univ.image code, F (metaplecticRetainedDecode r z)
    rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    simp_rw [hdecode]
    exact (Finset.sum_coe_sort U F).symm

end CubicFirstMoment

end

end OAI
