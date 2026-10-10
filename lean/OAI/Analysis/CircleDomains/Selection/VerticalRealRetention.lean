import OAI.Analysis.CircleDomains.Selection.RealSequenceRetention
import OAI.Analysis.CircleDomains.Transfer.VerticalRetainedCrossings

namespace OAI

/-! Actual retained real tests give vertical target crossing segments. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer.RealModelExhaustion
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem eventually_vertical_test_crossings
    (hsch : PlanarSchoenflies) (hG : IsOpen G)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
      finiteCoord ((M.stages (r n)).forward (z : Sphere))) F
      atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (A B : SmoothJordanCore G) (i : Fin A.count) (j : Fin B.count) (l : ℕ)
    (hOne : ∀ z ∈ frontier (jordanInterior (A.disk i)),
      d.physical l (Complex.equivRealProdCLM z) = 1)
    (hZero : ∀ z ∈ frontier (jordanInterior (B.disk j)),
      d.physical l (Complex.equivRealProdCLM z) = 0)
    (H K : ℂ ≃ₜ ℂ)
    (hH : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H))
    (hK : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (B.disk j))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior K))
    (hsideH : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk i))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H))
    (hsideK : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior K))
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ jordanInterior H)
    {L : ℝ} (hKL : closure (jordanInterior K) ⊆ ball 0 L) :
    ∀ᶠ n in atTop, ∀ y ∈ Complex.re '' C, ∃ a b : ℝ, a < b ∧
      (verticalLine y a : Sphere) ∈ (M.stages (r n)).domain ∧
      (verticalLine y b : Sphere) ∈ (M.stages (r n)).domain ∧
      verticalLine y a ∈ closedBall 0 L ∧ verticalLine y b ∈ closedBall 0 L ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (verticalLine y a)) = 0 ∧
      sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))
        ((M.stages (r n)).inverse (verticalLine y b)) = 1 := by
  let _ : ∀ n, Fintype (M.stages (r n)).indices :=
    fun n => (M.stages (r n)).finite_indices.fintype
  apply eventually_vertical_crossings_of_retained_test hsch
    (fun n => (M.stages (r n)).terminals.H)
    (fun n => (M.stages (r n)).terminals.disjoint_closures)
    (fun n => (M.stages (r n)).forward) (fun n => (M.stages (r n)).inverse)
    (fun n => (M.stages (r n)).domain) (fun n => (M.stages (r n)).equivalence)
    (fun n => (M.stages (r n)).circle_domain.1) (fun n => (M.stages (r n)).principal.1)
    hG A B i j (hr (M.eventually_model_contains A.isCompact A.subset))
    (hr (M.eventually_model_contains B.isCompact B.subset)) ?_ F hF hlim H K
    hH hK hsideH hsideK hHK hC hCH hKL
    (fun n => sphereRealFunction ((M.stages (r n)).functions (prefixIndex l (r n)))) ?_
  · intro q hq
    exact hr ((M.eventually_model_contains isCompact_singleton (singleton_subset_iff.mpr hq)).mono
      (fun _ hn => hn (mem_singleton q)))
  · have ha := hr (M.eventually_test_eq A.isCompact A.subset l)
    have hb := hr (M.eventually_test_eq B.isCompact B.subset l)
    filter_upwards [ha, hb] with n hnA hnB
    constructor
    · intro z hz
      simpa only [sphereRealFunction, finiteCoord_coe] using
        (hnA z ((A.inDomain (Subset.refl _)).boundary_subset_domain i ⟨z, hz, rfl⟩)).trans (hOne z hz)
    · intro z hz
      simpa only [sphereRealFunction, finiteCoord_coe] using
        (hnB z ((B.inDomain (Subset.refl _)).boundary_subset_domain j ⟨z, hz, rfl⟩)).trans (hZero z hz)

end CircleDomainRigidity.FiniteTransfer.RealModelExhaustion

end

end OAI
