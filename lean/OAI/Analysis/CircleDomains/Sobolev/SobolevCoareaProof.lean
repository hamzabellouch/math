import OAI.Analysis.CircleDomains.Sobolev.PhysicalFieldCoarea
import OAI.Analysis.CircleDomains.Sobolev.SobolevLipschitzRepresentatives
import OAI.Analysis.CircleDomains.Sobolev.SobolevNullFibers
import Mathlib.Data.Nat.Pairing

namespace OAI

/-! The exact weighted Sobolev coarea input is proved from the closed
Lipschitz representatives, their actual gradients, and the null-fiber
result for the remaining volume-null set. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma physical_field_coarea_null {u : EuclideanPlane → ℝ}
    (V : EuclideanPlane → EuclideanPlane) (q : EuclideanPlane → ℝ≥0∞)
    {N : Set EuclideanPlane} (hnull : volume N = 0)
    (hfiber : ∀ᵐ t, (μH[1] : Measure EuclideanPlane) (N ∩ u ⁻¹' {t}) = 0) :
    PhysicalFieldCoareaIdentity N u V q := by
  have he : sobolevLevelIntegral N u q =ᵐ[volume] fun _ => 0 := by
    filter_upwards [hfiber] with t ht
    change (∫⁻ x in N ∩ u ⁻¹' {t}, q x ∂μH[1]) = 0
    rw [Measure.restrict_eq_zero.mpr ht]
    exact lintegral_zero_measure q
  refine ⟨aemeasurable_const.congr he.symm,?_⟩
  rw [lintegral_congr_ae he,lintegral_zero,Measure.restrict_eq_zero.mpr hnull]
  exact (lintegral_zero_measure _).symm

lemma planarSobolevCoarea : PlanarSobolevCoarea := by
  intro u hu V hw hLp E hE hEb q hq
  obtain ⟨K,g,hK,hcover⟩ := locally_sobolev_lipschitz_representatives hu hw hLp
  let C : ℕ → Set EuclideanPlane := fun n => E ∩ K (Nat.unpair n)
  let A : ℕ → Set EuclideanPlane := disjointed C
  have hC (n : ℕ) : MeasurableSet (C n) := hE.inter (hK _).1.measurableSet
  have hA (n : ℕ) : MeasurableSet (A n) := MeasurableSet.disjointed hC n
  have hAC (n : ℕ) : A n ⊆ C n := disjointed_subset C n
  have hAE (n : ℕ) : A n ⊆ E := (hAC n).trans inter_subset_left
  have hAK (n : ℕ) : A n ⊆ K (Nat.unpair n) := (hAC n).trans inter_subset_right
  have hco (n : ℕ) : PhysicalFieldCoareaIdentity (A n) u V q := by
    exact physical_field_coarea_piece (hK _).2.1 (hA n) (hEb.subset (hAE n))
      (fun _ hx => (hK _).2.2.1 (hAK n hx))
      (ae_restrict_of_ae_restrict_of_subset (hAK n) (hK _).2.2.2) hq
  let U := ⋃ n, A n
  have hUE : U ⊆ E := iUnion_subset hAE
  have hU : U = E ∩ ⋃ i, K i := by
    change (⋃ n, disjointed C n) = _
    rw [iUnion_disjointed]
    ext x
    constructor
    · intro hx
      obtain ⟨n,hn⟩ := mem_iUnion.mp hx
      exact ⟨hn.1,mem_iUnion.mpr ⟨Nat.unpair n,hn.2⟩⟩
    · rintro ⟨hx,hxK⟩
      obtain ⟨⟨j,k⟩,hjk⟩ := mem_iUnion.mp hxK
      apply mem_iUnion.mpr
      refine ⟨Nat.pair j k,?_⟩
      simpa only [C,Nat.unpair_pair,mem_inter_iff] using And.intro hx hjk
  have hUc : MeasurableSet U := MeasurableSet.iUnion hA
  let N := E \ U
  have hN : MeasurableSet N := hE.diff hUc
  have hN0 : volume N = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hcover] with x hx hxn
    apply hxn.2
    rw [hU]
    exact ⟨hxn.1,hx⟩
  have hNco : PhysicalFieldCoareaIdentity N u V q := physical_field_coarea_null V q hN0
    (locally_sobolev_null_fibers hu hw hLp hN (hEb.subset sdiff_subset) hN0)
  have hUco : PhysicalFieldCoareaIdentity U u V q :=
    physical_field_coarea_iUnion hu V q A hA (disjoint_disjointed C) hco
  have hd : Disjoint U N := disjoint_sdiff_right
  have hall := physical_field_coarea_union hu V q hN hd hUco hNco
  have he : U ∪ N = E := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hUE hx
      · exact hx.1
    · intro hx
      by_cases hxU : x ∈ U
      · exact Or.inl hxU
      · exact Or.inr ⟨hx,hxU⟩
  rw [he] at hall
  exact hall

end CircleDomainRigidity

end

end OAI
