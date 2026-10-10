import Mathlib
import OAI.Analysis.Conductivity.Variational.QuantitativeGlobalCorrection
import OAI.Analysis.Conductivity.Branching.SmoothFamilyCorrectionTransport

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
lemma SmoothVanishingPairFamily.sum {ι : Type*} [Fintype ι]
    (r : ι → Fin 2 → P×Coord3 → ℝ) {p : P} {W : Set Coord3}
    (hr : ∀ i,SmoothVanishingPairFamily p W (r i)) :
    SmoothVanishingPairFamily p W (∑ i,r i) := by
  classical
  choose K hK hKW hs using fun i => (hr i).2.2
  refine ⟨fun j => ?_,fun j y => ?_,⋃ i,K i,isCompact_iUnion hK,iUnion_subset hKW,?_⟩
  · have he : ((∑ i,r i) j)=(fun x => ∑ i,r i j x) := by
      funext x; simp only [Finset.sum_apply]
    rw [he]
    exact ContDiff.sum (s:=Finset.univ) (fun i _ => (hr i).1 j)
  · simp only [Finset.sum_apply,(fun i => (hr i).2.1 j y),Finset.sum_const_zero]
  · intro q
    have he : (fun j y => (∑ i,r i) j (q,y))=∑ i,(fun j y => r i j (q,y)) := by
      funext j y; simp
    rw [he]
    exact PairSupported.sum _ _ (fun i _ => (hs i q).mono (subset_iUnion K i))

omit [FiniteDimensional ℝ P] in
lemma vanishing_regions_chain
    {u : P×Coord3 → Fin 2 → ℝ} (p : P) {U : Set Coord3} (hUc : IsPreconnected U)
    (hcover : (⋃ B : VanishingCorrectionRegion u p U,B.region)=U)
    (hreg : ∀ O : Set Coord3,IsOpen O → O.Nonempty → O⊆U →
      ∃ x∈O,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    (B C : VanishingCorrectionRegion u p U) :
    Relation.TransGen (fun B C : VanishingCorrectionRegion u p U =>
      ∃ x∈B.region∩C.region,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x)) B C := by
  have hc : IsPreconnected (⋃ B : VanishingCorrectionRegion u p U,B.region) := hcover.symm ▸ hUc
  have hp := hc.transGen_of_iUnion (fun B => B.region_open) B C B.region_nonempty C.region_nonempty
  apply Relation.TransGen.mono (fun D E hDE => ?_) B C hp
  exact hreg _ (D.region_open.inter E.region_open) hDE (inter_subset_left.trans D.region_subset)

omit [FiniteDimensional ℝ P] in
lemma vanishing_source_finite_split
    {u : P×Coord3 → Fin 2 → ℝ} (p : P) {U : Set Coord3}
    (hcover : (⋃ B : VanishingCorrectionRegion u p U,B.region)=U)
    {r : Fin 2 → P×Coord3 → ℝ} (hr : SmoothVanishingPairFamily p U r) :
    ∃ (s : Finset (VanishingCorrectionRegion u p U)) (g : s → Fin 2 → P×Coord3 → ℝ),
      (∀ i,SmoothVanishingPairFamily p i.val.region (g i)) ∧ (∑ i,g i)=r := by
  classical
  obtain ⟨K,hK,hKU,hs⟩ := hr.2.2
  have hcov : K⊆⋃ B : VanishingCorrectionRegion u p U,B.region := hcover.symm ▸ hKU
  obtain ⟨s,hsc⟩ := hK.elim_finite_subcover (fun B : VanishingCorrectionRegion u p U => B.region)
    (fun B => B.region_open) hcov
  have hsc' : K⊆⋃ B : s,B.val.region := by
    intro x hx
    obtain ⟨B,hB,hxB⟩ := mem_iUnion₂.mp (hsc hx)
    exact mem_iUnion.mpr ⟨⟨B,hB⟩,hxB⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ Coord3) hK.isClosed (fun B : s => B.val.region)
    (fun B => B.val.region_open) hsc'
  have hsρ (i : s) : HasCompactSupport (ρ i) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport _,i.val.region_bounded.subset (hρ i)⟩
  let g : s → Fin 2 → P×Coord3 → ℝ := fun i j z => ρ i z.2*r j z
  refine ⟨s,g,?_,?_⟩
  · intro i
    exact ⟨fun j => ((ρ i).contMDiff.contDiff.comp contDiff_snd).mul (hr.1 j),
      fun j y => by simp [g,hr.2.1 j y],tsupport (ρ i),hsρ i,hρ i,
      fun q j => tsupport_mul_subset_left⟩
  · funext j z
    simp only [Finset.sum_apply,g]
    rw [←Finset.sum_mul]
    by_cases hz : z.2∈K
    · have he := ρ.sum_eq_one hz
      rw [finsum_eq_sum_of_fintype] at he
      rw [he,one_mul]
    · have he : r j z=0 := image_eq_zero_of_notMem_tsupport (f:=fun y => r j (z.1,y))
        (fun h => hz (hs z.1 j h))
      rw [he,mul_zero]

theorem global_vanishing_family_correction
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P)
    {U : Set Coord3} (hUc : IsPreconnected U)
    (hcover : (⋃ B : VanishingCorrectionRegion u p U,B.region)=U)
    (hreg : ∀ O : Set Coord3,IsOpen O → O.Nonempty → O⊆U →
      ∃ x∈O,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {r : Fin 2 → P×Coord3 → ℝ} (hr : SmoothVanishingPairFamily p U r)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,physicalSourceMoment (fun y => u (q,y)) (fun j y => r j (q,y))=0 →
      BoundedPhysicallyCorrectable (fun y => u (q,y)) U (fun j y => r j (q,y)) ε := by
  classical
  by_cases hne : U.Nonempty
  · obtain ⟨x,hx⟩ := hne
    have hx' : x∈⋃ B : VanishingCorrectionRegion u p U,B.region := hcover.symm ▸ hx
    obtain ⟨B,_⟩ := mem_iUnion.mp hx'
    obtain ⟨s,g,hg,hge⟩ := vanishing_source_finite_split p hcover hr
    choose a ha ham hac using fun i : s => smooth_chain_source_transport hu p
      (vanishing_regions_chain p hUc hcover hreg i.val B) (hg i)
    have hA := SmoothVanishingPairFamily.sum a ha
    let δ : ℝ := ε/(Fintype.card s+1)
    have hδ : 0<δ := div_pos hε (by positivity)
    have hsolve := B.solve (∑ i,a i) hA δ hδ
    filter_upwards [hsolve,Filter.eventually_all.mpr ham,
      Filter.eventually_all.mpr (fun i => hac i δ hδ)] with q solve mom small total
    have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (q,y)) := hu.comp (contDiff_const.prodMk contDiff_id)
    have hQ : (fun j y => (∑ i,a i) j (q,y))=∑ i,(fun j y => a i j (q,y)) := by funext j y; simp
    have hG : (∑ i : s,(fun j y => g i j (q,y)))=(fun j y => r j (q,y)) := by
      funext j y
      have he := congrFun (congrFun hge j) (q,y)
      simpa only [Finset.sum_apply] using he
    have hAm : physicalSourceMoment (fun y => u (q,y)) (fun j y => (∑ i,a i) j (q,y))=0 := by
      rw [hQ,physicalSourceMoment_sum _ _ huq.continuous (fun i _ => (ha i).compact q)]
      simp_rw [mom]
      rw [←physicalSourceMoment_sum _ _ huq.continuous (fun i _ => (hg i).compact q),hG,total]
    have hb := solve hAm
    have ht := BoundedPhysicallyCorrectable.sum Finset.univ
      (fun i => (fun j y => g i j (q,y))-(fun j y => a i j (q,y))) (fun _ => δ) huq (fun i _ => small i)
    have h := ht.add huq hb
    rw [Finset.sum_sub_distrib,←hQ,sub_add_cancel,hG] at h
    have he : (∑ _i : s,δ)+δ=ε := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp [δ]
      field_simp
    rwa [he] at h
  · apply Filter.Eventually.of_forall
    intro q _
    have hz : (fun j y => r j (q,y))=0 := by
      funext j y
      exact image_eq_zero_of_notMem_tsupport (f:=fun y => r j (q,y)) (fun h => hne ⟨y,hr.supported q j h⟩)
    rw [hz]
    exact BoundedPhysicallyCorrectable.zero hε.le

end ScalarConductivity

end
end

end OAI
