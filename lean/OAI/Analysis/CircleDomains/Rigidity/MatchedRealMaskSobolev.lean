import OAI.Analysis.CircleDomains.Rigidity.MatchedRealMaskData
import OAI.Analysis.CircleDomains.Rigidity.TraceMaskOpenSobolev
import OAI.Analysis.CircleDomains.Rigidity.TraceEnumerationUnion

namespace OAI

/-! Apply the proved open-set Sobolev gluing to the constructed masks.
The only scalar hypotheses concern the actual smooth pullback on the original domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 def realPlaneDomain (G : Set Sphere) : Set (ℝ × ℝ) :=
  {p | (Complex.equivRealProdCLM.symm p : Sphere) ∈ G}

 theorem realPlaneDomain_open {G : Set Sphere} (hG : IsOpen G) : IsOpen (realPlaneDomain G) :=
  hG.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)

omit [Encodable D.IndexedMatchedPair] in
 theorem physical_maskDomain (W : D.IndexedMatchedPair → Set ℂ) :
    physicalPlaneDomain (maskDomain G W) = euclideanPlaneCoordinates ⁻¹'
      (realPlaneDomain G ∪ ⋃ j, Complex.equivRealProdCLM.symm ⁻¹' W j) := by
  ext x
  change ((complexPlaneCoordinates x : Sphere) ∈ G ∨
    (complexPlaneCoordinates x : Sphere) ∈ ⋃ j, ((↑) : ℂ → Sphere) '' W j) ↔ _
  simp only [mem_preimage,mem_union,mem_iUnion,realPlaneDomain,mem_ofPred_eq]
  constructor
  · rintro (h | ⟨j,z,hz,he⟩)
    · exact Or.inl h
    · have hzx : z = complexPlaneCoordinates x := OnePoint.coe_injective he
      exact Or.inr ⟨j,by simpa only [hzx,complexPlaneCoordinates,ContinuousLinearEquiv.trans_apply] using hz⟩
  · rintro (h | ⟨j,hj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j,complexPlaneCoordinates x,hj,rfl⟩

 theorem MatchedRealMask.sobolev
    {E : D.MatchedRoundDisks} {hG : IsOpen G} {hf : IsConformalEquivalence f G (f '' G)}
    {φ : Sphere → ℝ} {L : ℝ≥0} {m : ℕ} (M : MatchedRealMask E hG hf φ L m)
    (hb : ContDiffOn ℝ 1 (D.realSelectedScalar hG hf φ) (realPlaneDomain G))
    (hb2 : MemLp (fderiv ℝ (D.realSelectedScalar hG hf φ)) 2 (volume.restrict (realPlaneDomain G))) :
    Nonempty (DeGiorgi.MemW1pWitness 2
      (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates)
      (physicalPlaneDomain (maskDomain G M.neighborhood))) := by
  let V : ℕ → Set (ℝ × ℝ) := traceEnumeration (fun j => Complex.equivRealProdCLM.symm ⁻¹' M.neighborhood j) ∅
  have hVo (n : ℕ) : IsOpen (V n) := by
    by_cases hn : n ∈ Set.range (Encodable.encode : D.IndexedMatchedPair → ℕ)
    · obtain ⟨j,rfl⟩ := hn
      dsimp only [V]
      rw [traceEnumeration_encode]
      exact (M.neighborhood_open j).preimage Complex.equivRealProdCLM.symm.continuous
    · dsimp only [V]
      rw [traceEnumeration_missing _ _ hn]
      exact isOpen_empty
  have hVz (n : ℕ) (p : ℝ × ℝ) (hp : p ∈ V n) : M.cutoff n p = 0 ∧
      D.realSelectedScalar hG hf φ p ∈ E.traceInterval hG hf φ L n := by
    by_cases hn : n ∈ Set.range (Encodable.encode : D.IndexedMatchedPair → ℕ)
    · obtain ⟨j,rfl⟩ := hn
      dsimp only [V] at hp
      rw [traceEnumeration_encode] at hp
      simpa only [ContinuousLinearEquiv.apply_symm_apply,realSelectedScalar] using
        M.neighborhood_zero j (Complex.equivRealProdCLM.symm p) hp
    · dsimp only [V] at hp
      rw [traceEnumeration_missing _ _ hn] at hp
      exact hp.elim
  obtain ⟨H,_⟩ := trace_mask_open_sobolev M.smooth M.unit
    (fun _ => measurableSet_Ioo) (fun _ => by simp)
    (fun _ => ordConnected_Ioo) (E.traceScalarCenter hG hf φ)
    (fun j => ⟨sub_lt_self _ (E.traceWidth_pos L j),lt_add_of_pos_right _ (E.traceWidth_pos L j)⟩)
    (realPlaneDomain_open hG) hb hb2 V hVo hVz
    M.density_measurable M.density_nonneg M.density_memLp
    (fun n => M.pays.mono (fun _ h => h n)) 0 M.continuous M.compact
  have he : physicalPlaneDomain (maskDomain G M.neighborhood) =
      euclideanPlaneCoordinates ⁻¹' (realPlaneDomain G ∪ ⋃ j, V j) := by
    dsimp only [V]
    rw [traceEnumeration_iUnion]
    exact physical_maskDomain M.neighborhood
  rw [he]
  exact ⟨H⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
