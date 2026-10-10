import OAI.Geometry.HeilbronnTriangle.IntegralPlaneLattice

namespace OAI


noncomputable section
namespace Problem355.IntegralPlaneLattice
open Module MeasureTheory

instance standardLattice_isZLattice : IsZLattice ℝ standardLattice := by
  unfold standardLattice
  infer_instance

lemma castLinear_injective : Function.Injective castLinear := by
  intro v w h
  funext i
  have hi := congrArg (fun u : Ambient => u i) h
  change (v i : ℝ) = (w i : ℝ) at hi
  exact_mod_cast hi

lemma realLattice_top : realLattice ⊤ = standardLattice := by
  apply le_antisymm (realLattice_le_standard _)
  intro v hv
  choose z hz using (mem_standardLattice v).mp hv
  refine ⟨z, trivial, ?_⟩
  ext i
  exact hz i

lemma realLattice_spans (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
    Submodule.span ℝ (realLattice L : Set Ambient) = ⊤ := by
  apply top_unique
  rw [← stdBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  have hi : castVec (Pi.single i 1) = stdBasis i := by
    ext j
    simp [castVec, stdBasis, EuclideanSpace.basisFun_apply, Pi.single_apply]
  have hm : E • stdBasis i ∈ realLattice L := by
    refine ⟨E • Pi.single i 1, hL _, ?_⟩
    rw [map_smul]
    exact congrArg (fun u : Ambient => E • u) hi
  have hs : (E : ℝ) • stdBasis i ∈ Submodule.span ℝ (realLattice L : Set Ambient) := by
    rw [Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.subset_span hm
  exact (Submodule.smul_mem_iff _ (by exact_mod_cast hE : (E : ℝ) ≠ 0)).mp hs

lemma realLattice_isZLattice (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : IsZLattice ℝ (realLattice L) :=
  ⟨realLattice_spans L E hE hL⟩

lemma standardLattice_covolume : ZLattice.covolume standardLattice = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain standardLattice volume
    (ZSpan.isAddFundamentalDomain stdBasis volume)]
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped stdBasis volume)]
  change (volume (parallelepiped (EuclideanSpace.basisFun (Fin 3) ℝ))).toReal = 1
  rw [OrthonormalBasis.volume_parallelepiped]
  simp

lemma realLattice_relIndex (L : Submodule ℤ (Fin 3 → ℤ)) :
    (realLattice L).toAddSubgroup.relIndex standardLattice.toAddSubgroup =
      L.toAddSubgroup.index := by
  rw [← realLattice_top]
  change (L.toAddSubgroup.map castLinear.toAddMonoidHom).relIndex
      ((⊤ : AddSubgroup (Fin 3 → ℤ)).map castLinear.toAddMonoidHom) = _
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ castLinear_injective]
  simp

lemma one_le_norm_of_mem_standardLattice (v : Ambient) (hv : v ∈ standardLattice)
    (hv0 : v ≠ 0) : 1 ≤ ‖v‖ := by
  have hi : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv0
    ext i
    exact not_not.mp (fun hn => h ⟨i, hn⟩)
  obtain ⟨i, hi⟩ := hi
  obtain ⟨z, hz⟩ := (mem_standardLattice v).mp hv i
  have hz0 : z ≠ 0 := by
    intro h
    apply hi
    simpa [h] using hz.symm
  have ha : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast Int.one_le_abs hz0
  calc
    (1 : ℝ) ≤ |v i| := by simpa [hz] using ha
    _ ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i

lemma one_le_norm_of_mem_realLattice (L : Submodule ℤ (Fin 3 → ℤ))
    (v : Ambient) (hv : v ∈ realLattice L) (hv0 : v ≠ 0) : 1 ≤ ‖v‖ :=
  one_le_norm_of_mem_standardLattice v (realLattice_le_standard L hv) hv0

lemma realLattice_covolume (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
    ZLattice.covolume (realLattice L) = (L.toAddSubgroup.index : ℝ) := by
  let := realLattice_isZLattice L E hE hL
  have h := ZLattice.covolume_div_covolume_eq_relIndex'
    (realLattice L) standardLattice (realLattice_le_standard L)
  simpa [standardLattice_covolume, realLattice_relIndex] using h

end Problem355.IntegralPlaneLattice

end

end OAI
