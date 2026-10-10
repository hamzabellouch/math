import OAI.Probability.SLE.Geometry.CompactSmoothExtension

namespace OAI

/-! Nested compactly supported smooth cutoffs exhausting an open domain.
Only their positive sets need to be nested. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

structure SmoothDomainExhaustion (U : Set (ℝ×ℝ)) (z₀ : ℝ×ℝ) where
  cutoff : ℕ → ℝ×ℝ → ℝ
  smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (cutoff n)
  compact : ∀ n, HasCompactSupport (cutoff n)
  supported : ∀ n, tsupport (cutoff n) ⊆ U
  based : ∀ n, cutoff n z₀=1
  bounds : ∀ n z, cutoff n z∈Icc 0 1
  increasing : Monotone (fun n => support (cutoff n))
  exhausts : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ n in atTop, K ⊆ support (cutoff n)

lemma exists_smoothDomainExhaustion (U : Set (ℝ×ℝ)) (hU : IsOpen U)
    (z₀ : ℝ×ℝ) (hz₀ : z₀∈U) : Nonempty (SmoothDomainExhaustion U z₀) := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let x₀ : U := ⟨z₀,hz₀⟩
  obtain ⟨N,hN⟩ := K.exists_mem x₀
  let V (n : ℕ) : Set (ℝ×ℝ) := Subtype.val '' interior (K (n+N+1))
  have hVo (n) : IsOpen (V n) := hU.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior
  have hVK (n) : closure (V n) ⊆ Subtype.val '' K (n+N+1) := by
    apply closure_minimal (image_mono interior_subset)
    exact ((K.isCompact _).image continuous_subtype_val).isClosed
  have hVc (n) : IsCompact (closure (V n)) :=
    ((K.isCompact _).image continuous_subtype_val).of_isClosed_subset isClosed_closure (hVK n)
  have hVU (n) : closure (V n) ⊆ U := (hVK n).trans (by
    rintro z ⟨x,hx,rfl⟩
    exact x.property)
  have hV0 (n) : z₀∈V n := by
    exact ⟨x₀,K.subset_interior (by omega) hN,rfl⟩
  have hVm : Monotone V := by
    intro n m hnm
    exact image_mono (interior_mono (K.subset (by omega)))
  have hχ (n : ℕ) : ∃ χ : ℝ×ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧
      range χ ⊆ Icc 0 1 ∧ support χ=V n ∧ χ z₀=1 := by
    obtain ⟨χ,hχ,hb,hs,hone⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) (hVo n) (isClosed_singleton (x := z₀)) (singleton_subset_iff.mpr (hV0 n))
    exact ⟨χ,hχ,hb,hs,(hone z₀).mp (mem_singleton z₀)⟩
  choose χ hχ hb hs h0 using hχ
  refine ⟨⟨χ,hχ,?_,?_,h0,?_,?_,?_⟩⟩
  · intro n
    change IsCompact (closure (support (χ n)))
    rw [hs n]
    exact hVc n
  · intro n
    simpa only [tsupport,hs n] using hVU n
  · intro n z
    exact hb n (mem_range_self z)
  · simpa only [hs] using hVm
  · intro J hJ hJU
    have him : (Subtype.val : U → ℝ×ℝ) '' ((Subtype.val : U → ℝ×ℝ) ⁻¹' J)=J := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact hx
      · intro hz
        exact ⟨⟨z,hJU hz⟩,hz,rfl⟩
    have hJ' : IsCompact ((Subtype.val : U → ℝ×ℝ) ⁻¹' J) := by
      apply (Topology.IsEmbedding.subtypeVal.isCompact_iff
        (s := (Subtype.val : U → ℝ×ℝ) ⁻¹' J)).mpr
      rw [him]
      exact hJ
    obtain ⟨m,hm⟩ := K.exists_superset_of_isCompact hJ'
    filter_upwards [eventually_ge_atTop (m+1)] with n hn
    intro z hz
    rw [hs n]
    exact ⟨⟨z,hJU hz⟩,K.subset_interior (by omega) (hm hz),rfl⟩

end SLEExactGauge

end

end OAI
