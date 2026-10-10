import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixCoordinates

namespace OAI

/-! # Actual quotient boxes for every remaining root subgroup -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {T : Type*} [TopologicalSpace T]

def timeParam (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n)
    (z : (UpperRootTransverse n × T) × c.Time) : X n :=
  C.quotientParam g (z.1.1, (z.1.2, c.remainingWordHomeomorph hP hfinal z.2))

lemma timeParam_eq_action (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n)
    (z : (UpperRootTransverse n × T) × c.Time) :
    C.timeParam c hP hfinal g z =
      rightAction (Quotient.mk _ ((g * z.1.1.val) * C.base z.1.2)) (c.word z.2) :=
  C.quotientParam_eq_action g z.1.1 z.1.2 _

theorem timeParam_localHomeomorph (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n) :
    IsLocalHomeomorph (C.timeParam c hP hfinal g) := by
  let E := (Homeomorph.prodAssoc (UpperRootTransverse n) T c.Time).trans
    ((Homeomorph.refl (UpperRootTransverse n)).prodCongr
      ((Homeomorph.refl T).prodCongr (c.remainingWordHomeomorph hP hfinal)))
  exact (C.quotientParam_localHomeomorph g).comp E.isLocalHomeomorph

end RootPrefixCoordinates

structure RootPrefixBox {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n) where
  transverse : Set (UpperRootTransverse n × T)
  time : Set c.Time
  transverse_open : IsOpen transverse
  time_open : IsOpen time
  embedding : Topology.IsOpenEmbedding
    ((transverse ×ˢ time).domRestrict (C.timeParam c hP hfinal g))

theorem exists_rootPrefixBox_at_coordinates {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n)
    (z : (UpperRootTransverse n × T) × c.Time) :
    ∃ B : RootPrefixBox C c hP hfinal g, z ∈ B.transverse ×ˢ B.time := by
  obtain ⟨U,hUz,hU⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp
    (C.timeParam_localHomeomorph c hP hfinal g) z
  obtain ⟨V,W,hVo,hVz,hWo,hWz,hsub⟩ := mem_nhds_prod_iff'.mp hUz
  have he := hU.comp (Topology.IsOpenEmbedding.inclusion hsub
    ((hVo.prod hWo).preimage continuous_subtype_val))
  exact ⟨⟨V,W,hVo,hWo,he⟩,hVz,hWz⟩

namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
  {C : RootPrefixCoordinates n P T} {c : EliminationChain P D}
  {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

abbrev domain (B : RootPrefixBox C c hP hfinal g) := B.transverse ×ˢ B.time
abbrev param (B : RootPrefixBox C c hP hfinal g) :=
  B.domain.domRestrict (C.timeParam c hP hfinal g)
def range (B : RootPrefixBox C c hP hfinal g) := Set.range B.param

omit [MeasurableSpace T] [BorelSpace T] in
lemma range_open (B : RootPrefixBox C c hP hfinal g) : IsOpen B.range := B.embedding.isOpen_range

def coordinateMeasure (B : RootPrefixBox C c hP hfinal g) (μ : Measure (X n)) :
    Measure ((UpperRootTransverse n × T) × c.Time) :=
  (Measure.comap B.param μ).map Subtype.val

instance coordinateMeasure_finite (B : RootPrefixBox C c hP hfinal g) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsFiniteMeasure (B.coordinateMeasure μ) := by
  have he := B.embedding.measurableEmbedding
  have : IsFiniteMeasure (Measure.comap B.param μ) := ⟨by
    rw [he.comap_apply]
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) (measure_lt_top μ univ)⟩
  unfold coordinateMeasure
  infer_instance

lemma map_coordinateMeasure (B : RootPrefixBox C c hP hfinal g) (μ : Measure (X n)) :
    (B.coordinateMeasure μ).map (C.timeParam c hP hfinal g) = μ.restrict B.range := by
  rw [coordinateMeasure,Measure.map_map]
  · exact B.embedding.measurableEmbedding.map_comap μ
  · exact (C.timeParam_localHomeomorph c hP hfinal g).continuous.measurable
  · exact measurable_subtype_coe

def conditionalKernel (B : RootPrefixBox C c hP hfinal g) (μ : Measure (X n))
    [IsFiniteMeasure μ] : Kernel (UpperRootTransverse n × T) c.Time :=
  (B.coordinateMeasure μ).condKernel

instance conditionalKernel_markov (B : RootPrefixBox C c hP hfinal g) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsMarkovKernel (B.conditionalKernel μ) := by
  unfold conditionalKernel
  infer_instance

theorem disintegrate (B : RootPrefixBox C c hP hfinal g) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    Measure.map (C.timeParam c hP hfinal g)
      ((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ) = μ.restrict B.range := by
  rw [conditionalKernel,Measure.disintegrate]
  exact B.map_coordinateMeasure μ

end RootPrefixBox
end DukePrimeDegree

end

end OAI
