import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductMass
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRebase
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootContraction

namespace OAI

/-! # Support of the actual intrinsic product in root coordinates -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma exists_cube_subset_nhds_zero (c : EliminationChain P D)
    {U : Set c.Time} (hU : U ∈ 𝓝 c.zeroTime) :
    ∃ R : ℝ, 0 < R ∧ c.cube R ⊆ U := by
  let E := c.timeVectorHomeomorph
  have hE : E.symm 0 = c.zeroTime := by
    apply E.injective
    rw [E.apply_symm_apply]
    exact (c.timeVectorHomeomorph_zero).symm
  have hV : E.symm ⁻¹' U ∈ 𝓝 (0 : Fin c.roots.length → ℝ) := by
    apply E.symm.continuous.continuousAt.preimage_mem_nhds
    rwa [hE]
  obtain ⟨R,hR,hRU⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨R,hR,?_⟩
  intro t ht
  have hb : E t ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball,dist_pi_lt_iff hR]
    intro k
    simpa only [Real.dist_eq,Pi.zero_apply,sub_zero] using
      (c.timeVectorHomeomorph_cube R t).mp ht k
  have H := hRU hb
  simpa only [Set.mem_preimage,E.symm_apply_apply] using H

def remainingTimeProduct (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) : Measure c.Time :=
  (c.remainingIntrinsicProduct hP hf μ x).map (c.remainingWordHomeomorph hP hf).symm

lemma remainingTimeProduct_cube (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) (R : ℝ) :
    c.remainingTimeProduct hP hf μ x (c.cube R) =
      c.remainingIntrinsicProduct hP hf μ x
        (c.remainingWordHomeomorph hP hf '' c.cube R) := by
  let W := c.remainingWordHomeomorph hP hf
  rw [remainingTimeProduct,Measure.map_apply W.symm.measurable (c.cube_open R).measurableSet]
  congr 1
  ext g
  constructor
  · intro hg
    exact ⟨W.symm g,hg,W.apply_symm_apply g⟩
  · rintro ⟨t,ht,rfl⟩
    change W.symm (W t) ∈ c.cube R
    simpa only [W.symm_apply_apply] using ht

theorem ae_remainingTimeProduct_cube_pos (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ) :
    ∀ᵐ x ∂μ, ∀ R : ℝ, 0 < R →
      0 < c.remainingTimeProduct hP hf μ x (c.cube R) := by
  have hfree := ae_root_stabilizer_trivial d μ hA
  have hspec (p : ↥(allPositiveRoots (d+1) \ P)) := ae_intrinsicRootLeaf_spec
    (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ
    (hfree.mono fun _ hx => hx _ _ _)
  have hpos (p : ↥(allPositiveRoots (d+1) \ P)) := ae_intrinsicRootLeaf_ball_pos
    (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ
    (hfree.mono fun _ hx => hx _ _ _)
  filter_upwards [ae_all_iff.mpr hspec,ae_all_iff.mpr hpos] with x hx hp
  let : ∀ p : ↥(allPositiveRoots (d+1) \ P), IsLocallyFiniteMeasure
      (intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x) :=
    fun p => (hx p).1
  intro R hR
  rw [c.remainingTimeProduct_cube hP hf μ x R,remainingIntrinsicProduct,
    c.remainingProduct_cube_mass hP hf]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  have he : Ioo (-R) R = Metric.ball (0:ℝ) R := by
    ext t
    simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt,Set.mem_Ioo]
  rw [he]
  exact (hp p R hR).ne'

theorem ae_remainingTimeProduct_nhds_pos (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ) :
    ∀ᵐ x ∂μ, ∀ U ∈ 𝓝 c.zeroTime, 0 < c.remainingTimeProduct hP hf μ x U := by
  filter_upwards [ae_remainingTimeProduct_cube_pos d c hP hf μ hA] with x hx
  intro U hU
  obtain ⟨R,hR,hRU⟩ := c.exists_cube_subset_nhds_zero hU
  exact (hx R hR).trans_le (measure_mono hRU)

theorem ae_remainingTimeProduct_unit (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ x ∂μ, c.remainingTimeProduct hP hf μ x (c.cube 1)=1 := by
  simpa only [remainingTimeProduct_cube] using
    ae_remainingIntrinsicProduct_unit d c hP hf μ

end EliminationChain
end DukePrimeDegree

end

end OAI
