import OAI.Geometry.SurfaceImmersion.Primitive.VelocityNormalNonvanishing
import OAI.Geometry.Immersion.ClosedSurface.NormalJets
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Uniform normal nondegeneracy from the three bounded derivatives of a
primitive ansatz. No bound on its rapidly oscillating xx derivative is used. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

abbrev NormalTriple := Fin 3 → Vec

def tripleNormal (J : NormalTriple) : Vec := realNormalPart (J 0) (J 1) (J 2)

lemma contDiffAt_tripleNormal {J : NormalTriple}
    (hJ : gramDet (J 0) (J 1) ≠ 0) : ContDiffAt ℝ ∞ tripleNormal J := by
  have hslot (i : Fin 3) : ContDiffAt ℝ ∞ (fun K : NormalTriple => K i) J :=
    (ContinuousLinearMap.proj i : NormalTriple →L[ℝ] Vec).contDiff.contDiffAt
  exact contDiffAt_realNormalPart (hslot 0) (hslot 1) (hslot 2) hJ

def normalTripleNeighborhood (c : ℝ) : Set NormalTriple :=
  {J | gramDet (J 0) (J 1) ≠ 0 ∧ c < ‖tripleNormal J‖}

lemma isOpen_normalTripleNeighborhood (c : ℝ) : IsOpen (normalTripleNeighborhood c) := by
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hd : Continuous (fun K : NormalTriple => gramDet (K 0) (K 1)) := by
    unfold gramDet dotProduct
    fun_prop
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((contDiffAt_tripleNormal hJ.1).continuousAt.norm.eventually
      (lt_mem_nhds hJ.2))

/-- Compact leading tangent/second-derivative triples have one positive
normal margin and one perturbation radius, independent of the fast phase. -/
theorem compact_normal_triple_stability {K : Set NormalTriple}
    (hK : IsCompact K)
    (hD : ∀ J ∈ K, gramDet (J 0) (J 1) ≠ 0)
    (hN : ∀ J ∈ K, tripleNormal J ≠ 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ J ∈ K, ∀ H : NormalTriple,
      ‖H-J‖ < ε → gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖tripleNormal H‖ := by
  rcases K.eq_empty_or_nonempty with hzero | hne
  · refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    simp [hzero]
  have hc : ContinuousOn (fun J => ‖tripleNormal J‖) K :=
    fun J hJ => ((contDiffAt_tripleNormal (hD J hJ)).continuousAt.norm).continuousWithinAt
  obtain ⟨J₀,hJ₀,hmin⟩ := hK.exists_isMinOn hne hc
  let c := ‖tripleNormal J₀‖/2
  have hcpos : 0 < c := half_pos (norm_pos_iff.mpr (hN J₀ hJ₀))
  have hsub : K ⊆ normalTripleNeighborhood c := by
    intro J hJ
    exact ⟨hD J hJ,lt_of_lt_of_le (by have hh := hcpos; dsimp [c] at hh ⊢; linarith) (hmin hJ)⟩
  obtain ⟨ε,hε,he⟩ := hK.exists_thickening_subset_open
    (isOpen_normalTripleNeighborhood c) hsub
  refine ⟨ε,c,hε,hcpos,?_⟩
  intro J hJ H hHJ
  apply he
  exact Metric.mem_thickening_iff.mpr ⟨J,hJ,by simpa only [dist_eq_norm] using hHJ⟩

/-- Apply the three-derivative stability estimate to the leading velocity
geometry. It controls the actual normal component of the yy derivative. -/
theorem compact_leading_normal_stability {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) {X Y C V : E → Vec}
    (hX : ContinuousOn X K) (hY : ContinuousOn Y K)
    (hC : ContinuousOn C K) (hV : ContinuousOn V K)
    (hD : ∀ p ∈ K, gramDet (Y p) (C p) ≠ 0)
    (hYV : ∀ p ∈ K, Y p ⬝ᵥ V p = 0)
    (hCV : ∀ p ∈ K, C p ⬝ᵥ V p = 0)
    (hV0 : ∀ p ∈ K, V p ≠ 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ p ∈ K, ∀ H : NormalTriple,
      ‖H-![leadingTangent (X p) (Y p) (C p) (V p),Y p,C p]‖ < ε →
      gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖realNormalPart (H 0) (H 1) (H 2)‖ := by
  let J : E → NormalTriple := fun p =>
    ![leadingTangent (X p) (Y p) (C p) (V p),Y p,C p]
  have hT : ContinuousOn (fun p => leadingTangent (X p) (Y p) (C p) (V p)) K := by
    intro p hp
    have hn : ContinuousAt (fun q : Vec × Vec × Vec =>
        realNormalPart q.1 q.2.1 q.2.2) (Y p,C p,X p) :=
      (contDiffAt_realNormalPart (E := Vec × Vec × Vec)
        (X := fun q => q.1) (Y := fun q => q.2.1) (W := fun q => q.2.2)
        (p := (Y p,C p,X p)) (by fun_prop) (by fun_prop) (by fun_prop) (hD p hp)).continuousAt
    exact ((hX p hp).sub
      (hn.comp_continuousWithinAt (f := fun q : E => (Y q,C q,X q))
        ((hY p hp).prodMk ((hC p hp).prodMk (hX p hp))))).add (hV p hp)

  have hJ : ContinuousOn J K := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact hT
    · exact hY
    · exact hC
  obtain ⟨ε,c,hε,hc,hh⟩ := compact_normal_triple_stability (hK.image_of_continuousOn hJ)
    (by rintro _ ⟨p,hp,rfl⟩; exact (leading_normal_nondegenerate (hD p hp) (hYV p hp) (hCV p hp) (hV0 p hp)).1)
    (by rintro _ ⟨p,hp,rfl⟩; exact (leading_normal_nondegenerate (hD p hp) (hYV p hp) (hCV p hp) (hV0 p hp)).2)
  exact ⟨ε,c,hε,hc,fun p hp H hH => hh (J p) (mem_image_of_mem J hp) H hH⟩

end ClosedSurfaceR4.VelocityFrame

end

end OAI
