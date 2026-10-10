import OAI.Analysis.LipschitzHilbert.Trees.LineSamplingL2Path
import OAI.Analysis.LipschitzHilbert.Estimates.StrongOperatorDerivative

namespace OAI

/-! The actual strong L2 conjugation derivative. -/
noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
  (hc : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u)
  (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

theorem lineSampling_conjugation_tangent (m : SchwartzMap ℝ ℂ)
    (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) :
    lineSamplingTangent u hu hc hcompact t ht
        (lineSchwartzProjection m 1 (by norm_num)
          (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f))+
      lineSamplingSchwartz u hu hc hcompact t ht
        (lineSchwartzProjection m 1 (by norm_num)
          (lineSamplingInverseTangent u hu hc hcompact B hB hb t ht f))=
      lineSamplingSchwartz u hu hc hcompact t ht
        (lineSchwartzCommutator m (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht)
          (schwartzDerivative 1 (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f))) := by
  rw [lineSamplingTangent_eq u hu hc hcompact B hB hb,lineSchwartzProjection_derivative]
  let p := lineSchwartzProduct (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht)
    (schwartzDerivative 1 (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f))
  have hn : lineSchwartzProjection m 1 (by norm_num) (-p)=
      -lineSchwartzProjection m 1 (by norm_num) p :=
    map_neg (lineSchwartzProjectionLM m 1 (by norm_num)) p
  change _+lineSamplingSchwartz u hu hc hcompact t ht
    (lineSchwartzProjection m 1 (by norm_num) (-p))=_
  rw [hn,←map_add]
  rfl

theorem lineConjugation_L2_hasDerivAt (m : SchwartzMap ℝ ℂ)
    (t : ℝ) (ht : |t|<1/2) (f : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun s => lineSamplingL2Path u hu s
      (lineL2Projection m 1 (by norm_num)
        (lineSamplingInverseL2Path u hu B hB hb s (f.toLp 2 volume))))
      ((lineSamplingSchwartz u hu hc hcompact t ht.le
        (lineSchwartzCommutator m (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht.le)
          (schwartzDerivative 1 (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht.le f)))).toLp 2 volume) t := by
  let I := lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht.le f
  let q0 := lineSchwartzProjection m 1 (by norm_num) I
  let q' := lineSchwartzProjection m 1 (by norm_num)
    (lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f)
  let Q := fun s => lineL2Projection m 1 (by norm_num)
    (lineSamplingInverseL2Path u hu B hB hb s (f.toLp 2 volume))
  have hI : HasDerivAt (fun s => lineSamplingInverseL2Path u hu B hB hb s (f.toLp 2 volume))
      ((lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f).toLp 2 volume) t := by
    simpa only [lineSamplingInverseL2Path_onSchwartz u hu hc hcompact B hB hb] using
      lineSamplingInversePath_L2_hasDerivAt u hu hc hcompact B hB hb t ht f
  have hQ : HasDerivAt Q (q'.toLp 2 volume) t := by
    have hh := ((lineL2Projection m 1 (by norm_num)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hI
    change HasDerivAt Q (lineL2Projection m 1 (by norm_num)
      ((lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f).toLp 2 volume)) t at hh
    rw [lineL2Projection_onSchwartz] at hh
    exact hh
  have hQt : Q t=q0.toLp 2 volume := by
    simp only [Q,lineSamplingInverseL2Path_onSchwartz u hu hc hcompact B hB hb,
      lineSamplingInversePath,dite_eq_left ht.le,lineL2Projection_onSchwartz,q0,I]
  have hfixed : HasDerivAt (fun s => lineSamplingL2Path u hu s (Q t))
      ((lineSamplingTangent u hu hc hcompact t ht.le q0).toLp 2 volume) t := by
    rw [hQt]
    simpa only [lineSamplingL2Path_onSchwartz u hu hc hcompact] using
      lineSamplingPath_L2_hasDerivAt u hu hc hcompact t ht q0
  have hcont : ContinuousAt (fun s => lineSamplingL2Path u hu s (q'.toLp 2 volume)) t := by
    simpa only [lineSamplingL2Path_onSchwartz u hu hc hcompact] using
      (lineSamplingPath_L2_hasDerivAt u hu hc hcompact t ht q').continuousAt
  have hmain := hasDerivAt_strong_operator_apply
    (fun s => (lineSamplingL2Path u hu s).restrictScalars ℝ) Q t
    (q'.toLp 2 volume) ((lineSamplingTangent u hu hc hcompact t ht.le q0).toLp 2 volume) 2
    (Eventually.of_forall fun s => by
      rw [ContinuousLinearMap.norm_restrictScalars]
      exact lineSamplingL2Path_bound u hu s) hQ hcont hfixed
  change HasDerivAt (fun s => lineSamplingL2Path u hu s (Q s))
    ((lineSamplingTangent u hu hc hcompact t ht.le q0).toLp 2 volume+
      lineSamplingL2Path u hu t (q'.toLp 2 volume)) t at hmain
  have he : (lineSamplingTangent u hu hc hcompact t ht.le q0).toLp 2 volume+
      lineSamplingL2Path u hu t (q'.toLp 2 volume)=
      (lineSamplingSchwartz u hu hc hcompact t ht.le
        (lineSchwartzCommutator m (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht.le)
          (schwartzDerivative 1 I))).toLp 2 volume := by
    rw [lineSamplingL2Path_onSchwartz u hu hc hcompact]
    simp only [lineSamplingPath,dite_eq_left ht.le]
    calc
      _ = (lineSamplingTangent u hu hc hcompact t ht.le q0+
          lineSamplingSchwartz u hu hc hcompact t ht.le q').toLp 2 volume :=
        (map_add (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ _).symm
      _ = _ := congrArg (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume)
        (lineSampling_conjugation_tangent u hu hc hcompact B hB hb m t ht.le f)
  rw [he] at hmain
  exact hmain

end LipschitzHilbert.PacketRepresentation

end

end OAI
