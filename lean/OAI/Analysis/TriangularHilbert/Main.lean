import OAI.Analysis.TriangularHilbert.TruncationCoordinates

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Heat Filter
open scoped ENNReal
noncomputable section

lemma maximal_eq_cyclicMax_ae (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    maximal F G =ᵐ[volume] (fun z => cyclicMax (cyclicB F) (cyclicC G) (-z)) := by
  filter_upwards [measurePreserving_reflect.quasiMeasurePreserving.ae
    (ae_cubicSliceGood (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG))] with z hz
  rw [maximal,ite_eq_left hz.goodPoint]
  simp_rw [truncation_eq_cyclicHard]
  exact (cyclicMax_eq_iSup hz).symm

lemma aemeasurable_maximal (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    AEMeasurable (maximal F G) volume := by
  have h := (aemeasurable_cyclicMax (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG)).comp_quasiMeasurePreserving
    measurePreserving_reflect.quasiMeasurePreserving
  exact h.congr (maximal_eq_cyclicMax_ae F G hF hG).symm

lemma maximalNorm_eq_cyclicNorm (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    maximalNorm F G = cyclicNorm (cyclicB F) (cyclicC G) := by
  unfold maximalNorm cyclicNorm
  congr 1
  calc
    (∫⁻ z : Plane, maximal F G z ^ ((3:ℝ)/2)) =
        ∫⁻ z : Plane, cyclicMax (cyclicB F) (cyclicC G) (-z)^((3:ℝ)/2) := by
      apply lintegral_congr_ae
      filter_upwards [maximal_eq_cyclicMax_ae F G hF hG] with z hz
      rw [hz]
    _ = _ := measurePreserving_reflect.lintegral_comp_emb (Homeomorph.neg Plane).measurableEmbedding
      (fun z => cyclicMax (cyclicB F) (cyclicC G) z^((3:ℝ)/2))

theorem main_estimate : MainEstimate := by
  refine ⟨mainConstant,fun F G hF hG => ⟨ae_goodPoint F G hF hG,aemeasurable_maximal F G hF hG,?_⟩⟩
  rw [maximalNorm_eq_cyclicNorm F G hF hG]
  simpa only [eLpNorm_cyclicB hF,eLpNorm_cyclicC hG] using
    cyclicNorm_le (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG)
end
end TriangularHilbert
end

end OAI
