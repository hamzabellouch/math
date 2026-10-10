import OAI.Analysis.AncientFlat.Evolution.InitialContinuation
import OAI.Analysis.AncientFlat.Evolution.InitialCover

namespace OAI
noncomputable section
open Set Filter
namespace ParabolicInitial
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma initial_window_maps {h : ℝ} (p0 : V × ℝ) (hp0 : p0∈openSlab 1 h) :
    MapsTo (window p0 (1/4)) (cylinder 2) (initialStrip h) := by
  intro p hp
  refine ⟨?_,?_,?_⟩
  · change ‖p0.1+(1/4:ℝ) • p.1‖<3/2
    apply (norm_add_le _ _).trans_lt
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/4)]
    nlinarith [hp0.1,hp.1]
  · change (-1/4:ℝ)<p0.2+(1/4:ℝ)^4*p.2
    have ht := hp.2.1
    norm_num at ht
    nlinarith [hp0.2.1]
  · change p0.2+(1/4:ℝ)^4*p.2<h
    nlinarith [hp0.2.2,hp.2.2]
omit [InnerProductSpace ℝ V] in
lemma initialStrip_subset_closed (h : ℝ) : (initialStrip h : Set (V × ℝ))⊆initialClosedStrip h := by
  intro p hp
  exact ⟨hp.1,by linarith [hp.2.1],hp.2.2.le⟩
end ParabolicInitial

end

end OAI
