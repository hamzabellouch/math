import Mathlib
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.DensityPrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.Survival
import OAI.Probability.LatticeSurface.Convexity.USCEnvelope
import OAI.Probability.LatticeSurface.Convexity.USCGlobal
import OAI.Probability.LatticeSurface.Convexity.USCMarginal
import OAI.Probability.LatticeSurface.Convexity.USCPrekopa
import OAI.Probability.LatticeSurface.Convexity.USCProduct
import OAI.Probability.LatticeSurface.Convexity.Unimodal
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

open Set Filter

open scoped Topology

noncomputable section

namespace Overlap

end Overlap

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace Density

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Density

namespace FacetVolume

end FacetVolume

namespace Density

open FacetVolume

end Density

namespace Density

end Density

namespace Density

lemma even_integral_left {p : ℝ → ℝ} (heven : ∀ x,p (-x)=p x) (T : ℝ) :
    (∫ x in Iic (-T),p x)=∫ x in Ici T,p x := by
  rw [← integral_indicator measurableSet_Iic,← integral_indicator measurableSet_Ici]
  rw [← integral_neg_eq_self ((Iic (-T)).indicator p) volume]
  apply integral_congr_ae
  exact Eventually.of_forall (by
    intro x
    by_cases hx : T≤x
    · have hh : -x≤ -T := neg_le_neg hx
      simp [hx,hh,heven]
    · have hh : ¬ -x≤ -T := by simpa using hx
      simp [hx,hh])

lemma even_integral {p : ℝ → ℝ} (hi : Integrable p) (heven : ∀ x,p (-x)=p x) :
    (∫ x,p x)=2*(∫ x in Ici 0,p x) := by
  have h := integral_add_compl measurableSet_Ici hi (s:=Ici (0:ℝ))
  rw [compl_Ici,← integral_Iic_eq_integral_Iio] at h
  have he := even_integral_left heven 0
  simp only [neg_zero] at he
  rw [he] at h
  linarith

lemma even_tail {p : ℝ → ℝ} (hi : Integrable p) (heven : ∀ x,p (-x)=p x)
    {T : ℝ} (hT : 0<T) :
    (∫ x in {x | T≤|x|},p x)=2*(∫ x in Ici T,p x) := by
  have hset : {x : ℝ | T≤|x|}=Iic (-T)∪Ici T := by
    ext x
    simp only [mem_ofPred_eq,mem_union,mem_Iic,mem_Ici,le_abs]
    constructor
    · rintro (h|h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h|h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hd : Disjoint (Iic (-T)) (Ici T) := Set.disjoint_left.mpr (by
    intro point hleft hright
    linarith [mem_Iic.mp hleft, mem_Ici.mp hright])
  rw [hset,setIntegral_union hd measurableSet_Ici hi.integrableOn hi.integrableOn,even_integral_left heven]
  ring

lemma integral_shift_Ici (p : ℝ → ℝ) (T : ℝ) :
    (∫ r in Ici (0:ℝ),p (r+T))=∫ r in Ici T,p r := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) T).setIntegral_preimage_emb
    (Homeomorph.addRight T).measurableEmbedding p (Ici T)
  have he : (fun x : ℝ => x+T) ⁻¹' Ici T=Ici 0 := by
    ext x;simp only [mem_preimage,mem_Ici];constructor <;> intro h <;> linarith
  rw [he] at h
  exact h

end Density

end
end
end

end OAI
