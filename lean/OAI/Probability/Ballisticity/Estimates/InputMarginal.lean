import Mathlib
import OAI.Probability.Ballisticity.Estimates.LocalStoppedSplice
import OAI.Probability.Ballisticity.Entropy.AnchorEntropy

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def currentInput {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ)
    (X : EpisodeInput e) : (Environment d × (ℕ → HorizontalSpace e)) × LocalUpperField e :=
  ((X.1.1,fun a => X.1.2 (i,a)),X.2 (i,m))

lemma currentInput_measurable {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) :
    Measurable (currentInput e i m) := by
  exact ((measurable_fst.comp measurable_fst).prodMk
    (Measurable.of_eval fun a => (measurable_pi_apply (i,a)).comp
      (measurable_snd.comp measurable_fst))).prodMk
        ((measurable_pi_apply (i,m)).comp measurable_snd)

theorem episodeInputLaw_current {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (i : ℤ) (m : ℕ) :
    (episodeInputLaw e ν Q t ht).map (currentInput e i m) =
      (Q.compProd (currentAnchorKernel e (fun ω => t ω i) (ht i))).prod
        (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)) := by
  let f : EpisodeAnchors e → ℕ → HorizontalSpace e := fun U a => U (i,a)
  have hf : Measurable f := Measurable.of_eval fun a => measurable_pi_apply (i,a)
  have hK : (globalEpisodeAnchors e t ht).map f =
      currentAnchorKernel e (fun ω => t ω i) (ht i) := by
    ext ω : 1
    rw [Kernel.map_apply _ hf]
    exact globalEpisodeAnchors_current e t ht ω i
  have hπ : (episodeAuxiliaryLaw e ν).map (fun V => V (i,m)) =
      Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν) := by
    exact Measure.infinitePi_map_eval _ (i,m)
  change ((Q.compProd (globalEpisodeAnchors e t ht)).prod (episodeAuxiliaryLaw e ν)).map
    (Prod.map (Prod.map id f) (fun V => V (i,m))) = _
  rw [← Measure.map_prod_map _ _ (measurable_id.prodMap hf) (measurable_pi_apply (i,m)),
    ← Measure.compProd_map hf,hK,hπ]

end DirectionalTransience

end

end OAI
