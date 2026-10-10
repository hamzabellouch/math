import OAI.NumberTheory.DirichletL.Moments.FirstAnnularInput

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily

variable {ι:Type*}[Fintype ι]

def activeInput (s:Input ι):Input ι:={s with
  slots:=fun i=>(s.slots i).filter (fun I=>s.W i ((I.absNorm:ℝ)/s.P i)≠0)
  prime:=fun i I hI=>s.prime i I (Finset.mem_filter.mp hI).1
  coefficient_bound:=fun i I hI=>s.coefficient_bound i I (Finset.mem_filter.mp hI).1}

lemma original_active (s:Input ι)(R seed:Ideal HeckeFamily.O):
    original (activeInput s) R seed=(original s R seed).active:=by
  unfold original OriginalData.active
  congr 1
  funext j
  cases j <;> rfl

lemma active_volume (s:Input ι):volume (activeInput s)=volume s:=rfl

lemma active_normalized (s:Input ι)(R seed:Ideal HeckeFamily.O)(W:𝓢(ℝ,ℂ))(H:ℝ):
    normalizedGaussSource (activeInput s) R seed W H=normalizedGaussSource s R seed W H:=by
  rw [←normalized_input_coefficient,←normalized_input_coefficient,original_active]
  exact congrArg Complex.re ((original s R seed).active_gaussEnergy s.η fixedBadMask s.t (volume s) W H)

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI
