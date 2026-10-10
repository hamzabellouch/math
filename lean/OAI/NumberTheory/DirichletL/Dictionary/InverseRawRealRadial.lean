import OAI.NumberTheory.DirichletL.Dictionary.InverseRawRadial

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawRealRadial
open InverseInitialConjugateEnergy ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

theorem exists_real_raw_radial_majorant:
    ∃Φ:𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x,(Φ x).im=0) ∧
      (∀x∈Set.Icc (0:ℝ) 1,Φ x=1):=by
  have hsub:Set.Icc (0:ℝ) 1⊆Set.Ioo (-1) 2:=by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v:ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv:ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf:ContDiff ℝ ∞ f).pow 2)
  have hsupp:Function.support v⊆Set.Icc (-1) 2:=by
    intro x hx
    have hn:x∈Function.support f:=by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  have hvc:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x
    exact Complex.ofReal_im _
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

theorem smoothedEnergy_eq_complex_norm (Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hreal:∀x,(Φ x).im=0)
    (H:ℝ)(hH:0<H)(f:O→ℂ):
    smoothedEnergy Φ H f=
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/H)*(‖f u‖^2:ℝ)‖:=by
  rw [real_smoothed_sum_eq Φ (fun x _=>hreal x) hH,
    Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (smoothedEnergy_nonneg Φ (fun x _=>hΦ x) hH f)]

end SevenEighths.DetectorDictionaryInverseRawRealRadial

end

end OAI
