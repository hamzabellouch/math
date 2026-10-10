import Mathlib
import OAI.Probability.SLELocalization.CommonClocks

namespace OAI


/-! Conformal localization and Loewner Cocycle estimates. -/

section
noncomputable section
open Set Filter
open scoped Topology
namespace SLEExactGauge
open LoewnerCutoff

theorem loewner_inverse_cocycle {U : ℝ → ℝ} {γ η : ℝ → ℂ}
    {g f G F : ℝ → ℂ → ℂ} (h : IsLoewnerTraceUsing U γ g f)
    {T : ℝ} (hT : 0 ≤ T)
    (hnew : IsLoewnerTraceUsing (fun t => U (T+t)-U T) η G F)
    {s : ℝ} (hs : 0 ≤ s) {w : ℂ} (hw : w ∈ halfPlane) :
    f (T+s) (w+(U T:ℂ)) = f T (F s w+(U T:ℂ)) := by
  let x := f (T+s) (w+(U T:ℂ))
  let y := F s w
  have hsum : 0 ≤ T+s := add_nonneg hT hs
  have hw' : w+(U T:ℂ) ∈ halfPlane := by simpa [halfPlane] using hw
  have hx : x ∈ localizationDomain γ (T+s) := h.2.2.2.2.2.2.2.2.1 (T+s) hsum hw'
  have hy : y ∈ localizationDomain η s := hnew.2.2.2.2.2.2.2.2.1 s hs hw
  have hfin : g (T+s) x = w+(U T:ℂ) := h.2.2.2.2.2.2.2.2.2.2.1 (T+s) hsum _ hw'
  have hnewfin : G s y = w := hnew.2.2.2.2.2.2.2.2.2.2.1 s hs _ hw
  have hxl (t : ℝ) (ht : t ∈ Icc 0 s) : w.im ≤ (g (T+t) x).im := by
    have HH := h.height_antitone hsum hx
      ⟨add_nonneg hT ht.1,by linarith [ht.2]⟩ ⟨hsum,le_rfl⟩
      (by linarith [ht.2])
    simpa only [hfin,Complex.add_im,Complex.ofReal_im,add_zero] using HH
  have hyl (t : ℝ) (ht : t ∈ Icc 0 s) : w.im ≤ (G t y).im := by
    simpa only [hnewfin] using hnew.height_antitone hs hy ht ⟨hs,le_rfl⟩ ht.2
  have hc : ContinuousOn (fun t => g (T+t) x-(U T:ℂ)) (Icc 0 s) :=
    ((h.continuous_eval hsum hx).comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => ⟨add_nonneg hT ht.1,by change T+t ≤ T+s; linarith [ht.2]⟩)).sub continuousOn_const
  have hd (t : ℝ) (ht : t ∈ Ioc 0 s) :
      HasDerivWithinAt (fun t => g (T+t) x-(U T:ℂ))
        (velocity w.im (U (T+t)-U T) (g (T+t) x-(U T:ℂ))) (Iic t) t := by
    rw [velocity_eq (by simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using hxl t ⟨ht.1.le,ht.2⟩)]
    have HH := ((h.2.2.2.2.2.2.2.2.2.2.2.2.1 (T+t) (by linarith [ht.1]) x
      (survivingDomain_mono (by linarith [ht.2]) hx)).scomp t
      ((hasDerivAt_id t).const_add T)).sub_const (U T:ℂ)
    have heq : g (T+t) x-(U T:ℂ)-((U (T+t)-U T:ℝ):ℂ) =
        g (T+t) x-(U (T+t):ℂ) := by rw [Complex.ofReal_sub]; ring
    rw [heq]
    simpa only [one_smul,Function.comp_def,id_eq] using HH.hasDerivWithinAt
  have hdnew (t : ℝ) (ht : t ∈ Ioc 0 s) :
      HasDerivWithinAt (fun t => G t y)
        (velocity w.im (U (T+t)-U T) (G t y)) (Iic t) t := by
    rw [velocity_eq (hyl t ⟨ht.1.le,ht.2⟩)]
    exact (hnew.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht.1 y
      (survivingDomain_mono ht.2 hy)).hasDerivWithinAt
  have he : EqOn (fun t => g (T+t) x-(U T:ℂ)) (fun t => G t y) (Icc 0 s) :=
    ODE_solution_unique_of_mem_Icc_left (s := fun _ => univ)
      (fun t _ => (velocity_lipschitz hw (U (T+t)-U T)).lipschitzOnWith)
      hc hd (fun _ _ => mem_univ _)
      (hnew.continuous_eval hs hy) hdnew (fun _ _ => mem_univ _)
      (by simp only [hfin,hnewfin,add_sub_cancel_right])
  have he0 := he ⟨le_rfl,hs⟩
  dsimp only at he0
  rw [add_zero,hnew.initial y hy.1.1] at he0
  have hearg : g T x = y+(U T:ℂ) := by rw [← he0]; ring
  change x = f T (y+(U T:ℂ))
  rw [← hearg]
  exact (h.2.2.2.2.2.2.2.2.2.1 T hT x
    (survivingDomain_mono (le_add_of_nonneg_right hs) hx)).symm

end SLEExactGauge

end

end

/-! Conformal localization and Loewner Trace Composition estimates. -/

noncomputable section
open Set Filter
open scoped Topology OnePoint
namespace SLEExactGauge

theorem loewner_trace_composition_of_extension {U : ℝ → ℝ} {γ η : ℝ → ℂ}
    {g f G F : ℝ → ℂ → ℂ} (h : IsLoewnerTraceUsing U γ g f)
    {T : ℝ} (hT : 0 ≤ T)
    (hnew : IsLoewnerTraceUsing (fun t => U (T+t)-U T) η G F)
    (Fbar : ℂ → OnePoint ℂ)
    (hext : ∀ w ∈ halfPlane, Fbar w = (f T w : OnePoint ℂ))
    (hc : ContinuousOn Fbar {w : ℂ | 0 ≤ w.im})
    {s : ℝ} (hs : 0 ≤ s) :
    Fbar (η s+(U T:ℂ)) = (γ (T+s) : OnePoint ℂ) := by
  let V := U (T+s)-U T
  let a : ℝ → ℂ := fun y => (V:ℂ)+(y:ℂ)*Complex.I
  have ha (y : ℝ) (hy : 0 < y) : a y ∈ halfPlane := by
    simpa [a,halfPlane] using hy
  have hfa (y : ℝ) (hy : 0 < y) : F s (a y)+(U T:ℂ) ∈ halfPlane := by
    have hh := (hnew.2.2.2.2.2.2.2.2.1 s hs (ha y hy)).1.1
    simpa only [halfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero] using hh
  have hlim : Tendsto (fun y => F s (a y)+(U T:ℂ)) (𝓝[>] (0:ℝ))
      (𝓝[{w : ℂ | 0 ≤ w.im}] (η s+(U T:ℂ))) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_,?_⟩
    · exact (hnew.2.2.2.2.2.2.2.2.2.2.2.2.2 s hs).add_const (U T:ℂ)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hfa y hy).le
  have hp : 0 ≤ (η s+(U T:ℂ)).im := by
    simpa only [Complex.add_im,Complex.ofReal_im,add_zero] using hnew.2.2.1 s hs
  have hleft := ((hc _ hp).tendsto).comp hlim
  have hright : Tendsto (fun y : ℝ => (f (T+s)
      ((U (T+s):ℂ)+(y:ℂ)*Complex.I) : OnePoint ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 (γ (T+s) : OnePoint ℂ)) :=
    OnePoint.continuous_coe.continuousAt.tendsto.comp
      (h.2.2.2.2.2.2.2.2.2.2.2.2.2 (T+s) (add_nonneg hT hs))
  have heq : (fun y : ℝ => Fbar (F s (a y)+(U T:ℂ))) =ᶠ[𝓝[>] (0:ℝ)]
      (fun y : ℝ => (f (T+s) ((U (T+s):ℂ)+(y:ℂ)*Complex.I) : OnePoint ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [hext _ (hfa y hy),← loewner_inverse_cocycle h hT hnew hs (ha y hy)]
    congr 2
    dsimp [a,V]
    rw [Complex.ofReal_sub]
    ring
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

end SLEExactGauge

end

end OAI
