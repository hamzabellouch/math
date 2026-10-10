import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDuhamelEstimate
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarInitialBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralActionGronwall

namespace OAI

/-! A true solution is bounded by an explicitly constructed approximate frame.
The loss is the exponential of the integral of its scaled residual. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_perturbed_transfer
    (R E C c : ℝ) (hRE : R≤ E) (hC : 0≤ C) (hc : 0<c)
    (D U q : ℝ → ℂ × ℂ) (V e : ℝ → ℂ) (W : ℂ) (k H : ℝ → ℝ)
    (hDc : ContinuousOn D (Icc R E)) (hUc : ContinuousOn U (Icc R E))
    (hqc : ContinuousOn q (Icc R E)) (hec : ContinuousOn e (Icc R E))
    (hkc : ContinuousOn k (Icc R E)) (hHc : ContinuousOn H (Icc R E))
    (hk : ∀ t ∈ Icc R E, 0<k t) (hH : MonotoneOn H (Icc R E))
    (hW : c≤‖W‖) (hdet : ∀ t ∈ Icc R E, spectralScalarWronskian (D t) (U t)=W)
    (hD : ∀ t ∈ Ioo R E, HasDerivAt D (spectralScalarField (V t) (D t)) t)
    (hU : ∀ t ∈ Ioo R E, HasDerivAt U (spectralScalarField (V t) (U t)) t)
    (hq : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField (V t) (q t)+(0,e t*(q t).1)) t)
    (hDb : ∀ t ∈ Icc R E, spectralShellNorm (k t) (D t)≤ C*Real.exp (H t))
    (hUb : ∀ t ∈ Icc R E, spectralShellNorm (k t) (U t)≤ C*Real.exp (-H t)) :
    ∀ r ∈ Icc R E, spectralShellNorm (k r) (q r)≤
      (2*C^2/c)*spectralShellNorm (k R) (q R)*
        Real.exp (H r-H R+∫ t in R..r, (2*C^2/c)*‖e t‖/(k t)^2) := by
  let A := 2*C^2/c
  let X := fun r => spectralShellNorm (k r) (q r)
  let g := fun r => A*‖e r‖/(k r)^2
  have hA : 0≤ A := by dsimp only [A]; positivity
  have hX : ContinuousOn X (Icc R E) :=
    (hkc.mul hqc.fst.norm).add ((hkc.inv₀ (fun t ht => (hk t ht).ne')).mul hqc.snd.norm)
  have hg : ContinuousOn g (Icc R E) :=
    (continuousOn_const.mul hec.norm).div (hkc.pow 2) (fun t ht => pow_ne_zero _ (hk t ht).ne')
  have hg0 (t : ℝ) (ht : t ∈ Icc R E) : 0≤ g t := by dsimp only [g]; positivity
  have hW0 : W≠0 := norm_pos_iff.mp (hc.trans_le hW)
  have hRI : R ∈ Icc R E := ⟨le_rfl,hRE⟩
  have hbound (r : ℝ) (hr : r ∈ Icc R E) :
      X r≤ (A*X R)*Real.exp (H r-H R)+
        ∫ t in R..r, g t*Real.exp ((H r-H R)-(H t-H R))*X t := by
    have hs : Icc R r ⊆ Icc R E := Icc_subset_Icc le_rfl hr.2
    have hi := spectralScalarInitialTerm_bound D U W (q R)
      (k r) (k R) C c (H r) (H R) r R (hk r hr).le (hk R hRI) hC hc hW
      (hDb r hr) (hDb R hRI) (hUb r hr) (hUb R hRI)
    rw [abs_of_nonneg (sub_nonneg.mpr (hH hRI hr hr.1))] at hi
    have hker (t : ℝ) (ht : t ∈ Icc R r) :
        spectralShellNorm (k r) (spectralScalarTransferKernel D U W r t)≤
          A/k t*Real.exp (H r-H t) := by
      have hh := spectralScalarTransferKernel_bound D U W (k r) (k t) C c (H r) (H t)
        r t (hk r hr).le (hk t (hs ht)) hC hc hW
        (hDb r hr) (hDb t (hs ht)) (hUb r hr) (hUb t (hs ht))
      rw [abs_of_nonneg (sub_nonneg.mpr (hH (hs ht) hr ht.2))] at hh
      convert hh using 1
      dsimp only [A]
      ring
    have hd := spectralScalarDuhamelIntegral_residual_bound R r A hr.1 hA D U q W e k H
      (hDc.mono hs) (hUc.mono hs) (hqc.mono hs) (hec.mono hs)
      (hkc.mono hs) (hHc.mono hs) (fun t ht => hk t (hs ht)) hker
    have heq := spectralScalarDuhamel_representation R E D U q V
      (fun t => e t*(q t).1) W hDc hUc hqc (hec.mul hqc.fst) hW0 hdet hD hU hq r hr
    calc
      X r ≤ spectralShellNorm (k r)
          ((spectralScalarWronskian (q R) (U R)/W) • D r+
            (spectralScalarWronskian (D R) (q R)/W) • U r)+
          spectralShellNorm (k r) (spectralScalarDuhamelIntegral R D U W (fun t => e t*(q t).1) r) := by
        change spectralShellNorm (k r) (q r)≤ _
        rw [heq]
        exact spectralShellNorm_add_le (k r) (hk r hr).le _ _
      _ ≤ _ := by
        have hdelta (t : ℝ) : (H r-H R)-(H t-H R)=H r-H t := by ring
        simpa only [A,g,X,hdelta,mul_assoc,mul_left_comm,mul_comm] using add_le_add hi hd
  exact spectral_action_gronwall R E (A*X R) hRE X g (fun r => H r-H R)
    hX hg (hHc.sub continuousOn_const) hg0 hbound

end DefocusingNLS

end OAI
