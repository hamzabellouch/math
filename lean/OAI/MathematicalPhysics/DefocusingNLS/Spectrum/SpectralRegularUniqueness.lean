import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularState
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFiniteUniqueness

namespace OAI

/-! Uniqueness of the regular four-component equation on an annulus away from zero. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

private theorem fourTerm_bound (k A B c u v w : ℂ) (M : ℝ)
    (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ‖-k*u+A*v+B*w-c*v‖ ≤ (‖k‖+‖A‖+‖B‖+‖c‖)*M := by
  calc
    _ ≤ (‖-k*u‖+‖A*v‖+‖B*w‖)+‖c*v‖ :=
      (norm_sub_le _ _).trans (add_le_add norm_add₃_le le_rfl)
    _ = ‖k‖*‖u‖+‖A‖*‖v‖+‖B‖*‖w‖+‖c‖*‖v‖ := by simp only [norm_mul,norm_neg]
    _ ≤ ‖k‖*M+‖A‖*M+‖B‖*M+‖c‖*M := by gcongr
    _ = _ := by ring

noncomputable def spectralRegularFieldBound (d : ℕ) (A B cp cm : ℂ) (r : ℝ) : ℝ :=
  1+‖(d : ℂ)/(r : ℂ)+Complex.I*(r : ℂ)/2‖+
    ‖(d : ℂ)/(r : ℂ)-Complex.I*(r : ℂ)/2‖+‖A‖+‖B‖+‖cp‖+‖cm‖

theorem spectralRegularField_norm (d : ℕ) (A B cp cm : ℂ) (r : ℝ) (Z : E₄) :
    ‖spectralRegularField d A B cp cm r Z‖ ≤ spectralRegularFieldBound d A B cp cm r*‖Z‖ := by
  have hpv := (norm_fst_le Z.1).trans (norm_fst_le Z)
  have hpd := (norm_snd_le Z.1).trans (norm_fst_le Z)
  have hmv := (norm_fst_le Z.2).trans (norm_snd_le Z)
  have hmd := (norm_snd_le Z.2).trans (norm_snd_le Z)
  have hp := fourTerm_bound ((d : ℂ)/(r : ℂ)+Complex.I*(r : ℂ)/2)
    A B cp Z.1.2 Z.1.1 Z.2.1 ‖Z‖ hpd hpv hmv
  have hm := fourTerm_bound ((d : ℂ)/(r : ℂ)-Complex.I*(r : ℂ)/2)
    (star A) (star B) cm Z.2.2 Z.2.1 Z.1.1 ‖Z‖ hmd hmv hpv
  simp only [norm_star] at hm
  have hb : 1 ≤ spectralRegularFieldBound d A B cp cm r := by
    unfold spectralRegularFieldBound
    linarith [norm_nonneg ((d : ℂ)/(r : ℂ)+Complex.I*(r : ℂ)/2),
      norm_nonneg ((d : ℂ)/(r : ℂ)-Complex.I*(r : ℂ)/2),
      norm_nonneg A,norm_nonneg B,norm_nonneg cp,norm_nonneg cm]
  apply max_le <;> apply max_le
  · exact hpd.trans (le_mul_of_one_le_left (norm_nonneg Z) hb)
  · exact hp.trans (by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg Z)
      unfold spectralRegularFieldBound
      linarith [norm_nonneg ((d : ℂ)/(r : ℂ)-Complex.I*(r : ℂ)/2),norm_nonneg cm])
  · exact hmd.trans (le_mul_of_one_le_left (norm_nonneg Z) hb)
  · have he : -((d : ℂ)/(r : ℂ)-Complex.I*(r : ℂ)/2)*Z.2.2+
        star B*Z.1.1+star A*Z.2.1-cm*Z.2.1=
      -((d : ℂ)/(r : ℂ)-Complex.I*(r : ℂ)/2)*Z.2.2+
        star A*Z.2.1+star B*Z.1.1-cm*Z.2.1 := by ring
    change ‖-((d : ℂ)/(r : ℂ)-Complex.I*(r : ℂ)/2)*Z.2.2+
        star B*Z.1.1+star A*Z.2.1-cm*Z.2.1‖ ≤ _
    rw [he]
    exact hm.trans (by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg Z)
      unfold spectralRegularFieldBound
      linarith [norm_nonneg ((d : ℂ)/(r : ℂ)+Complex.I*(r : ℂ)/2),norm_nonneg cp])

theorem spectralRegularFieldBound_continuousOn (d : ℕ) (A B : ℝ →ᵇ ℂ)
    (cp cm : ℂ) (L R : ℝ) (hL : 0 < L) :
    ContinuousOn (fun r => spectralRegularFieldBound d (A r) (B r) cp cm r) (Icc L R) := by
  have hd : ContinuousOn (fun r : ℝ => (d : ℂ)/(r : ℂ)) (Icc L R) :=
    continuousOn_const.div Complex.continuous_ofReal.continuousOn (fun r hr =>
      Complex.ofReal_ne_zero.mpr (ne_of_gt (hL.trans_le hr.1)))
  have hi : ContinuousOn (fun r : ℝ => Complex.I*(r : ℂ)/2) (Icc L R) := by fun_prop
  exact ((((((continuousOn_const.add (hd.add hi).norm).add (hd.sub hi).norm).add
    A.continuous.norm.continuousOn).add B.continuous.norm.continuousOn).add
      continuousOn_const).add continuousOn_const)

theorem spectralRegular_zero_on_annulus (d : ℕ) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ)
    (Z : ℝ → E₄) (L R : ℝ) (hL : 0 < L) (hZ : ContinuousOn Z (Icc L R))
    (hD : ∀ r ∈ Icc L R, HasDerivAt Z (spectralRegularField d (A r) (B r) cp cm r (Z r)) r)
    (hz : Z R=0) (r : ℝ) (hr : r ∈ Icc L R) : Z r=0 := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc L R)).exists_bound_of_continuousOn
    (spectralRegularFieldBound_continuousOn d A B cp cm L R hL)
  apply spectral_zero_on_annulus Z (fun t => spectralRegularField d (A t) (B t) cp cm t (Z t))
    L R C hZ hD _ hz r hr
  intro t ht
  apply (spectralRegularField_norm d (A t) (B t) cp cm t (Z t)).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (le_abs_self _).trans ((by simpa only [Real.norm_eq_abs] using hC t ht))

end DefocusingNLS

end OAI
