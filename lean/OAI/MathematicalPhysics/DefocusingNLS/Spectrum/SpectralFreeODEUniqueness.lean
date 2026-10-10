import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeFluxGauge
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedStateExtension

namespace OAI

/-! Backward propagation of the free physical equation from its outer trace. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralFreePhysicalPairField (b ζ η : ℂ) (r : ℝ) (Z : E₄) : E₄ :=
  (spectralFreePhysicalField 1 b ζ η r Z.1,spectralFreePhysicalField (-1) b ζ η r Z.2)

theorem spectralFreePhysicalPairField_eq (b ζ η : ℂ) (r : ℝ) (Z : E₄) :
    spectralFreePhysicalPairField b ζ η r Z=
      spectralRegularField 11 0 0 (b+Complex.I*ζ-η/(r : ℂ)^2)
        (b-Complex.I*ζ-η/(r : ℂ)^2) r Z := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [spectralFreePhysicalPairField,spectralFreePhysicalField,spectralRegularField]
  ring

theorem spectralFreePhysicalPairField_sub (b ζ η : ℂ) (r : ℝ) (X Y : E₄) :
    spectralFreePhysicalPairField b ζ η r (X-Y)=
      spectralFreePhysicalPairField b ζ η r X-spectralFreePhysicalPairField b ζ η r Y := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [spectralFreePhysicalPairField,spectralFreePhysicalField,Prod.fst_sub,Prod.snd_sub] <;> ring

theorem spectralFree_zero_on_annulus (b ζ η : ℂ) (Z : ℝ → E₄) (L R : ℝ)
    (hL : 0 < L) (hLR : L < R) (hZ : ContinuousOn Z (Icc L R))
    (hD : ∀ r ∈ Ioo L R, HasDerivAt Z (spectralFreePhysicalPairField b ζ η r (Z r)) r)
    (hz : Z R=0) (r : ℝ) (hr : r ∈ Icc L R) : Z r=0 := by
  have hn (t : ℝ) (ht : t ∈ Icc L R) : (t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hL.trans_le ht.1).ne'
  have ht : ContinuousOn (fun t : ℝ => (t : ℂ)) (Icc L R) := Complex.continuous_ofReal.continuousOn
  have hk : ContinuousOn (fun t : ℝ => 11/(t : ℂ)) (Icc L R) := continuousOn_const.div ht hn
  have hi : ContinuousOn (fun t : ℝ => Complex.I*(t : ℂ)/2) (Icc L R) := by fun_prop
  have he : ContinuousOn (fun t : ℝ => η/(t : ℂ)^2) (Icc L R) :=
    continuousOn_const.div (ht.pow 2) (fun t ht => pow_ne_zero 2 (hn t ht))
  have hp : ContinuousOn (fun t : ℝ => b+Complex.I*ζ-η/(t : ℂ)^2) (Icc L R) :=
    continuousOn_const.sub he
  have hm : ContinuousOn (fun t : ℝ => b-Complex.I*ζ-η/(t : ℂ)^2) (Icc L R) :=
    continuousOn_const.sub he
  have hG : ContinuousOn (fun t : ℝ => spectralFreePhysicalPairField b ζ η t (Z t)) (Icc L R) := by
    simpa only [spectralFreePhysicalPairField,spectralFreePhysicalField,one_mul,neg_mul,
      neg_neg,sub_eq_add_neg,neg_div,Pi.neg_apply,Pi.add_apply,Pi.mul_apply,Pi.sub_apply] using
      (hZ.fst.snd.prodMk (((hk.add hi).neg.mul hZ.fst.snd).sub (hp.mul hZ.fst.fst))).prodMk
        (hZ.snd.snd.prodMk (((hk.sub hi).neg.mul hZ.snd.snd).sub (hm.mul hZ.snd.fst)))
  have hB : ContinuousOn (fun t : ℝ => spectralRegularFieldBound 11 0 0
      (b+Complex.I*ζ-η/(t : ℂ)^2) (b-Complex.I*ζ-η/(t : ℂ)^2) t) (Icc L R) := by
    exact ((((((continuousOn_const.add (hk.add hi).norm).add (hk.sub hi).norm).add
      continuousOn_const).add continuousOn_const).add hp.norm).add hm.norm)
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc L R)).exists_bound_of_continuousOn hB
  apply spectral_zero_on_open_annulus Z _ L R C hLR hZ hG hD _ hz r hr
  intro t ht
  rw [spectralFreePhysicalPairField_eq]
  apply (spectralRegularField_norm 11 0 0 _ _ t (Z t)).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (le_abs_self _).trans ((by simpa only [Real.norm_eq_abs] using hC t ht))

theorem spectralFree_eq_on_annulus (b ζ η : ℂ) (X Y : ℝ → E₄) (L R : ℝ)
    (hL : 0 < L) (hLR : L < R) (hX : ContinuousOn X (Icc L R)) (hY : ContinuousOn Y (Icc L R))
    (hDX : ∀ r ∈ Ioo L R, HasDerivAt X (spectralFreePhysicalPairField b ζ η r (X r)) r)
    (hDY : ∀ r ∈ Ioo L R, HasDerivAt Y (spectralFreePhysicalPairField b ζ η r (Y r)) r)
    (hXY : X R=Y R) : EqOn X Y (Icc L R) := by
  intro r hr
  apply sub_eq_zero.mp
  exact spectralFree_zero_on_annulus b ζ η (fun t => X t-Y t) L R hL hLR
    (hX.sub hY) (fun t ht => by
      have hd : HasDerivAt (fun s => X s-Y s)
          (spectralFreePhysicalPairField b ζ η t (X t)-spectralFreePhysicalPairField b ζ η t (Y t)) t :=
        (hDX t ht).sub (hDY t ht)
      exact hd.congr_deriv (spectralFreePhysicalPairField_sub b ζ η t (X t) (Y t)).symm)
    (by simp only [hXY,sub_self]) r hr

end DefocusingNLS

end OAI
