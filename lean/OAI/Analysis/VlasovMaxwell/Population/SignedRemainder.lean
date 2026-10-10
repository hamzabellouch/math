import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ConeMotion

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

lemma intervalIntegral_vec_apply {g : ℝ → Vec} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (i : Fin 3) :
    (∫ t in a..b, g t) i = ∫ t in a..b, g t i := by
  exact ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).intervalIntegral_comp_comm hg).symm

lemma ac_weighted_vector_ibp {ψ : ℝ → ℝ} {g g' : ℝ → Vec} {a b : ℝ}
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hg : ContDiffOn ℝ 1 g (uIcc a b))
    (hg' : ContinuousOn g' (uIcc a b))
    (hd : ∀ t ∈ uIoo a b, HasDerivAt g (g' t) t) :
    ∫ t in a..b, ψ t • g' t =
      ψ b • g b - ψ a • g a - ∫ t in a..b, deriv ψ t • g t := by
  have h₁ : IntervalIntegrable (fun t => ψ t • g' t) volume a b :=
    (hψ.continuousOn.smul hg').intervalIntegrable
  have h₂ : IntervalIntegrable (fun t => deriv ψ t • g t) volume a b :=
    hψ.intervalIntegrable_deriv.smul_continuousOn hg.continuousOn
  ext i
  rw [intervalIntegral_vec_apply h₁,PiLp.sub_apply,PiLp.sub_apply,
    PiLp.smul_apply,PiLp.smul_apply,intervalIntegral_vec_apply h₂]
  simp only [PiLp.smul_apply,smul_eq_mul]
  have hgi : ContDiffOn ℝ 1 (fun t => g t i) (uIcc a b) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp_contDiffOn hg
  have he : (∫ t in a..b, ψ t * g' t i) =
      ∫ t in a..b, ψ t * deriv (fun s => g s i) t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have hi := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt t (hd t ht)
    change HasDerivAt (fun s => g s i) (g' t i) t at hi
    exact congrArg (fun x => ψ t*x) hi.deriv.symm
  rw [he]
  exact hψ.integral_mul_deriv_eq_deriv_mul hgi.absolutelyContinuousOnInterval

lemma ac_weighted_signed_ibp {ψ : ℝ → ℝ} {P K R : ℝ → Vec}
    {W W' : ℝ → Vec →L[ℝ] Vec} {a b : ℝ}
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hP : ContDiffOn ℝ 1 P (uIcc a b))
    (hW : ContDiffOn ℝ 1 W (uIcc a b))
    (hW' : ContinuousOn W' (uIcc a b))
    (hK : ContinuousOn K (uIcc a b)) (hR : ContinuousOn R (uIcc a b))
    (hPd : ∀ t ∈ uIoo a b, HasDerivAt P (-K t+R t) t)
    (hWd : ∀ t ∈ uIoo a b, HasDerivAt W (W' t) t) :
    ∫ t in a..b, ψ t • W t (K t) =
      ψ a • W a (P a) - ψ b • W b (P b) +
      ∫ t in a..b,
        deriv ψ t • W t (P t) + ψ t • (W' t (P t)+W t (R t)) := by
  have hg : ContDiffOn ℝ 1 (fun t => W t (P t)) (uIcc a b) := hW.clm_apply hP
  have hg' : ContinuousOn (fun t => W' t (P t)+W t (-K t+R t)) (uIcc a b) :=
    (hW'.clm_apply hP.continuousOn).add (hW.continuousOn.clm_apply (hK.neg.add hR))
  have h := ac_weighted_vector_ibp hψ hg hg'
    (fun t ht => (hWd t ht).clm_apply (hPd t ht))
  have hI₁ : IntervalIntegrable (fun t => ψ t • W t (K t)) volume a b :=
    (hψ.continuousOn.smul (hW.continuousOn.clm_apply hK)).intervalIntegrable
  have hI₂ : IntervalIntegrable (fun t => ψ t • (W' t (P t)+W t (R t))) volume a b :=
    (hψ.continuousOn.smul ((hW'.clm_apply hP.continuousOn).add
      (hW.continuousOn.clm_apply hR))).intervalIntegrable
  have hI₃ : IntervalIntegrable (fun t => deriv ψ t • W t (P t)) volume a b :=
    hψ.intervalIntegrable_deriv.smul_continuousOn hg.continuousOn
  have he : (fun t => ψ t • (W' t (P t)+W t (-K t+R t))) =
      (fun t => ψ t • (W' t (P t)+W t (R t)) - ψ t • W t (K t)) := by
    funext t
    simp only [map_add,map_neg,smul_add,smul_neg]
    abel
  rw [he,intervalIntegral.integral_sub hI₂ hI₁] at h
  rw [intervalIntegral.integral_add hI₃ hI₂]
  have hh := congrArg (fun v => (∫ t in a..b, ψ t • (W' t (P t)+W t (R t))) - v) h
  convert hh using 1 <;> abel

def signedRemainder (r : ℝ) (a u n aₜ : Vec) : Vec :=
  ((1-dot a u)/(r^2*(1-dot n a)^2)) •
    (((1-dot a a)/(1-dot n a)) • n-a) +
  (dot aₜ (signedPrimitive a u n)/(r*(1-dot n a)^2)) • n

lemma contDiffOn_retardedPrimitive {r : ℝ → ℝ} {a u n : ℝ → Vec} {S : Set ℝ}
    (hr : ContDiffOn ℝ 1 r S) (ha : ContDiffOn ℝ 1 a S)
    (hu : ContDiffOn ℝ 1 u S) (hn : ContDiffOn ℝ 1 n S)
    (hr0 : ∀ s ∈ S, r s ≠ 0) (hd : ∀ s ∈ S, 1-dot (n s) (u s) ≠ 0)
    (hD : ∀ s ∈ S, 1-dot (n s) (a s) ≠ 0) :
    ContDiffOn ℝ 1 (fun s => retardedPrimitive (r s) (a s) (u s) (n s)) S := by
  have hdu : ContDiffOn ℝ 1 (fun s => 1-dot (n s) (u s)) S := by
    simpa only [dot_eq_inner,Pi.sub_apply] using contDiffOn_const.sub (hn.inner ℝ hu)
  have hDa : ContDiffOn ℝ 1 (fun s => 1-dot (n s) (a s)) S := by
    simpa only [dot_eq_inner,Pi.sub_apply] using contDiffOn_const.sub (hn.inner ℝ ha)
  have hea : ContDiffOn ℝ 1 (fun s => 1-dot (a s) (u s)) S := by
    simpa only [dot_eq_inner,Pi.sub_apply] using contDiffOn_const.sub (ha.inner ℝ hu)
  exact ((hr.mul hdu).inv (fun s hs => mul_ne_zero (hr0 s hs) (hd s hs))).smul
    (hu.sub ((hea.div hDa hD).smul hn))

lemma continuousOn_signedRemainder {r : ℝ → ℝ} {a u n aₜ : ℝ → Vec} {S : Set ℝ}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S)
    (hu : ContinuousOn u S) (hn : ContinuousOn n S) (haₜ : ContinuousOn aₜ S)
    (hr0 : ∀ s ∈ S, r s ≠ 0) (hD : ∀ s ∈ S, 1-dot (n s) (a s) ≠ 0) :
    ContinuousOn (fun s => signedRemainder (r s) (a s) (u s) (n s) (aₜ s)) S := by
  have hDa : ContinuousOn (fun s => 1-dot (n s) (a s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hn.inner ha)
  have hea : ContinuousOn (fun s => 1-dot (a s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (ha.inner hu)
  have haa : ContinuousOn (fun s => 1-dot (a s) (a s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (ha.inner ha)
  have hp : ContinuousOn (fun s => signedPrimitive (a s) (u s) (n s)) S :=
    hu.sub ((hea.div hDa hD).smul hn)
  have hatp : ContinuousOn (fun s => dot (aₜ s) (signedPrimitive (a s) (u s) (n s))) S := by
    simpa only [dot_eq_inner] using haₜ.inner hp
  exact ((hea.div ((hr.pow 2).mul (hDa.pow 2))
    (fun s hs => mul_ne_zero (pow_ne_zero _ (hr0 s hs)) (pow_ne_zero _ (hD s hs)))).smul
      (((haa.div hDa hD).smul hn).sub ha)).add
    ((hatp.div (hr.mul (hDa.pow 2))
      (fun s hs => mul_ne_zero (hr0 s hs) (pow_ne_zero _ (hD s hs)))).smul hn)

lemma continuousOn_signedForceKernel {r : ℝ → ℝ} {a u n u' : ℝ → Vec} {S : Set ℝ}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S)
    (hu : ContinuousOn u S) (hn : ContinuousOn n S) (hu' : ContinuousOn u' S)
    (hr0 : ∀ s ∈ S, r s ≠ 0) (hd : ∀ s ∈ S, 1-dot (n s) (u s) ≠ 0)
    (hD : ∀ s ∈ S, 1-dot (n s) (a s) ≠ 0) :
    ContinuousOn (fun s => signedForceKernel (r s) (a s) (u s) (n s) (u' s)) S := by
  have hdu : ContinuousOn (fun s => 1-dot (n s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hn.inner hu)
  have hDa : ContinuousOn (fun s => 1-dot (n s) (a s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hn.inner ha)
  have huu : ContinuousOn (fun s => 1-dot (u s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hu.inner hu)
  have hnu' : ContinuousOn (fun s => dot (n s) (u' s)) S := by
    simpa only [dot_eq_inner] using hn.inner hu'
  have hv : ContinuousOn (fun s => sourceVelocityRate (u s) (n s) (u' s)) S :=
    ((hdu.inv₀ hd).smul hu').add
      ((hnu'.div (hdu.pow 2) (fun s hs => pow_ne_zero _ (hd s hs))).smul (hu.sub hn))
  have hc {w : ℝ → Vec} (hw : ContinuousOn w S) :
      ContinuousOn (fun s => coneTransform (a s) (n s) (w s)) S := by
    have haw : ContinuousOn (fun s => dot (a s) (w s)) S := by
      simpa only [dot_eq_inner] using ha.inner hw
    exact hw.add ((haw.div hDa hD).smul hn)
  exact (((hr.inv₀ hr0).smul (hc hv)).neg).sub
    ((huu.div ((hr.pow 2).mul hdu)
      (fun s hs => mul_ne_zero (pow_ne_zero _ (hr0 s hs)) (hd s hs))).smul
        (hc ((hdu.inv₀ hd).smul (hu.sub hn))))

lemma weighted_signed_identity_on_branch
    {r : ℝ → ℝ} {a u n u' aₜ : ℝ → Vec}
    {ψ : ℝ → ℝ} {W W' : ℝ → Vec →L[ℝ] Vec} {b c : ℝ}
    (hψ : AbsolutelyContinuousOnInterval ψ b c)
    (hr : ContDiffOn ℝ 1 r (uIcc b c)) (ha : ContDiffOn ℝ 1 a (uIcc b c))
    (hu : ContDiffOn ℝ 1 u (uIcc b c)) (hn : ContDiffOn ℝ 1 n (uIcc b c))
    (hW : ContDiffOn ℝ 1 W (uIcc b c)) (hW' : ContinuousOn W' (uIcc b c))
    (hu' : ContinuousOn u' (uIcc b c)) (haₜ : ContinuousOn aₜ (uIcc b c))
    (hr0 : ∀ s ∈ uIcc b c, r s ≠ 0)
    (hd : ∀ s ∈ uIcc b c, 1-dot (n s) (u s) ≠ 0)
    (hD : ∀ s ∈ uIcc b c, 1-dot (n s) (a s) ≠ 0)
    (hrd : ∀ s ∈ uIoo b c, HasDerivAt r
      ((1-dot (n s) (u s))/(1-dot (n s) (a s))-1) s)
    (had : ∀ s ∈ uIoo b c, HasDerivAt a
      (((1-dot (n s) (u s))/(1-dot (n s) (a s))) • aₜ s) s)
    (hud : ∀ s ∈ uIoo b c, HasDerivAt u (u' s) s)
    (hnd : ∀ s ∈ uIoo b c, HasDerivAt n ((r s)⁻¹ • coneMotion (a s) (u s) (n s)) s)
    (hWd : ∀ s ∈ uIoo b c, HasDerivAt W (W' s) s) :
    ∫ s in b..c, ψ s • W s (signedForceKernel (r s) (a s) (u s) (n s) (u' s)) =
      ψ b • W b (retardedPrimitive (r b) (a b) (u b) (n b)) -
      ψ c • W c (retardedPrimitive (r c) (a c) (u c) (n c)) +
      ∫ s in b..c,
        deriv ψ s • W s (retardedPrimitive (r s) (a s) (u s) (n s)) +
        ψ s • (W' s (retardedPrimitive (r s) (a s) (u s) (n s)) +
          W s (signedRemainder (r s) (a s) (u s) (n s) (aₜ s))) := by
  apply ac_weighted_signed_ibp hψ
    (contDiffOn_retardedPrimitive hr ha hu hn hr0 hd hD) hW hW'
    (continuousOn_signedForceKernel hr.continuousOn ha.continuousOn hu.continuousOn
      hn.continuousOn hu' hr0 hd hD)
    (continuousOn_signedRemainder hr.continuousOn ha.continuousOn hu.continuousOn
      hn.continuousOn haₜ hr0 hD) _ hWd
  intro s hs
  have hs' : s ∈ uIcc b c := Ioo_subset_Icc_self hs
  have hder := hasDerivAt_retardedPrimitive (hrd s hs) (had s hs) (hud s hs) (hnd s hs)
    (hr0 s hs') (hd s hs') (hD s hs')
  convert hder using 1
  have he := signed_force_identity (r s) (a s) (u s) (n s) (u' s) (aₜ s)
    (hr0 s hs') (hd s hs') (hD s hs')
  rw [he]
  unfold signedRemainder
  abel

end RVM

end

end OAI
