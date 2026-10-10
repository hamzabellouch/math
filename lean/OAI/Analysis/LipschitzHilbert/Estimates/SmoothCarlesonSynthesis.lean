import OAI.Analysis.LipschitzHilbert.Fourier.LineSchwartzPairing
import OAI.Analysis.LipschitzHilbert.Estimates.SmoothCarlesonEnergy

namespace OAI

/-! Duality turns the proved smooth Carleson analysis bound into the
actual finite paraproduct synthesis bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def smoothCarlesonDualConstant : ℝ :=
  36*dyadicCarlesonConstant*(lineCellMaximalConstant reassemblyLow (1/128))^2

theorem smoothCarlesonDualConstant_nonneg : 0≤smoothCarlesonDualConstant := by
  unfold smoothCarlesonDualConstant
  exact mul_nonneg (mul_nonneg (by norm_num) dyadicCarlesonConstant_pos.le) (sq_nonneg _)

def dyadicParaproduct (I : Finset ℤ) (b : SchwartzMap ℝ ℂ)
    (H : ℤ → SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ∑ k∈I, lineSchwartzProduct
    (lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b) (H k)

theorem dyadicParaproduct_lowpass (b h : SchwartzMap ℝ ℂ) (k : ℤ)
    (hh : ∀ eta, (𝓕 h : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤64/scale k) :
    let p := lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b
    lineSchwartzProjection reassemblyLow ((1/128)*scale k) (by have := scale_pos k; positivity)
      (lineSchwartzProduct p h)=lineSchwartzProduct p h := by
  intro p
  apply lineLowpass_absorb
  intro eta heta
  have hp := dyadicProjection_frequency (scale k) (scale_pos k) b
  have hg := lineSchwartzProduct_band p h ((13/6)/scale k) (64/scale k)
    (fun x hx => (hp x hx).2) hh eta heta
  have hs := (scale_pos k)
  have hu : scale k*|eta|≤13/6+64 := by
    have hmul := mul_le_mul_of_nonneg_left hg hs.le
    field_simp [hs.ne'] at hmul
    nlinarith only [hmul]
  rw [abs_mul,abs_of_pos (by positivity : (0:ℝ)<(1/128)*scale k)]
  nlinarith

theorem smooth_carleson_synthesis (I : Finset ℤ) (b : SchwartzMap ℝ ℂ)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, ‖b x‖≤B) (H : ℤ → SchwartzMap ℝ ℂ)
    (hH : ∀ k∈I, ∀ eta, (𝓕 (H k) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤64/scale k) :
    (∫ x, ‖dyadicParaproduct I b H x‖^2)≤
      smoothCarlesonDualConstant*B^2*(∑ k∈I, ∫ x, ‖H k x‖^2) := by
  let F := dyadicParaproduct I b H
  let P := fun k => lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' b
  let Q := fun k => lineSchwartzProjection reassemblyLow ((1/128)*scale k)
    (by have := scale_pos k; positivity) F
  let G := fun k => lineSchwartzProduct (P k) (Q k)
  let D := smoothCarlesonDualConstant*B^2
  let E := ∑ k∈I, ∫ x, ‖H k x‖^2
  have hD : 0≤D := mul_nonneg smoothCarlesonDualConstant_nonneg (sq_nonneg B)
  have hE : 0≤E := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hFnorm : ‖F.toLp 2 volume‖^2=∫ x, ‖F x‖^2 :=
    memLp_toL2_norm_sq volume F (F.memLp 2 volume)
  have hnorm (f : SchwartzMap ℝ ℂ) : ‖f.toLp 2 volume‖^2=∫ x, ‖f x‖^2 :=
    memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  have hsumH : (∑ k∈I, ‖(H k).toLp 2 volume‖^2)=E :=
    Finset.sum_congr rfl (fun k _ => hnorm (H k))
  have hG : (∑ k∈I, ‖(G k).toLp 2 volume‖^2)≤D*‖F.toLp 2 volume‖^2 := by
    have hc := (smooth_carleson_energy I b b.continuous.measurable B hB hb (1/128) (by norm_num) F).2
    have he (k : ℤ) (x : ℝ) : G k x=smoothDyadicProduct b F (1/128) (by norm_num) k x := by
      dsimp [G,P,Q]
      simp only [lineSchwartzProduct_apply,lineSchwartzProjection_eq_convolution,smoothDyadicProduct]
    simpa only [hnorm,he,D,smoothCarlesonDualConstant] using hc
  have hpair (k : ℤ) (hk : k∈I) :
      ‖inner ℂ ((lineSchwartzProduct (P k) (H k)).toLp 2 volume) (F.toLp 2 volume)‖≤
        ‖(H k).toLp 2 volume‖*‖(G k).toLp 2 volume‖ := by
    have habs := dyadicParaproduct_lowpass b (H k) k (hH k hk)
    have hadj := lineSchwartzProjection_inner reassemblyLow reassemblyLow_conj
      ((1/128)*scale k) (by have := scale_pos k; positivity) (lineSchwartzProduct (P k) (H k)) F
    rw [habs] at hadj
    rw [hadj]
    have hp := lineSchwartzProduct_inner_bound (P k) (H k) (Q k)
    rw [←hnorm (G k),Real.sqrt_sq (norm_nonneg _)] at hp
    exact hp
  have hid : inner ℂ (F.toLp 2 volume) (F.toLp 2 volume)=
      ∑ k∈I, inner ℂ ((lineSchwartzProduct (P k) (H k)).toLp 2 volume) (F.toLp 2 volume) := by
    have he : F.toLp 2 volume=∑ k∈I, (lineSchwartzProduct (P k) (H k)).toLp 2 volume :=
      map_sum (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ I
    rw [he]
    exact sum_inner _ _ _
  have hbound : ‖F.toLp 2 volume‖^2≤Real.sqrt E*Real.sqrt (D*‖F.toLp 2 volume‖^2) := by
    calc
      _ = ‖inner ℂ (F.toLp 2 volume) (F.toLp 2 volume)‖ := by
        simp only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
      _ = ‖∑ k∈I, inner ℂ ((lineSchwartzProduct (P k) (H k)).toLp 2 volume) (F.toLp 2 volume)‖ := congrArg norm hid
      _ ≤ ∑ k∈I, ‖inner ℂ ((lineSchwartzProduct (P k) (H k)).toLp 2 volume) (F.toLp 2 volume)‖ := norm_sum_le _ _
      _ ≤ ∑ k∈I, ‖(H k).toLp 2 volume‖*‖(G k).toLp 2 volume‖ := Finset.sum_le_sum hpair
      _ ≤ Real.sqrt (∑ k∈I, ‖(H k).toLp 2 volume‖^2)*Real.sqrt (∑ k∈I, ‖(G k).toLp 2 volume‖^2) :=
        Real.sum_mul_le_sqrt_mul_sqrt I _ _
      _ ≤ _ := by
        rw [←hsumH]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hG)
          (Real.sqrt_nonneg (∑ k∈I, ‖(H k).toLp 2 volume‖^2))
  rw [Real.sqrt_mul hD,Real.sqrt_sq (norm_nonneg _)] at hbound
  have hfinal : ‖F.toLp 2 volume‖^2≤D*E := by
    by_cases hz : ‖F.toLp 2 volume‖=0
    · rw [hz]; simpa only [zero_pow (by decide : 2≠0)] using mul_nonneg hD hE
    · have hpos : 0<‖F.toLp 2 volume‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hn : ‖F.toLp 2 volume‖≤Real.sqrt E*Real.sqrt D := by
        apply (mul_le_mul_iff_right₀ hpos).mp
        nlinarith only [hbound]
      have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
      simpa only [mul_pow,Real.sq_sqrt hE,Real.sq_sqrt hD,mul_comm] using hs
  simpa only [hFnorm,D,E,mul_assoc] using hfinal

end LipschitzHilbert.PacketRepresentation

end

end OAI
