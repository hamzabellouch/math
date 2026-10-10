import OAI.Probability.SLE.Geometry.SimpleArcPlaneComplement
import Mathlib.Analysis.Normed.Field.Lemmas

namespace OAI

/-! Inverting a bounded obstacle and adding the point at infinity at
zero. This is the domain used for conformal normalization at infinity. -/
noncomputable section
open Set Complex Metric Filter
open scoped Topology

namespace SLEExactGauge

def invertedExterior (K : Set ℂ) : Set ℂ := {z | z=0 ∨ z⁻¹ ∉ K}

lemma invertedExterior_eq_insert (K : Set ℂ) :
    invertedExterior K=insert 0 (Inv.inv '' Kᶜ) := by
  ext z
  change (z=0 ∨ z⁻¹ ∉ K) ↔ z=0 ∨ ∃ w ∈ Kᶜ, w⁻¹=z
  constructor
  · rintro (rfl|hz)
    · exact Or.inl rfl
    · exact Or.inr ⟨z⁻¹,hz,inv_inv z⟩
  · rintro (rfl|⟨w,hw,rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (by rw [inv_inv]; exact hw)

lemma zero_mem_invertedExterior (K : Set ℂ) : (0:ℂ) ∈ invertedExterior K := Or.inl rfl

lemma invertedExterior_isOpen {K : Set ℂ} (hK : IsCompact K) :
    IsOpen (invertedExterior K) := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.subset_ball_lt 0 (0:ℂ)
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  by_cases hz0 : z=0
  · subst z
    apply mem_of_superset (ball_mem_nhds 0 (by positivity : 0 < 1/(R+1)))
    intro w hw
    by_cases hw0 : w=0
    · exact Or.inl hw0
    right
    intro hwK
    have hsmall : ‖w‖ < 1/(R+1) := by simpa only [mem_ball,dist_zero_right] using hw
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hlarge : R+1 < ‖w‖⁻¹ := by
      rw [← one_div,lt_div_iff₀ hn]
      nlinarith [(lt_div_iff₀ (by linarith : 0 < R+1)).mp hsmall]
    have hb : ‖w‖⁻¹ < R := by
      simpa only [mem_ball,dist_zero_right,norm_inv] using hbound hwK
    linarith
  · have hinv : z⁻¹ ∈ Kᶜ := hz.resolve_left hz0
    have hpre := (continuousAt_inv₀ hz0).preimage_mem_nhds
      (hK.isClosed.isOpen_compl.mem_nhds hinv)
    exact mem_of_superset hpre (fun _ h => Or.inr h)

lemma zero_mem_closure_inverted_complement {K : Set ℂ} (hK : Bornology.IsBounded K) :
    (0:ℂ) ∈ closure (Inv.inv '' Kᶜ) := by
  obtain ⟨R,hR,hbound⟩ := hK.subset_ball_lt 0 (0:ℂ)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let M := R+1+1/ε
  have hM : 0 < M := by dsimp [M]; positivity
  have hMR : R < M := by dsimp [M]; linarith [one_div_pos.mpr hε]
  have hMe : 1/ε < M := by dsimp [M]; linarith
  have hnot : (M:ℂ) ∈ Kᶜ := by
    intro hh
    have hb := hbound hh
    have he : ‖(M:ℂ)‖=M := by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
    rw [mem_ball,dist_zero_right,he] at hb
    linarith
  refine ⟨(M:ℂ)⁻¹,⟨(M:ℂ),hnot,rfl⟩,?_⟩
  have hsmall : M⁻¹ < ε := by
    rw [← one_div,div_lt_iff₀ hM]
    nlinarith [(div_lt_iff₀ hε).mp hMe]
  simpa only [dist_eq_norm,zero_sub,norm_neg,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hM] using hsmall

theorem invertedExterior_connected {K : Set ℂ} (hb : Bornology.IsBounded K)
    (h0 : (0:ℂ) ∈ K) (hc : IsConnected Kᶜ) : IsConnected (invertedExterior K) := by
  have hi : ContinuousOn (Inv.inv : ℂ → ℂ) Kᶜ := by
    intro z hz
    have hn : z ≠ (0:ℂ) := fun he => hz (he.symm ▸ h0)
    exact (continuousAt_inv₀ hn).continuousWithinAt
  have himage := hc.image Inv.inv hi
  rw [invertedExterior_eq_insert K]
  apply himage.subset_closure (subset_insert 0 _)
  intro z hz
  rcases hz with rfl|hz
  · exact zero_mem_closure_inverted_complement hb
  · exact subset_closure hz

end SLEExactGauge

end

end OAI
