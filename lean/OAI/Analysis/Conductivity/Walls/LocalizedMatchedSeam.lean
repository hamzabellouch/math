import Mathlib
import OAI.Analysis.Conductivity.Sobolev.MatchedSeamH1

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

def cutMatchedValue (τ χ p : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  if 0<τ x then χ x*p x else 0

def cutMatchedGradient (τ χ p : (Fin 3 → ℝ) → ℝ)
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ) (i : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  if 0<τ x then fderiv ℝ χ x (Pi.single i 1)*p x+χ x*F x (Pi.single i 1) else 0

lemma cutMatchedValue_memLp {τ χ p : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    (hτ : Continuous τ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hD : MeasurableSet D) (hp : MemLp p 2 (volume.restrict D))
    (hs : ∀ x∈tsupport χ,0<τ x → x∈D) :
    MemLp (cutMatchedValue τ χ p) 2 volume := by
  have hm := (memLp_indicator_iff_restrict hD).mpr hp
  have hm' : MemLp (χ*(D.indicator p)) 2 volume :=
    (hχ.memLp_top_of_hasCompactSupport hc volume).mul hm
  have hh := hm'.indicator (isOpen_lt (continuous_const (y:=(0:ℝ))) hτ).measurableSet
  apply MemLp.ae_eq _ hh
  filter_upwards [] with x
  by_cases ht : 0<τ x
  · by_cases hx : x∈D
    · simp [cutMatchedValue,ht,hx]
    · have hn : x∉tsupport χ := fun h => hx (hs x h ht)
      simp [cutMatchedValue,ht,hx,image_eq_zero_of_notMem_tsupport hn]
  · simp [cutMatchedValue,ht]

theorem localized_matched_seam_H1_pi {τ χ p : (Fin 3 → ℝ) → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) {D : Set (Fin 3 → ℝ)} (hD : MeasurableSet D)
    (hp : MemLp p 2 (volume.restrict D))
    (hs : ∀ x∈tsupport χ,0<τ x → x∈D)
    (hl : ∀ x∈tsupport χ,0<τ x → LocalLipAt p x)
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ)
    (hF : ∀ i : Fin 3,MemLp (fun x => F x (Pi.single i 1)) 2 (volume.restrict D))
    (hd : ∀ᵐ x∂volume.restrict D,0<τ x → HasFDerivAt p (F x) x)
    {R : ℝ} (hR : R<3) (hb : ∀ x∈tsupport χ,‖WithLp.toLp 2 x‖≤R)
    (hthin : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*
      ∫ x in {x | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2},(cutMatchedValue τ χ p x)^2) atTop (𝓝 0)) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=cutMatchedValue τ χ p (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=cutMatchedGradient τ χ p F i (WithLp.ofLp x)) := by
  have hχd := hχ.differentiable (by simp)
  have hχf : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by simp)
  have hgm (i : Fin 3) : MemLp (cutMatchedGradient τ χ p F i) 2 volume := by
    have h1 := cutMatchedValue_memLp hτ.continuous (hχf.clm_apply continuous_const)
      (hc.fderiv_apply ℝ (Pi.single i 1)) hD hp
      (fun x hx ht => hs x (tsupport_fderiv_apply_subset ℝ _ hx) ht)
    have h2 := cutMatchedValue_memLp hτ.continuous hχ.continuous hc hD (hF i) hs
    convert h1.add h2 using 1
    funext x
    by_cases ht : 0<τ x <;> simp [cutMatchedValue,cutMatchedGradient,ht]
  have hu_eq {x : Fin 3 → ℝ} (ht : 0<τ x) :
      cutMatchedValue τ χ p =ᶠ[𝓝 x] (fun y => χ y*p y) := by
    filter_upwards [hτ.continuous.continuousAt.eventually (lt_mem_nhds ht)] with y hy
    exact ite_eq_left hy
  have hz_eq {x : Fin 3 → ℝ} (hx : x∉tsupport χ) :
      cutMatchedValue τ χ p =ᶠ[𝓝 x] 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    change χ y=0 at hy
    simp [cutMatchedValue,hy]
  have hul (x : Fin 3 → ℝ) (ht : 0<τ x) : LocalLipAt (cutMatchedValue τ χ p) x := by
    by_cases hx : x∈tsupport χ
    · exact ((localLipAt_of_contDiffAt (hχ.of_le (by simp)).contDiffAt).mul (hl x hx ht)).congr (hu_eq ht).symm
    · exact (localLipAt_of_contDiffAt (contDiffAt_const (c:=(0:ℝ)))).congr (hz_eq hx).symm
  have hud (i : Fin 3) : ∀ᵐ x,0<τ x → HasLineDerivAt ℝ (cutMatchedValue τ χ p)
      (cutMatchedGradient τ χ p F i x) x (Pi.single i 1) := by
    filter_upwards [(ae_restrict_iff' hD).mp hd] with x hx ht
    by_cases hxχ : x∈tsupport χ
    · have hh := (hχd x).hasFDerivAt.mul (hx (hs x hxχ ht) ht)
      have hh' := (hh.congr_of_eventuallyEq (hu_eq ht)).hasLineDerivAt (Pi.single i 1)
      simpa [cutMatchedGradient,ht,add_comm,mul_comm] using hh'
    · have hzero : cutMatchedGradient τ χ p F i x=0 := by
        have hd0 : fderiv ℝ χ x (Pi.single i 1)=0 :=
          image_eq_zero_of_notMem_tsupport (f:=fun y => fderiv ℝ χ y (Pi.single i 1))
            (fun h => hxχ (tsupport_fderiv_apply_subset ℝ _ h))
        simp [cutMatchedGradient,ht,image_eq_zero_of_notMem_tsupport hxχ,hd0]
      rw [hzero]
      exact ((hasFDerivAt_const (c:=(0:ℝ)) x).congr_of_eventuallyEq (hz_eq hxχ)).hasLineDerivAt _
  apply compact_matched_seam_H1_pi hτ (cutMatchedValue_memLp hτ.continuous hχ.continuous hc hD hp hs)
    hul (cutMatchedGradient τ χ p F) hgm hud _ hR _ hthin
  · exact Eventually.of_forall (fun x hx => by simp [cutMatchedValue,cutMatchedGradient,not_lt.mpr hx])
  · intro x hx
    have hnot : x∉tsupport χ := fun h => (hb x h).not_gt hx
    simp [cutMatchedValue,image_eq_zero_of_notMem_tsupport hnot]

end ScalarConductivity

end

end OAI
