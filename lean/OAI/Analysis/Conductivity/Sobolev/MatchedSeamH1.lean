import Mathlib
import OAI.Analysis.Conductivity.Variational.WholeWeakClosure
import OAI.Analysis.Conductivity.Walls.SeamL2

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

theorem compact_matched_seam_H1 {τ u : R3 → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (hu : MemLp u 2 volume)
    (hlocal : ∀ x,0<τ x → LocalLipAt u x)
    (g : Fin 3 → R3 → ℝ) (hg : ∀ i,MemLp (g i) 2 volume)
    (hd : ∀ i,∀ᵐ x,0<τ x → HasLineDerivAt ℝ u (g i x) x (EuclideanSpace.single i 1))
    (hz : ∀ᵐ x,τ x≤0 → u x=0 ∧ ∀ i,g i x=0)
    {R : ℝ} (hR : R<3) (hs : ∀ x,R<‖x‖ → u x=0)
    (hthin : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*∫ x in seamLayer τ n,u x^2) atTop (𝓝 0)) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=u x ∧ ∀ i,weakGradient w x i=g i x) := by
  let f : ℕ → R3 → ℝ := fun n x => seamCutoff n (τ x)*u x
  have hfs (n : ℕ) (x : R3) (hx : R<‖x‖) : f n x=0 := by
    dsimp [f]; rw [hs x hx,mul_zero]
  have hfl (n : ℕ) : ∃ L,LipschitzWith L (f n) :=
    seamCutoff_mul_lipschitz hτ.locallyLipschitz hlocal (bounded_support_compact hs) n
  choose L hL using hfl
  have hfm (n : ℕ) : MemLp (f n) 2 volume :=
    (hL n).continuous.memLp_of_hasCompactSupport (bounded_support_compact (hfs n))
  let d : ℕ → Fin 3 → R3 → ℝ := fun n i x => lineDeriv ℝ (f n) x (EuclideanSpace.single i 1)
  have hdm (n : ℕ) (i : Fin 3) : MemLp (d n i) 2 volume :=
    lipschitz_lineDeriv_memLp (hL n) (hfs n) _
  have hv : Tendsto (fun n => (hfm n).toLp (f n)) atTop (𝓝 (hu.toLp u)) := by
    apply memLp_toLp_tendsto_of_sq hfm hu
    exact seamCutoff_L2_approx hτ.continuous hu (hz.mono (fun x hx ht => (hx ht).1))
  have hgrad (i : Fin 3) : Tendsto (fun n => (hdm n i).toLp (d n i)) atTop (𝓝 ((hg i).toLp (g i))) := by
    apply memLp_toLp_tendsto_of_sq (fun n => hdm n i) (hg i)
    exact seamCutoff_gradient_L2_approx hτ _ hu (hg i) (hd i)
      (hz.mono (fun x hx ht => ⟨(hx ht).1,(hx ht).2 i⟩)) (fun n => hdm n i) hthin
  have hw (i : Fin 3) : WeakL2Direction (hu.toLp u) ((hg i).toLp (g i)) (EuclideanSpace.single i 1) := by
    apply WeakL2Direction.closed hv (hgrad i)
    intro n
    exact (lipschitz_weakDirection (hL n) _).congr (hfm n).coeFn_toLp (hdm n i).coeFn_toLp
  let F : Fin 4 → WholeL2 := Fin.cases (hu.toLp u) (fun i => (hg i).toLp (g i))
  obtain ⟨w,hw₀,he⟩ := compact_weak_H1 F hw hR (by
    filter_upwards [hu.coeFn_toLp] with x hx
    intro hn
    exact hx.trans (hs x hn))
  refine ⟨w,hw₀,?_⟩
  have hv' := hu.coeFn_toLp.filter_mono (ae_mono (Measure.restrict_le_self (s:=ball)))
  have hg' := (ae_all_iff.mpr (fun i => (hg i).coeFn_toLp)).filter_mono
    (ae_mono (Measure.restrict_le_self (s:=ball)))
  filter_upwards [he,hv',hg'] with x hx hy hz
  exact ⟨hx.1.trans hy,fun i => (hx.2 i).trans (hz i)⟩

theorem compact_matched_seam_H1_pi {τ u : (Fin 3 → ℝ) → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (hu : MemLp u 2 volume)
    (hlocal : ∀ x,0<τ x → LocalLipAt u x)
    (g : Fin 3 → (Fin 3 → ℝ) → ℝ) (hg : ∀ i,MemLp (g i) 2 volume)
    (hd : ∀ i,∀ᵐ x,0<τ x → HasLineDerivAt ℝ u (g i x) x (Pi.single i 1))
    (hz : ∀ᵐ x,τ x≤0 → u x=0 ∧ ∀ i,g i x=0)
    {R : ℝ} (hR : R<3) (hs : ∀ x,R<‖WithLp.toLp 2 x‖ → u x=0)
    (hthin : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*
      ∫ x in {x | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2},u x^2) atTop (𝓝 0)) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=u (WithLp.ofLp x) ∧ ∀ i,weakGradient w x i=g i (WithLp.ofLp x)) := by
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hm : MeasurePreserving E volume volume := PiLp.volume_preserving_ofLp (Fin 3)
  have hd' (i : Fin 3) : ∀ᵐ x : R3,0<τ (E x) →
      HasLineDerivAt ℝ (u ∘ E) (g i (E x)) x (EuclideanSpace.single i 1) := by
    filter_upwards [hm.quasiMeasurePreserving.ae (hd i)] with x hx ht
    have hh := hx ht
    have he : E (EuclideanSpace.single i 1)=Pi.single i 1 := rfl
    simpa only [HasLineDerivAt,Function.comp_apply,map_add,map_smul,he]
      using hh
  have hthin' : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*
      ∫ x in seamLayer (τ ∘ E) n,(u (E x))^2) atTop (𝓝 0) := by
    convert hthin using 1
    ext n
    congr 1
    have hs' : MeasurableSet {x : Fin 3 → ℝ | 0<τ x ∧ ((n:ℝ)+1)*τ x≤2} :=
      (measurableSet_lt measurable_const hτ.continuous.measurable).inter
        (measurableSet_le (measurable_const.mul hτ.continuous.measurable) measurable_const)
    exact (hm.restrict_preimage hs').integral_comp E.toHomeomorph.measurableEmbedding (fun x => u x^2)
  apply compact_matched_seam_H1 (hτ.comp E.lipschitzWith) (hu.comp_measurePreserving hm)
    (fun x ht => (hlocal (E x) ht).comp (E.lipschitzWith.locallyLipschitz x))
    (fun i => g i ∘ E) (fun i => (hg i).comp_measurePreserving hm) hd'
    (hm.quasiMeasurePreserving.ae hz) hR _ hthin'
  intro x hx
  exact hs (E x) hx

end ScalarConductivity

end

end OAI
