import Mathlib
import OAI.Analysis.Conductivity.Variational.LocalSmoothWeakDerivative

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma regularRegion_contDiff (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (U : Set Coord3) : ContDiffOn ℝ (↑(⊤:ℕ∞)) u (regularRegion u A U) := by
  intro x hx
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp hx
  exact ((hO.2.1 x hxO).contDiffAt (hO.1.mem_nhds hxO)).contDiffWithinAt

lemma original_cartesian_representative_gradient (w : H1) {U : Set Coord3}
    (hU : IsOpen U) (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball)
    (v : Coord3 → ℝ) (hv : ContDiffOn ℝ (↑(⊤:ℕ∞)) v U)
    (he : (fun y => weakValue w (WithLp.toLp 2 y))=ᵐ[volume.restrict U] v) :
    ∀ᵐ y : Coord3,y∈U → ∀ i : Fin 3,
      weakGradient w (WithLp.toLp 2 y) i=fderiv ℝ v y (Pi.single i 1) := by
  let Q : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hV : IsOpen (Q ⁻¹' U) := hU.preimage Q.continuous
  have hv' : ContDiffOn ℝ (↑(⊤:ℕ∞)) (v ∘ Q) (Q ⁻¹' U) :=
    hv.comp Q.contDiff.contDiffOn (fun _ hx => hx)
  have he' : weakValue w=ᵐ[volume.restrict (Q ⁻¹' U)] v ∘ Q := by
    apply (ae_restrict_iff' hV.measurableSet).mpr
    have hh := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      ((ae_restrict_iff' hU.measurableSet).mp he)
    filter_upwards [hh] with x hx hxU
    exact hx hxU
  have hh := original_contDiffOn_representative_gradient w hV (fun x hx => hUb _ hx)
    (v ∘ Q) hv' he'
  have hh' := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae hh
  filter_upwards [hh'] with y hy hyU i
  rw [hy hyU]
  have hd : DifferentiableAt ℝ v y := (hv.differentiableOn (by simp) y hyU).differentiableAt
    (hU.mem_nhds hyU)
  have hg : (gradient (v ∘ Q) (WithLp.toLp 2 y)) i=
      fderiv ℝ (v ∘ Q) (WithLp.toLp 2 y) (EuclideanSpace.single i 1) := by
    simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using
      (inner_gradient_right (f:=v ∘ Q) (x:=EuclideanSpace.single i 1) (y:=WithLp.toLp 2 y))
  rw [hg,fderiv_comp _ hd Q.differentiableAt,Q.fderiv]
  rfl

theorem physical_representative_glue {ι : Type*} (O : ι → Set Coord3)
    (hO : ∀ i,IsOpen (O i)) {U : Set Coord3} (hUm : MeasurableSet U)
    (hOU : ∀ i,O i⊆U) (hUb : ∀ y∈U,WithLp.toLp 2 y∈ball)
    (hcover : ∀ᵐ y : Coord3,y∈U → y∈⋃ i,O i)
    (w : Fin 2 → H1) (g : ι → Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (hreg : ∀ i,RegularPatch (g i) A (O i))
    (he : ∀ i,(fun y j => weakValue (w j) (WithLp.toLp 2 y))=ᵐ[volume.restrict (O i)] g i) :
    ∃ v : Coord3 → Fin 2 → ℝ,
      (∀ᵐ y : Coord3,y∈U → v y=fun j => weakValue (w j) (WithLp.toLp 2 y)) ∧
      (∀ᵐ y : Coord3,y∈U → ∀ i : Fin 3,∀ j : Fin 2,
        fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i) ∧
      volume (U \ regularRegion v A U)=0 := by
  obtain ⟨v,hvg,hve,hvs⟩ := smooth_representatives_glue volume O hO
    (fun y j => weakValue (w j) (WithLp.toLp 2 y)) g (fun i => (hreg i).2.1) he
  have hV : IsOpen (⋃ i,O i) := isOpen_iUnion hO
  have hVU : (⋃ i,O i)⊆U := iUnion_subset hOU
  have hve' := (ae_restrict_iff' hV.measurableSet).mp hve
  have hd (j : Fin 2) := original_cartesian_representative_gradient (w j) hV
    (fun y hy => hUb y (hVU hy)) (fun y => v y j)
    ((contDiffOn_pi.mp hvs) j) (hve.mono (fun y hy => congrFun hy j))
  refine ⟨v,?_,?_,?_⟩
  · filter_upwards [hcover,hve'] with y hc he hy
    exact (he (hc hy)).symm
  · filter_upwards [hcover,ae_all_iff.mpr hd] with y hc hd hy i j
    exact (hd j (hc hy) i).symm
  · have hmem : ∀ᵐ y : Coord3 ∂volume.restrict U,y∈regularRegion v A U := by
      filter_upwards [ae_restrict_of_ae hcover,ae_restrict_mem hUm] with y hc hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hc hy)
      exact mem_regularRegion_iff.mpr ⟨O i,hOU i,
        (hreg i).congr (hvg i) (fun _ _ => rfl),hi⟩
    have he : {y : Coord3 | ¬(y∈U → y∈regularRegion v A U)}=U \ regularRegion v A U := by
      ext y
      simp only [mem_ofPred_eq,Set.mem_sdiff,Classical.not_imp]
    rw [←he]
    exact ae_iff.mp ((ae_restrict_iff' hUm).mp hmem)

end ScalarConductivity

end
end

end OAI
