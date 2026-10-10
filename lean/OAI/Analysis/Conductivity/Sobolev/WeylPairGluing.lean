import Mathlib
import OAI.Analysis.Conductivity.Variational.WeakHarmonicClassical
import OAI.Analysis.Conductivity.Variational.SmoothRepresentativeGluing

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

theorem weakWeyl_pair_cartesian_representative (f : Fin 2 → WholeL2) {U : Set R3}
    (hU : IsOpen U) (hf : ∀ j,WeaklyHarmonicOn (f j) U) :
    ∃ u : Coord3 → Fin 2 → ℝ,
      ContDiffOn ℝ (↑(⊤:ℕ∞)) u ((WithLp.toLp 2 : Coord3 → R3) ⁻¹' U) ∧
      (∀ᵐ y : Coord3,y∈(WithLp.toLp 2 : Coord3 → R3) ⁻¹' U →
        u y=fun j => f j (WithLp.toLp 2 y)) ∧
      ∀ᵐ y : Coord3,y∈(WithLp.toLp 2 : Coord3 → R3) ⁻¹' U →
        y∈regularRegion u (fun _ => ⟨1,Matrix.transpose_one⟩)
          ((WithLp.toLp 2 : Coord3 → R3) ⁻¹' U) := by
  classical
  let I := {p : R3×ℝ // 0<p.2 ∧ Metric.closedBall p.1 p.2⊆U}
  let O : I → Set R3 := fun i => Metric.ball i.val.1 (i.val.2/4)
  let g : I → R3 → Fin 2 → ℝ := fun i x j => radialMollify (f j) (i.val.2/4) x
  have hO (i : I) : IsOpen (O i) := Metric.isOpen_ball
  have hOU (i : I) : O i⊆U := by
    have hh : i.val.2 / 4 ≤ i.val.2 := by linarith [i.property.1]
    exact ((Metric.ball_subset_ball hh).trans Metric.ball_subset_closedBall).trans i.property.2
  have hcover : (⋃ i : I,O i)=U := by
    apply Subset.antisymm (iUnion_subset hOU)
    intro x hx
    obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
    exact mem_iUnion.mpr ⟨⟨(x,r),hr,hball⟩,Metric.mem_ball_self (by change 0<r/4; positivity)⟩
  have hgs (i : I) : ContDiff ℝ (↑(⊤:ℕ∞)) (g i) := by
    apply contDiff_pi.mpr
    intro j
    exact (weakWeyl_local (hf j) i.property.1 i.property.2).1
  have hge (i : I) : (fun x j => f j x)=ᵐ[volume.restrict (O i)] g i := by
    have hh (j : Fin 2) := (weakWeyl_local (hf j) i.property.1 i.property.2).2
    filter_upwards [ae_all_iff.mpr hh] with x hx
    exact funext hx
  obtain ⟨v,hvg,hve,hvs⟩ := smooth_representatives_glue volume O hO
    (fun x j => f j x) g (fun i => (hgs i).contDiffOn) hge
  rw [hcover] at hve hvs
  let P : Coord3 ≃L[ℝ] R3 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  let V : Set Coord3 := P ⁻¹' U
  let u : Coord3 → Fin 2 → ℝ := v ∘ P
  have hus : ContDiffOn ℝ (↑(⊤:ℕ∞)) u V :=
    hvs.comp P.contDiff.contDiffOn (fun _ hx => hx)
  have he : ∀ᵐ y : Coord3,y∈V → u y=fun j => f j (P y) := by
    have hh := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
      ((ae_restrict_iff' hU.measurableSet).mp hve)
    filter_upwards [hh] with y hy hyV
    exact (hy hyV).symm
  refine ⟨u,hus,he,?_⟩
  let A : Coord3 → Symmetric3 := fun _ => ⟨1,Matrix.transpose_one⟩
  have hp (i : I) : ∀ᵐ x∂volume.restrict (O i),P.symm x∈regularRegion u A V := by
    have hh := weakWeyl_pair_ae_regular (hf 0) (hf 1) i.property.1 i.property.2
    filter_upwards [ae_restrict_of_ae hh,ae_restrict_mem (hO i).measurableSet] with x hx hxO
    obtain ⟨r,hr,hball,hreg⟩ := hx hxO
    let W : Set Coord3 := P ⁻¹' Metric.ball x r
    have hW : IsOpen W := Metric.isOpen_ball.preimage P.continuous
    have hWV : W⊆V := preimage_mono (hball.trans (hOU i))
    have hg (j : Fin 2) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun x => g i x j) (Metric.ball x r) :=
      ((weakWeyl_local (hf j) i.property.1 i.property.2).1).contDiffOn
    have hrr := HarmonicPairRegularOn.toCartesian Metric.isOpen_ball hg hreg
    have heW : EqOn u (fun y j => g i (P y) j) W := by
      intro y hy
      exact hvg i (hball hy)
    refine mem_regularRegion_iff.mpr ⟨W,hWV,⟨hW,hus.mono hWV,contDiff_const.contDiffOn,
      hrr.congr hW heW⟩,?_⟩
    change P (P.symm x)∈Metric.ball x r
    rw [P.apply_symm_apply]
    exact Metric.mem_ball_self hr
  have hpU := ae_on_open_cover volume O hO
    (fun x => P.symm x∈regularRegion u A V) hp
  rw [hcover] at hpU
  have hh := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU.measurableSet).mp hpU)
  filter_upwards [hh] with y hy hyV
  exact hy hyV

end ScalarConductivity

end
end

end OAI
