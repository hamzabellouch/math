import OAI.Geometry.NodalSets.Elliptic.CorrugationGainStage

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology

theorem exists_finite_corrugation_gain {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (o : Coord) (L : ℝ), 0 < L →
      ∀ (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (U : Set Coord),
      IsOpen U → Icc o (fun j ↦ o j+L) ⊆ U → ContDiffOn ℝ ∞ g U →
      (∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), ∀ u v, g y u v = g y v u) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v) →
      ∀ S : Coord → ℝ, ContDiffOn ℝ ∞ S U →
      sourceDirectionalAdmissibleOn g S (Icc o (fun j ↦ o j+L)) →
      ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ w : Coord → ℝ,
      ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      tsupport w ⊆ interior (Icc o (fun j ↦ o j+L)) ∧ (∀ x, |w x| < ε) ∧
      sourceDirectionalAdmissibleOn g (S+w) (Icc o (fun j ↦ o j+L)) ∧
      (1+γ)^n*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x) ≤
        ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g (S+w) x := by
  obtain ⟨γ,hγ,hstage⟩ := exists_small_corrugation_gain_stage hc hM
  refine ⟨γ,hγ,?_⟩
  intro o L hL g U hU hDU hg hp hsym hcmp S hS hadm n
  induction n with
  | zero =>
    intro ε hε
    refine ⟨0,contDiff_const,HasCompactSupport.zero,?_,?_,?_,?_⟩
    · simp
    · simpa using fun _ : Coord ↦ hε
    · simpa using hadm
    · simp
  | succ n ih =>
    intro ε hε
    obtain ⟨v,hv,hvc,hvs,hvb,hva,hvg⟩ := ih (ε/2) (by linarith)
    obtain ⟨w,hw,hwc,hws,hwb,hwa,hwg⟩ := hstage o L hL g U hU hDU hg hp hsym hcmp
      (S+v) (hS.add hv.contDiffOn) hva (ε/2) (by linarith)
    refine ⟨v+w,hv.add hw,hvc.add hwc,(tsupport_add v w).trans (union_subset hvs hws),?_,?_,?_⟩
    · intro x
      change |v x+w x| < ε
      exact (abs_add_le _ _).trans_lt (by linarith [hvb x,hwb x])
    · simpa only [add_assoc] using hwa
    · calc
        (1+γ)^(n+1)*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x) =
            (1+γ)*((1+γ)^n*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x)) := by
              rw [pow_succ]; ring
        _ ≤ (1+γ)*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g (S+v) x) :=
          mul_le_mul_of_nonneg_left hvg (by linarith)
        _ ≤ ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g (S+(v+w)) x := by
          simpa only [add_assoc] using hwg

open Yau.Jets Set Filter
open scoped Topology

lemma sourceDirectionalAdmissible_congr (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S R : Coord → ℝ) {x : Coord} (he : S =ᶠ[𝓝 x] R) :
    sourceDirectionalAdmissibleOn g S {x} ↔ sourceDirectionalAdmissibleOn g R {x} := by
  have hp : metricGradient g S x = metricGradient g R x := by simp only [metricGradient,he.fderiv_eq]
  have hH : sourceHessian g S x = sourceHessian g R x := by
    simp only [sourceHessian,he.fderiv_eq,he.fderiv.fderiv_eq]
  simp only [sourceDirectionalAdmissibleOn,mem_singleton_iff,forall_eq,hp,hH]

lemma sourceDirectionalAdmissible_support (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S w : Coord → ℝ) {K D : Set Coord} (hs : tsupport w ⊆ D)
    (hold : sourceDirectionalAdmissibleOn g S K)
    (hnew : sourceDirectionalAdmissibleOn g (S+w) D) :
    sourceDirectionalAdmissibleOn g (S+w) K := by
  intro x hx
  by_cases hd : x ∈ D
  · exact hnew x hd
  · have he : S+w =ᶠ[𝓝 x] S := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun hw ↦ hd (hs hw))] with y hy
      simp [hy]
    have hh : sourceDirectionalAdmissibleOn g S {x} := fun y hy ↦ by
      rw [mem_singleton_iff] at hy
      subst y
      exact hold x hx
    exact ((sourceDirectionalAdmissible_congr g (S+w) S he).mpr hh) x (mem_singleton x)

end Yau.Geometry

end

end OAI
