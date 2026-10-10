import OAI.Geometry.NodalSets.Elliptic.CorrugationFiniteGainLemmas

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal
noncomputable section

theorem exists_large_admissible_corrugation (o : Coord) {L : ℝ} (hL : 0 < L)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    {U : Set Coord} (hU : IsOpen U) (hDU : Icc o (fun j ↦ o j+L) ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ Icc o (fun j ↦ o j+L), ∀ u v, g y u v = g y v u)
    (hadm : sourceDirectionalAdmissibleOn g S (Icc o (fun j ↦ o j+L)))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : Coord → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      tsupport w ⊆ interior (Icc o (fun j ↦ o j+L)) ∧ (∀ x, |w x| < ε) ∧ (∀ x, |w x| ≤ ε/2) ∧
      ContDiffOn ℝ ∞ (S+w) U ∧
      T < ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g (S+w) x ∧
      ∃ V : Set Coord, IsOpen V ∧ Icc o (fun j ↦ o j+L) ⊆ V ∧ V ⊆ U ∧
        sourceDirectionalAdmissibleOn g (S+w) V := by
  let D := Icc o (fun j ↦ o j+L)
  obtain ⟨c,hc,M,hM,hcmp⟩ := compact_metric_comparison g isCompact_Icc (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨γ,hγ,hfinite⟩ := exists_finite_corrugation_gain hc hM
  obtain ⟨m,hm,B,hB,hs⟩ := corrugationOldSlope_compact_bounds g S isCompact_Icc hU hDU hg hS hp
    (fun y hy ↦ (hadm y hy).1)
  have hvol : volume.real D = L^4 := by
    simp [D,measureReal_def,Real.volume_Icc_pi,ENNReal.toReal_ofReal hL.le]
  have hoint : IntegrableOn (corrugationOldSlope g S) D :=
    ((corrugationOldSlope_continuousOn g S hU hg hS hp).mono hDU).integrableOn_Icc
  have hlow : m*volume.real D ≤ ∫ x in D, corrugationOldSlope g S x := by
    have hh := setIntegral_mono_on (integrableOn_const (isCompact_Icc.measure_ne_top (μ := volume)))
      hoint measurableSet_Icc (fun x hx ↦ (hs x hx).1)
    simpa only [setIntegral_const,smul_eq_mul,mul_comm] using hh
  have hpos : 0 < ∫ x in D, corrugationOldSlope g S x := by
    rw [hvol] at hlow
    exact (mul_pos hm (pow_pos hL 4)).trans_le hlow
  obtain ⟨n,hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by linarith : 1 < 1+γ)).eventually_gt_atTop
    (T/(∫ x in D, corrugationOldSlope g S x))).exists
  have hn' : T < (1+γ)^n*(∫ x in D, corrugationOldSlope g S x) := (div_lt_iff₀ hpos).mp hn
  obtain ⟨w,hw,hwc,hws,hwb,hwa,hwg⟩ := hfinite o L hL g U hU hDU hg hp hsym hcmp S hS hadm n (ε/2) (by linarith)
  have hnewS := hS.add hw.contDiffOn
  refine ⟨w,hw,hwc,hws,fun x ↦ (hwb x).trans (by linarith),fun x ↦ (hwb x).le,hnewS,hn'.trans_le hwg,?_⟩
  exact source_admissibility_neighborhood g (S+w) hU hDU hg hnewS hp hwa

end
end Yau.Geometry

end OAI
