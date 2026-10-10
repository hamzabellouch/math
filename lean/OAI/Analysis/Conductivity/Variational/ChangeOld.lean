import Mathlib
import OAI.Analysis.Conductivity.Geometry.CompactSplitSubpatch

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma fderiv_eq_of_eqOn_open {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {O : Set E} (hO : IsOpen O)
    {u v : E → V} (he : EqOn u v O) {x : E} (hx : x ∈ O) :
    fderiv ℝ u x = fderiv ℝ v x := by
  apply Filter.EventuallyEq.fderiv_eq
  exact Filter.EventuallyEq.filter_mono (he.eventuallyEq_of_mem (hO.mem_nhds hx)) le_rfl

def CompactTwoFieldReplacement.changeOld
    {μ : Measure Coord3} {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    (R : CompactTwoFieldReplacement μ O u A) (he : EqOn u v O) (hAB : EqOn A B O) :
    CompactTwoFieldReplacement μ O v B where
  du := R.du
  dF := R.dF
  tensor := R.tensor
  smooth_du := R.smooth_du
  compact_du := R.compact_du
  support_du := R.support_du
  smooth_dF := R.smooth_dF
  compact_dF := R.compact_dF
  support_dF := R.support_dF
  cauchy_dF := R.cauchy_dF
  smooth_tensor := R.smooth_tensor
  rank := by
    intro x hx
    rw [← fderiv_eq_of_eqOn_open hO (show EqOn (fun y => u y+R.du y)
      (fun y => v y+R.du y) O from fun y hy => by dsimp only; rw [he hy]) hx]
    exact R.rank x hx
  constitutive := by
    intro x hx
    rw [← fderiv_eq_of_eqOn_open hO (show EqOn (fun y => u y+R.du y)
      (fun y => v y+R.du y) O from fun y hy => by dsimp only; rw [he hy]) hx]
    rw [R.constitutive x hx]
    simp only [conductivityFlux, hAB hx, fderiv_eq_of_eqOn_open hO he hx]

theorem exists_locally_smooth_compact_split
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) {p : Coord3}
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hpU : p ∈ U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hD : Function.Surjective (fderiv ℝ u p))
    (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
    (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
    {θ c m : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hm : 0 < m) (hpath : ∀ z ∈ Icc (-θ) (1-θ), m ≤ 1+c*z)
    (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-θ) (1-θ), ContinuousAt C z)
    (hCs : ∀ z ∈ Icc (-θ) (1-θ), ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun t => (C t).val) z)
    (hdet : ∀ z ∈ Icc (-θ) (1-θ), 0 < (splitJacobian d L c z).det)
    (hconstit : ∀ z ∈ Icc (-θ) (1-θ),
      (C z).val = (splitJacobian d L c z).det⁻¹ •
        (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
    {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
    (hCG : ∀ z ∈ Icc (-θ) (1-θ), (z, C z) ∈ G) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ (R : CompactTwoFieldReplacement μ O u A) (q : Coord3 → ℝ),
        ContDiff ℝ (↑(⊤ : ℕ∞)) q ∧ (∀ x, q x ∈ Icc (-θ) (1-θ)) ∧
        (∀ x ∈ O, (q x, R.tensor x) ∈ G) ∧
        μ {x | x ∈ O ∧ q x ≠ -θ ∧ q x ≠ 1-θ} ≤ ENNReal.ofReal ε := by
  obtain ⟨v, V, hv, _, hV, hpV, hVU, he⟩ := exists_smooth_compact_extension
    hU hUb isCompact_singleton (singleton_subset_iff.mpr hpU) u hu
  have hep : fderiv ℝ v p = fderiv ℝ u p := fderiv_eq_of_eqOn_open hV he (hpV (mem_singleton p))
  have hAp : ContinuousAt A p :=
    Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      (hA.continuousOn.continuousAt (hU.mem_nhds hpU))
  have hdivv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ V → (∫ x, fderiv ℝ ψ x ((conductivityFlux v A x).col j) ∂μ) = 0 := by
    intro j ψ hψ hc hs
    rw [derivative_test_integral_congr μ ψ _ (fun x => (conductivityFlux u A x).col j) (by
      intro x hx
      simp only [conductivityFlux, fderiv_eq_of_eqOn_open hV he (hs hx)])]
    exact hdiv j ψ hψ hc (hs.trans hVU)
  obtain ⟨W, hW, hpW, hWV, hWc, hw⟩ := exists_compact_split_on_subpatch μ v hv A hAp
    hV (hUb.subset hVU) (hpV (mem_singleton p)) (hA.mono hVU) hdivv (hep ▸ hD)
    d L hLd B hB hBn hθ hθ1 hm hpath C hC hCs hdet hconstit hG hCG
  refine ⟨W, hW, hpW, hWV.trans hVU, hWc, ?_⟩
  intro O hO hOW ε hε
  obtain ⟨R, q, hq, hqr, hqG, hqm⟩ := hw O hO hOW ε hε
  exact ⟨R.changeOld hO (he.mono (hOW.trans (subset_closure.trans hWV))) (fun _ _ => rfl),
    q, hq, hqr, hqG, hqm⟩

end ScalarConductivity

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem local_compact_piola_difference_regular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : E ≃ E) (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y)
    (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (F : E → E) (hF : ContDiffOn ℝ (↑(⊤ : ℕ∞)) F U) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => piolaFlux Y F x-F x) ∧
    HasCompactSupport (fun x => piolaFlux Y F x-F x) ∧
    tsupport (fun x => piolaFlux Y F x-F x) ⊆ K := by
  obtain ⟨G, W, hG, _, _, hKW, _, he⟩ := exists_smooth_compact_extension hU hUb hK hKU F hF
  have hsame : (fun x => piolaFlux Y F x-F x) = fun x => piolaFlux Y G x-G x := by
    funext x
    by_cases hx : x ∈ K
    · have hix := (equiv_mapsTo_of_fixed_compl Y K hoff).2 hx
      dsimp only [piolaFlux]
      rw [he (hKW hx), he (hKW hix)]
    · rw [piolaFlux_eq_off Y hK.isClosed hoff F hx,
        piolaFlux_eq_off Y hK.isClosed hoff G hx, sub_self, sub_self]
  have hs : tsupport (fun x => piolaFlux Y F x-F x) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (by dsimp only; rw [piolaFlux_eq_off Y hK.isClosed hoff F hn, sub_self])
  refine ⟨?_, hK.of_isClosed_subset isClosed_closure hs, hs⟩
  rw [hsame]
  exact (piolaFlux_contDiff Y hY hi G hG).sub hG

theorem local_compact_updated_flux_regular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : E ≃ E) (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y)
    (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (F δ : E → E) (hF : ContDiffOn ℝ (↑(⊤ : ℕ∞)) F U)
    (hδ : ContDiff ℝ (↑(⊤ : ℕ∞)) δ) (hsδ : tsupport δ ⊆ K) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ∧
    HasCompactSupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ∧
    tsupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ⊆ K := by
  obtain ⟨hs, _, hsk⟩ := local_compact_piola_difference_regular Y hY hi hU hUb hK hKU hoff F hF
  have hp := piolaFlux_contDiff Y hY hi δ hδ
  have hps := piolaFlux_tsupport_subset Y hK.isClosed hoff δ hsδ
  have heq : (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) =
      fun x => (piolaFlux Y F x-F x)+piolaFlux Y δ x := by
    rw [piolaFlux_add]
    funext x; simp only [sub_eq_add_neg]; ac_rfl
  have htotal : tsupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ⊆ K := by
    rw [heq]
    exact (tsupport_add _ _).trans (union_subset hsk hps)
  refine ⟨?_, hK.of_isClosed_subset isClosed_closure htotal, htotal⟩
  rw [heq]
  exact hs.add hp

end ScalarConductivity

end

end OAI
