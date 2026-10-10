import Mathlib
import OAI.Analysis.Conductivity.Geometry.LocalSplitSubpatchRetained
import OAI.Analysis.Conductivity.Flux.PiolaFluxAdd

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

theorem exists_compact_split_on_subpatch
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {p : Coord3} (hAp : ContinuousAt A p)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hpU : p ∈ U)
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
        ContDiff ℝ (↑(⊤ : ℕ∞)) q ∧
        (∀ x, q x ∈ Icc (-θ) (1-θ)) ∧
        (∀ x ∈ O, (q x, R.tensor x) ∈ G) ∧
        μ {x | x ∈ O ∧ q x ≠ -θ ∧ q x ≠ 1-θ} ≤ ENNReal.ofReal ε := by
  obtain ⟨X, W, hW, hpW, hWU, hWc, hWX, hX, hXi, hop⟩ :=
    exists_local_split_on_subpatch_retained μ u hu A hAp hD d L hLd B hB hBn
      hθ hθ1 hm hpath C hC hdet hconstit hG hCG hU hpU
  refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
  intro O hO hOW ε hε
  have hOU : O ⊆ U := hOW.trans (subset_closure.trans hWU)
  have hOX : O ⊆ X.source := hOW.trans hWX
  obtain ⟨χ, H, F, hχc, hχO, hχb, hHr, hF, hFs, hFdiv, hn⟩ := hop O hO hOW ε hε
  obtain ⟨n, hn⟩ := hn.exists
  obtain ⟨Y, hY, hYi, hoffO, _, hform, hpure, hstate⟩ := hn
  have hχt : tsupport χ.val ⊆ X.target := hχO.trans (by
    rintro y ⟨x, hx, rfl⟩; exact X.map_source (hOX hx))
  let K := X.symm '' tsupport χ.val
  have hK : IsCompact K := hχc.image_of_continuousOn (X.symm.continuousOn.mono hχt)
  have hKO : K ⊆ O := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hχO hy
    simpa only [X.left_inv (hOX ht)] using ht
  have hχp := localPullback_tsupport X χ.val hχc hχt
  have hoff : ∀ x ∉ K, Y x = x := by
    intro x hx
    have hz := image_eq_zero_of_notMem_tsupport (fun h => hx (hχp.2.1 h))
    rw [hform x, hz, mul_zero, zero_mul, zero_smul, add_zero]
  let z : Coord3 → ℝ := fun x => localPullback X χ.val x *
    (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x))
  have hz : ContDiff ℝ (↑(⊤ : ℕ∞)) z :=
    (localPullback_contDiff X hX.contDiffOn χ.val (smoothScalar_contDiff χ) hχc hχt).mul
      ((smoothScalar_contDiff (smoothDirection 1 H)).comp
        (contDiff_const.mul (L.contDiff.comp hX)))
  have hzr : ∀ x, z x ∈ Icc (-θ) (1-θ) := fun x =>
    scalar_cutoff_segment hθ.le (by linarith) (localPullback_bounds X χ.val hχb x) (hHr _)
  obtain ⟨R, hRt⟩ := synchronized_compact_replacement μ u hu A hU hUb hOU hK hKO hA hdiv
    Y hY hYi hoff z hz C (fun x _ => hCs _ (hzr x)) (F (n+1 : ℝ))
    (hF _) (fun j => (hFs _ j).2.2) (hFdiv _) (fun x hx =>
      ⟨(hstate x hx).1, (hstate x hx).2.1, (hstate x hx).2.2.2⟩)
  let q : Coord3 → ℝ := z ∘ Y.symm
  have him : MapsTo Y.symm O O := (equiv_mapsTo_of_fixed_compl Y O hoffO).2
  refine ⟨R, q, hz.comp hYi, fun x => hzr _, ?_, hpure⟩
  intro x hx
  have ht := hRt (Y.symm x) (him hx)
  rw [Y.apply_symm_apply] at ht
  rw [ht]
  exact (hstate (Y.symm x) (him hx)).2.2.1

end ScalarConductivity

end

end OAI
