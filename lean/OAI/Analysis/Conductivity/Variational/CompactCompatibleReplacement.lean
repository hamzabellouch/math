import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactSelectedReplacement

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
open Matrix Set MeasureTheory
open scoped Matrix.Norms.Elementwise

structure CompactCompatibleReplacement (μ : Measure Coord3) (O : Set Coord3)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) where
  du : Coord3 → Fin 2 → ℝ
  dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ
  tensor : Coord3 → Symmetric3
  smooth_du : ContDiff ℝ (↑(⊤ : ℕ∞)) du
  compact_du : HasCompactSupport du
  support_du : tsupport du ⊆ O
  smooth_dF : ContDiff ℝ (↑(⊤ : ℕ∞)) dF
  compact_dF : HasCompactSupport dF
  support_dF : tsupport dF ⊆ O
  cauchy_dF : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
    (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0
  smooth_tensor : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (tensor x).val) O
  constitutive : ∀ x ∈ O, (tensor x).val *
    gradientColumns (fderiv ℝ (fun y => u y+du y) x) = conductivityFlux u A x + dF x

def CompactTwoFieldReplacement.forgetRank {μ : Measure Coord3} {O : Set Coord3}
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactTwoFieldReplacement μ O u A) : CompactCompatibleReplacement μ O u A where
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
  constitutive := R.constitutive

lemma gradientColumns_affine_column {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {l κ : Fin 2 → ℝ}
    (he : ∀ x ∈ O, ∀ j, u x j = l j * v x 0 + κ j)
    (hv : DifferentiableOn ℝ v O) {x : Coord3} (hx : x ∈ O) (i : Fin 3) (j : Fin 2) :
    gradientColumns (fderiv ℝ u x) i j = l j * gradientColumns (fderiv ℝ v x) i 0 := by
  let w : Coord3 → Fin 2 → ℝ := fun x j => l j * v x 0 + κ j
  have hw : HasFDerivAt w
      (ContinuousLinearMap.pi (fun j => l j •
        ((ContinuousLinearMap.proj 0).comp (fderiv ℝ v x)))) x := by
    apply hasFDerivAt_pi.mpr
    intro j
    exact (((ContinuousLinearMap.proj 0).hasFDerivAt.comp x
      (hv x hx |>.differentiableAt (hO.mem_nhds hx)).hasFDerivAt).const_mul (l j)).add_const (κ j)
  have heq : EqOn u w O := fun y hy => funext (he y hy)
  rw [fderiv_eq_of_eqOn_open hO heq hx, hw.fderiv]
  rfl

def CompactSelectedReplacement.affineTransfer
    {μ : Measure Coord3} {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {l κ : Fin 2 → ℝ}
    (he : ∀ x ∈ O, ∀ j, u x j = l j * v x 0 + κ j)
    (hv : ContDiffOn ℝ (↑(⊤ : ℕ∞)) v O)
    (R : CompactSelectedReplacement {0} μ O v A) :
    CompactCompatibleReplacement μ O u A := by
  classical
  let du : Coord3 → Fin 2 → ℝ := fun x j => l j * R.du x 0
  let dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun x i j => l j * R.dF x i 0
  have hdu : ContDiff ℝ (↑(⊤ : ℕ∞)) du :=
    contDiff_pi.mpr (fun j => contDiff_const.mul (contDiff_pi.mp R.smooth_du 0))
  have hdF : ContDiff ℝ (↑(⊤ : ℕ∞)) dF :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => contDiff_const.mul
      (contDiff_pi.mp (contDiff_pi.mp R.smooth_dF i) 0)))
  have hsu : Function.support du ⊆ Function.support R.du := by
    intro x hx hz
    apply hx
    ext j
    simp [du, hz]
  have hsF : Function.support dF ⊆ Function.support R.dF := by
    intro x hx hz
    apply hx
    ext i j
    simp [dF, hz]
  have hsdu : tsupport du ⊆ tsupport R.du := closure_mono hsu
  have hsdF : tsupport dF ⊆ tsupport R.dF := closure_mono hsF
  refine ⟨du, dF, R.tensor, hdu, R.compact_du.mono hsu, hsdu.trans R.support_du,
    hdF, R.compact_dF.mono hsF, hsdF.trans R.support_dF, ?_, R.smooth_tensor, ?_⟩
  · intro j ψ hψ
    have hecol : (fun x => (dF x).col j) = fun x => l j • (R.dF x).col 0 := rfl
    simp_rw [show ∀ x, (dF x).col j = l j • (R.dF x).col 0 from fun x => congrFun hecol x,
      map_smul, smul_eq_mul]
    rw [integral_const_mul, R.cauchy_dF 0 (by simp) ψ hψ, mul_zero]
  · intro x hx
    have hnew (y : Coord3) (hy : y ∈ O) (j : Fin 2) :
        (u y + du y) j = l j * (v y + R.du y) 0 + κ j := by
      simp only [Pi.add_apply, du, he y hy j]
      ring
    have hvd := hv.differentiableOn (by simp)
    have hvo := (hv.add R.smooth_du.contDiffOn).differentiableOn (by simp)
    ext i j
    change (∑ k, (R.tensor x).val i k * gradientColumns (fderiv ℝ (fun y => u y+du y) x) k j) =
      (∑ k, (A x).val i k * gradientColumns (fderiv ℝ u x) k j) + l j * R.dF x i 0
    simp_rw [gradientColumns_affine_column hO hnew hvo hx,
      gradientColumns_affine_column hO he hvd hx]
    have hr := congrFun (congrFun (R.constitutive x hx) i) 0
    change (∑ k, (R.tensor x).val i k * gradientColumns (fderiv ℝ (fun y => v y+R.du y) x) k 0) =
      (∑ k, (A x).val i k * gradientColumns (fderiv ℝ v x) k 0) + R.dF x i 0 at hr
    calc
      ∑ k, (R.tensor x).val i k * (l j * gradientColumns (fderiv ℝ (fun y => v y+R.du y) x) k 0) =
          l j * ∑ k, (R.tensor x).val i k * gradientColumns (fderiv ℝ (fun y => v y+R.du y) x) k 0 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      _ = l j * ((∑ k, (A x).val i k * gradientColumns (fderiv ℝ v x) k 0) + R.dF x i 0) := by rw [hr]
      _ = (∑ k, (A x).val i k * (l j * gradientColumns (fderiv ℝ v x) k 0)) + l j * R.dF x i 0 := by
        rw [mul_add, Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro k _; ring

lemma CompactSelectedReplacement.affineTransfer_relation
    {μ : Measure Coord3} {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {l κ : Fin 2 → ℝ}
    (he : ∀ x ∈ O, ∀ j, u x j = l j * v x 0 + κ j)
    (hv : ContDiffOn ℝ (↑(⊤ : ℕ∞)) v O)
    (R : CompactSelectedReplacement {0} μ O v A) :
    ∀ x ∈ O, ∀ j, (u x + (R.affineTransfer hO he hv).du x) j =
      l j * (v x + R.du x) 0 + κ j := by
  intro x hx j
  change u x j + l j * R.du x 0 = _
  rw [he x hx j]
  simp only [Pi.add_apply]
  ring

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def CompactSelectedReplacement.changeOld
    {J : Set (Fin 2)}
    {μ : Measure Coord3} {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    (R : CompactSelectedReplacement J μ O u A) (he : EqOn u v O) (hAB : EqOn A B O) :
    CompactSelectedReplacement J μ O v B where
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

theorem exists_locally_smooth_selected_split
    (J : Set (Fin 2))
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) {p : Coord3}
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hpU : p ∈ U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j ∈ J, ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
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
      ∃ (R : CompactSelectedReplacement J μ O u A) (q : Coord3 → ℝ),
        ContDiff ℝ (↑(⊤ : ℕ∞)) q ∧ (∀ x, q x ∈ Icc (-θ) (1-θ)) ∧
        (∀ x ∈ O, (q x, R.tensor x) ∈ G) ∧
        μ {x | x ∈ O ∧ q x ≠ -θ ∧ q x ≠ 1-θ} ≤ ENNReal.ofReal ε := by
  obtain ⟨v, V, hv, _, hV, hpV, hVU, he⟩ := exists_smooth_compact_extension
    hU hUb isCompact_singleton (singleton_subset_iff.mpr hpU) u hu
  have hep : fderiv ℝ v p = fderiv ℝ u p := fderiv_eq_of_eqOn_open hV he (hpV (mem_singleton p))
  have hAp : ContinuousAt A p :=
    Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      (hA.continuousOn.continuousAt (hU.mem_nhds hpU))
  have hdivv : ∀ j ∈ J, ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ V → (∫ x, fderiv ℝ ψ x ((conductivityFlux v A x).col j) ∂μ) = 0 := by
    intro j hj ψ hψ hc hs
    rw [derivative_test_integral_congr μ ψ _ (fun x => (conductivityFlux u A x).col j) (by
      intro x hx
      simp only [conductivityFlux, fderiv_eq_of_eqOn_open hV he (hs hx)])]
    exact hdiv j hj ψ hψ hc (hs.trans hVU)
  obtain ⟨W, hW, hpW, hWV, hWc, hw⟩ := exists_selected_split_on_subpatch J μ v hv A hAp
    hV (hUb.subset hVU) (hpV (mem_singleton p)) (hA.mono hVU) hdivv (hep ▸ hD)
    d L hLd B hB hBn hθ hθ1 hm hpath C hC hCs hdet hconstit hG hCG
  refine ⟨W, hW, hpW, hWV.trans hVU, hWc, ?_⟩
  intro O hO hOW ε hε
  obtain ⟨R, q, hq, hqr, hqG, hqm⟩ := hw O hO hOW ε hε
  exact ⟨R.changeOld hO (he.mono (hOW.trans (subset_closure.trans hWV))) (fun _ _ => rfl),
    q, hq, hqr, hqG, hqm⟩

end ScalarConductivity

end

end OAI
