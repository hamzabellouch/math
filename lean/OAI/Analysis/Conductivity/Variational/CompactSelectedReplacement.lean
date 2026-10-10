import Mathlib
import OAI.Analysis.Conductivity.Variational.ChangeOld

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

structure CompactSelectedReplacement (J : Set (Fin 2)) (μ : Measure Coord3) (O : Set Coord3)
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
  cauchy_dF : ∀ j ∈ J, ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
    (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0
  smooth_tensor : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (tensor x).val) O
  rank : ∀ x ∈ O, LinearIndependent ℝ
    (gradientColumns (fderiv ℝ (fun y => u y+du y) x)).col
  constitutive : ∀ x ∈ O, (tensor x).val *
    gradientColumns (fderiv ℝ (fun y => u y+du y) x) = conductivityFlux u A x + dF x

theorem synchronized_selected_replacement
    (J : Set (Fin 2))
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {U O K : Set Coord3}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hOU : O ⊆ U)
    (hK : IsCompact K) (hKO : K ⊆ O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j ∈ J, ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (Y : Coord3 ≃ Coord3) (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y)
    (hYi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm) (hoff : ∀ x ∉ K, Y x = x)
    (z : Coord3 → ℝ) (hz : ContDiff ℝ (↑(⊤ : ℕ∞)) z)
    (C : ℝ → Symmetric3)
    (hC : ∀ x ∈ O, ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun t => (C t).val) (z x))
    (δ : Fin 2 → Coord3 → Coord3)
    (hδ : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (δ j))
    (hsδ : ∀ j, tsupport (δ j) ⊆ K)
    (hδdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (δ j x) ∂μ) = 0)
    (hstate : ∀ x ∈ O,
      let E := gradientColumns (fderiv ℝ u x)
      let Ft := conductivityFlux u A x + Matrix.of (fun i j => δ j x i)
      let J := operatorMatrix (fderiv ℝ Y x)
      let At := repairPushed (C (z x)) J E Ft
      0 < J.det ∧ LinearIndependent ℝ E.col ∧
        At.val * gradientColumns (fderiv ℝ (u ∘ Y.symm) (Y x)) = pushFlux J Ft) :
    ∃ R : CompactSelectedReplacement J μ O u A, ∀ x ∈ O,
      R.tensor (Y x) = repairPushed (C (z x)) (operatorMatrix (fderiv ℝ Y x))
        (gradientColumns (fderiv ℝ u x))
        (conductivityFlux u A x + Matrix.of (fun i j => δ j x i)) := by
  classical
  let Ft : Coord3 → Matrix (Fin 3) (Fin 2) ℝ :=
    fun x => conductivityFlux u A x + Matrix.of (fun i j => δ j x i)
  let G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ :=
    fun x => Matrix.of (fun i j => piolaFlux Y (fun t => (Ft t).col j) x i)
  let dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun x => G x - conductivityFlux u A x
  let B : Coord3 → Symmetric3 := fun x => repairPushed (C (z x))
    (operatorMatrix (fderiv ℝ Y x)) (gradientColumns (fderiv ℝ u x)) (Ft x)
  let du : Coord3 → Fin 2 → ℝ := fun x => u (Y.symm x)-u x
  have heq : (fun x => u x+du x) = u ∘ Y.symm := by
    funext x; simp only [du, Function.comp_apply]; abel
  have him : MapsTo Y.symm O O := (equiv_mapsTo_of_fixed_compl Y O
    (fun x hx => hoff x (fun hk => hx (hKO hk)))).2
  have hF := conductivityFlux_contDiffOn u hu A hU hA
  have hcol (j : Fin 2) : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun x => (conductivityFlux u A x).col j) U := by
    apply contDiffOn_pi.mpr; intro i
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hF i) j
  have hdcol (j : Fin 2) := local_compact_updated_flux_regular Y hY hYi hU hUb hK
    (hKO.trans hOU) hoff (fun x => (conductivityFlux u A x).col j) (δ j)
    (hcol j) (hδ j) (hsδ j)
  have hdFe (j : Fin 2) : (fun x => (dF x).col j) =
      fun x => piolaFlux Y (fun t => (conductivityFlux u A t).col j + δ j t) x -
        (conductivityFlux u A x).col j := by rfl
  have hdFs : ContDiff ℝ (↑(⊤ : ℕ∞)) dF := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    exact contDiff_pi.mp (hdFe j ▸ (hdcol j).1) i
  have hdsupp : tsupport dF ⊆ K := tsupport_matrix_subset dF hK.isClosed
    (fun j => hdFe j ▸ (hdcol j).2.2)
  have hdu := local_compact_recomposition_difference Y hYi hU hUb hK
    (hKO.trans hOU) hoff u hu.contDiffOn
  have hBs : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (B x).val) O := by
    intro x hx
    have hd := (hstate x hx).1.ne'
    have hi := (hstate x hx).2.1
    have hFt : ContDiffAt ℝ (↑(⊤ : ℕ∞)) Ft x := by
      apply ((hF x (hOU hx)).contDiffAt (hU.mem_nhds (hOU hx))).add
      apply contDiffAt_pi.mpr; intro i
      apply contDiffAt_pi.mpr; intro j
      exact contDiffAt_pi.mp (hδ j).contDiffAt i
    exact (contDiffAt_repairPushed (fun x => C (z x)) _ _ _
      ((hC x hx).comp x hz.contDiffAt)
      ((operatorMatrix_contDiff (m := Fin 3) (n := Fin 3)).contDiffAt.comp x (hY.contDiffAt.fderiv_right (by simp)))
      (contDiff_gradientColumns u hu).contDiffAt hFt hd hi).contDiffWithinAt
  refine ⟨{
    du := du, dF := dF, tensor := B ∘ Y.symm
    smooth_du := hdu.1, compact_du := hdu.2.1, support_du := hdu.2.2.trans hKO
    smooth_dF := hdFs, compact_dF := hK.of_isClosed_subset isClosed_closure hdsupp
    support_dF := hdsupp.trans hKO
    cauchy_dF := ?_
    smooth_tensor := hBs.comp hYi.contDiffOn him
    rank := ?_
    constitutive := ?_ }, ?_⟩
  · intro j hj ψ hψ
    have hh := local_compact_updated_flux μ Y hY hYi hU hUb hK (hKO.trans hOU) hoff
      (fun x => (conductivityFlux u A x).col j) (δ j) (hcol j) (hdiv j hj)
      (hδ j) (hsδ j) (hδdiv j)
    simpa only [congrFun (hdFe j)] using hh.2.2.2 ψ hψ
  · intro x hx
    rw [heq, ← Y.apply_symm_apply x, gradientColumns_recomposition Y
      (hY.differentiable (by simp)) (hYi.differentiable (by simp)) u (hu.differentiable (by simp))]
    exact pushGradient_rank _ (hstate (Y.symm x) (him hx)).1.ne' _
      (hstate (Y.symm x) (him hx)).2.1
  · intro x hx
    rw [heq]
    have hh := (hstate (Y.symm x) (him hx)).2.2
    rw [Y.apply_symm_apply] at hh
    change (B (Y.symm x)).val * gradientColumns (fderiv ℝ (u ∘ Y.symm) x) =
      conductivityFlux u A x + dF x
    rw [hh]
    have he : conductivityFlux u A x+dF x=G x := by simp only [dF]; abel
    rw [he]
    ext i j
    have hd : 0 < (fderiv ℝ Y (Y.symm x)).det := by
      rw [← operatorMatrix_det]; exact (hstate (Y.symm x) (him hx)).1
    have hp := piolaFlux_columns Y Ft hd j
    rw [Y.apply_symm_apply] at hp
    exact congrFun hp.symm i
  · intro x _
    simp only [Function.comp_apply, Y.symm_apply_apply, B, Ft]

theorem exists_selected_split_on_subpatch
    (J : Set (Fin 2))
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {p : Coord3} (hAp : ContinuousAt A p)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hpU : p ∈ U)
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
  obtain ⟨R, hRt⟩ := synchronized_selected_replacement J μ u hu A hU hUb hOU hK hKO hA hdiv
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
