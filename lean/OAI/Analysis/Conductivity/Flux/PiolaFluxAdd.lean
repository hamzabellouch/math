import Mathlib
import OAI.Analysis.Conductivity.Variational.QuantitativeLocalTwoFieldSplit
import OAI.Analysis.Conductivity.Variational.SmoothCompactExtension

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
open Set MeasureTheory Filter Topology

lemma piolaFlux_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : E ≃ E) (F G : E → E) :
    piolaFlux Y (fun x => F x + G x) = fun x => piolaFlux Y F x + piolaFlux Y G x := by
  funext x
  simp only [piolaFlux, map_add, smul_add]

lemma piolaFlux_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : E ≃ E) {K : Set E} (hK : IsClosed K) (hoff : ∀ x ∉ K, Y x = x)
    (F : E → E) (hF : tsupport F ⊆ K) : tsupport (piolaFlux Y F) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  have hi := equiv_symm_eq_off Y hoff x hn
  have hz : F x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hn (hF h))
  apply hx
  simp only [piolaFlux, hi, hz, map_zero, smul_zero]

theorem local_compact_recomposition_difference
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Y : E ≃ E) (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (u : E → V) (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => u (Y.symm x)-u x) ∧
    HasCompactSupport (fun x => u (Y.symm x)-u x) ∧
    tsupport (fun x => u (Y.symm x)-u x) ⊆ K := by
  obtain ⟨v, W, hv, _, _, hKW, _, he⟩ := exists_smooth_compact_extension hU hUb hK hKU u hu
  have heq : (fun x => u (Y.symm x)-u x) = fun x => v (Y.symm x)-v x := by
    funext x
    by_cases hx : x ∈ K
    · have hix := (equiv_mapsTo_of_fixed_compl Y K hoff).2 hx
      rw [he (hKW hx), he (hKW hix)]
    · rw [equiv_symm_eq_off Y hoff x hx]
      simp
  have hs : tsupport (fun x => u (Y.symm x)-u x) ⊆ K :=
    tsupport_comp_equiv_sub Y.symm hK.isClosed (equiv_symm_eq_off Y hoff) u
  refine ⟨?_, hK.of_isClosed_subset isClosed_closure hs, hs⟩
  rw [heq]
  exact (hv.comp hi).sub hv

theorem local_compact_updated_flux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (Y : E ≃ E)
    (hY : ContDiff ℝ (↑(⊤ : ℕ∞)) Y) (hi : ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm)
    {K U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hoff : ∀ x ∉ K, Y x = x)
    (F δ : E → E) (hF : ContDiffOn ℝ (↑(⊤ : ℕ∞)) F U)
    (hdiv : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0)
    (hδ : ContDiff ℝ (↑(⊤ : ℕ∞)) δ) (hsδ : tsupport δ ⊆ K)
    (hδdiv : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (δ x) ∂μ) = 0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ∧
    HasCompactSupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ∧
    tsupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ⊆ K ∧
    ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (piolaFlux Y (fun z => F z+δ z) x-F x) ∂μ) = 0 := by
  obtain ⟨hs, hc, hsk, hpair⟩ := local_compact_piola_Cauchy_difference μ Y hY hi
    hU hUb hK hKU hoff F hF hdiv
  have hp := piolaFlux_contDiff Y hY hi δ hδ
  have hps := piolaFlux_tsupport_subset Y hK.isClosed hoff δ hsδ
  have hpc : HasCompactSupport (piolaFlux Y δ) := hK.of_isClosed_subset isClosed_closure hps
  have heq : (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) =
      fun x => (piolaFlux Y F x-F x)+piolaFlux Y δ x := by
    rw [piolaFlux_add]
    funext x; simp only [sub_eq_add_neg]; ac_rfl
  have htotal : tsupport (fun x => piolaFlux Y (fun z => F z+δ z) x-F x) ⊆ K := by
    rw [heq]
    exact (tsupport_add (fun x => piolaFlux Y F x-F x) (piolaFlux Y δ)).trans (union_subset hsk hps)
  refine ⟨?_, hK.of_isClosed_subset isClosed_closure htotal, htotal, ?_⟩
  · rw [heq]
    exact hs.add hp
  · intro ψ hψ
    simp_rw [congrFun heq, map_add]
    rw [integral_add (smooth_flux_integrable_pairing μ _ hs.continuous hc ψ hψ)
      (smooth_flux_integrable_pairing μ _ hp.continuous hpc ψ hψ), hpair ψ hψ,
      piolaFlux_zero_pairing μ Y hY hi δ hδdiv ψ hψ, zero_add]

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma operatorMatrix_contDiff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {k : WithTop ℕ∞} :
    ContDiff ℝ k (operatorMatrix : ((n → ℝ) →L[ℝ] (m → ℝ)) → Matrix m n ℝ) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  exact contDiff_pi.mp (contDiff_id.clm_apply contDiff_const) i

lemma contDiff_gradientColumns {m : Type*} [Fintype m] [DecidableEq m]
    (u : Coord3 → m → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => gradientColumns (fderiv ℝ u x)) := by
  rw [contDiff_iff_contDiffAt]; intro x
  exact contDiffAt_matrix_transpose ((operatorMatrix_contDiff (m := m) (n := Fin 3)).contDiffAt.comp x
    (hu.contDiffAt.fderiv_right (by simp)))

noncomputable def conductivityFlux (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    (x : Coord3) : Matrix (Fin 3) (Fin 2) ℝ :=
  (A x).val * gradientColumns (fderiv ℝ u x)

lemma conductivityFlux_contDiffOn (u : Coord3 → Fin 2 → ℝ)
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hU : IsOpen U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (conductivityFlux u A) U := by
  intro x hx
  exact (contDiffAt_matrix_mul ((hA x hx).contDiffAt (hU.mem_nhds hx))
    (contDiff_gradientColumns u hu).contDiffAt).contDiffWithinAt

structure CompactTwoFieldReplacement (μ : Measure Coord3) (O : Set Coord3)
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
  rank : ∀ x ∈ O, LinearIndependent ℝ
    (gradientColumns (fderiv ℝ (fun y => u y+du y) x)).col
  constitutive : ∀ x ∈ O, (tensor x).val *
    gradientColumns (fderiv ℝ (fun y => u y+du y) x) = conductivityFlux u A x + dF x

lemma tsupport_matrix_subset {X m n : Type*} [TopologicalSpace X]
    [Fintype m] [Fintype n] (F : X → Matrix m n ℝ) {K : Set X} (hK : IsClosed K)
    (hF : ∀ j, tsupport (fun x => (F x).col j) ⊆ K) : tsupport F ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  apply hx
  ext i j
  exact congrFun (image_eq_zero_of_notMem_tsupport (fun hk => hn (hF j hk))) i

theorem synchronized_compact_replacement
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {U O K : Set Coord3}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hOU : O ⊆ U)
    (hK : IsCompact K) (hKO : K ⊆ O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
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
    ∃ R : CompactTwoFieldReplacement μ O u A, ∀ x ∈ O,
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
  have hdcol (j : Fin 2) := local_compact_updated_flux μ Y hY hYi hU hUb hK
    (hKO.trans hOU) hoff (fun x => (conductivityFlux u A x).col j) (δ j)
    (hcol j) (hdiv j) (hδ j) (hsδ j) (hδdiv j)
  have hdFe (j : Fin 2) : (fun x => (dF x).col j) =
      fun x => piolaFlux Y (fun t => (conductivityFlux u A t).col j + δ j t) x -
        (conductivityFlux u A x).col j := by rfl
  have hdFs : ContDiff ℝ (↑(⊤ : ℕ∞)) dF := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    exact contDiff_pi.mp (hdFe j ▸ (hdcol j).1) i
  have hdsupp : tsupport dF ⊆ K := tsupport_matrix_subset dF hK.isClosed
    (fun j => hdFe j ▸ (hdcol j).2.2.1)
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
  · intro j ψ hψ
    simpa only [congrFun (hdFe j)] using (hdcol j).2.2.2 ψ hψ
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

end ScalarConductivity

end

end OAI
