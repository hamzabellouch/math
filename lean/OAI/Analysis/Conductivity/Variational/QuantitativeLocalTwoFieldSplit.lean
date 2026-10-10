import Mathlib
import OAI.Analysis.Conductivity.Variational.PairedPotential
import OAI.Analysis.Conductivity.Sobolev.LocalPullbackTsupportInside

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
open scoped ENNReal Matrix.Norms.Elementwise
theorem exists_quantitative_local_two_field_split
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {p : Coord3} (hA : ContinuousAt A p)
    (hD : Function.Surjective (fderiv ℝ u p))
    (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
    (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
    {θ c m : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hm : 0 < m) (hpath : ∀ z ∈ Icc (-θ) (1-θ), m ≤ 1 + c * z)
    (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-θ) (1-θ), ContinuousAt C z)
    (hdet : ∀ z ∈ Icc (-θ) (1-θ), 0 < (splitJacobian d L c z).det)
    (hconstit : ∀ z ∈ Icc (-θ) (1-θ),
      (C z).val = (splitJacobian d L c z).det⁻¹ •
        (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
    {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
    (hCG : ∀ z ∈ Icc (-θ) (1-θ), (z, C z) ∈ G)
    {U : Set Coord3} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ (X : OpenPartialHomeomorph Coord3 Coord3) (W : Set Coord3),
      IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧ W ⊆ X.source ∧
      ∀ ε : ℝ, 0 < ε →
      ∃ (χ : SmoothScalar Coord3) (H : SmoothScalar ℝ) (F : ℝ → Fin 2 → Coord3 → Coord3),
        HasCompactSupport χ.val ∧ tsupport χ.val ⊆ X '' W ∧
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) ∧
        (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
        (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ W) ∧
        (∀ k j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
          (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
        ∀ᶠ n : ℕ in atTop, ∃ Y : Coord3 ≃ Coord3,
          ContDiff ℝ (↑(⊤ : ℕ∞)) Y ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm ∧
          (∀ x ∉ W, Y x = x) ∧ Y '' W = W ∧
          (∀ x, Y x = x + (c * (n+1 : ℝ)⁻¹ * localPullback X χ.val x *
            H.val ((n+1 : ℝ) * L (X x))) • d) ∧
          μ {x | x ∈ W ∧
            localPullback X χ.val (Y.symm x) *
              (smoothDirection 1 H).val ((n+1 : ℝ) * L (X (Y.symm x))) ≠ -θ ∧
            localPullback X χ.val (Y.symm x) *
              (smoothDirection 1 H).val ((n+1 : ℝ) * L (X (Y.symm x))) ≠ 1-θ} ≤
            ENNReal.ofReal ε ∧
          ∀ x ∈ W,
            let z := localPullback X χ.val x * (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x))
            let E := gradientColumns (fderiv ℝ u x)
            let Ft := (A x).val * E + Matrix.of (fun i j => F (n+1 : ℝ) j x i)
            let J := operatorMatrix (fderiv ℝ Y x)
            let At := repairPushed (C z) J E Ft
            0 < J.det ∧ LinearIndependent ℝ E.col ∧ (z, At) ∈ G ∧
              At.val * gradientColumns (fderiv ℝ (u ∘ Y.symm) (Y x)) = pushFlux J Ft := by
  have hb : 0 ≤ 1-θ := by linarith
  have hb1 : 1-θ ≤ 1 := by linarith
  obtain ⟨X, V, hV, hpV, hVU, hVX, hX, hXi, M, hM, hop⟩ :=
    exists_local_two_field_split μ u hu A hA hD d L hLd B hB hBn
      hθ.le hb hθ1.le hb1 hm hpath C hC hdet hconstit hG hCG hU hpU
  obtain ⟨W, hW, hpW, hWV, hWc, hXW, D, hDpos, hDb⟩ :=
    exists_bounded_chart_neighborhood X hX.continuous hXi hV hVX hpV
  have hWV' : W ⊆ V := subset_closure.trans hWV
  have hWX : W ⊆ X.source := hWV'.trans hVX
  have hL : L ≠ 0 := by intro hz; simp only [hz, _root_.zero_apply] at hLd; norm_num at hLd
  refine ⟨X, W, hW, hpW, hWV.trans hVU, hWc, hWX, ?_⟩
  intro ε hε
  obtain ⟨χ, H, hχc, hχW, hχb, hHp, hHm, hHb, hHr, hpure⟩ :=
    exists_chart_pure_profile μ X hW hWX (hXi.differentiableOn (by simp))
      hXW hXW.measure_lt_top.ne hDpos hDb L hL hθ hθ1 (div_pos hε hM)
  obtain ⟨F, hF, hFs, hdiv, hlim⟩ := hop H hHp hHm hHb hHr χ hχc
    (hχW.trans (image_mono hWV')) hχb
  have hχt : tsupport χ.val ⊆ X.target := hχW.trans (by
    rintro y ⟨x, hx, rfl⟩; exact X.map_source (hWX hx))
  have hχp : tsupport (localPullback X χ.val) ⊆ W :=
    localPullback_tsupport_inside X χ.val hχc hWX hχW
  refine ⟨χ, H, F, hχc, hχW, hχb, hF, ?_, hdiv, ?_⟩
  · intro k j
    refine ⟨(hFs k j).1, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hFs k j).2.2 hx
    obtain ⟨z, hz, rfl⟩ := hχW hy
    simpa only [X.left_inv (hWX hz)] using hz
  have hnat : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually hlim, hpure] with n hn hnp
  obtain ⟨Y, hY, hYi, _, _, hform, hYM, hstate⟩ := hn
  have hoff : ∀ x ∉ W, Y x = x := by
    intro x hx
    have hz := image_eq_zero_of_notMem_tsupport (fun h => hx (hχp h))
    rw [hform x, hz, mul_zero, zero_mul, zero_smul, add_zero]
  have himage := equiv_image_set_of_eq_off Y W hoff
  refine ⟨Y, hY, hYi, hoff, himage, hform, ?_, fun x hx => hstate x (hWV' hx)⟩
  let z : Coord3 → ℝ := fun x => localPullback X χ.val x *
    (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x))
  have hz : Continuous z :=
    (localPullback_contDiff X hX.contDiffOn χ.val (smoothScalar_contDiff χ) hχc hχt).continuous.mul
      ((smoothScalar_contDiff (smoothDirection 1 H)).continuous.comp
        (continuous_const.mul (L.continuous.comp hX.continuous)))
  have he := pushed_exception_measure_le μ Y (hY.differentiable (by simp))
    hW.measurableSet himage z hz (-θ) (1-θ) hYM
  calc
    _ ≤ ENNReal.ofReal M * μ {x | x ∈ W ∧ z x ≠ -θ ∧ z x ≠ 1-θ} := he
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (ε/M) := mul_le_mul_right hnp _
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul hM.le, mul_div_cancel₀ ε hM.ne']

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma contDiffAt_matrix_mul {X m n p : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype m] [Fintype n] [Fintype p] {k : WithTop ℕ∞}
    {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ} {x : X}
    (hA : ContDiffAt ℝ k A x) (hB : ContDiffAt ℝ k B x) :
    ContDiffAt ℝ k (fun y => A y * B y) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum (fun l _ =>
    ((contDiffAt_pi.mp (contDiffAt_pi.mp hA i)) l).mul
      ((contDiffAt_pi.mp (contDiffAt_pi.mp hB l)) j))

lemma contDiffAt_matrix_transpose {X m n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype m] [Fintype n] {k : WithTop ℕ∞} {A : X → Matrix m n ℝ} {x : X}
    (hA : ContDiffAt ℝ k A x) : ContDiffAt ℝ k (fun y => (A y)ᵀ) x := by
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    contDiffAt_pi.mp (contDiffAt_pi.mp hA j) i))

lemma contDiffAt_matrix_det {X n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype n] [DecidableEq n] {k : WithTop ℕ∞} {A : X → Matrix n n ℝ} {x : X}
    (hA : ContDiffAt ℝ k A x) : ContDiffAt ℝ k (fun y => (A y).det) x := by
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum (fun σ _ => contDiffAt_const.mul
    (contDiffAt_prod (fun i _ => contDiffAt_pi.mp (contDiffAt_pi.mp hA (σ i)) i)))

lemma contDiffAt_matrix_inv {X n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype n] [DecidableEq n] {k : WithTop ℕ∞} {A : X → Matrix n n ℝ} {x : X}
    (hA : ContDiffAt ℝ k A x) (hd : (A x).det ≠ 0) :
    ContDiffAt ℝ k (fun y => (A y)⁻¹) x := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  apply ((contDiffAt_matrix_det hA).inv hd).smul
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  simp_rw [Matrix.adjugate_apply]
  apply contDiffAt_matrix_det
  apply contDiffAt_pi.mpr; intro l
  apply contDiffAt_pi.mpr; intro r
  by_cases hl : l = j
  · subst l; simpa only [Matrix.updateRow_self] using
      (contDiffAt_const : ContDiffAt ℝ k (fun _ : X => (Pi.single i (1:ℝ) : n → ℝ) r) x)
  · simpa only [Matrix.updateRow_ne hl] using
      (contDiffAt_pi.mp (contDiffAt_pi.mp hA l) r)

lemma contDiffAt_repairError {X m : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype m] [DecidableEq m] {k : WithTop ℕ∞}
    (A : X → Symmetric3) (E R : X → Matrix (Fin 3) m ℝ) {x : X}
    (hA : ContDiffAt ℝ k (fun y => (A y).val) x)
    (hE : ContDiffAt ℝ k E x) (hR : ContDiffAt ℝ k R x)
    (hi : LinearIndependent ℝ (E x).col) :
    ContDiffAt ℝ k (fun y => (repairError (A y) (E y) (R y)).val) x := by
  have hL := contDiffAt_matrix_mul
    (contDiffAt_matrix_inv (contDiffAt_matrix_mul (contDiffAt_matrix_transpose hE) hE)
      (gram_det_ne_zero (E x) hi)) (contDiffAt_matrix_transpose hE)
  have hD := ((contDiffAt_matrix_mul hR hL).add
    (contDiffAt_matrix_mul (contDiffAt_matrix_transpose hL) (contDiffAt_matrix_transpose hR))).sub
      (contDiffAt_matrix_mul (contDiffAt_matrix_mul
        (contDiffAt_matrix_transpose hL) (contDiffAt_matrix_mul (contDiffAt_matrix_transpose hE) hR)) hL)
  change ContDiffAt ℝ k (fun y => (A y).val +
    (1/2 : ℝ) • (symmetricCorrection (E y) (R y) (((E y)ᵀ * E y)⁻¹ * (E y)ᵀ) +
      (symmetricCorrection (E y) (R y) (((E y)ᵀ * E y)⁻¹ * (E y)ᵀ))ᵀ)) x
  apply hA.add
  apply ContDiffAt.const_smul
  exact hD.add (contDiffAt_matrix_transpose hD)

lemma contDiffAt_repairPushed {X m : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype m] [DecidableEq m] {k : WithTop ℕ∞}
    (A : X → Symmetric3) (J : X → Mat3) (E F : X → Matrix (Fin 3) m ℝ) {x : X}
    (hA : ContDiffAt ℝ k (fun y => (A y).val) x) (hJ : ContDiffAt ℝ k J x)
    (hE : ContDiffAt ℝ k E x) (hF : ContDiffAt ℝ k F x)
    (hdet : (J x).det ≠ 0) (hi : LinearIndependent ℝ (E x).col) :
    ContDiffAt ℝ k (fun y => (repairPushed (A y) (J y) (E y) (F y)).val) x := by
  have hG : ContDiffAt ℝ k (fun y => pushGradient (J y) (E y)) x :=
    contDiffAt_matrix_mul (contDiffAt_matrix_transpose (contDiffAt_matrix_inv hJ hdet)) hE
  have hP : ContDiffAt ℝ k (fun y => pushFlux (J y) (F y)) x :=
    ((contDiffAt_matrix_det hJ).inv hdet).smul (contDiffAt_matrix_mul hJ hF)
  exact contDiffAt_repairError _ _ _ hA hG (hP.sub (contDiffAt_matrix_mul hA hG))
    (pushGradient_rank (J x) hdet (E x) hi)

end ScalarConductivity

end

end OAI
