import OAI.Analysis.MatrixScaling.Geodesic

namespace OAI

/-! Existence and uniqueness of scaling minimizers. -/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem posDef_det_re_pos {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) :
    0 < P.det.re := by
  exact (RCLike.pos_iff.mp hP.det_pos).1

theorem continuousOn_scalingPotential (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun P : HermitianMatrices d => scalingPotential T P.val)
      (spectralWindow d a b) := by
  have hP : Continuous (fun P : HermitianMatrices d => P.val.det.re) :=
    Complex.continuous_re.comp continuous_subtype_val.matrix_det
  have hD : Continuous (fun P : HermitianMatrices d => scalingMap T P.val) :=
    continuous_scalingMap (fun _ : HermitianMatrices d => T) continuous_const
      (fun P : HermitianMatrices d => P.val) continuous_subtype_val
  have hQ : Continuous (fun P : HermitianMatrices d => (1+scalingMap T P.val).det.re) :=
    Complex.continuous_re.comp (continuous_const.add hD).matrix_det
  have hp : ContinuousOn (fun P : HermitianMatrices d => Real.log P.val.det.re)
      (spectralWindow d a b) := hP.continuousOn.log (fun P h => ne_of_gt
    (posDef_det_re_pos (spectralWindow_posDef ha h)))
  have hq : ContinuousOn (fun P : HermitianMatrices d => Real.log (1+scalingMap T P.val).det.re)
      (spectralWindow d a b) := hQ.continuousOn.log (fun P h => ne_of_gt (posDef_det_re_pos
    (Matrix.PosDef.one.add_posSemidef (scalingMap_positive T (spectralWindow_posDef ha h).posSemidef))))
  exact hq.sub (hp.const_mul (3/2))

/-- Minimizing on a spectral window gives a global minimum when all
points below the comparison value lie in the window. -/
theorem scaling_minimum_of_sublevel_bound
    (T : Fin n → Matrix (Fin r) (Fin d) ℂ) {a b C : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hbound : ∀ (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosDef),
      scalingPotential T P ≤ C → (⟨P,hP.1⟩ : HermitianMatrices d) ∈ spectralWindow d a b)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.PosDef) (hQC : scalingPotential T Q ≤ C) :
    ∃ P : Matrix (Fin d) (Fin d) ℂ, P.PosDef ∧
      ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef → scalingPotential T P ≤ scalingPotential T R := by
  obtain ⟨P,hP,hmin⟩ := (isCompact_spectralWindow ha.le hb).exists_isMinOn
    ⟨⟨Q,hQ.1⟩, hbound Q hQ hQC⟩ (continuousOn_scalingPotential T ha)
  refine ⟨P.val, spectralWindow_posDef ha hP, ?_⟩
  intro R hR
  by_cases hRC : scalingPotential T R ≤ C
  · have hm := hmin (hbound R hR hRC)
    exact hm
  · have hm := hmin (hbound Q hQ hQC)
    exact hm.trans (hQC.trans (le_of_lt (lt_of_not_ge hRC)))

theorem scaling_minimizer_exists {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ))) (y : Y) :
    ∃ P : Matrix (Fin d) (Fin d) ℂ, P.PosDef ∧
      ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef →
        scalingPotential (T y) P ≤ scalingPotential (T y) R := by
  obtain ⟨ε,hε,hbound⟩ := uniform_scaling_sublevels T hT hexpand
  let C := scalingPotential (T y) 1
  let B := C - (d-1)*((3/2)*Real.log ε)
  apply scaling_minimum_of_sublevel_bound (T y)
    (a := Real.exp (-2*B/3)) (b := Real.exp (2*B-4*Real.log ε)) (C := C)
    (Real.exp_pos _) (Real.exp_pos _).le
  · intro P hP hC
    exact hbound C y P hP hC
  · exact Matrix.PosDef.one
  · exact le_rfl

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem scaling_minimizer_unique (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    {P Q : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (hminP : ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef → scalingPotential T P ≤ scalingPotential T R)
    (hminQ : ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef → scalingPotential T Q ≤ scalingPotential T R) :
    P = Q := by
  by_contra hneq
  obtain ⟨L,h,hL,hzero,hone⟩ := exists_spectralCurve_between hP hQ
  have hnonzero : ∃ j, h j ≠ 0 := by
    by_contra hn
    push Not at hn
    have he : spectralCurve L h 0 = spectralCurve L h 1 := by
      simp only [spectralCurve, hn, zero_mul]
    exact hneq (hzero.symm.trans (he.trans hone))
  obtain ⟨j,hj⟩ := hnonzero
  have hs := scalingPotential_strictConvex_spectralCurve T hexpand L hL h j hj
  have hstrict := hs.2
  have hmid := hstrict (x := 0) (y := 1) (a := (1/2 : ℝ)) (b := (1/2 : ℝ))
    (Set.mem_univ _) (Set.mem_univ _) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, hzero, hone] at hmid
  have hpq := hminP Q hQ
  have hqp := hminQ P hP
  have hpm := hminP (spectralCurve L h (1/2)) (spectralCurve_posDef L hL h _)
  linarith

theorem existsUnique_scaling_minimizer (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    ∃! P : Matrix (Fin d) (Fin d) ℂ, P.PosDef ∧
      ∀ Q : Matrix (Fin d) (Fin d) ℂ, Q.PosDef → scalingPotential T P ≤ scalingPotential T Q := by
  obtain ⟨P,hP,hmin⟩ := scaling_minimizer_exists (fun _ : Unit => T)
    continuous_const (fun _ => hexpand) ()
  refine ⟨P,⟨hP,hmin⟩,?_⟩
  intro Q hQ
  exact scaling_minimizer_unique T hexpand hQ.1 hP hQ.2 hmin

end Kaplansky

end

end OAI
