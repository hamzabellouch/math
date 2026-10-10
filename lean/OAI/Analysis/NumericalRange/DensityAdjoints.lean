import OAI.Analysis.NumericalRange.BoundaryCalculus

namespace OAI

universe u_247 u_248

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {n : Type u_247} {m : Type u_248} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
lemma densityField_star (L : C(UnitAddCircle,Matrix n n ℂ)) (hL : ∀ t, (L t).IsHermitian)
    (X Y : Matrix n m ℂ) :
    l2Star (densityField (μ := AddCircle.haarAddCircle) L X Y) = densityField L Y X := by
  apply Lp.ext
  filter_upwards [l2StarL_ae (densityField (μ := AddCircle.haarAddCircle) L X Y),
    densityField_ae (μ := AddCircle.haarAddCircle) L X Y,
    densityField_ae (μ := AddCircle.haarAddCircle) L Y X] with t hs hx hy
  change l2StarL (densityField L X Y) t = _
  rw [hs,hx,hy,hsStar_apply,fromHS_toHS,weightedDensity_star,(hL t).eq]
lemma hsTrace_mean_coefficient (u : C(UnitAddCircle,Matrix m m ℂ)) (ij : m × m) :
    fourierCoeff (l2Coordinate ij (hsTraceLp u)) 0 =
      (∫ t, u t ∂AddCircle.haarAddCircle) ij.1 ij.2 := by
  have hi := u.continuous.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle)
    (HasCompactSupport.of_compactSpace _)
  rw [matrix_integral_entry hi]
  simp only [fourierCoeff,neg_zero,fourier_zero,one_smul]
  apply integral_congr_ae
  filter_upwards [l2Coordinate_ae ij (hsTraceLp u),hsTraceLp_ae u] with t hc hu
  rw [hc,hu]
  rfl
lemma hsTrace_mean_zero_iff (u : C(UnitAddCircle,Matrix m m ℂ)) :
    matrixFourier.proj 0 (hsTraceLp u) = 0 ↔ (∫ t, u t ∂AddCircle.haarAddCircle) = 0 := by
  constructor
  · intro hz
    ext i j
    have hh := congrArg (fun v : MatrixCircleL2 (m := m) => fourierCoeff (l2Coordinate (i,j) v) 0) hz
    rw [coordinate_matrixFourier,scalarFourier_coefficient] at hh
    simp only [frequencyPart,hsTrace_mean_coefficient] at hh
    simpa [fourierCoeff] using hh
  · intro hz
    apply l2Coordinate_injective
    intro ij
    apply circle_fourier_ext
    intro k
    rw [coordinate_matrixFourier,scalarFourier_coefficient]
    by_cases hk : k = 0
    · subst k
      rw [show frequencyPart 0 = 0 from rfl,ite_eq_left rfl,hsTrace_mean_coefficient,hz]
      simp [fourierCoeff]
    · have hn : frequencyPart k ≠ 0 := by
        simp only [frequencyPart,ite_eq_right hk]
        split_ifs <;> decide
      simp [hn,fourierCoeff]
lemma densityField_mean_zero (L : C(UnitAddCircle,Matrix n n ℂ)) (X Y : Matrix n m ℂ)
    (h : (∫ t, weightedDensity (L t) X Y ∂AddCircle.haarAddCircle) = 0) :
    matrixFourier.proj 0 (densityField (μ := AddCircle.haarAddCircle) L X Y) = 0 := by
  let u : C(UnitAddCircle,Matrix m m ℂ) :=
    ⟨fun t => weightedDensity (L t) X Y,continuous_weightedDensity L.continuous X Y⟩
  change matrixFourier.proj 0 (hsTraceLp u) = 0
  exact (hsTrace_mean_zero_iff u).mpr h
lemma densityField_mean_nonzero (L : C(UnitAddCircle,Matrix n n ℂ)) (X : Matrix n m ℂ)
    (h : (∫ t, weightedDensity (L t) X X ∂AddCircle.haarAddCircle).trace = 1) :
    matrixFourier.proj 0 (densityField (μ := AddCircle.haarAddCircle) L X X) ≠ 0 := by
  intro hz
  let u : C(UnitAddCircle,Matrix m m ℂ) :=
    ⟨fun t => weightedDensity (L t) X X,continuous_weightedDensity L.continuous X X⟩
  change matrixFourier.proj 0 (hsTraceLp u) = 0 at hz
  have hh := (hsTrace_mean_zero_iff u).mp hz
  change (∫ t, weightedDensity (L t) X X ∂AddCircle.haarAddCircle) = 0 at hh
  rw [hh,Matrix.trace_zero] at h
  exact zero_ne_one h
lemma left_adjoint_of_ae {F : UnitAddCircle → Matrix m m ℂ}
    (L : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m))
    (hL : ∀ u, L u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (F t*fromHS (u t)))
    {p r : MatrixCircleL2 (m := m)}
    (hp : p =ᵐ[AddCircle.haarAddCircle] fun t => toHS ((F t)ᴴ*fromHS (r t))) :
    p = L.adjoint r := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hp,hL u] with t hp hl
  rw [hp,hl]
  change inner ℂ (hsLeft (F t)ᴴ (r t)) (u t) = inner ℂ (r t) (hsLeft (F t) (u t))
  rw [← hsLeft_adjoint,ContinuousLinearMap.adjoint_inner_left]
lemma right_adjoint_of_ae {F : UnitAddCircle → Matrix m m ℂ}
    (R : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m))
    (hR : ∀ u, R u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (u t)*F t))
    {q r : MatrixCircleL2 (m := m)}
    (hq : q =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (r t)*(F t)ᴴ)) :
    q = R.adjoint r := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hq,hR u] with t hq hr
  rw [hq,hr]
  change inner ℂ (hsRight (F t)ᴴ (r t)) (u t) = inner ℂ (r t) (hsRight (F t) (u t))
  rw [← hsRight_adjoint,ContinuousLinearMap.adjoint_inner_left]
end CompleteCrouzeix

end

end

end OAI
