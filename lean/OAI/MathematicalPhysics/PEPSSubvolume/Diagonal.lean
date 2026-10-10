import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.Transition

namespace OAI

/-! Spectral diagonal gradients of actual maximizing filters. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.DiagonalStationarity
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.KernelNormalization
open PolynomialPEPS.Subvolume.UnitaryStationarity
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def tiltCost (e h : ι → ℝ) (p t : ℝ) : ℝ :=
  ∑ i, (e i)^p * Real.exp (p*t*h i)

omit [DecidableEq ι] in
theorem tiltCost_zero (e h : ι → ℝ) (p : ℝ) (hs : ∑ i, (e i)^p = 1) :
    tiltCost e h p 0 = 1 := by simpa [tiltCost] using hs

omit [DecidableEq ι] in
theorem tiltCost_pos (e h : ι → ℝ) (p t : ℝ)
    (he : ∀ i, 0 ≤ e i) (hs : ∑ i, (e i)^p = 1) :
    0 < tiltCost e h p t := by
  have ha : ∃ i, 0 < (e i)^p := by
    by_contra hn
    push Not at hn
    have hz : ∑ i, (e i)^p ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
    linarith
  obtain ⟨i,hi⟩ := ha
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (Real.rpow_nonneg (he j) _) (Real.exp_pos _).le
  · exact ⟨i,Finset.mem_univ i,mul_pos hi (Real.exp_pos _)⟩

omit [DecidableEq ι] in
theorem tiltCost_power (e h : ι → ℝ) (p t : ℝ) (he : ∀ i, 0 ≤ e i) :
    ∑ i, (e i*Real.exp (t*h i))^p = tiltCost e h p t := by
  unfold tiltCost
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.mul_rpow (he i) (Real.exp_pos _).le,← Real.exp_mul]
  congr 2
  ring

omit [DecidableEq ι] in
theorem tiltCost_derivative (e h : ι → ℝ) (p : ℝ) :
    HasDerivAt (tiltCost e h p) (p*∑ i, (e i)^p*h i) 0 := by
  have hD (i : ι) : HasDerivAt (fun t : ℝ => (e i)^p*Real.exp (p*t*h i))
      ((e i)^p*(p*h i)) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul p).mul_const (h i)).exp.const_mul ((e i)^p)
  have he : (∑ i, (e i)^p*(p*h i)) = p*∑ i, (e i)^p*h i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hf : tiltCost e h p = ∑ i, (fun t : ℝ => (e i)^p * Real.exp (p*t*h i)) := by
    ext t
    simp [tiltCost]
  rw [hf]
  simpa +instances only [he] using!
    HasDerivAt.sum (u := Finset.univ) (fun i _ => hD i)

omit [DecidableEq ι] in
theorem tiltScale_derivative (e h : ι → ℝ) (p : ℝ) (hp : p ≠ 0)
    (hs : ∑ i, (e i)^p = 1) :
    HasDerivAt (fun t => scale (tiltCost e h p t) p) (-∑ i, (e i)^p*h i) 0 := by
  have hD := (tiltCost_derivative e h p).rpow_const (p := -(1/p))
    (Or.inl (by rw [tiltCost_zero e h p hs]; norm_num))
  unfold scale
  convert hD using 1
  rw [tiltCost_zero e h p hs,Real.one_rpow]
  field_simp

theorem diagonal_moment (T : Matrix ι ι ℂ →ₗ[ℂ] E)
    (U : unitary (Matrix ι ι ℂ)) (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    (p : ℝ) (hp : p ≠ 0) (hs : ∑ i, (e i)^p = 1)
    (hb : ∀ d : ι → ℝ, (∀ i, 0 ≤ d i) → (∑ i, (d i)^p = 1) →
      ‖T (spectralHom U (fun i => (d i : ℂ)))‖ ≤
        ‖T (spectralHom U (fun i => (e i : ℂ)))‖)
    (h : ι → ℝ) :
    (inner ℂ (T (spectralHom U (fun i => (e i : ℂ))))
      (T (spectralHom U (fun i => (e i*h i : ℂ))))).re =
      ‖T (spectralHom U (fun i => (e i : ℂ)))‖^2 * ∑ i, (e i)^p*h i := by
  let F := spectralHom U (fun i => (e i : ℂ))
  let l : Matrix ι ι ℂ →L[ℂ] ℂ := (innerSL ℂ (T F)).comp T.toContinuousLinearMap
  have hM : F*spectralHom U (fun i => (h i : ℂ)) =
      spectralHom U (fun i => (e i*h i : ℂ)) := by
    rw [← map_mul]
    rfl
  have hD := (hasDerivAt_curve_zero U h).const_mul F
  have hDl : HasDerivAt (fun z : ℂ => l (F*curve U h z))
      (l (spectralHom U (fun i => (e i*h i : ℂ)))) 0 := by
    have hD' := l.hasFDerivAt.comp_hasDerivAt 0 hD
    rw [hM] at hD'
    simpa +instances only [Function.comp_def] using! hD'
  have h0 : l (F*curve U h 0) = inner ℂ (T F) (T F) := by simp [l]
  have hDg := (tiltScale_derivative e h p hp hs).mul hDl.real_of_complex
  have hG0 : scale (tiltCost e h p 0) p = 1 := by
    simp [tiltCost_zero e h p hs,scale]
  have hm : IsLocalMax (fun t : ℝ =>
      scale (tiltCost e h p t) p * (l (F*curve U h (t:ℂ))).re) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    let d : ι → ℝ := fun i => scale (tiltCost e h p t) p * (e i*Real.exp (t*h i))
    have hS := tiltCost_pos e h p t he hs
    have hd : ∀ i, 0 ≤ d i := fun i => mul_nonneg (scale_pos _ _ hS).le
      (mul_nonneg (he i) (Real.exp_pos _).le)
    have hsum : ∑ i, (d i)^p = 1 := power_sum _
      (fun i => mul_nonneg (he i) (Real.exp_pos _).le) _ _ hS hp
      (tiltCost_power e h p t he)
    have heq : spectralHom U (fun i => (d i : ℂ)) =
        (scale (tiltCost e h p t) p : ℂ) • (F*curve U h (t:ℂ)) := by
      rw [show F*curve U h (t:ℂ) = spectralHom U
        (fun i => (e i:ℂ)*Complex.exp ((t:ℂ)*(h i:ℂ))) by exact (spectralHom U).map_mul _ _ |>.symm,
        ← map_smul]
      apply congrArg (spectralHom U)
      ext i
      simp [d,Complex.ofReal_mul,Complex.ofReal_exp]
    have hb' := real_inner_le_of_norm_le (T F) _ (hb d hd hsum)
    rw [heq,map_smul,inner_smul_right] at hb'
    dsimp only
    simp only [Complex.ofReal_zero,hG0,h0,one_mul]
    simpa +instances only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using! hb'
  have hz := hm.hasDerivAt_eq_zero hDg
  simp only [Complex.ofReal_zero,hG0,h0,one_mul] at hz
  have hnorm : (inner ℂ (T F) (T F)).re = ‖T F‖^2 := by
    change RCLike.re (inner ℂ (T F) (T F)) = ‖T F‖^2
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (T F)).symm
  rw [hnorm] at hz
  change -(∑ i, (e i)^p*h i) * ‖T F‖^2 +
    (inner ℂ (T F) (T (spectralHom U (fun i => (e i*h i:ℂ))))).re = 0 at hz
  dsimp only [F] at hz ⊢
  nlinarith only [hz]

end PolynomialPEPS.Subvolume.DiagonalStationarity

namespace PolynomialPEPS.Subvolume.ActualDiagonal
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.OptimizerGauge PolynomialPEPS.Subvolume.ActualTransition
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.DiagonalStationarity
variable {L q : ℕ}

theorem spectral_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) :
    (spectralHom U (fun i => (e i:ℂ))).PosSemidef := by
  exact (Matrix.PosSemidef.diagonal (fun i => Complex.nonneg_iff.mpr ⟨he i,rfl⟩)).mul_mul_conjTranspose_same
    (U : Matrix ι ι ℂ)

theorem optimizer_diagonal_moment (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (hk : k < n) (hp : 2/a k ≠ 0)
    (U : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
    (e h : RegionConfiguration q (X k) → ℝ) (he : ∀ i, 0 ≤ e i)
    (hrep : (F k).matrix = spectralHom U (fun i => (e i : ℂ))) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
    (inner ℂ v (replacementOutput A (X k) ψ k n hk
      (spectralHom U (fun i => (e i*h i : ℂ))))).re =
      ‖v‖^2 * ∑ i, (e i)^(2/a k)*h i := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let T := replacementOutput A (X k) ψ k n hk
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  have ht : T (F k).matrix = v := by
    change asMap (L := L) (q := q) (orderedPrefix (Function.update A k (A k)) n) ψ = v
    rw [Function.update_eq_self]
  have hfv : filteredVector (fun j : Fin n => F j.val) ψ = v := by
    unfold filteredVector
    rw [PhysicalCurve.orderedFilterProduct_eq_prefix]
  have hs : ∑ i, (e i)^(2/a k) = 1 := by
    have hs := hF.1 ⟨k,hk⟩
    unfold filterTracePower NestedFilter.tracePower at hs
    have hs' := sum_eigenvalues_spectralHom U e (spectral_positive U e he).isHermitian
      (fun t => t^(2/a k))
    have heig := (F k).positive.isHermitian.eigenvalues_eq_eigenvalues_iff
      (spectral_positive U e he).isHermitian
    have heq := heig.mpr (congrArg Matrix.charpoly hrep)
    rw [heq] at hs
    exact hs'.symm.trans hs
  have hb (d : RegionConfiguration q (X k) → ℝ) (hd : ∀ i, 0 ≤ d i)
      (hsd : ∑ i, (d i)^(2/a k) = 1) :
      ‖T (spectralHom U (fun i => (d i:ℂ)))‖ ≤ ‖T (spectralHom U (fun i => (e i:ℂ)))‖ := by
    let G : LocalPositiveFilter q (X k) := ⟨_,spectral_positive U d hd⟩
    have hG : filterTracePower G (2/a k) = 1 := by
      exact (sum_eigenvalues_spectralHom U d G.positive.isHermitian (fun t => t^(2/a k))).trans hsd
    have hb := one_replacement_bound hq X hX a ψ n F hF k hk 1 G hG
    rw [← hrep,ht,← hfv]
    simpa +instances only [OneMemClass.coe_one,one_mul] using! hb
  have hm := diagonal_moment T U e he (2/a k) hp hs hb h
  rw [← hrep,ht] at hm
  exact hm

end PolynomialPEPS.Subvolume.ActualDiagonal

end

end OAI
