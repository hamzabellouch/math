import OAI.Analysis.FreeEntropy.UniformMicrostateTests

namespace OAI

noncomputable section
open Finset Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def totalSecond (m : List (Fin n) → ℂ) : ℝ := ∑i : Fin n,(m [i,i]).re
 theorem totalSecond_continuous : Continuous (totalSecond (n := n)) := by
  unfold totalSecond
  fun_prop
 theorem totalSecond_matrix (a : MatrixCoordinates n d) : totalSecond (matrixMoment a)=(d:ℝ)⁻¹*‖a‖^2 := by
  simp only [totalSecond,matrixMoment_second_hs,hsNorm_sq,← mul_sum,hermitianChart_normSq]
 theorem totalSecond_norm_bound (hd : 0<d) {p : ℕ} (a : MatrixCoordinates (p+1) d)
    (ha : totalSecond (matrixMoment a)<4*p) : ‖a‖≤2*Real.sqrt ((p:ℝ)*d) := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  rw [totalSecond_matrix] at ha
  have hh := mul_lt_mul_of_pos_left ha hd'
  rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0≤(p:ℝ)*d)]
  nlinarith
 section Operators
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M)
 theorem wordMoment_second (X : Fin n → H →L[ℂ] H) (hX : ∀i,IsSelfAdjoint (X i)) (i : Fin n) :
    (wordMoment τ X [i,i]).re=‖X i τ.vacuum‖^2 := by
  have he := inner_selfAdjoint_word τ X hX i [i]
  simpa [wordEval,inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow] using (congrArg Complex.re he).symm
 end Operators
namespace Model
variable (p : ℕ) [NeZero p]
 theorem totalSecond_X (h : ℝ) (hh : 0≤h) :
    totalSecond (wordMoment (τ p) (X p h))=∑i : Fin (p+1),(variance p i+h) := by
  simp only [totalSecond,wordMoment_second (τ p) (X p h) (X_selfAdjoint p h),X_variance p h hh]
 theorem totalSecond_X_lt (hp : 2≤p) {h : ℝ} (hh : 0≤h) (hh1 : h<1) :
    totalSecond (wordMoment (τ p) (X p h))<4*p := by
  rw [totalSecond_X p h hh]
  have hb : (∑i : Fin (p+1),(variance p i+h))≤(p+1:ℝ)*(1+h) := by
    calc
      _ ≤ ∑i : Fin (p+1),(1+h) := sum_le_sum (fun i _ => add_le_add (variance_le_one p hp i) (le_refl h))
      _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  nlinarith
 theorem totalSecond_heat_le (hp : 2≤p) {h s : ℝ} (hh : 0≤h) (hs : 0 ≤ s) :
    totalSecond (wordMoment (τ p) (heatTuple (X p h) (auxiliaryNoise p) s))≤(p+1:ℝ)*(1+h+s) := by
  have hsa := FreeTensor.heatTuple_selfAdjoint (X p h) (auxiliaryNoise p) (X_selfAdjoint p h) (auxiliaryNoise_selfAdjoint p) s
  simp only [totalSecond,wordMoment_second (τ p) _ hsa]
  change (∑i : Fin (p+1),‖doublyNoised p h s i (τ p).vacuum‖^2)≤_
  simp only [doublyNoised_variance p h s hh hs]
  calc
    _ ≤ ∑i : Fin (p+1),(1+h+s) := sum_le_sum (fun i _ => by
      have hb := variance_le_one p hp i
      change ‖C p i (τ p).vacuum‖^2≤1 at hb
      linarith)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
 theorem diagonalMicrostates_norm_eventually (hp : 2≤p) {h : ℝ} (hh : 0≤h) (hh1 : h<1) (R : ℝ) :
    ∀ᶠk : ℕ in atTop,∀d : ℕ,0<d → ∀a : MatrixCoordinates (p+1) d,
      a∈diagonalMicrostates (τ p) (X p h) R k d → ‖a‖≤2*Real.sqrt ((p:ℝ)*d) := by
  have he := diagonalMicrostates_uniform_open (τ p) (X p h) R {m | totalSecond m<4*p}
    (isOpen_lt totalSecond_continuous continuous_const) (totalSecond_X_lt p hp hh hh1)
  filter_upwards [he] with k hk d hd a ha
  exact totalSecond_norm_bound hd a (hk d a ha)
end Model
end FiniteEntropySeparation

end

end OAI
