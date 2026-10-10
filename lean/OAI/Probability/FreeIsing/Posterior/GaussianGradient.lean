import OAI.Probability.FreeIsing.Posterior.GaussianTimeDerivative

namespace OAI

noncomputable section

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V]

def fieldSquareGradient (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  2 * fieldMean energy spin observable x * fieldCovariance energy spin observable x v

def fieldSquareHessianDiagonal (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  2 * fieldCovariance energy spin observable x v ^ 2 -
    4 * fieldMean energy spin observable x * fieldMean energy spin (fun s => spin s v) x *
      fieldCovariance energy spin observable x v

theorem continuous_fieldSquareGradient (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldSquareGradient energy spin observable x v) :=
  ((continuous_fieldMean energy spin observable).const_mul 2).mul
    (continuous_fieldCovariance energy spin observable v)

theorem continuous_fieldSquareHessianDiagonal (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (v : V) :
    Continuous (fun x => fieldSquareHessianDiagonal energy spin observable x v) := by
  exact (((continuous_fieldCovariance energy spin observable v).pow 2).const_mul 2).sub
    ((((continuous_fieldMean energy spin observable).const_mul 4).mul
      (continuous_fieldMean energy spin (fun s => spin s v))).mul
        (continuous_fieldCovariance energy spin observable v))

theorem abs_fieldSquareGradient_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (A : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldSquareGradient energy spin observable x v| ≤ 4 * A ^ 2 := by
  have hm := abs_fieldMean_le energy spin observable x A hbound
  have hc := abs_fieldCovariance_le energy spin observable x v A hcoord hbound
  have hA : 0 ≤ A := (abs_nonneg _).trans hm
  unfold fieldSquareGradient
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |fieldMean energy spin observable x| * |fieldCovariance energy spin observable x v| ≤
      2 * A * (2 * A) := by gcongr
    _ = 4 * A ^ 2 := by ring

variable [DecidableEq V]

omit [Nonempty S] in
lemma fieldCovariance_coordinate_tilt (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ) :
    fieldCovariance energy spin observable (fun u => x u + if u = v then t else 0) v =
      tiltCovariance (fieldEnergy energy spin x) (fun s => spin s v) observable t := by
  simp only [fieldCovariance, fieldMean_coordinate_tilt, tiltCovariance]

theorem hasDerivAt_fieldSquareGradient_coordinate (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1) :
    HasDerivAt (fun r => fieldSquareGradient energy spin observable
        (fun u => x u + if u = v then r else 0) v)
      (fieldSquareHessianDiagonal energy spin observable
        (fun u => x u + if u = v then t else 0) v) t := by
  have hd := ((hasDerivAt_mean_covariance (fieldEnergy energy spin x)
    (fun s => spin s v) observable t).const_mul 2).mul
      (hasDerivAt_tiltCovariance (fieldEnergy energy spin x) (fun s => spin s v)
        observable t hcoord)
  simp only [fieldSquareGradient, fieldSquareHessianDiagonal,
    fieldMean_coordinate_tilt, fieldCovariance_coordinate_tilt]
  change HasDerivAt (fun r => 2 * mean (fieldEnergy energy spin x)
    (fun s => spin s v) observable r *
      tiltCovariance (fieldEnergy energy spin x) (fun s => spin s v) observable r) _ t at hd
  apply hd.congr_deriv
  ring

theorem abs_fieldSquareHessianDiagonal_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (A : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldSquareHessianDiagonal energy spin observable x v| ≤ 16 * A ^ 2 := by
  have hd := (hasDerivAt_fieldSquareGradient_coordinate energy spin observable x v 0 hcoord).deriv
  have hfirst : (fun r => fieldSquareGradient energy spin observable
      (fun u => x u + if u = v then r else 0) v) =
      deriv (fun r => fieldMean energy spin observable
        (fun u => x u + if u = v then r else 0) ^ 2) := by
    funext r
    simp only [fieldSquareGradient, fieldMean_coordinate_tilt, fieldCovariance_coordinate_tilt]
    exact (deriv_mean_square _ _ _ _).symm
  rw [hfirst] at hd
  simp only [ite_self, add_zero] at hd
  rw [← hd]
  exact abs_deriv_deriv_fieldMean_square_coordinate_le energy spin observable x v 0 A hcoord hbound

omit [Fintype V] in
lemma update_eq_zero_shift (x : V → ℝ) (v : V) (t : ℝ) :
    Function.update x v t =
      (fun u => Function.update x v 0 u + if u = v then t else 0) := by
  funext u
  by_cases hu : u = v
  · subst u
    simp
  · simp [hu]

theorem hasDerivAt_fieldSquareGradient_update (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) (t : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1) :
    HasDerivAt (fun r => fieldSquareGradient energy spin observable (Function.update x v r) v)
      (fieldSquareHessianDiagonal energy spin observable (Function.update x v t) v) t := by
  simpa only [← update_eq_zero_shift] using
    hasDerivAt_fieldSquareGradient_coordinate energy spin observable (Function.update x v 0) v t hcoord

theorem hasDerivAt_fieldSquareGradient_affine_update
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (x : V → ℝ) (v : V) (a b t : ℝ)
    (hcoord : ∀ s, spin s v = -1 ∨ spin s v = 1) :
    HasDerivAt (fun r => fieldSquareGradient energy spin observable
        (Function.update x v (a + b * r)) v)
      (b * fieldSquareHessianDiagonal energy spin observable
        (Function.update x v (a + b * t)) v) t := by
  have hd := (hasDerivAt_fieldSquareGradient_update energy spin observable x v (a + b * t)
    hcoord).comp t (((hasDerivAt_id t).const_mul b).const_add a)
  simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using hd

end Problem367.FinitePosterior

end

end OAI
