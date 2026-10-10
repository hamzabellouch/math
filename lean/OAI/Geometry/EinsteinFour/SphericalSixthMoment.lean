import OAI.Geometry.EinsteinFour.SphericalMomentRecurrence

namespace OAI

/-! The degree-six formula follows from the infinitesimal rotation recurrence
and the already proved quartic formula. Only positivity and finiteness of the
unnormalized Hausdorff mass remain in the spherical input. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

private theorem fiveOmit_vector (j k l m n : Fin 4) (q : FourSpace) (r : Fin 5) :
    fiveOmit ![j, k, l, m, n] q r =
      ![q k * q l * q m * q n, q j * q l * q m * q n,
        q j * q k * q m * q n, q j * q k * q l * q n,
        q j * q k * q l * q m] r := by
  rw [fiveOmit_eq_succAbove]
  fin_cases r <;> simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  all_goals norm_num [Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.succ]
  all_goals ring

private theorem delta_comm (i j : Fin 4) : delta i j = delta j i := by
  simp only [delta, eq_comm]

variable [IsProbabilityMeasure sphereMeasure]

theorem actual_spherical_sixth (i j k l m n : Fin 4) :
    (∫ q : Directions, q.val i * q.val j * q.val k * q.val l * q.val m * q.val n
      ∂sphereMeasure) = momentSix i j k l m n := by
  have h := spherical_sixth_recurrence i ![j, k, l, m, n]
  have hp (q : Directions) : q.val i * fiveProduct ![j, k, l, m, n] q.val =
      q.val i * q.val j * q.val k * q.val l * q.val m * q.val n := by
    simp only [fiveProduct, Fin.prod_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one]
    ring
  simp_rw [hp, fiveOmit_vector] at h
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, actual_spherical_fourth] at h
  simp_rw [delta_comm] at h
  unfold momentSix
  linarith

theorem follandMoments_of_probability : FollandMoments where
  probability := inferInstance
  second := actual_spherical_second
  fourth := actual_spherical_fourth
  sixth := actual_spherical_sixth

end
end PositiveEinsteinFour.Angular

end OAI
