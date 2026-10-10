import OAI.MathematicalPhysics.DefocusingNLS.Certificates.IntegerPolynomialDisk
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.CenteredPolynomial
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.PolynomialRootEnumeration

namespace OAI

/-! # Applying the rational certificates to the separator polynomials -/

open Polynomial

namespace DefocusingNLS.SeparatorArithmetic

noncomputable section

theorem scaledSeparatorPolynomial_degree (ℓ : ℕ) :
    (scaledSeparatorPolynomial ℓ).natDegree ≤ 15 := by
  apply natDegree_sum_le_of_forall_le
  intro n hn
  exact (natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hn; omega)

theorem eval_degree_fifteen (p : Polynomial ℂ) (hdegree : p.natDegree ≤ 15) (z : ℂ) :
    p.eval z = p.coeff 0 + p.coeff 1 * z +
      ∑ i : Fin 14, p.coeff ((i : ℕ) + 2) * z ^ ((i : ℕ) + 2) := by
  rw [p.eval_eq_sum_range' (lt_of_le_of_lt hdegree (by decide : 15 < 16))]
  rw [show 16 = 2 + 14 by decide, Finset.sum_range_add]
  have hfirst : ∑ n ∈ Finset.range 2, p.coeff n * z ^ n =
      p.coeff 0 + p.coeff 1 * z := by simp [Finset.sum_range_succ]
  rw [hfirst]
  simp only [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => p.coeff (i + 2) * z ^ (i + 2)), Nat.add_comm 2]

theorem diskErrorBound_eq_sum (ℓ : ℕ) (c : GaussianInt) :
    diskErrorBound ℓ c = coefficientUpper (centeredCoefficient ℓ c 0) +
      ∑ i : Fin 14, coefficientUpper (centeredCoefficient ℓ c ((i : ℕ) + 2)) *
        (100 : ℤ) ^ ((i : ℕ) + 2) := by
  unfold diskErrorBound
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, diskRadius,
    Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      coefficientUpper (centeredCoefficient ℓ c (i + 2)) * (100 : ℤ) ^ (i + 2))]

theorem complex_taylor_coeff (ℓ : ℕ) (c : GaussianInt) (i : ℕ) (hi : i ≤ 16) :
    (taylor (c : ℂ) ((scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex)).coeff i =
      (centeredCoefficient ℓ c i : ℂ) := by
  rw [← map_taylor, coeff_map, ← centeredCoefficient_eq ℓ c i hi]

/-- Every certified disk contains an actual zero of the translated, scaled
separator polynomial. -/
theorem root_in_certified_disk (ℓ : Fin 4) (j : Fin 15) :
    ∃ z : ℂ, ‖z - (diskCenters ℓ j : ℂ)‖ ≤ 100 ∧
      ((scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex).IsRoot z := by
  let c := diskCenters ℓ j
  obtain ⟨w, hw, hzero⟩ := root_of_integer_coefficient_bound
    (centeredCoefficient ℓ c 0) (centeredCoefficient ℓ c 1)
    (fun i => centeredCoefficient ℓ c ((i : ℕ) + 2)) 100
    (disk_linear_nonzero ℓ j) (by
      have h := disk_bound ℓ j
      change diskErrorBound ℓ c ≤ coefficientLower (centeredCoefficient ℓ c 1) * 100 at h
      rwa [diskErrorBound_eq_sum] at h)
  refine ⟨w + (c : ℂ), ?_, ?_⟩
  · change ‖w + (c : ℂ) - (c : ℂ)‖ ≤ 100
    simpa only [add_sub_cancel_right, Nat.cast_ofNat] using hw
  let p := (scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex
  have hdegree : (taylor (c : ℂ) p).natDegree ≤ 15 := by
    rw [natDegree_taylor]
    exact (natDegree_map_le).trans (scaledSeparatorPolynomial_degree ℓ)
  have hcoeff (i : ℕ) (hi : i ≤ 16) :
      (taylor (c : ℂ) p).coeff i = (centeredCoefficient ℓ c i : ℂ) := by
    exact complex_taylor_coeff ℓ c i hi
  have heval := eval_degree_fifteen (taylor (c : ℂ) p) hdegree w
  rw [hcoeff 0 (by decide), hcoeff 1 (by decide)] at heval
  have hcoeff' (i : Fin 14) :
      (taylor (c : ℂ) p).coeff ((i : ℕ) + 2) =
        (centeredCoefficient ℓ c ((i : ℕ) + 2) : ℂ) := hcoeff _ (by omega)
  simp_rw [hcoeff'] at heval
  rw [hzero] at heval
  change p.eval (w + (c : ℂ)) = 0
  rwa [taylor_eval] at heval

theorem scaledSeparatorPolynomial_complex_ne_zero (ℓ : Fin 4) :
    (scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex ≠ 0 := by
  intro hzero
  have h := complex_taylor_coeff ℓ (diskCenters ℓ 0) 1 (by decide)
  rw [hzero, map_zero, coeff_zero] at h
  exact (disk_linear_nonzero ℓ 0) (GaussianInt.toComplex_eq_zero.mp h.symm)

theorem complex_disk_centers_separated (ℓ : Fin 4) (i j : Fin 15) (hij : i ≠ j) :
    2 * (100 : ℝ) < ‖(diskCenters ℓ i : ℂ) - (diskCenters ℓ j : ℂ)‖ := by
  obtain hre | him := disk_centers_separated ℓ i j hij
  · have h : 2 * (100 : ℝ) <
        |(diskCenters ℓ i : ℂ).re - (diskCenters ℓ j : ℂ).re| := by
      simp only [← GaussianInt.intCast_re]
      exact_mod_cast hre
    exact h.trans_le (by simpa only [Complex.sub_re] using
      Complex.abs_re_le_norm ((diskCenters ℓ i : ℂ) - (diskCenters ℓ j : ℂ)))
  · have h : 2 * (100 : ℝ) <
        |(diskCenters ℓ i : ℂ).im - (diskCenters ℓ j : ℂ).im| := by
      simp only [← GaussianInt.intCast_im]
      exact_mod_cast him
    exact h.trans_le (by simpa only [Complex.sub_im] using
      Complex.abs_im_le_norm ((diskCenters ℓ i : ℂ) - (diskCenters ℓ j : ℂ)))

theorem zero_tail_no_axis_zero (ℓ : Fin 4) {x : ℂ}
    (hx : ((scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex).IsRoot x) :
    x.re ≠ 0 := by
  classical
  obtain ⟨z, _, hz, hroots⟩ := roots_of_fifteen_disks
    ((scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex)
    (scaledSeparatorPolynomial_complex_ne_zero ℓ)
    (natDegree_map_le.trans (scaledSeparatorPolynomial_degree ℓ))
    (fun j => (diskCenters ℓ j : ℂ)) 100
    (complex_disk_centers_separated ℓ) (root_in_certified_disk ℓ)
  apply no_axis_root_of_disks _ (scaledSeparatorPolynomial_complex_ne_zero ℓ)
    (fun i => (diskCenters ℓ i : ℂ)) z 100 hroots _ (fun i => (hz i).1) hx
  intro i
  rw [← GaussianInt.intCast_re]
  exact_mod_cast disk_centers_avoid_axis ℓ i

/-- The zero-tail polynomial has exactly two, one, zero, zero roots in the
open right half-plane, for angular modes zero through three respectively. -/
theorem zero_tail_positive_root_count (ℓ : Fin 4) :
    (((scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex).roots.toFinset.filter
      (fun z => 0 < z.re)).card = positiveRootCount ℓ := by
  classical
  obtain ⟨z, hinj, hz, hroots⟩ := roots_of_fifteen_disks
    ((scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex)
    (scaledSeparatorPolynomial_complex_ne_zero ℓ)
    (natDegree_map_le.trans (scaledSeparatorPolynomial_degree ℓ))
    (fun j => (diskCenters ℓ j : ℂ)) 100
    (complex_disk_centers_separated ℓ) (root_in_certified_disk ℓ)
  have haxis (j : Fin 15) : (100 : ℝ) < |(diskCenters ℓ j : ℂ).re| := by
    rw [← GaussianInt.intCast_re]
    exact_mod_cast disk_centers_avoid_axis ℓ j
  rw [positive_real_root_count_of_disks _ _ z 100 hinj hroots haxis (fun i => (hz i).1)]
  convert positive_disk_count ℓ using 1
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← GaussianInt.intCast_re]
  exact Int.cast_pos

theorem zero_tail_closed_half_plane_count (ℓ : Fin 4) :
    (((scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex).roots.toFinset.filter
      (fun z => 0 ≤ z.re)).card = positiveRootCount ℓ := by
  classical
  have heq :
      (((scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex).roots.toFinset.filter
        (fun z => 0 ≤ z.re)) =
      (((scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex).roots.toFinset.filter
        (fun z => 0 < z.re)) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hle⟩
      have hroot : ((scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex).IsRoot x :=
        (mem_roots (scaledSeparatorPolynomial_complex_ne_zero ℓ)).mp
          (Multiset.mem_toFinset.mp hx)
      exact ⟨hx, lt_of_le_of_ne hle (zero_tail_no_axis_zero ℓ hroot).symm⟩
    · exact fun h => ⟨h.1, h.2.le⟩
  rw [heq, zero_tail_positive_root_count]

end
end DefocusingNLS.SeparatorArithmetic

end OAI
