import OAI.Combinatorics.PolynomialVacuum.Algebra.InterpolationDefinitions

namespace OAI

namespace PolynomialVacuumInterpolation
open MvPolynomial Classical

@[simp] theorem mergeVariable_C {ι : Type*} (i j : ι) (a : ℂ) :
    mergeVariable i j (C a) = C a := by simp [mergeVariable]
@[simp] theorem mergeVariable_X {ι : Type*} (i j k : ι) :
    mergeVariable i j (X k) = if k=i then X j else X k := by simp [mergeVariable]

 
theorem nodeFactor_dvd_sub_merge {ι : Type*} (i j : ι) (p : MvPolynomial ι ℂ) :
    nodeFactor i j ∣ p-mergeVariable i j p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr =>
    rw [map_add]
    convert dvd_add hp hr using 1
    ring
  | mul_X p k hp =>
    rw [map_mul]
    have hk : nodeFactor i j ∣ X k-mergeVariable i j (X k) := by
      by_cases h : k=i
      · subst k; simp [nodeFactor]
      · simp [h]
    have hh : p*X k-mergeVariable i j p*mergeVariable i j (X k) =
        (p-mergeVariable i j p)*X k+mergeVariable i j p*(X k-mergeVariable i j (X k)) := by ring
    rw [hh]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hk _)

@[simp] theorem mergeVariable_nodeFactor {ι : Type*} (i j : ι) :
    mergeVariable i j (nodeFactor i j) = 0 := by
  classical
  by_cases h : j=i <;> simp [nodeFactor,h]

theorem nodeFactor_dvd_iff {ι : Type*} (i j : ι) (p : MvPolynomial ι ℂ) :
    nodeFactor i j ∣ p ↔ mergeVariable i j p=0 := by
  constructor
  · rintro ⟨r,rfl⟩; simp
  · intro h
    simpa [h] using nodeFactor_dvd_sub_merge i j p

theorem nodeFactor_ne_zero {ι : Type*} {i j : ι} (hij : i ≠ j) : nodeFactor i j ≠ 0 := by
  intro h
  exact hij (MvPolynomial.X_injective (sub_eq_zero.mp h))

theorem nodeFactor_prime {ι : Type*} {i j : ι} (hij : i ≠ j) : Prime (nodeFactor i j) := by
  refine ⟨nodeFactor_ne_zero hij,?_,?_⟩
  · intro h
    have h' := h.map (mergeVariable i j)
    simp only [mergeVariable_nodeFactor] at h'
    exact not_isUnit_zero h'
  · intro p r h
    rw [nodeFactor_dvd_iff,map_mul,mul_eq_zero] at h
    exact h.imp ((nodeFactor_dvd_iff i j p).mpr) ((nodeFactor_dvd_iff i j r).mpr)

theorem nodeFactor_not_dvd {ι : Type*} {i j k : ι}
    (_hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ nodeFactor i j ∣ nodeFactor i k := by
  rw [nodeFactor_dvd_iff]
  simpa [nodeFactor,hik.symm] using nodeFactor_ne_zero hjk

 

theorem nodeFactor_isRelPrime {ι : Type*} {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    IsRelPrime (nodeFactor i j) (nodeFactor i k) := by
  exact (nodeFactor_prime hij).irreducible.isRelPrime_iff_not_dvd.mpr
    (nodeFactor_not_dvd hij hik hjk)

end PolynomialVacuumInterpolation

end OAI
