import OAI.Analysis.Laughlin.Spin.Multidegree

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem bracket_particle_degree {N : ℕ} (k i j : Fin N) :
    (bracket i j).IsWeightedHomogeneous (particleDegreeWeight k)
      ((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) := by
  have h (a : Fin N) (b : Bool) := isWeightedHomogeneous_X (R := ℂ) (particleDegreeWeight k) (a,b)
  have h1 := (h i false).mul (h j true)
  have h2 := (h j false).mul (h i true)
  exact h1.sub (by simpa only [particleDegreeWeight,Nat.add_comm] using h2)

theorem particle_pair_degree_count {N : ℕ} (k : Fin N) :
    (∑ i : Fin N, ∑ j : Fin N, if i<j then
      ((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0)=N-1 := by
  have hsplit : (∑ i : Fin N, ∑ j : Fin N, if i<j then
      ((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0) =
      (∑ j : Fin N, if k<j then 1 else 0)+(∑ i : Fin N, if i<k then 1 else 0) := by
    have he (i j : Fin N) : (if i<j then
        ((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0) =
        (if i=k then (if k<j then 1 else 0) else 0)+
        (if j=k then (if i<k then 1 else 0) else 0) := by
      split_ifs <;> omega
    simp_rw [he,Finset.sum_add_distrib]
    simp
  rw [hsplit,← Finset.sum_add_distrib]
  have hentry (j : Fin N) : (if k<j then 1 else 0)+(if j<k then 1 else 0) =
      (if j=k then 0 else 1 : ℕ) := by
    split_ifs <;> omega
  simp_rw [hentry]
  simp [Finset.sum_ite,Finset.filter_ne']

theorem laughlinPolynomial_particle_degree (N : ℕ) (k : Fin N) :
    (laughlinPolynomial N).IsWeightedHomogeneous (particleDegreeWeight k) (3*(N-1)) := by
  have hp := IsWeightedHomogeneous.prod (Finset.univ : Finset (Fin N))
    (fun i => ∏ j : Fin N, if i<j then bracket i j^3 else 1)
    (fun i => ∑ j : Fin N, if i<j then
      3*((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0) (w := particleDegreeWeight k) (by
      intro i hi
      apply IsWeightedHomogeneous.prod
      intro j hj
      by_cases hij : i<j
      · simpa only [ite_eq_left hij,nsmul_eq_mul,Nat.cast_id] using (bracket_particle_degree k i j).pow 3
      · simp only [ite_eq_right hij]
        exact isWeightedHomogeneous_one ℂ _)
  have hs : (∑ i : Fin N, ∑ j : Fin N, if i<j then
      3*((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0)=3*(N-1) := by
    have he (i j : Fin N) : (if i<j then
        3*((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0) =
        3*(if i<j then ((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0) := by
      by_cases h : i<j <;> simp [h]
    simp_rw [he,← Finset.mul_sum]
    rw [particle_pair_degree_count]
  rw [hs] at hp
  exact hp

theorem spinPolynomial_laughlinVector (N : ℕ) :
    spinPolynomial (laughlinVector N (3*(N-1)))=laughlinPolynomial N := by
  exact spinPolynomial_reconstruct _ (laughlinPolynomial_particle_degree N)

theorem laughlinVector_ne_zero (N : ℕ) : laughlinVector N (3*(N-1)) ≠ 0 := by
  intro h
  have he := spinPolynomial_laughlinVector N
  rw [h] at he
  have hz : spinPolynomial (0 : State N (3*(N-1)))=0 := by simp [spinPolynomial]
  rw [hz] at he
  exact laughlinPolynomial_ne_zero N he.symm

end Laughlin

end OAI
