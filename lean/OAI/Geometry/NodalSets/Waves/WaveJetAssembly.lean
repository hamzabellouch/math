import OAI.Geometry.NodalSets.Elliptic.EikonalPolynomial

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def beamVector (g : Fin 4 → Fin 4 → CPoly) (phi : CPoly) (i : Fin 4) : CPoly :=
  C 2 * ∑ j, g i j * pderiv j phi

def beamScalar (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly) (phi : CPoly) : CPoly :=
  polynomialSecondOrder g b phi + C 6

lemma beamVector_center (v : Fin 4 → ℂ) (g : Fin 4 → Fin 4 → CPoly)
    (hmetric : ∀ i j, homogeneousComponent 0 (g i j) = if i = j then 1 else 0)
    (phi : CPoly) (hfirst : ∀ i, pderiv i (homogeneousComponent 1 phi) = C (v i)) :
    ∀ i, homogeneousComponent 0 (beamVector g phi i) = C (2 * v i) := by
  intro i
  have hc0 (a b : CPoly) : homogeneousComponent 0 (a * b) =
      homogeneousComponent 0 a * homogeneousComponent 0 b := by
    simpa using homogeneousComponent_mul a b 0
  unfold beamVector
  rw [homogeneousComponent_C_mul, map_sum]
  simp only [hc0, homogeneousComponent_pderiv, Nat.zero_add, hfirst, hmetric,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, map_mul]

theorem polynomial_transport_hierarchy (w : Fin 4 → ℂ) (hw : w ≠ 0)
    (W : Fin 4 → CPoly) (hW : ∀ i, homogeneousComponent 0 (W i) = C (w i))
    (c : CPoly) (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly) (m J : ℕ) :
    ∃ P : ℕ → CPoly,
      (∀ j, homogeneousComponent 0 (P j) = if j = 0 then 1 else 0) ∧
      (∀ j k, m + 1 + 2 * (J - j) < k → homogeneousComponent k (P j) = 0) ∧
      (∀ n, n < m + 1 + 2 * J → homogeneousComponent n (polynomialTransport W c 0 (P 0)) = 0) ∧
      ∀ j, j < J → ∀ n, n < m + 1 + 2 * (J - (j + 1)) →
        homogeneousComponent n (polynomialTransport W c (-polynomialSecondOrder g b (P j))
          (P (j + 1))) = 0 := by
  obtain ⟨P, hzero, hdeg, hfirst, hnext⟩ := finite_transport_polynomials w hw
    (fun r i ↦ homogeneousComponent r (W i)) (polynomialJet c)
    (fun r i j ↦ homogeneousComponent r (g i j)) (fun r i ↦ homogeneousComponent r (b i)) m J
  refine ⟨P, hzero, hdeg, ?_, ?_⟩
  · intro n hn
    rw [← transportCoefficient_eq w W hW c 0 (P 0) n]
    have hz : polynomialJet (0 : CPoly) = (0 : Jet) := funext (fun k ↦ map_zero _)
    rw [hz]
    exact hfirst n hn
  · intro j hj n hn
    rw [← transportCoefficient_eq w W hW c (-polynomialSecondOrder g b (P j)) (P (j + 1)) n]
    have hforce : polynomialJet (-polynomialSecondOrder g b (P j)) =
        fun k ↦ -secondOrderCoefficient (fun r i j ↦ homogeneousComponent r (g i j))
          (fun r i ↦ homogeneousComponent r (b i)) (polynomialJet (P j)) k := by
      funext k
      rw [secondOrderCoefficient_eq]
      exact map_neg (homogeneousComponent k) _
    rw [hforce]
    exact hnext j hj n hn

theorem polynomial_wave_jets (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly)
    (hmetric : ∀ i j, homogeneousComponent 0 (g i j) = if i = j then 1 else 0)
    (initial : Jet) (hi : ∀ k, (initial k).IsHomogeneous k)
    (hfirst : ∀ i, pderiv i (initial 1) = C (v i))
    (hcenter : (∑ i, v i * v i) + 4 = 0)
    (hsecond : eikonalCoefficient v (fun r i j ↦ homogeneousComponent r (g i j)) 0 initial = 0)
    (m J : ℕ) :
    ∃ (phi : CPoly) (A : ℕ → CPoly),
      (∀ k, k ≤ 2 → homogeneousComponent k phi = initial k) ∧
      (∀ d, m + 2 * J + 3 < d → homogeneousComponent d phi = 0) ∧
      (∀ d, d ≤ m + 2 * J + 2 → homogeneousComponent d (polynomialEikonal g phi) = 0) ∧
      (∀ j, homogeneousComponent 0 (A j) = if j = 0 then 1 else 0) ∧
      (∀ j k, m + 1 + 2 * (J - j) < k → homogeneousComponent k (A j) = 0) ∧
      (∀ n, n < m + 1 + 2 * J →
        homogeneousComponent n (polynomialTransport (beamVector g phi) (beamScalar g b phi) 0 (A 0)) = 0) ∧
      ∀ j, j < J → ∀ n, n < m + 1 + 2 * (J - (j + 1)) →
        homogeneousComponent n (polynomialTransport (beamVector g phi) (beamScalar g b phi)
          (-polynomialSecondOrder g b (A j)) (A (j + 1))) = 0 := by
  obtain ⟨phi, hkeep, hdegree, heik⟩ := polynomial_eikonal_jets v hv g hmetric initial hi hfirst
    hcenter hsecond (m + 2 * J + 1)
  have hf : ∀ i, pderiv i (homogeneousComponent 1 phi) = C (v i) := by
    intro i
    rw [show homogeneousComponent 1 phi = initial 1 from hkeep 1 (by omega), hfirst]
  have hv2 : (fun i ↦ 2 * v i) ≠ (0 : Fin 4 → ℂ) := by
    intro h
    apply hv
    funext i
    have := congrFun h i
    simpa using this
  obtain ⟨A, hA0, hAd, hAfirst, hAnext⟩ := polynomial_transport_hierarchy (fun i ↦ 2 * v i) hv2
    (beamVector g phi) (beamVector_center v g hmetric phi hf) (beamScalar g b phi) g b m J
  exact ⟨phi, A, hkeep, by simpa [Nat.add_assoc] using hdegree,
    by simpa [Nat.add_assoc] using heik, hA0, hAd, hAfirst, hAnext⟩

end
end Yau.Jets

end OAI
