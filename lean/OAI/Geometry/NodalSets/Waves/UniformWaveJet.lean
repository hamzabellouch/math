import OAI.Geometry.NodalSets.Elliptic.SmoothBeamJet
import OAI.Geometry.NodalSets.Elliptic.UniformEikonal
import OAI.Geometry.NodalSets.Elliptic.UniformTransportPolynomial

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma beamVector_family (g : T → Fin 4 → Fin 4 → CPoly) (phi : T → CPoly)
    (hg : ∀ i j, ContinuousPolyFamily (fun t ↦ g t i j))
    (hp : ContinuousPolyFamily phi) (i : Fin 4) :
    ContinuousPolyFamily (fun t ↦ beamVector (g t) (phi t) i) := by
  apply ContinuousPolyFamily.mul (.const _)
  exact ContinuousPolyFamily.sum _ (fun j _ ↦ (hg i j).mul (hp.pderiv j))

lemma secondOrder_family (g : T → Fin 4 → Fin 4 → CPoly)
    (b : T → Fin 4 → CPoly) (phi : T → CPoly)
    (hg : ∀ i j, ContinuousPolyFamily (fun t ↦ g t i j))
    (hb : ∀ i, ContinuousPolyFamily (fun t ↦ b t i))
    (hp : ContinuousPolyFamily phi) :
    ContinuousPolyFamily (fun t ↦ polynomialSecondOrder (g t) (b t) (phi t)) := by
  apply ContinuousPolyFamily.add
  · apply ContinuousPolyFamily.sum
    intro i _
    exact ContinuousPolyFamily.sum _ (fun j _ ↦ (hg i j).mul ((hp.pderiv j).pderiv i))
  · exact ContinuousPolyFamily.sum _ (fun i _ ↦ (hb i).mul (hp.pderiv i))

lemma beamScalar_family (g : T → Fin 4 → Fin 4 → CPoly)
    (b : T → Fin 4 → CPoly) (phi : T → CPoly)
    (hg : ∀ i j, ContinuousPolyFamily (fun t ↦ g t i j))
    (hb : ∀ i, ContinuousPolyFamily (fun t ↦ b t i))
    (hp : ContinuousPolyFamily phi) :
    ContinuousPolyFamily (fun t ↦ beamScalar (g t) (b t) (phi t)) :=
  (secondOrder_family g b phi hg hb hp).add (.const _)

theorem polynomial_wave_jets_continuous
    (v : T → Fin 4 → ℂ) (hv : ∀ j, Continuous (fun t ↦ v t j))
    (i : Fin 4) (hvi : ∀ t, v t i ≠ 0)
    (g : T → Fin 4 → Fin 4 → CPoly) (b : T → Fin 4 → CPoly)
    (hg : ∀ i j, ContinuousPolyFamily (fun t ↦ g t i j))
    (hb : ∀ i, ContinuousPolyFamily (fun t ↦ b t i))
    (hmetric : ∀ t i j, homogeneousComponent 0 (g t i j) = if i = j then 1 else 0)
    (initial : T → Jet) (hi : ∀ t k, (initial t k).IsHomogeneous k)
    (hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k))
    (hfirst : ∀ t i, pderiv i (initial t 1) = C (v t i))
    (hcenter : ∀ t, (∑ i, v t i * v t i) + 4 = 0)
    (hsecond : ∀ t, eikonalCoefficient (v t)
      (fun r i j ↦ homogeneousComponent r (g t i j)) 0 (initial t) = 0) (m J : ℕ) :
    ∃ (phi : T → CPoly) (A : ℕ → T → CPoly),
      ContinuousPolyFamily phi ∧ (∀ j, ContinuousPolyFamily (A j)) ∧
      (∀ t k, k ≤ 2 → homogeneousComponent k (phi t) = initial t k) ∧
      (∀ t d, m + 2 * J + 3 < d → homogeneousComponent d (phi t) = 0) ∧
      (∀ t d, d ≤ m + 2 * J + 2 →
        homogeneousComponent d (polynomialEikonal (g t) (phi t)) = 0) ∧
      (∀ j t, homogeneousComponent 0 (A j t) = if j = 0 then 1 else 0) ∧
      (∀ j t k, m + 1 + 2 * (J - j) < k → homogeneousComponent k (A j t) = 0) ∧
      (∀ t n, n < m + 1 + 2 * J → homogeneousComponent n
        (polynomialTransport (beamVector (g t) (phi t)) (beamScalar (g t) (b t) (phi t))
          0 (A 0 t)) = 0) ∧
      ∀ j, j < J → ∀ t n, n < m + 1 + 2 * (J - (j + 1)) → homogeneousComponent n
        (polynomialTransport (beamVector (g t) (phi t)) (beamScalar (g t) (b t) (phi t))
          (-polynomialSecondOrder (g t) (b t) (A j t)) (A (j + 1) t)) = 0 := by
  obtain ⟨phi, hpc, hkeep, hdegree, hsolve, _⟩ := finite_eikonal_polynomial_continuous
    v hv i hvi (fun t r i j ↦ homogeneousComponent r (g t i j))
    (fun r i j ↦ (hg i j).homogeneousComponent r) initial hi hic hsecond (m + 2 * J + 1)
  have hf : ∀ t i, pderiv i (homogeneousComponent 1 (phi t)) = C (v t i) := by
    intro t i
    rw [show homogeneousComponent 1 (phi t) = initial t 1 from hkeep t 1 (by omega), hfirst]
  have he : ∀ t d, d ≤ m + 2 * J + 2 →
      homogeneousComponent d (polynomialEikonal (g t) (phi t)) = 0 := by
    intro t d hd
    cases d with
    | zero =>
      unfold polynomialEikonal
      have hc0 (a b : CPoly) : homogeneousComponent 0 (a * b) =
          homogeneousComponent 0 a * homogeneousComponent 0 b := by
        simpa using homogeneousComponent_mul a b 0
      simp only [map_add, map_sum, hc0, homogeneousComponent_pderiv, Nat.zero_add, hf, hmetric]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [homogeneousComponent_eq_self (isHomogeneous_C (Fin 4) (4 : ℂ))]
      simpa only [map_add, map_sum, map_mul, map_zero] using congrArg C (hcenter t)
    | succ n =>
      rw [← eikonalCoefficient_eq (v t) (g t) (hmetric t) (phi t) (hf t) n]
      exact hsolve t n (by omega)
  have hW := beamVector_family g phi hg hpc
  have hc := beamScalar_family g b phi hg hb hpc
  obtain ⟨A, hAc, hA0, hAd, hAfirst, hAnext⟩ := finite_transport_polynomials_continuous
    (fun t j ↦ 2 * v t j) (fun j ↦ continuous_const.mul (hv j))
    i (fun t ↦ mul_ne_zero (by norm_num) (hvi t))
    (fun t r j ↦ homogeneousComponent r (beamVector (g t) (phi t) j))
    (fun t ↦ polynomialJet (beamScalar (g t) (b t) (phi t)))
    (fun t r i j ↦ homogeneousComponent r (g t i j))
    (fun t r i ↦ homogeneousComponent r (b t i))
    (fun r j ↦ (hW j).homogeneousComponent r) (fun r ↦ hc.homogeneousComponent r)
    (fun r i j ↦ (hg i j).homogeneousComponent r)
    (fun r i ↦ (hb i).homogeneousComponent r) m J
  refine ⟨phi, A, hpc, hAc, hkeep, ?_, he, hA0, hAd, ?_, ?_⟩
  · simpa [Nat.add_assoc, polynomialJet] using hdegree
  · intro t n hn
    rw [← transportCoefficient_eq (fun j ↦ 2 * v t j) _
      (beamVector_center (v t) (g t) (hmetric t) (phi t) (hf t)) _ 0 (A 0 t) n]
    have hz : polynomialJet (0 : CPoly) = (0 : Jet) := funext (fun k ↦ map_zero _)
    rw [hz]
    exact hAfirst t n hn
  · intro j hj t n hn
    rw [← transportCoefficient_eq (fun j ↦ 2 * v t j) _
      (beamVector_center (v t) (g t) (hmetric t) (phi t) (hf t)) _
      (-polynomialSecondOrder (g t) (b t) (A j t)) (A (j + 1) t) n]
    have hforce : polynomialJet (-polynomialSecondOrder (g t) (b t) (A j t)) =
        fun k ↦ -secondOrderCoefficient (fun r i j ↦ homogeneousComponent r (g t i j))
          (fun r i ↦ homogeneousComponent r (b t i)) (polynomialJet (A j t)) k := by
      funext k
      rw [secondOrderCoefficient_eq]
      exact map_neg (homogeneousComponent k) _
    rw [hforce]
    exact hAnext j hj t n hn

theorem smooth_wave_jets_continuous
    (v : T → Fin 4 → ℂ) (hv : ∀ j, Continuous (fun t ↦ v t j))
    (i : Fin 4) (hvi : ∀ t, v t i ≠ 0)
    (g : T → Fin 4 → Fin 4 → Coord → ℂ) (b : T → Fin 4 → Coord → ℂ)
    (G : T → Fin 4 → Fin 4 → CPoly) (B : T → Fin 4 → CPoly)
    (hG : ∀ i j, ContinuousPolyFamily (fun t ↦ G t i j))
    (hB : ∀ i, ContinuousPolyFamily (fun t ↦ B t i))
    (hg : ∀ t i j, ContDiff ℝ ∞ (g t i j)) (hb : ∀ t i, ContDiff ℝ ∞ (b t i))
    (hmetric : ∀ t i j, homogeneousComponent 0 (G t i j) = if i = j then 1 else 0)
    (initial : T → Jet) (hi : ∀ t k, (initial t k).IsHomogeneous k)
    (hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k))
    (hfirst : ∀ t i, pderiv i (initial t 1) = C (v t i))
    (hcenter : ∀ t, (∑ i, v t i * v t i) + 4 = 0)
    (hsecond : ∀ t, eikonalCoefficient (v t)
      (fun r i j ↦ homogeneousComponent r (G t i j)) 0 (initial t) = 0) (m J : ℕ)
    (hgj : ∀ t i j, FlatAt m (fun x ↦ g t i j x - reval (G t i j) x) 0)
    (hbj : ∀ t i, FlatAt m (fun x ↦ b t i x - reval (B t i) x) 0) :
    ∃ (phi : T → CPoly) (A : ℕ → T → CPoly),
      ContinuousPolyFamily phi ∧ (∀ j, ContinuousPolyFamily (A j)) ∧
      (∀ t k, k ≤ 2 → homogeneousComponent k (phi t) = initial t k) ∧
      (∀ t d, m + 2 * J + 3 < d → homogeneousComponent d (phi t) = 0) ∧
      (∀ j t, homogeneousComponent 0 (A j t) = if j = 0 then 1 else 0) ∧
      (∀ j t k, m + 1 + 2 * (J - j) < k → homogeneousComponent k (A j t) = 0) ∧
      (∀ t, FlatAt m (smoothEikonal (g t) (reval (phi t))) 0) ∧
      (∀ t, FlatAt m (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
        (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))) 0) ∧
      ∀ j, j < J → ∀ t, FlatAt m
        (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
          (smoothBeamScalar (g t) (b t) (reval (phi t)))
          (fun x ↦ -smoothSecondOrder (g t) (b t) (reval (A j t)) x)
          (reval (A (j + 1) t))) 0 := by
  obtain ⟨phi, A, hpc, hAc, hkeep, hdeg, he, hA0, hAd, ht0, htj⟩ :=
    polynomial_wave_jets_continuous v hv i hvi G B hG hB hmetric initial hi hic
      hfirst hcenter hsecond m J
  refine ⟨phi, A, hpc, hAc, hkeep, hdeg, hA0, hAd, ?_, ?_, ?_⟩
  · intro t
    exact smooth_eikonal_flat (G t) (phi t) (hg t) (hgj t) (fun k hk ↦ he t k (by omega))
  · intro t
    have hp : ∀ k, k ≤ m → homogeneousComponent k
        (polynomialTransport (beamVector (G t) (phi t)) (beamScalar (G t) (B t) (phi t))
          (-polynomialSecondOrder (G t) (B t) 0) (A 0 t)) = 0 := by
      intro k hk
      simpa [polynomialSecondOrder] using ht0 t k (by omega)
    have h := smooth_beam_transport_flat (G t) (B t) (phi t) 0 (A 0 t)
      (hg t) (hb t) (hgj t) (hbj t) hp
    have hz : (fun x ↦ -smoothSecondOrder (g t) (b t) (reval 0) x) = fun _ ↦ 0 := by
      ext x
      simp [smoothSecondOrder, coordPartial_reval, reval]
    rw [hz] at h
    exact h
  · intro j hj t
    exact smooth_beam_transport_flat (G t) (B t) (phi t) (A j t) (A (j + 1) t)
      (hg t) (hb t) (hgj t) (hbj t) (fun k hk ↦ htj j hj t k (by omega))

end
end Yau.Jets

end OAI
