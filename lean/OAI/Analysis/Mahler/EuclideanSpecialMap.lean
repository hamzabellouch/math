import OAI.Analysis.Mahler.SpecialMassHypotheses
import OAI.Analysis.Mahler.OpenHessian

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter Finset Asymptotics
open scoped Topology
variable {n N : ℕ}

noncomputable def euclideanCoordinates : Mahler.ComplexEuclidean n ≃L[ℂ] (Fin n → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)

noncomputable def euclideanStripDomain (A : Matrix (Fin N) (Fin n) ℝ) :
    Set (Mahler.ComplexEuclidean n) := euclideanCoordinates ⁻¹' complexStripDomain A

noncomputable def euclideanSpecialMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (j : Fin N) (z : Mahler.ComplexEuclidean n) : ℂ :=
  specialMap A m (euclideanCoordinates z) j

lemma euclideanSpecialTau (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Mahler.ComplexEuclidean n) :
    Mahler.tau (euclideanSpecialMap A m) z = specialTau A m (euclideanCoordinates z) := by
  simp only [Mahler.tau,euclideanSpecialMap,specialTau,Complex.normSq_eq_norm_sq]

lemma differentiableOn_euclideanSpecialMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (j : Fin N) : DifferentiableOn ℂ (euclideanSpecialMap A m j) (euclideanStripDomain A) := by
  have h := differentiableOn_pi.mp (differentiableOn_specialMap A m) j
  exact h.comp euclideanCoordinates.differentiable.differentiableOn (fun z hz => hz)

lemma euclideanSpecial_remainder (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    IsBigO (𝓝[≠] (0 : Mahler.ComplexEuclidean n))
      (fun z => (WithLp.toLp 2 (fun j => euclideanSpecialMap A m j z -
        MvPolynomial.eval (fun i => z i) (specialLeadingPolynomial A m j)) :
          Mahler.ComplexEuclidean N)) (fun z => ‖z‖ ^ (m + 1)) := by
  have ht : Tendsto (euclideanCoordinates (n := n)) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [map_zero] using
      ((euclideanCoordinates (n := n)).continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hcomp := (specialMap_leading_remainder A m).comp_tendsto ht
  have hnorm := (euclideanCoordinates.toContinuousLinearMap.isBigO_id
    (𝓝[≠] (0 : Mahler.ComplexEuclidean n))).norm_norm.pow (m+1)
  have hout := (euclideanCoordinates (n := N)).symm.isBigO_comp
    (fun z : Mahler.ComplexEuclidean n => specialMap A m (euclideanCoordinates z) -
      specialLeadingMap A m (euclideanCoordinates z)) (𝓝[≠] 0)
  have h := hout.trans (hcomp.trans hnorm)
  simpa only [euclideanSpecialMap,specialLeadingPolynomial_eval,euclideanCoordinates,
    PiLp.coe_continuousLinearEquiv,PiLp.coe_symm_continuousLinearEquiv,Pi.sub_apply] using! h

lemma euclideanSpecial_compact_closure (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    IsCompact (closure (euclideanStripDomain A ∩ {z | Mahler.tau (euclideanSpecialMap A m) z < R})) ∧
      closure (euclideanStripDomain A ∩ {z | Mahler.tau (euclideanSpecialMap A m) z < R}) ⊆
        euclideanStripDomain A := by
  have h := specialTau_compact_closure A hA hm hR hR1
  let S := {z | z ∈ complexStripDomain A ∧ specialTau A m z < R}
  let K := (euclideanCoordinates (n := n)) ⁻¹' closure S
  have hK : IsCompact K := euclideanCoordinates.toHomeomorph.isCompact_preimage.mpr h.1
  have hs : euclideanStripDomain A ∩ {z | Mahler.tau (euclideanSpecialMap A m) z < R} ⊆ K := by
    intro z hz
    apply subset_closure
    exact ⟨hz.1,by simpa only [euclideanSpecialTau,mem_ofPred_eq] using hz.2⟩
  have hclosure := closure_minimal hs hK.isClosed
  exact ⟨hK.of_isClosed_subset isClosed_closure hclosure,fun z hz => h.2 (hclosure hz)⟩

/-- The mass hypotheses hold
for the special map, including the Euclidean Taylor estimate. -/
theorem euclideanSpecial_massHypotheses (A : Matrix (Fin N) (Fin n) ℝ)
    (hn : 1 ≤ n) (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 2 ≤ m) :
    Mahler.MassHypotheses n N m (euclideanStripDomain A)
      (euclideanSpecialMap A m) (specialLeadingPolynomial A m) := by
  have hm0 : 0 < m := by omega
  refine ⟨hn,by omega,?_,?_,differentiableOn_euclideanSpecialMap A m,?_,
    specialLeadingPolynomial_homogeneous A m,?_,euclideanSpecial_remainder A m,?_⟩
  · exact (isOpen_complexStripDomain A).preimage euclideanCoordinates.continuous
  · change euclideanCoordinates 0 ∈ complexStripDomain A
    simpa only [map_zero] using zero_mem_complexStripDomain A
  · intro z hz
    have h := specialMap_eq_zero_iff A hA hm0 hz
    constructor
    · intro hf
      have he := h.mp (funext hf)
      exact euclideanCoordinates.injective (he.trans (map_zero _).symm)
    · intro hz0 j
      have he := h.mpr (by simp only [hz0,map_zero])
      exact congrFun he j
  · intro z hz
    by_contra h
    push Not at h
    have he : specialLeadingMap A m (euclideanCoordinates z) = 0 := by
      funext j
      simpa only [specialLeadingPolynomial_eval,euclideanCoordinates,PiLp.coe_continuousLinearEquiv,Pi.zero_apply] using! h j
    have hz0 := (specialLeadingMap_eq_zero_iff A hA hm0 _).mp he
    exact hz (euclideanCoordinates.injective (hz0.trans (map_zero _).symm))
  · intro R hR hR1
    exact euclideanSpecial_compact_closure A hA hm0 hR hR1

end SymmetricMahler

end OAI
