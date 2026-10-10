import OAI.Analysis.KadisonKastler.ReducingCommutantCorner
import OAI.Analysis.KadisonKastler.FiniteFactorCommutantNear
import OAI.Analysis.KadisonKastler.PreparedPairCorrection
import OAI.Analysis.KadisonKastler.NearInclusionDistance

namespace OAI

/-! # Commutant approximation after aligning a reducing subspace

The finite-factor estimate is applied before moving the neighbor. This
keeps the error linear in the original gap, with no repeated amplification
constant after the unitary correction.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

theorem cornerCompression_mem_reducing_commutant
    (M : VonNeumannAlgebra H) (hp : E.starProjection ∈ M.commutant)
    {T : H →L[ℂ] H} (hT : T ∈ M.commutant) :
    cornerCompression E T ∈
      (generatedVonNeumannAlgebra (commutantReducingHom E M hp).range).commutant := by
  rw [commutant_reducingClosure]
  apply (mem_representedCorner E M.commutant hp _).mpr
  rw [cornerExtension_compression]
  exact M.commutant.mul_mem (M.commutant.mul_mem hp hT) hp

variable [TopologicalSpace.SeparableSpace H]

theorem reducing_commutant_approx_after_alignment
    (M N : VonNeumannAlgebra H) (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (hpM : E.starProjection ∈ M.commutant)
    (u : unitary (H →L[ℂ] H))
    (hpN : E.starProjection ∈ (unitaryConjugateAlgebra (star u) N).commutant)
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 1 / 3200000000)
    (hgap : kkDistance M N < 2 * γ)
    (hu : ‖(u : H →L[ℂ] H) - 1‖ ≤ 200000000 * γ)
    (T : E →L[ℂ] E)
    (hT : T ∈ (generatedVonNeumannAlgebra (commutantReducingHom E M hpM).range).commutant)
    (hnT : ‖T‖ ≤ 1) :
    ∃ D ∈ (generatedVonNeumannAlgebra
        (commutantReducingHom E (unitaryConjugateAlgebra (star u) N) hpN).range).commutant,
      ‖D - T‖ < 404500000 * γ := by
  have hExt : cornerExtension E T ∈ M.commutant := by
    rw [commutant_reducingClosure] at hT
    exact (mem_representedCorner E M.commutant hpM T).mp hT
  obtain ⟨D, hD, hDT⟩ := finiteFactor_commutant_approx_of_gap N M hN
    (by positivity : 0 < 2 * γ) (by rwa [kkDistance_comm])
    (cornerExtension E T) hExt (by simpa only [norm_cornerExtension] using hnT)
  let V := unitaryConj (star u) D
  have hV : V ∈ (unitaryConjugateAlgebra (star u) N).commutant :=
    unitaryConj_mem_conjugated_commutant N (star u) hD
  refine ⟨cornerCompression E V, cornerCompression_mem_reducing_commutant E _ hpN hV, ?_⟩
  have hDn : ‖D‖ ≤ 1 + 4000000 * γ := by
    have h := norm_le_norm_sub_add D (cornerExtension E T)
    rw [norm_cornerExtension] at h
    linarith
  have hstar : ‖((star u : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
      ‖(u : H →L[ℂ] H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using norm_star ((u : H →L[ℂ] H) - 1)
  have hVD : ‖V - D‖ ≤ 400000000 * γ * (1 + 4000000 * γ) := by
    have h := norm_unitaryConj_sub_le (star u) D
    rw [hstar] at h
    have hu2 : 2 * ‖(u : H →L[ℂ] H) - 1‖ ≤ 400000000 * γ := by linarith
    exact h.trans (mul_le_mul hu2 hDn (norm_nonneg D)
      (by positivity : 0 ≤ 400000000 * γ))
  have he : cornerCompression E V - T = cornerCompression E (V - cornerExtension E T) := by
    rw [map_sub, cornerCompression_extension]
  rw [he]
  apply (norm_cornerCompression_le E _).trans_lt
  have hdist := norm_sub_le_norm_sub_add_norm_sub V D (cornerExtension E T)
  have hpoly : 400000000 * γ * (1 + 4000000 * γ) + 4000000 * γ < 404500000 * γ := by
    nlinarith
  linarith

theorem nearInclusion_reducing_commutants_after_alignment
    (M N : VonNeumannAlgebra H) (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (hpM : E.starProjection ∈ M.commutant)
    (u : unitary (H →L[ℂ] H))
    (hpN : E.starProjection ∈ (unitaryConjugateAlgebra (star u) N).commutant)
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 1 / 3200000000)
    (hgap : kkDistance M N < 2 * γ)
    (hu : ‖(u : H →L[ℂ] H) - 1‖ ≤ 200000000 * γ) :
    NearInclusion
      (generatedVonNeumannAlgebra (commutantReducingHom E M hpM).range).commutant
      (generatedVonNeumannAlgebra
        (commutantReducingHom E (unitaryConjugateAlgebra (star u) N) hpN).range).commutant
      (405000000 * γ) := by
  refine ⟨404500000 * γ, by linarith, ?_⟩
  intro T hT
  obtain ⟨D, hD, hDT⟩ := reducing_commutant_approx_after_alignment E M N hN hpM
    u hpN hγ hsmall hgap hu T hT.1 hT.2
  exact (Metric.infDist_le_dist_of_mem hD).trans
    (by simpa only [dist_eq_norm, norm_sub_rev] using hDT.le)

theorem reducing_commutant_reverse_approx_after_alignment
    (M N : VonNeumannAlgebra H) (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hpM : E.starProjection ∈ M.commutant)
    (u : unitary (H →L[ℂ] H))
    (hpN : E.starProjection ∈ (unitaryConjugateAlgebra (star u) N).commutant)
    {γ : ℝ} (hγ : 0 < γ) (hgap : kkDistance M N < 2 * γ)
    (hu : ‖(u : H →L[ℂ] H) - 1‖ ≤ 200000000 * γ)
    (T : E →L[ℂ] E)
    (hT : T ∈ (generatedVonNeumannAlgebra
      (commutantReducingHom E (unitaryConjugateAlgebra (star u) N) hpN).range).commutant)
    (hnT : ‖T‖ ≤ 1) :
    ∃ D ∈ (generatedVonNeumannAlgebra (commutantReducingHom E M hpM).range).commutant,
      ‖D - T‖ < 404000000 * γ := by
  have hExt : cornerExtension E T ∈ (unitaryConjugateAlgebra (star u) N).commutant := by
    rw [commutant_reducingClosure] at hT
    exact (mem_representedCorner E _ hpN T).mp hT
  let S := unitaryConj u (cornerExtension E T)
  have hS : S ∈ N.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp hExt
      (unitaryConj (star u) a) ⟨a, ha, rfl⟩
    have he := congrArg (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u) hc
    rw [map_mul, map_mul] at he
    have hinv : unitaryConj u (unitaryConj (star u) a) = a := by
      simpa only [star_star] using unitaryConj_star_unitaryConj (star u) a
    simpa only [show ∀ X : H →L[ℂ] H,
      (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u) X = unitaryConj u X from fun _ => rfl,
      hinv] using he
  have hnS : ‖S‖ ≤ 1 := by
    change ‖unitaryConj u (cornerExtension E T)‖ ≤ 1
    simpa only [norm_unitaryConj, norm_cornerExtension] using hnT
  obtain ⟨D, hD, hDS⟩ := finiteFactor_commutant_approx_of_gap M N hM
    (by positivity : 0 < 2 * γ) hgap S hS hnS
  refine ⟨cornerCompression E D, cornerCompression_mem_reducing_commutant E M hpM hD, ?_⟩
  have hSE : ‖S - cornerExtension E T‖ ≤ 400000000 * γ := by
    have hn := norm_unitaryConj_sub_le u (cornerExtension E T)
    rw [norm_cornerExtension] at hn
    exact hn.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (by norm_num)) (norm_nonneg T)).trans
        (by nlinarith))
  have he : cornerCompression E D - T = cornerCompression E (D - cornerExtension E T) := by
    rw [map_sub, cornerCompression_extension]
  rw [he]
  apply (norm_cornerCompression_le E _).trans_lt
  have hd := norm_sub_le_norm_sub_add_norm_sub D S (cornerExtension E T)
  linarith

theorem reverse_nearInclusion_reducing_commutants_after_alignment
    (M N : VonNeumannAlgebra H) (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hpM : E.starProjection ∈ M.commutant)
    (u : unitary (H →L[ℂ] H))
    (hpN : E.starProjection ∈ (unitaryConjugateAlgebra (star u) N).commutant)
    {γ : ℝ} (hγ : 0 < γ) (hgap : kkDistance M N < 2 * γ)
    (hu : ‖(u : H →L[ℂ] H) - 1‖ ≤ 200000000 * γ) :
    NearInclusion
      (generatedVonNeumannAlgebra
        (commutantReducingHom E (unitaryConjugateAlgebra (star u) N) hpN).range).commutant
      (generatedVonNeumannAlgebra (commutantReducingHom E M hpM).range).commutant
      (405000000 * γ) := by
  refine ⟨404000000 * γ, by linarith, ?_⟩
  intro T hT
  obtain ⟨D, hD, hDT⟩ := reducing_commutant_reverse_approx_after_alignment E M N hM hpM
    u hpN hγ hgap hu T hT.1 hT.2
  exact (Metric.infDist_le_dist_of_mem hD).trans
    (by simpa only [dist_eq_norm, norm_sub_rev] using hDT.le)

theorem kkDistance_reducing_commutants_after_alignment
    (M N : VonNeumannAlgebra H)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (hpM : E.starProjection ∈ M.commutant)
    (u : unitary (H →L[ℂ] H))
    (hpN : E.starProjection ∈ (unitaryConjugateAlgebra (star u) N).commutant)
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 1 / 3200000000)
    (hgap : kkDistance M N < 2 * γ)
    (hu : ‖(u : H →L[ℂ] H) - 1‖ ≤ 200000000 * γ) :
    kkDistance
      (generatedVonNeumannAlgebra (commutantReducingHom E M hpM).range).commutant
      (generatedVonNeumannAlgebra
        (commutantReducingHom E (unitaryConjugateAlgebra (star u) N) hpN).range).commutant ≤
      810000000 * γ := by
  have hf := nearInclusion_reducing_commutants_after_alignment E M N hN hpM
    u hpN hγ hsmall hgap hu
  have hr := reverse_nearInclusion_reducing_commutants_after_alignment E M N hM hpM
    u hpN hγ hgap hu
  have h := kkDistance_le_two_mul_of_nearInclusions (by positivity) hf hr
  nlinarith

end

end KadisonKastler

end OAI
