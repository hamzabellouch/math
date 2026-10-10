import Mathlib
import OAI.Probability.Ballisticity.Crossings.FixedLowerCutoffEscape
import OAI.Probability.Ballisticity.Estimates.SharedShrinking
import OAI.Probability.Ballisticity.Crossings.UniformLowerCutoff
import OAI.Probability.Ballisticity.Estimates.ObservedPotential

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

structure OccupationData {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) (t : ℝ) where
  l : ℝ
  ε : ℝ
  u₀ : ℝ
  C : ℝ
  q : ℝ
  l_pos : 0 < l
  l_le_one : l ≤ 1
  ε_pos : 0 < ε
  u₀_pos : 0 < u₀
  C_pos : 0 < C
  q_pos : 0 < q
  doubling : (2:ℝ)^((7:ℝ)/4) ≤ 4/(1+4*ε)
  upper : ∀ u : ℝ, u₀ ≤ u →
    fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) u*
      (independentConditionedPairLaw ν (realPosition (step e))).real
        {P | l*u < |commonIncrementProcess (realPosition (step e)) f 0 P|} ≤ ε →
    ∀ x y : Lattice d, signedHeight e x=signedHeight e y → |signedCoordinate f (x-y)|=u →
    ∀ b R : ℝ, b ≤ u → u ≤ R →
    let H := ⌊t*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) u⌋₊
    0 < H ∧ u^((3:ℝ)/2)+t/(128*commonMeanWidth ν (realPosition (step e)))*u^((3:ℝ)/2) ≤
      ∫ P, observedPotential b R
        (signedCoordinate f ((boundaryData (realPosition (step e)) ((signedHeight e x+H:ℤ):ℝ) P).endpoints.1-
          (boundaryData (realPosition (step e)) ((signedHeight e x+H:ℤ):ℝ) P).endpoints.2))
        ∂sharedConditionedPairLaw ν (realPosition (step e)) x y
  shrink : ∀ u : ℝ, u₀ ≤ u →
    fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) u*
      (independentConditionedPairLaw ν (realPosition (step e))).real
        {P | l*u < |commonIncrementProcess (realPosition (step e)) f 0 P|} ≤ ε →
    ∀ x y : Lattice d, signedHeight e x=signedHeight e y → |signedCoordinate f (x-y)|=u →
    (sharedConditionedPairLaw ν (realPosition (step e)) x y).real
      {P | ∃ h ≤ ⌊t*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) u⌋₊,
        |physicalFirstHitGap (realPosition (step e)) f x y h P| ≤ u/2} ≤
      8*Real.exp (-commonMeanWidth ν (realPosition (step e))/(16*t))
  escape : ∀ b : ℝ, (b=u₀ ∨ ∃ D : ℝ, u₀ ≤ D ∧
      ε ≤ fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) D*
        (independentConditionedPairLaw ν (realPosition (step e))).real
          {P | l*D < |commonIncrementProcess (realPosition (step e)) f 0 P|} ∧ b=4*D) →
      LowerEscape ν e f b C q

lemma exists_occupationData {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {t : ℝ} (ht : 0 < t) (htmax : t ≤ 1/1000000) :
    Nonempty (OccupationData ν e f t) := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let n := fluctuationScale μ S
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  obtain ⟨l₁,ε₁,R₁,hl₁,hl₁one,hε₁,hR₁,hup⟩ := shared_boundary_potential_drift ν hue e f hef htrans ht htmax
  obtain ⟨l₂,ε₂,R₂,hl₂,hl₂one,hε₂,hR₂,hshr⟩ := shared_uniform_good_shrinking ν hue e f hef htrans ht
  have hpow : (2:ℝ)^((7:ℝ)/4) < 4 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
      (by norm_num : (7:ℝ)/4 < 2)
    norm_num [Real.rpow_two] at h ⊢
    exact h
  let ε₀ := (4-(2:ℝ)^((7:ℝ)/4))/16
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  let l := min l₁ l₂
  let ε := min ε₁ (min ε₂ ε₀)
  have hl : 0 < l := lt_min hl₁ hl₂
  have hl1 : l ≤ 1 := (min_le_left _ _).trans hl₁one.le
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ hε₀)
  have hε₁' : ε ≤ ε₁ := min_le_left _ _
  have hε₂' : ε ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨Cb,qb,D₀,hCb,hqb,hD₀,hbad⟩ := bad_radius_lower_escape_uniform ν hue e f hef htrans hl hl1 hε
  let u₀ := max (max R₁ R₂) D₀
  have hu₀ : 0 < u₀ := hD₀.trans_le (le_max_right _ _)
  have hR₁' : R₁ ≤ u₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hR₂' : R₂ ≤ u₀ := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨Cf,qf,hCf,hqf,hfixed⟩ := fixed_lower_cutoff_escape ν hue e f hef htrans hu₀
  refine ⟨{
    l := l, ε := ε, u₀ := u₀, C := max Cb Cf, q := min qb qf,
    l_pos := hl, l_le_one := hl1, ε_pos := hε, u₀_pos := hu₀,
    C_pos := hCb.trans_le (le_max_left _ _), q_pos := lt_min hqb hqf,
    doubling := ?_, upper := ?_, shrink := ?_, escape := ?_ }⟩
  · apply (le_div_iff₀ (by positivity : (0:ℝ) < 1+4*ε)).mpr
    have heps : ε ≤ ε₀ := (min_le_right _ _).trans (min_le_right _ _)
    have hp : 0 ≤ (2:ℝ)^((7:ℝ)/4) := Real.rpow_nonneg (by norm_num) _
    have hh := mul_le_mul_of_nonneg_left heps hp
    dsimp [ε₀] at hh
    nlinarith [sq_nonneg ((2:ℝ)^((7:ℝ)/4)-4)]
  · intro u hu hg x y hxy hgap b R hb hR
    apply hup u (hR₁'.trans hu) _ x y hxy hgap b R hb hR
    have ht' : μ.real {P | l₁*u < |S P|} ≤ μ.real {P | l*u < |S P|} := by
      apply measureReal_mono _ (measure_ne_top μ _)
      intro P hP
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (min_le_left _ _) (hu₀.le.trans hu)) hP
    exact (mul_le_mul_of_nonneg_left ht' (fluctuationScale_nonneg μ S u)).trans (hg.trans hε₁')
  · intro u hu hg x y hxy hgap
    apply hshr u (hR₂'.trans hu) _ x y hxy hgap
    have ht' : μ.real {P | l₂*u < |S P|} ≤ μ.real {P | l*u < |S P|} := by
      apply measureReal_mono _ (measure_ne_top μ _)
      intro P hP
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (min_le_right _ _) (hu₀.le.trans hu)) hP
    exact (mul_le_mul_of_nonneg_left ht' (fluctuationScale_nonneg μ S u)).trans (hg.trans hε₂')
  · intro b hb
    rcases hb with rfl | ⟨D,hD,hg,rfl⟩
    · exact LowerEscape.mono hfixed (le_max_right _ _) (min_le_right _ _)
    · exact (hbad D ((le_max_right _ _).trans hD) hg).mono (le_max_left _ _) (min_le_left _ _)

end DirectionalTransience

end

end

end OAI
