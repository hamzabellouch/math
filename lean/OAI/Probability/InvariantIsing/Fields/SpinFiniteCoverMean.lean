import OAI.Probability.InvariantIsing.Fields.SpinFiniteCover
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPressureFluctuation

namespace OAI

/-! Haar fluctuations allow a fixed finite spin cover to be used inside
the expectation of the full pressure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing

theorem haar_finite_cover_mean_pressure_upper (hpub : HaarConcentrationInput) :
    ∃ B : ℝ, 0<B ∧ ∀ N, 3≤N →
    ∀ (μ : Measure (SpecialOrthogonal N)), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ (J : Type*) (Q : Finset J), Q.Nonempty → ∀ S : J → Finset (Spin N),
    (∀ j∈Q, (S j).Nonempty) → ∀ (f : Spin N → Spin N) (d : ℕ),
    (∀ σ, f σ∈Q.biUnion S) → (∀ σ, hammingDist σ (f σ)≤d) →
    ∀ (eig c : Fin N → ℝ) (K C t V : ℝ), 0<K → 0≤C → 0≤t →
    (∀ i, |eig i|≤K) → (∀ i, |c i|≤C) →
    (∀ j∈Q, (∫ U, restrictedRotatedPressure (S j) eig (specialRotation U) c ∂μ)≤V) →
    (∫ U, rotatedPressure eig (specialRotation U) c ∂μ) ≤
      V+Q.card*Real.sqrt (B*K^2/N)+(N:ℝ)⁻¹*(Real.log Q.card+
        2*K*Real.sqrt ((N:ℝ)*d)+2*C*d+t*d)+Real.log (1+Real.exp (-t)) := by
  obtain ⟨B,hB,hfluc⟩ := haar_restrictedPressure_mean_fluctuation hpub
  refine ⟨B,hB,?_⟩
  intro N hN μ hμ hμinv J Q hQ S hS f d hf hd eig c K C t V hK hC ht heig hc hmean
  classical
  have : IsProbabilityMeasure μ := hμ
  let F := fun j U => restrictedRotatedPressure (S j) eig (specialRotation U) c
  let D := fun U => ∑ j∈Q, |F j U-∫ V, F j V ∂μ|
  have hFi j (hj : j∈Q) : Integrable (F j) μ :=
    (hfluc N hN μ hμ hμinv (S j) (hS j hj) eig c K hK heig).1
  have hDi : Integrable D μ := by
    exact integrable_finsetSum _ (fun j hj => ((hFi j hj).sub (integrable_const _)).abs)
  have hD : (∫ U, D U ∂μ)≤Q.card*Real.sqrt (B*K^2/N) := by
    change (∫ U, ∑ j∈Q, |F j U-∫ V, F j V ∂μ| ∂μ)≤_
    rw [integral_finsetSum _ (fun j hj =>
      (show Integrable (fun U => |F j U-∫ V, F j V ∂μ|) μ from
        ((hFi j hj).sub (integrable_const _)).abs))]
    calc
      _ ≤ ∑ _j∈Q, Real.sqrt (B*K^2/N) := Finset.sum_le_sum (fun j hj =>
        (hfluc N hN μ hμ hμinv (S j) (hS j hj) eig c K hK heig).2)
      _ = _ := by simp
  have hi : Integrable (fun U => rotatedPressure eig (specialRotation U) c) μ := by
    simpa only [restrictedRotatedPressure_univ] using
      (hfluc N hN μ hμ hμinv Finset.univ Finset.univ_nonempty eig c K hK heig).1
  let E : ℝ := (N:ℝ)⁻¹*(Real.log Q.card+2*K*Real.sqrt ((N:ℝ)*d)+2*C*d+t*d)+
    Real.log (1+Real.exp (-t))
  have hp (U : SpecialOrthogonal N) : rotatedPressure eig (specialRotation U) c ≤ V+D U+E := by
    have hm : ∀ j∈Q, restrictedRotatedPressure (S j) eig (specialRotation U) c≤V+D U := by
      intro j hj
      have hb : |F j U-∫ V, F j V ∂μ|≤D U :=
        Finset.single_le_sum (fun a _ => abs_nonneg (F a U-∫ V, F a V ∂μ)) hj
      have ha := le_abs_self (F j U-∫ V, F j V ∂μ)
      have hme := hmean j hj
      change F j U≤V+D U
      linarith
    have hh := full_pressure_le_finite_cover (by omega) Q hQ S hS f d hf hd eig c
      (specialRotation U) hK.le hC ht heig hc hm
    simpa only [E,add_assoc] using hh
  have hh := integral_mono hi (((integrable_const V).add hDi).add (integrable_const E)) hp
  change (∫ U, rotatedPressure eig (specialRotation U) c ∂μ)≤∫ U, V+D U+E ∂μ at hh
  rw [integral_add (f := fun U => V+D U) (g := fun _ => E)
      ((integrable_const V).add hDi) (integrable_const E),
    integral_add (f := fun _ => V) (g := D) (integrable_const V) hDi] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  dsimp only [E] at hh
  linarith

end InvariantIsing

end

end OAI
