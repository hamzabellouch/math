import OAI.Probability.BenjaminiSchramm.GhostDifferentialAssembly
import OAI.Probability.BenjaminiSchramm.ModularSchur

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ghostKernel_mono_field {h k x : ℝ} (hhk : h ≤ k) (hx : 0 ≤ x) :
    ghostKernel h x ≤ ghostKernel k x := by
  unfold ghostKernel
  apply sub_le_sub_left
  exact Real.exp_le_exp.mpr (by nlinarith)

lemma ghostMagnetization_le_derivative_add_twoGhost_same
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {h : ℝ} (hh : 0 < h) :
    ghostMagnetization μ X h ≤ h*ghostMagnetizationDerivative μ X h +
      2*∫ ω, ghostKernel h (X ω)^2 ∂μ := by
  apply (ghostMagnetization_le_derivative_add_two_ghost μ X hX hX0 hh).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply integral_mono
    (integrable_ghostKernel_sq μ X hX hX0 (by positivity : 0 ≤ h/2))
    (integrable_ghostKernel_sq μ X hX hX0 hh.le)
  intro ω
  exact pow_le_pow_left₀ (ghostKernel_nonneg (by positivity) (hX0 ω))
    (ghostKernel_mono_field (by linarith) (hX0 ω)) 2

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem root_quarterGhost_differential
    (hinj : Function.Injective G)
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (hq : (criticalModel G).QuasiTransitive)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (hmoment : ∀ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
      (criticalModel G).quarterThreeQuarterMoment p x < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      (∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostMagnetization p x (t^4)) ≤
      C*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostMagnetization p x (t^4))^2 +
      t^4*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostDerivative p x (t^4)) +
      C*t^6*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostDerivative p x (t^4)) := by
  let H := criticalModel G
  let O := (H.orbitRepresentatives hq).roots
  obtain ⟨K,_,hK⟩ := H.uniform_quarterGhost_moment_bound hq p hmoment
  obtain ⟨D,_,hD⟩ := H.uniform_incident_bound hq
  obtain ⟨B,hB⟩ := H.uniform_ball_bound hq 1
  obtain ⟨A,hA,hbound⟩ := root_twoGhost_bound G hinj hc hl hq p hp hfin K hK D B hD hB
  let C := max 2 (2*A)
  have hC2 : 2 ≤ C := le_max_left _ _
  have hCA : 2*A ≤ C := le_max_right _ _
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro t ht _
  let h : ℝ≥0 := ⟨t^4,by positivity⟩
  have hh : (0 : ℝ) < h := by change 0 < t^4; exact pow_pos ht 4
  let M := ∑ x ∈ O, H.quarterGhostMagnetization p x (t^4)
  let Derv := ∑ x ∈ O, H.quarterGhostDerivative p x (t^4)
  have hDnonneg (x : V) : 0 ≤ H.quarterGhostDerivative p x (t^4) :=
    integral_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hDerv : 0 ≤ Derv := Finset.sum_nonneg fun x _ => hDnonneg x
  have hdouble : (∑ x ∈ O, H.quarterGhostDerivative p x (2*h)) ≤ Derv := by
    apply Finset.sum_le_sum
    intro x _
    unfold CriticalPercolation.BondGraph.quarterGhostDerivative ghostMagnetizationDerivative
    apply integral_mono
      (hasDerivAt_ghostMagnetization (H.law p) _ (H.measurable_quarterTiltedMass x).ennreal_toReal
        (fun _ => ENNReal.toReal_nonneg) (by positivity : (0 : ℝ) < 2*h)).1
      (hasDerivAt_ghostMagnetization (H.law p) _ (H.measurable_quarterTiltedMass x).ennreal_toReal
        (fun _ => ENNReal.toReal_nonneg) (by positivity : (0 : ℝ) < t^4)).1
    intro ω
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    apply Real.exp_le_exp.mpr
    change -(2*t^4)*(H.quarterTiltedMass ω x).toReal ≤ -(t^4)*(H.quarterTiltedMass ω x).toReal
    exact mul_le_mul_of_nonneg_right (by nlinarith [pow_nonneg ht.le 4]) ENNReal.toReal_nonneg
  have hpow : (h : ℝ)^(3/2 : ℝ) = t^6 := by
    change (t^4)^(3/2 : ℝ) = t^6
    rw [←Real.rpow_natCast_mul ht.le]
    norm_num
  have hsq := hbound h hh
  rw [hpow] at hsq
  have herror := mul_le_mul_of_nonneg_left hdouble (by positivity : 0 ≤ A*t^6)
  have hbase : M ≤ t^4*Derv + 2*(∑ x ∈ O,
      ∫ ω, ghostKernel h (H.quarterTiltedMass ω x).toReal^2 ∂law p) := by
    calc
      _ ≤ ∑ x ∈ O, (t^4*H.quarterGhostDerivative p x (t^4) +
          2*∫ ω, ghostKernel h (H.quarterTiltedMass ω x).toReal^2 ∂law p) := by
        apply Finset.sum_le_sum
        intro x _
        exact ghostMagnetization_le_derivative_add_twoGhost_same (H.law p)
          (fun ω => (H.quarterTiltedMass ω x).toReal) (H.measurable_quarterTiltedMass x).ennreal_toReal
          (fun _ => ENNReal.toReal_nonneg) (by positivity)
      _ = _ := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  have h1 : 2*M^2 ≤ C*M^2 := mul_le_mul_of_nonneg_right hC2 (sq_nonneg M)
  have h2 : 2*A*t^6*Derv ≤ C*t^6*Derv :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCA (by positivity)) hDerv
  change M ≤ C*M^2+t^4*Derv+C*t^6*Derv
  change (∑ x ∈ O, ∫ ω, ghostKernel h (H.quarterTiltedMass ω x).toReal^2 ∂law p) ≤
    M^2+A*t^6*(∑ x ∈ O, H.quarterGhostDerivative p x (2*h)) at hsq
  change A*t^6*(∑ x ∈ O, H.quarterGhostDerivative p x (2*h)) ≤ A*t^6*Derv at herror
  nlinarith

theorem finite_quarterSusceptibility_of_moments
    (hinj : Function.Injective G)
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (hq : (criticalModel G).QuasiTransitive)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (hmoment : ∀ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
      (criticalModel G).quarterThreeQuarterMoment p x < ⊤) :
    ∀ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
      (criticalModel G).tiltedSusceptibility p (1/4) x < ⊤ := by
  let H := criticalModel G
  let O := (H.orbitRepresentatives hq).roots
  let ι := ↥O
  let : MeasurableSpace ι := ⊤
  let root : ι → V := fun i => i.1
  obtain ⟨C,hC,hdiff⟩ := root_quarterGhost_differential G hinj hc hl hq p hp hfin hmoment
  have hM (h : ℝ) (hh : 0 ≤ h) : H.rootQuarterGhostMagnetization root p h =
      ∑ x ∈ O, H.quarterGhostMagnetization p x h := by
    rw [H.rootQuarterGhostMagnetization_eq_sum root p hh]
    exact Finset.sum_coe_sort O (fun x => H.quarterGhostMagnetization p x h)
  have hD (h : ℝ) (hh : 0 < h) : H.rootQuarterGhostDerivative root p h =
      ∑ x ∈ O, H.quarterGhostDerivative p x h := by
    rw [H.rootQuarterGhostDerivative_eq_sum root p hh]
    exact Finset.sum_coe_sort O (fun x => H.quarterGhostDerivative p x h)
  have hresult := H.root_quarterTiltedSusceptibility_lt_top_of_moment_and_differential root p
    (fun i => hmoment i.1 i.2) C hC (by
      intro t ht ht1
      rw [hM _ (by positivity),hD _ (by positivity)]
      exact hdiff t ht ht1)
  intro x hx
  exact hresult ⟨x,hx⟩

end Percolation.BenjaminiSchramm

end

end OAI
