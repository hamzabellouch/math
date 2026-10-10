import OAI.Combinatorics.Progressions.Estimates.NormalizedJetMeasurability
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityRiemann

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem principalTuple_density_l1 {D α I : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] [Fintype I]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L M : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : PrincipalTupleIndex B h → Option α → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α+1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (ρ : (JointBlockParameter B h α → ℝ) → (I → ℝ) → ℝ) (hρ : Measurable (Function.uncurry ρ))
    (R H K : ℝ≥0) (hbound : ∀ x ∈ Metric.closedBall 0 1, ∀ v, ‖ρ x v‖ ≤ H)
    (hlip : ∀ v, LipschitzOnWith K (fun x => ρ x v) (Metric.closedBall 0 1))
    (hs : ∀ x ∈ Metric.closedBall 0 1, ∀ v, (R : ℝ) < ‖v‖ → ρ x v = 0) :
    let E := (2 * (H : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + K) *
      ∑ j, (M j : ℝ)/L j
    let Δ := fun v => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun y => ρ (fun s => (y ⟨s.1, s.2.1, s.2.2.1⟩ s.2.2.2 : ℝ) / L ⟨s.1, s.2.1, s.2.2.1⟩) v) -
      ∫ x, ρ x v ∂jointBooleanSource h
    Integrable Δ ∧ (∫ v, |Δ v|) ≤ E * (2 * (R : ℝ))^Fintype.card I := by
  dsimp only
  let p := FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
    (m j) (r j) (hm j) (hmM j) (hsize j))
  let T : (∀ j, IntegerScalarCubeBox α (L j)) → (JointBlockParameter B h α → ℝ) := fun y s =>
    (y ⟨s.1, s.2.1, s.2.2.1⟩ s.2.2.2 : ℝ) / L ⟨s.1, s.2.1, s.2.2.1⟩
  have hT (y) : T y ∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact principalTuple_normalized_norm_le B h hL y
  have he (v) := principalTuple_residue_riemann_on_box B h L M hL m r hm hmM hsize hsmall
    (fun x => ρ x v) (hlip v) H.coe_nonneg (fun x hx => hbound x hx v)
  exact finiteSource_density_l1_of_uniform_bound p T (jointBooleanSource h) (Metric.closedBall 0 1)
    hT (jointBooleanSource_ae_closedBall B h) ρ R.coe_nonneg hs
    (finiteSource_density_error_measurable p T (jointBooleanSource h) ρ hρ) he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem normalizedJetDensity_principalTuple_riemann {Z K D α I J N : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1) (rows : I → Finset α)
    {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (R H Kf S : ℝ≥0) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : LipschitzWith Kf f) (hg : Continuous g)
    (hfs : ∀ u, (R : ℝ) < ‖u‖ → f u = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hfb : ∀ u, ‖f u‖ ≤ H) (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (L M : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : PrincipalTupleIndex B h → Option α → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α+1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (v : I → ℝ) :
    let ρ := fun x => normalizedJetDensity A F e input z rows f g x v
    let Lip := pivotKernelLip J A R Kf *
      (Fintype.card N * polynomialBoxLip (Fintype.card (JointBlockParameter B h α)) degree (normalizedJetMass α degree)) * S
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun y => ρ (fun s => (y ⟨s.1, s.2.1, s.2.2.1⟩ s.2.2.2 : ℝ) / L ⟨s.1, s.2.1, s.2.2.1⟩)) -
      ∫ x, ρ x ∂jointBooleanSource h| ≤
      (2 * (pivotKernelCap J A R H : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + Lip) *
        ∑ j, (M j : ℝ)/L j := by
  dsimp only
  have hb := normalizedJetDensity_bounds A F e input z hz rows hd R H Kf S hf hg hfs hgs hfb hg0 hgmass v
  exact principalTuple_residue_riemann_on_box B h L M hL m r hm hmM hsize hsmall
    (fun x => normalizedJetDensity A F e input z rows f g x v) hb.2
    (pivotKernelCap J A R H).coe_nonneg (fun x _ => hb.1 x)

theorem normalizedJetDensity_retained_riemann {Ω Z K D α I J N : Type*} [MeasurableSpace Ω]
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (R H Kf S : ℝ≥0) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : LipschitzWith Kf f) (hg : Continuous g)
    (hfs : ∀ u, (R : ℝ) < ‖u‖ → f u = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hfb : ∀ u, ‖f u‖ ≤ H) (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (L M : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : PrincipalTupleIndex B h → Option α → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α+1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Ω → Z → ℝ)
    (hz : ∀ j, Measurable (fun u => z u j)) (hbox : ∀ᵐ u ∂μ, ∀ j, |z u j| ≤ 1)
    (v : Ω → I → ℝ) (hv : ∀ i, Measurable (fun u => v u i)) :
    let ρ := fun u x => normalizedJetDensity A F e input (z u) rows f g x (v u)
    let Lip := pivotKernelLip J A R Kf *
      (Fintype.card N * polynomialBoxLip (Fintype.card (JointBlockParameter B h α)) degree (normalizedJetMass α degree)) * S
    |(∫ u, (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun y => ρ u (fun s => (y ⟨s.1, s.2.1, s.2.2.1⟩ s.2.2.2 : ℝ) / L ⟨s.1, s.2.1, s.2.2.1⟩)) ∂μ) -
      ∫ x, ρ x.1 x.2 ∂μ.prod (jointBooleanSource h)| ≤
      (2 * (pivotKernelCap J A R H : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + Lip) *
        ∑ j, (M j : ℝ)/L j := by
  dsimp only
  have hmeas := normalizedJetDensity_measurable_comp (Ω := Ω × (JointBlockParameter B h α → ℝ))
    A F e input rows hf.continuous hg hfs hgs
    (fun q => z q.1) (fun j => (hz j).comp measurable_fst)
    (fun q => q.2) (fun j => (measurable_pi_apply j).comp measurable_snd)
    (fun q => v q.1) (fun i => (hv i).comp measurable_fst)
  apply finiteSource_product_comparison _ _ μ (jointBooleanSource h)
    (fun q => normalizedJetDensity A F e input (z q.1) rows f g q.2 (v q.1)) hmeas
    (fun q => splitPivotDensity_norm_le_cap A F _ R H S hf.continuous hg hfs hgs hfb hg0 hgmass (v q.1))
  filter_upwards [hbox] with u hu
  exact normalizedJetDensity_principalTuple_riemann B h A F e input (z u) hu rows hd R H Kf S
    hf hg hfs hgs hfb hg0 hgmass L M hL m r hm hmM hsize hsmall (v u)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem normalizedJetDensity_principalTuple_l1 {Z K D α I J N : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1) (rows : I → Finset α)
    {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (R H Kf S : ℝ≥0) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : LipschitzWith Kf f) (hg : Continuous g)
    (hfs : ∀ u, (R : ℝ) < ‖u‖ → f u = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hfb : ∀ u, ‖f u‖ ≤ H) (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (L M : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : PrincipalTupleIndex B h → Option α → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α+1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ)/L j) < volume.real (scalarCubeDomain α)) :
    let ρ := normalizedJetDensity A F e input z rows f g
    let Lip := pivotKernelLip J A R Kf *
      (Fintype.card N * polynomialBoxLip (Fintype.card (JointBlockParameter B h α)) degree (normalizedJetMass α degree)) * S
    let E := (2 * (pivotKernelCap J A R H : ℝ) * scalarCubeGridBoundaryConstant α /
      volume.real (scalarCubeDomain α) + Lip) * ∑ j, (M j : ℝ)/L j
    let Δ := fun v => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun y => ρ (fun s => (y ⟨s.1, s.2.1, s.2.2.1⟩ s.2.2.2 : ℝ) / L ⟨s.1, s.2.1, s.2.2.1⟩) v) -
      ∫ x, ρ x v ∂jointBooleanSource h
    Integrable Δ ∧ (∫ v, |Δ v|) ≤ E * (2 * (normalizedJetOutputRadius α N A F degree R S : ℝ))^Fintype.card I := by
  dsimp only
  have hb (v) := normalizedJetDensity_bounds A F e input z hz rows hd R H Kf S hf hg hfs hgs hfb hg0 hgmass v
  exact principalTuple_density_l1 B h L M hL m r hm hmM hsize hsmall
    (normalizedJetDensity A F e input z rows f g)
    (normalizedJetDensity_measurable A F e input z rows hf.continuous hg hfs hgs)
    (normalizedJetOutputRadius α N A F degree R S) (pivotKernelCap J A R H) _
    (fun x _ v => (hb v).1 x) (fun v => (hb v).2)
    (fun x hx v hv => normalizedJetDensity_zero_outside A F e input z hz rows hd R S hf.continuous hg hfs hgs
      x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx) v hv)

end Erdos3

end

end OAI
