import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalBlockLimit
import OAI.Probability.InvariantIsing.Cavity.CavityCascadeCovarianceLaw
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianJointTest

namespace OAI

/-! Gaussian marking of the physical spectral-group block. The variance
is the projected overlap divided by the group proportion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix

namespace InvariantIsing

def cavityGroupBlockCovariance {m r : ℕ} (q : ℕ) (ρ : Fin m → ℝ)
    (x : SpectralBlock m r) :
    Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ :=
  cavityGroupReplicaCovariance q (fun a i j => (x i j a : ℝ) / ρ a)

lemma continuous_cavityGroupBlockCovariance {m r : ℕ} (q : ℕ) (ρ : Fin m → ℝ) :
    Continuous (cavityGroupBlockCovariance (r := r) q ρ) := by
  apply (continuous_cavityGroupReplicaCovariance q).comp
  fun_prop

lemma cavityGroupBlockCovariance_posSemidef {m r q : ℕ}
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (x : SpectralArray (m + 1)) (hx : SpectralGram x) :
    (cavityGroupBlockCovariance q ρ (cavitySpectralGroupBlock m r x)).PosSemidef :=
  cavitySpectralBlockCovariance_posSemidef ρ hρ x hx

lemma cavity_cascade_group_covariance_posSemidef {m r q : ℕ}
    (n : ℕ) (b a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0) (ha1 : a n ≤ 1)
    (d : SpectralEntry m) (f : Fin m → ℝ → Icc (-1 : ℝ) 1)
    (hf : ∀ j, Continuous (f j)) (hmono : ∀ j, Monotone (fun t => (f j t : ℝ)))
    (h0 : ∀ j, 0 ≤ (f j (a 0) : ℝ)) (hD : ∀ j, (f j (a n) : ℝ) ≤ (d j : ℝ))
    (ρ : Fin m → ℝ) (hρ : ∀ j, 0 ≤ ρ j) :
    ∀ᵐ x ∂(cascadeCompactLaw n b a : Measure JointArray),
      (cavityGroupBlockCovariance q ρ (cavitySynchronizedBlock d f (arrayBlock spinArray r x))).PosSemidef := by
  let z : Icc (-1 : ℝ) 1 := ⟨0, by norm_num⟩
  let d' : SpectralEntry (m + 1) := Fin.lastCases z d
  let f' : Fin (m + 1) → ℝ → Icc (-1 : ℝ) 1 := Fin.lastCases (fun _ => z) f
  have hf' : ∀ j, Continuous (f' j) := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [f', Fin.lastCases_last] using
        (continuous_const : Continuous (fun _ : ℝ => z))
    · simpa only [f', Fin.lastCases_castSucc] using hf i
  have he := cavity_cascade_synchronized_covariance_posSemidef (r := r) (q := q)
    n b a ha ha0 ha1 d' f' hf'
    (by simpa only [f', Fin.lastCases_castSucc] using hmono)
    (by simpa only [f', Fin.lastCases_castSucc] using h0)
    (by simpa only [f', d', Fin.lastCases_castSucc] using hD) ρ hρ
  simpa only [cavitySpectralBlockCovariance, cavityGroupBlockCovariance,
    cavitySynchronizedBlock, f', d', Fin.lastCases_castSucc] using he

theorem cavity_canonical_marked_group_block_tendsto {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (d : Fin (m + 1) → ℝ) (hd0 : ∀ a, 0 ≤ d a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = d a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hoff : ∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      spectralOffWardResidual Q ρ eig a b Φ = 0)
    (hdiag : ∀ a b, spectralDiagonalWardResidual Q ρ eig a b = 0)
    (r q : ℕ) (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q hP hn
    let B := fun x : JointArray => cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p)
      (cavityCanonicalLabel ρ eig hρ hρsum p) (arrayBlock spinArray r x)
    Tendsto (fun n => ∫ x, ∫ z, F (B x, z)
      ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (B x))
      ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 (∫ x, ∫ z, F (cavitySpectralGroupBlock m r x, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (cavitySpectralGroupBlock m r x))
        ∂(Q : Measure (SpectralArray (m + 1))))) := by
  intro p B
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let H : SpectralBlock m r →ᵇ ℝ := G.compContinuous
    ⟨fun x => (x, cavityGroupBlockCovariance q ρ x),
      continuous_id.prodMk (continuous_cavityGroupBlockCovariance q ρ)⟩
  have ht := cavity_canonical_group_block_tendsto Q hgg hG d hd0 hd hE hP hn
    ρ eig hρ hρsum hoff hdiag r H
  change Tendsto (fun n => ∫ x, H (B x)
    ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
    atTop (𝓝 (∫ x, H (cavitySpectralGroupBlock m r x) ∂(Q : Measure (SpectralArray (m + 1))))) at ht
  have hS n : ∀ᵐ x ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray),
      (cavityGroupBlockCovariance q ρ (B x)).PosSemidef :=
    cavity_cascade_group_covariance_posSemidef n (uniformExponent n) (uniformCellAverage p n)
      (uniformCellAverage_monotone p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n)
      (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n 0).1
      (uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n n).2
      (cavityCanonicalDiagonal ρ eig hρ hρsum p) (cavityCanonicalLabel ρ eig hρ hρsum p)
      (continuous_cavityCanonicalLabel ρ eig hρ hρsum p)
      (cavityCanonicalCoordinate_monotone ρ eig hρ hρsum p)
      (fun a => cavityCanonicalCoordinate_nonneg ρ eig hρ hρsum p a _)
      (fun a => cavityCanonicalCoordinate_le_diagonal ρ eig hρ hρsum p a _)
      ρ (fun a => (hρ a).le)
  have heS n : (∫ x, H (B x)
      ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray)) =
      ∫ x, ∫ z, F (B x, z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (B x))
        ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray) :=
    integral_congr_ae ((hS n).mono fun x hx => hExt _ _ hx)
  have heQ : (∫ x, H (cavitySpectralGroupBlock m r x) ∂(Q : Measure (SpectralArray (m + 1)))) =
      ∫ x, ∫ z, F (cavitySpectralGroupBlock m r x, z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (cavitySpectralGroupBlock m r x))
        ∂(Q : Measure (SpectralArray (m + 1))) :=
    integral_congr_ae (hG.mono fun x hx => hExt _ _
      (cavityGroupBlockCovariance_posSemidef ρ (fun a => (hρ a).le) x hx))
  simpa only [heS, heQ] using ht

end InvariantIsing

end

end OAI
