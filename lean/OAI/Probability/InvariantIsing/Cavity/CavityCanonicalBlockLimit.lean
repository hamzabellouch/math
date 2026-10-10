import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalSynchronization
import OAI.Probability.InvariantIsing.Cavity.CavityCascadeSpectralLimit

namespace OAI

/-! Canonical spectral-group blocks of finite cascades converge to the
actual Ward-identified spectral array. The auxiliary tree coordinate is
not needed by these physical group observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityCanonicalDiagonal {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) : SpectralEntry m := fun a =>
  ⟨spectralGroupDiagonal ρ eig hρ hρsum p a,
    ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (spectralGroupDiagonal_nonneg ρ eig hρ hρsum p a),
      spectralGroupDiagonal_le_one ρ eig hρ hρsum p a⟩⟩

def cavitySpectralGroupBlock (m r : ℕ) (x : SpectralArray (m + 1)) : SpectralBlock m r :=
  fun i j a => x (i,j) a.castSucc

lemma continuous_cavitySpectralGroupBlock (m r : ℕ) :
    Continuous (cavitySpectralGroupBlock m r) := by
  unfold cavitySpectralGroupBlock
  fun_prop

lemma cavity_spectral_spin_gram {m : ℕ} {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), GramDiagonal 1 (spectralSpinArray x) := by
  have hs : (∑ a, spectralSpinWeight m a * q a) = 1 := by
    simpa only [Fin.sum_univ_castSucc, spectralSpinWeight, Fin.lastCases_castSucc,
      Fin.lastCases_last, one_mul, zero_mul, add_zero] using spectralPartition_diagonal_sum hP q hd
  filter_upwards [hG, hd] with x hx hdx
  simpa only [hs, spectralLinearArray_spinWeight] using
    spectralGram_linear hx q (spectralSpinWeight m) hdx (spectralSpinWeight_nonneg m)

theorem cavity_canonical_group_block_tendsto {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hoff : ∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      spectralOffWardResidual Q ρ eig a b Φ = 0)
    (hdiag : ∀ a b, spectralDiagonalWardResidual Q ρ eig a b = 0)
    (r : ℕ) (F : SpectralBlock m r →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q hP hn
    Tendsto (fun n => ∫ x, F (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hρsum p)
      (cavityCanonicalLabel ρ eig hρ hρsum p) (arrayBlock spinArray r x))
      ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage p n) : Measure JointArray))
      atTop (𝓝 (∫ x, F (cavitySpectralGroupBlock m r x) ∂(Q : Measure (SpectralArray (m + 1))))) := by
  intro p
  obtain ⟨hdq, hsync⟩ := cavity_canonical_group_synchronization hgg hG q hq hd hE hP hn
    ρ eig hρ hρsum hoff hdiag
  let d := cavityCanonicalDiagonal ρ eig hρ hρsum p
  let f := cavityCanonicalLabel ρ eig hρ hρsum p
  let G : (Fin r → Fin r → ℝ) →ᵇ ℝ := F.compContinuous
    ⟨cavitySynchronizedBlock d f, continuous_cavitySynchronizedBlock d f
      (continuous_cavityCanonicalLabel ρ eig hρ hρsum p)⟩
  have hGG : HasGhirlandaGuerra spectralSpinArray (Q : Measure (SpectralArray (m + 1))) := by
    have hh : HasGhirlandaGuerra (spectralLinearArray (spectralSpinWeight m))
        (Q : Measure (SpectralArray (m + 1))) :=
      hgg.real_map (continuous_spectralLinearEntry (spectralSpinWeight m)).measurable
    have he : spectralLinearArray (spectralSpinWeight m) = (spectralSpinArray (m := m)) :=
      funext spectralLinearArray_spinWeight
    rw [he] at hh
    exact hh
  have hU : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), IsUltrametricArray (spectralSpinArray x) := by
    simpa only [spectralLinearArray_spinWeight] using spectralGG_linear_ultrametric hgg hG q hq hd
      (fun e => hE e e.injective) (spectralSpinWeight m) (spectralSpinWeight_nonneg m)
  have hlaw : (Q : Measure (SpectralArray (m + 1))).map (fun x => spectralSpinArray x 0 1) =
      unitUniform.map p := (spectralSpinQuantilePath_law Q hP hn).symm
  have ht := cavity_cascade_spin_block_tendsto (Q : Measure (SpectralArray (m + 1)))
    spectralSpinArray (continuous_spectralSpinArray m).measurable hGG
    (cavity_spectral_spin_gram hG q hd hP) hU p p.monotone
    (fun s => ⟨p.nonneg s, p.le_one s⟩) hlaw r G
  have he : (∫ x, G (arrayBlock spectralSpinArray r x) ∂(Q : Measure (SpectralArray (m + 1)))) =
      ∫ x, F (cavitySpectralGroupBlock m r x) ∂(Q : Measure (SpectralArray (m + 1))) := by
    apply integral_congr_ae
    filter_upwards [hd, hsync] with x hdx hsx
    change F (cavitySynchronizedBlock d f (arrayBlock spectralSpinArray r x)) =
      F (cavitySpectralGroupBlock m r x)
    congr 1
    funext i j a
    apply Subtype.ext
    by_cases hij : i = j
    · subst j
      simp only [cavitySynchronizedBlock, ite_true, cavitySpectralGroupBlock]
      exact ((hdx i a.castSucc).trans (hdq a)).symm
    · simp only [cavitySynchronizedBlock, ite_eq_right hij, cavitySpectralGroupBlock, arrayBlock]
      exact (hsx i j (fun he => hij (Fin.ext he)) a).symm
  rw [he] at ht
  exact ht

end InvariantIsing

end

end OAI
