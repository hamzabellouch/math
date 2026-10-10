import OAI.Probability.InvariantIsing.Cavity.CavityCascadeBlockLimit
import OAI.Probability.InvariantIsing.Spectral.SpectralArrayGG

namespace OAI

/-! Synchronized spectral labels are retained in the finite-cascade
approximation of the scalar GG overlap law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavitySynchronizedBlock {m r : ℕ} (d : SpectralEntry m)
    (f : Fin m → ℝ → Icc (-1 : ℝ) 1) (R : Fin r → Fin r → ℝ) : SpectralBlock m r :=
  fun i j a => if i = j then d a else f a (R i j)

lemma continuous_cavitySynchronizedBlock {m r : ℕ} (d : SpectralEntry m)
    (f : Fin m → ℝ → Icc (-1 : ℝ) 1) (hf : ∀ a, Continuous (f a)) :
    Continuous (cavitySynchronizedBlock (r := r) d f) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_pi
  intro a
  by_cases hij : i = j
  · simp only [cavitySynchronizedBlock, ite_eq_left hij]
    exact continuous_const
  · simp only [cavitySynchronizedBlock, ite_eq_right hij]
    exact (hf a).comp (by fun_prop)

theorem cavity_cascade_spectral_block_tendsto {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray m))
    (B : SpectralArray m → RealArray) (hB : Measurable B)
    (hGG : HasGhirlandaGuerra B (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), GramDiagonal 1 (B x))
    (hU : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), IsUltrametricArray (B x))
    (q : ℝ → ℝ) (hq : Monotone q) (hb : ∀ u, q u ∈ Icc (0 : ℝ) 1)
    (hp : (Q : Measure (SpectralArray m)).map (fun x => B x 0 1) = unitUniform.map q)
    (d : SpectralEntry m) (f : Fin m → ℝ → Icc (-1 : ℝ) 1) (hf : ∀ a, Continuous (f a))
    (hdiag : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, x (i, i) a = d a)
    (hsync : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i j, i ≠ j →
      ∀ a, x (i, j) a = f a (B x i j))
    (r : ℕ) (F : SpectralBlock m r →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, F (cavitySynchronizedBlock d f (arrayBlock spinArray r x))
      ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage q n) : Measure JointArray))
      atTop (𝓝 (∫ x, F (spectralBlockView m r x) ∂(Q : Measure (SpectralArray m)))) := by
  let G : (Fin r → Fin r → ℝ) →ᵇ ℝ :=
    F.compContinuous ⟨cavitySynchronizedBlock d f, continuous_cavitySynchronizedBlock d f hf⟩
  have ht := cavity_cascade_spin_block_tendsto (Q : Measure (SpectralArray m)) B hB
    hGG hG hU q hq hb hp r G
  have he : (∫ x, G (arrayBlock B r x) ∂(Q : Measure (SpectralArray m))) =
      ∫ x, F (spectralBlockView m r x) ∂(Q : Measure (SpectralArray m)) := by
    apply integral_congr_ae
    filter_upwards [hdiag, hsync] with x hx hs
    change F (cavitySynchronizedBlock d f (arrayBlock B r x)) = F (spectralBlockView m r x)
    congr 1
    funext i j a
    by_cases hij : i = j
    · subst j
      simpa only [cavitySynchronizedBlock, ite_true, spectralBlockView] using (hx i a).symm
    · simpa only [cavitySynchronizedBlock, ite_eq_right hij, spectralBlockView, arrayBlock] using
        (hs i j (fun he => hij (Fin.ext he)) a).symm
  rw [he] at ht
  exact ht

end InvariantIsing

end

end OAI
