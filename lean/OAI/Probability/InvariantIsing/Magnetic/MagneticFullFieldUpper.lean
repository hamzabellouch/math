import OAI.Probability.InvariantIsing.Magnetic.MagneticRoundedFieldUpper
import OAI.Probability.InvariantIsing.Magnetic.MagneticCoverDistance
import OAI.Probability.InvariantIsing.Fields.SpinCoverParameters
import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupRounding
import OAI.Probability.InvariantIsing.Magnetic.MagneticFiniteTrial
import OAI.Probability.InvariantIsing.Core.FiniteVariationalBounds
import OAI.Probability.InvariantIsing.Fields.SpinGroupFieldPressure
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPressureFluctuation

namespace OAI

/-! The finite-spectrum pressure upper bound after taking the path infimum,
under Haar and Gaussian concentration hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_fullField_pressure_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : ∀ k, Fin (N k) → A)
    (γ b : A → ℝ) (hγ : ∀ a, 0<γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun k a => (spinGroupSize (group k) a:ℝ)/(N k:ℝ)) atTop (𝓝 γ))
    : ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop,
      (∫ U, rotatedPressure (eig k) (specialRotation U) (fun i => b (group k i)) ∂μ k) ≤
        (finiteMagneticFunctional (finiteR ρ lam hρpos hρsum) γ b).toReal+ε := by
  classical
  intro ε hε
  let V := (finiteMagneticFunctional (finiteR ρ lam hρpos hρsum) γ b).toReal
  let C := ∑ a, |b a|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb a : |b a|≤C := Finset.single_le_sum (f := fun a => |b a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  obtain ⟨B,hB,hcoverBound⟩ := haar_finite_cover_mean_pressure_upper hhaar
  obtain ⟨δ,t,hδ,ht,hsmall⟩ := exists_small_spinCover_error K C (show 0<ε/3 by positivity)
  obtain ⟨Q,hQ,hnet⟩ := finite_rational_magnetization_cover (A := A) hδ
  let S := fun k (q : RationalMagnetization A) => spinGroupSlice (group k)
    (fun a => magneticRoundedCount (spinGroupSize (group k) a) (q.val a:ℝ))
  have hS k q : (S k q).Nonempty := spinGroupSlice_nonempty (group k) _
    (fun a => magneticRoundedCount_le _ (q.property a).le)
  let d := fun k => ⌈δ*N k+Fintype.card A⌉₊
  have hproj k := magnetic_grid_projection (group k) hδ Q hnet
  choose f hf hd using hproj
  have hmeans : ∀ᶠ k in atTop, ∀ q∈Q,
      (∫ U, restrictedRotatedPressure (S k q) (eig k) (specialRotation U)
        (fun i => b (group k i)) ∂μ k)≤V+ε/3 := by
    have hh (q : Q) := finiteSpectrum_magneticRoundedFieldPressure_upper hhaar hgauss
      N hN hNlim m μ hμinv eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ
      group γ b hγ hγsum hgroup q.val (ε/3) (by positivity)
    have hh' := (Filter.eventually_all).mpr hh
    filter_upwards [hh'] with k hk q hq
    exact hk ⟨q,hq⟩
  have herr := spinCover_error_tendsto N d (fun k => by have := hN k; omega)
    hNlim Q.card B K C t δ
    (magnetic_cover_distance_tendsto N (fun k => by have := hN k; omega) hNlim (Fintype.card A) hδ)
  have hevent := herr.eventually (Iio_mem_nhds (show
    2*K*Real.sqrt δ+(2*C+t)*δ+Real.log (1+Real.exp (-t)) <
      (2*K*Real.sqrt δ+(2*C+t)*δ+Real.log (1+Real.exp (-t)))+ε/3 by linarith))
  filter_upwards [hmeans,hevent] with k hk he
  have hup := hcoverBound (N k) (hN k) (μ k) inferInstance (hμinv k)
    (RationalMagnetization A) Q hQ (S k) (fun q _ => hS k q) (f k) (d k) (hf k) (hd k)
    (eig k) (fun i => b (group k i)) K C t (V+ε/3) hK hC ht (heig k)
    (fun i => hb (group k i)) hk
  change (∫ U, rotatedPressure (eig k) (specialRotation U) (fun i => b (group k i)) ∂μ k)≤V+ε
  dsimp only [d] at he hup
  linarith

end InvariantIsing

end

end OAI
