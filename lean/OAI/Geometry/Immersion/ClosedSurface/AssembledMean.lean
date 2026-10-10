import OAI.Geometry.Immersion.ClosedSurface.LocalMean
import OAI.Geometry.Immersion.ClosedSurface.MeanSupport

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean Set



def extendedMeanTerm (U : Set Base) (δ s : ℝ) (F : RField 4) (ψ : Base → ℝ)
    (Q : Base → Tensor →L[ℝ] ℝ) (χ e : Base → Base) (q : ℕ)
    (η : ℝ) (A : Base → Tensor) : Base → Tensor :=
  U.indicator (meanTerm δ s F ψ Q χ e q η A)

lemma meanTerm_vanishes {U K : Set Base} {χ : Base → Base} {ψ : Base → ℝ}
    (hsp : ∀ p ∈ U, χ p ∈ tsupport ψ → p ∈ K)
    (δ s : ℝ) (F : RField 4) (Q : Base → Tensor →L[ℝ] ℝ) (e : Base → Base)
    (q : ℕ) (η : ℝ) (A : Base → Tensor) :
    ∀ p ∈ U, p ∉ K → meanTerm δ s F ψ Q χ e q η A p = 0 := by
  intro p hp hn
  have hz : χ p ∉ tsupport (meanTensor δ (η * s) F (phaseAmplitude ψ (coefficient Q e A)) q) :=
    fun hh => hn (hsp p hp (meanTensor_tsupport δ (η * s) F ψ (coefficient Q e A) q hh))
  unfold meanTerm
  rw [image_eq_zero_of_notMem_tsupport hz, map_zero]




theorem actual_extended_mean_bounds {U V S : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
    {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}
    (h : LocalBounds U V s r ρ R reference F ψ Q χ e)
    (d : Budgets U V s F ψ Q χ e) (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ)
    (hS : IsClosed S) (hSU : S ⊆ U) (hsp : ∀ p ∈ U, χ p ∈ tsupport ψ → p ∈ S)
    {δ : ℝ} (hδ : 0 < δ) (q : ℕ) :
    ∃ B K : ℕ → ℝ → ℝ, MeanBounds univ s reference r (q + 2)
      (extendedMeanTerm U δ s F ψ Q χ e q) B K := by
  classical
  obtain ⟨B, K, hT⟩ := actual_local_mean_bounds h d hs hs1 hρ hδ q
  have hb {A : Base → Tensor} (hA : InTrialBall univ reference r A) :
      InTrialBall U reference r A := fun p hp => hA p (mem_univ p)
  have hz := meanTerm_vanishes hsp δ s F Q e q
  refine ⟨B, K, ?_⟩
  constructor
  · exact hT.B_pos
  · exact hT.K_pos
  · intro η hη hη1 A hA hball
    exact (contDiff_indicator_of_support h.openU hS hSU
      (hT.smooth η hη hη1 A (hA.mono (subset_univ U)) (hb hball)) (hz η A)).contDiffOn
  · intro η hη hη1 m C A hC hA hball hAB
    have hm := hT.value η hη hη1 m C A hC (hA.mono (subset_univ U)) (hb hball)
      (hAB.restrict_open h.openU)
    exact hm.indicator_of_support h.openU hS hSU
      (mul_nonneg hη.le (le_trans zero_le_one (hT.B_pos m C hC))) (hz η A)
  · intro η hη hη1 m C D A A' hC hD hA hA' hball hball' hbA hbA' hbD
    have hm := hT.difference η hη hη1 m C D A A' hC hD
      (hA.mono (subset_univ U)) (hA'.mono (subset_univ U)) (hb hball) (hb hball')
      (hbA.restrict_open h.openU) (hbA'.restrict_open h.openU) (hbD.restrict_open h.openU)
    have hzero : ∀ p ∈ U, p ∉ S →
        (meanTerm δ s F ψ Q χ e q η A - meanTerm δ s F ψ Q χ e q η A') p = 0 := by
      intro p hp hn
      simp only [Pi.sub_apply, hz η A p hp hn, hz η A' p hp hn, sub_self]
    have hh := hm.indicator_of_support h.openU hS hSU
      (mul_nonneg (mul_nonneg (le_trans zero_le_one (hT.K_pos m C hC)) hη.le) hD) hzero
    apply hh.congr
    intro p hp
    by_cases hpU : p ∈ U
    · simp [extendedMeanTerm, indicator_of_mem hpU]
    · simp [extendedMeanTerm, indicator_of_notMem hpU]

end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean Set




def assembledMean {ι : Type*} (a : Finset ι) (U : ι → Set Base) (δ s : ℝ)
    (F : ι → RField 4) (ψ : ι → Base → ℝ) (Q : ι → Base → Tensor →L[ℝ] ℝ)
    (χ e : ι → Base → Base) (q : ℕ) (η : ℝ) (A : Base → Tensor) : Base → Tensor :=
  fun p => ∑ i ∈ a, extendedMeanTerm (U i) δ s (F i) (ψ i) (Q i) (χ i) (e i) q η A p




theorem assembledMean_bounds {ι : Type*} (a : Finset ι)
    {U V S : ι → Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
    {F : ι → RField 4} {ψ : ι → Base → ℝ} {Q : ι → Base → Tensor →L[ℝ] ℝ}
    {χ e : ι → Base → Base}
    (h : ∀ i ∈ a, LocalBounds (U i) (V i) s r ρ R reference (F i) (ψ i) (Q i) (χ i) (e i))
    (d : ∀ i ∈ a, Budgets (U i) (V i) s (F i) (ψ i) (Q i) (χ i) (e i))
    (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ)
    (hS : ∀ i ∈ a, IsClosed (S i)) (hSU : ∀ i ∈ a, S i ⊆ U i)
    (hsp : ∀ i ∈ a, ∀ p ∈ U i, χ i p ∈ tsupport (ψ i) → p ∈ S i)
    {δ : ℝ} (hδ : 0 < δ) (q : ℕ) :
    ∃ B K : ℕ → ℝ → ℝ, MeanBounds univ s reference r (q + 2)
      (assembledMean a U δ s F ψ Q χ e q) B K := by
  classical
  have he (i : {i // i ∈ a}) := actual_extended_mean_bounds (h i i.2) (d i i.2)
    hs hs1 hρ (hS i i.2) (hSU i i.2) (hsp i i.2) hδ q
  choose B K hT using he
  let B' : ι → ℕ → ℝ → ℝ := fun i => if hi : i ∈ a then B ⟨i, hi⟩ else fun _ _ => 1
  let K' : ι → ℕ → ℝ → ℝ := fun i => if hi : i ∈ a then K ⟨i, hi⟩ else fun _ _ => 1
  refine ⟨fun m C => 1 + ∑ i ∈ a, B' i m C, fun m C => 1 + ∑ i ∈ a, K' i m C, ?_⟩
  apply MeanBounds.finset_sum uniqueDiffOn_univ hs.le a
    (fun i => extendedMeanTerm (U i) δ s (F i) (ψ i) (Q i) (χ i) (e i) q) B' K'
  intro i hi
  simpa only [B', K', dite_eq_left hi] using hT ⟨i, hi⟩




theorem assembledMean_finite_adjustment {ι : Type*} (a : Finset ι)
    {U V S : ι → Set Base} {s r₀ r₁ ρ R : ℝ} {reference H : Base → Tensor}
    {F : ι → RField 4} {ψ : ι → Base → ℝ} {Q : ι → Base → Tensor →L[ℝ] ℝ}
    {χ e : ι → Base → Base}
    (h : ∀ i ∈ a, LocalBounds (U i) (V i) s r₁ ρ R reference (F i) (ψ i) (Q i) (χ i) (e i))
    (d : ∀ i ∈ a, Budgets (U i) (V i) s (F i) (ψ i) (Q i) (χ i) (e i))
    (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ) (hgap : r₀ < r₁)
    (hS : ∀ i ∈ a, IsClosed (S i)) (hSU : ∀ i ∈ a, S i ⊆ U i)
    (hsp : ∀ i ∈ a, ∀ p ∈ U i, χ i p ∈ tsupport (ψ i) → p ∈ S i)
    {δ : ℝ} (hδ : 0 < δ) (q n : ℕ) {C : ℕ → ℝ}
    (hC : ∀ m, 1 ≤ C m) (hH : ContDiff ℝ ∞ H)
    (hH0 : ∀ p, ‖H p - reference p‖ ≤ r₀)
    (hbH : ∀ m, WeightedBound univ s m (C m) H) :
    ∃ B K : ℕ → ℝ → ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ η, 0 < η → η ≤ η₀ → ∀ j ≤ n,
        ContDiff ℝ ∞ (trial H (assembledMean a U δ s F ψ Q χ e q) η j) ∧
        InTrialBall univ reference r₁ (trial H (assembledMean a U δ s F ψ Q χ e q) η j) ∧
        (∀ m, WeightedBound univ s m (sizeBound (q + 2) C B j m)
          (trial H (assembledMean a U δ s F ψ Q χ e q) η j)) ∧
        (∀ m, WeightedBound univ s m (differenceBound (q + 2) C B K j m * η ^ (j + 1))
          (trial H (assembledMean a U δ s F ψ Q χ e q) η j +
            assembledMean a U δ s F ψ Q χ e q η
              (trial H (assembledMean a U δ s F ψ Q χ e q) η j) - H)) := by
  obtain ⟨B, K, hT⟩ := assembledMean_bounds a h d hs hs1 hρ hS hSU hsp hδ q
  obtain ⟨η₀, hη₀, hη₁, htrial⟩ := finite_substitution uniqueDiffOn_univ hs.le hgap hT hC
    hH.contDiffOn (fun p _ => hH0 p) hbH n
  refine ⟨B, K, η₀, hη₀, hη₁, ?_⟩
  intro η hη hsmall j hj
  obtain ⟨hsmooth, hball, hsize, hrest⟩ := htrial η hη hsmall j hj
  exact ⟨contDiffOn_univ.mp hsmooth, hball, hsize, hrest⟩

end ClosedSurfaceR4.PhaseMean

end

end OAI
