import OAI.Geometry.Immersion.ClosedSurface.LocalMean
import OAI.Geometry.Immersion.ClosedSurface.ForcedSolve
import OAI.Geometry.Immersion.ClosedSurface.FreeSolve

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RootMean Set Filter
open ClosedSurfaceR4.QuadraticMean (displacement sumDisplacement)


structure SupportedFreeChart (F : RField 4) (φ ψ : Base → ℝ) (S : Set Base) where
  U : Set Base
  V : Set Base
  χ : Base → Base
  e : Base → Base
  openU : IsOpen U
  closedS : IsClosed S
  supportU : S ⊆ U
  smoothFe : ContDiff ℝ ∞ (F ∘ e)
  domain : RealModeDomain (F ∘ e) V
  smoothχ : ContDiffOn ℝ ∞ χ U
  maps : MapsTo χ U V
  inverse : EqOn (e ∘ χ) id U
  phase : ∀ p ∈ U, (χ p).1 = φ p
  cutoff : ∀ p ∈ U, χ p ∈ tsupport ψ → p ∈ S

def SupportedFreeChart.amplitude {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    (c : SupportedFreeChart F φ ψ S) (u : Base → ℝ) (δ τ : ℝ) (q : ℕ) : Field 4 :=
  c.U.indicator (chartFreeAmplitude δ τ (F ∘ c.e) (phaseAmplitude ψ u) q c.χ)



structure FreeBudget {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    (c : SupportedFreeChart F φ ψ S) (u : Base → ℝ) (τ s : ℝ) (q m : ℕ) where
  K : ℝ
  C : ℝ
  N : ℝ
  J : ℝ
  D : ℝ
  nonnegK : 0 ≤ K
  nonnegC : 0 ≤ C
  nonnegN : 0 ≤ N
  oneLEJ : 1 ≤ J
  nonnegD : 0 ≤ D
  smoothAmplitude : ContDiffOn ℝ ∞ (phaseAmplitude ψ u) c.V
  coefficients : ReconstructionCoefficientBound (fun p => complexify ((F ∘ c.e) p))
    c.V s (m + q + 1) K
  amplitude : WeightedBound c.V s (m + q + 1) C (phaseAmplitude ψ u)
  normal : WeightedBound c.V s (m + q + 1) N (freeNormal (F ∘ c.e))
  coordinate : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ c.U,
    ‖iteratedFDerivWithin ℝ j c.χ c.U p‖ ≤ J
  coordinateDerivative : ∀ v, ‖v‖ ≤ 1 → WeightedBound c.U τ m D (coordDeriv v c.χ)

def FreeBudget.seedConstant {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    {c : SupportedFreeChart F φ ψ S} {u : Base → ℝ} {τ s : ℝ} {q m : ℕ}
    (b : FreeBudget c u τ s q m) : ℝ := Real.sqrt 2 * 2 ^ (m + q + 1) * b.C * b.N

def FreeBudget.size {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    {c : SupportedFreeChart F φ ψ S} {u : Base → ℝ} {τ s : ℝ} {q m : ℕ}
    (b : FreeBudget c u τ s q m) : ℝ :=
  (m.factorial : ℝ) * (2 ^ m * ((1 + freeModeConstant 4 m b.K q) * b.seedConstant)) * b.J ^ m

def FreeBudget.residual {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    {c : SupportedFreeChart F φ ψ S} {u : Base → ℝ} {τ s : ℝ} {q m : ℕ}
    (b : FreeBudget c u τ s q m) : ℝ :=
  4 * (2 ^ m * (2 ^ m * ((m.factorial : ℝ) *
    (2 ^ m * (fullErrorConstant 4 (m + q) b.K ^ (q + 1) * (τ / s) ^ (q + 1) * b.seedConstant)) *
    b.J ^ m) * b.D) * b.D)

lemma SupportedFreeChart.amplitude_smooth {F : RField 4} {φ ψ u : Base → ℝ} {S : Set Base}
    (c : SupportedFreeChart F φ ψ S) (hu : ContDiffOn ℝ ∞ (phaseAmplitude ψ u) c.V)
    (δ τ : ℝ) (q : ℕ) :
    ContDiff ℝ ∞ (c.amplitude u δ τ q) ∧ tsupport (c.amplitude u δ τ q) ⊆ S := by
  have hz := chartFree_vanishes c.cutoff δ τ (F ∘ c.e) u q
  exact ⟨contDiff_indicator_of_support c.openU c.closedS c.supportU
    (contDiffOn_chartFreeAmplitude c.smoothFe c.domain hu c.smoothχ c.maps δ τ q) hz,
    tsupport_indicator_subset c.closedS hz⟩



theorem SupportedFreeChart.displacement_spec {F : RField 4} {φ ψ u : Base → ℝ} {S : Set Base}
    (c : SupportedFreeChart F φ ψ S) {δ τ s : ℝ} (hδ : 0 ≤ δ)
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) {q m : ℕ}
    (b : FreeBudget c u τ s q m) :
    let X := displacement τ φ (c.amplitude u δ τ q)
    ContDiff ℝ ∞ X ∧ tsupport X ⊆ S ∧
    WeightedBound univ τ m (b.size * (δ * τ)) X ∧
    WeightedBound univ τ m (b.residual * (δ * τ)) (realLinearizedTensor F X) := by
  have hbV := weighted_freeSeed c.smoothFe c.domain hδ hτ.le hs b.nonnegC b.nonnegN
    b.smoothAmplitude b.amplitude b.normal
  have hseedpos : 0 ≤ b.seedConstant := by
    dsimp [FreeBudget.seedConstant]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) b.nonnegC) b.nonnegN
  have hh := weighted_extended_chart_free c.smoothFe c.openU c.domain c.closedS c.supportU
    c.smoothχ c.maps c.inverse b.smoothAmplitude c.cutoff δ hτ hs hτs hs1 b.nonnegK
    (mul_nonneg hseedpos (mul_nonneg hδ hτ.le)) b.oneLEJ b.nonnegD q m b.coefficients hbV
    b.coordinate b.coordinateDerivative
  dsimp only at hh ⊢
  have he : displacement τ (fun p => (c.χ p).1) (c.amplitude u δ τ q) =
      displacement τ φ (c.amplitude u δ τ q) := by
    funext p
    by_cases hp : p ∈ c.U
    · simp only [displacement, c.phase p hp]
    · have hz : c.amplitude u δ τ q p = 0 := indicator_of_notMem hp _
      rw [displacement_zero_value τ _ hz, displacement_zero_value τ _ hz]
  simp only [SupportedFreeChart.amplitude] at he ⊢
  rw [he] at hh
  refine ⟨hh.1, hh.2.1, ?_, ?_⟩
  · convert hh.2.2.1 using 1; simp only [FreeBudget.size, FreeBudget.seedConstant]; ring
  · convert hh.2.2.2 using 1; simp only [FreeBudget.residual, FreeBudget.seedConstant]; ring

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RootMean Set Filter
open ClosedSurfaceR4.QuadraticMean (displacement sumDisplacement)



theorem finite_free_displacement {ι : Type*} [Fintype ι] {F : RField 4}
    (hF : ContDiff ℝ ∞ F) {φ ψ u : ι → Base → ℝ} {S : ι → Set Base}
    (c : ∀ i, SupportedFreeChart F (φ i) (ψ i) (S i))
    {δ τ s : ℝ} (hδ : 0 ≤ δ) (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (q m : ℕ) (b : ∀ i, FreeBudget (c i) (u i) τ s q m) :
    let Z := fun i => (c i).amplitude (u i) δ τ q
    let X := sumDisplacement τ φ Z
    (∀ i, ContDiff ℝ ∞ (Z i) ∧ tsupport (Z i) ⊆ S i) ∧
    ContDiff ℝ ∞ X ∧ tsupport X ⊆ ⋃ i, S i ∧
    WeightedBound univ τ m ((∑ i, (b i).size) * (δ * τ)) X ∧
    WeightedBound univ τ m ((∑ i, (b i).residual) * (δ * τ)) (realLinearizedTensor F X) := by
  classical
  dsimp only
  have hh (i) := (c i).displacement_spec hδ hτ hs hτs hs1 (b i)
  have hsm := fun i => (hh i).1
  refine ⟨fun i => (c i).amplitude_smooth (b i).smoothAmplitude δ τ q,
    ContDiff.sum (fun i _ => hsm i), ?_, ?_, ?_⟩
  · apply closure_minimal _ (isClosed_iUnion_of_finite fun i => (c i).closedS)
    intro p hp
    by_contra hn
    apply hp
    apply Finset.sum_eq_zero
    intro i _
    exact image_eq_zero_of_notMem_tsupport
      (fun hh' => hn (mem_iUnion.mpr ⟨i, (hh i).2.1 hh'⟩))
  · have hb := WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ _ _
      (fun i _ => (hsm i).contDiffOn) (fun i _ => (hh i).2.2.1)
    rwa [← Finset.sum_mul] at hb
  · have he (p) : realLinearizedTensor F
        (sumDisplacement τ φ (fun i => (c i).amplitude (u i) δ τ q)) p =
        ∑ i, realLinearizedTensor F (displacement τ (φ i) ((c i).amplitude (u i) δ τ q)) p :=
      realLinearized_sum_right F (fun i => (hsm i).differentiable (by simp) p)
    have hb := WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ _ _
      (fun i _ => contDiffOn_realLinearizedTensor isOpen_univ hF.contDiffOn (hsm i).contDiffOn)
      (fun i _ => (hh i).2.2.2)
    rw [← Finset.sum_mul] at hb
    apply hb.congr
    intro p _
    exact he p

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RootMean Set Filter


def FreeBudget.slowSize {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    {c : SupportedFreeChart F φ ψ S} {u : Base → ℝ} {τ s : ℝ} {q m : ℕ}
    (b : FreeBudget c u τ s q m) : ℝ :=
  (m.factorial : ℝ) * ((1 + freeModeConstant 4 m b.K q) * b.seedConstant) * b.J ^ m

lemma SupportedFreeChart.amplitude_bound {F : RField 4} {φ ψ u : Base → ℝ} {S : Set Base}
    (c : SupportedFreeChart F φ ψ S) {δ τ s : ℝ} (hδ : 0 ≤ δ)
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1) {q m : ℕ}
    (b : FreeBudget c u τ s q m) :
    WeightedBound univ s m (b.slowSize * (δ * τ)) (c.amplitude u δ τ q) := by
  have hv := freeSeed_isFree c.smoothFe c.domain δ τ b.smoothAmplitude
  have hd := c.domain.complexDomain c.smoothFe
  have hm := contDiffOn_modeApprox τ hd hv.smooth (f := fun _ => 0) contDiffOn_const q
  have hseedpos : 0 ≤ b.seedConstant := by
    unfold FreeBudget.seedConstant
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) b.nonnegC) b.nonnegN
  have hbV := weighted_freeSeed c.smoothFe c.domain hδ hτ.le hs b.nonnegC b.nonnegN
    b.smoothAmplitude b.amplitude b.normal
  have hbA := weighted_modeApprox_free hτ (contDiff_complexify c.smoothFe) hd hs hτs hs1
    b.nonnegK (mul_nonneg hseedpos (mul_nonneg hδ hτ.le))
    hv.smooth hv.perpX hv.perpY hv.perpSecond q m b.coefficients hbV
  have hcpos := freeModeConstant_nonneg 4 m q b.nonnegK
  have hcomp := hbA.comp_coordinates c.openU.uniqueDiffOn hd.isOpen.uniqueDiffOn hs hs1
    b.oneLEJ (by positivity) c.smoothχ hm c.maps b.coordinate
  have hJ := zero_le_one.trans b.oneLEJ
  have hz := chartFree_vanishes c.cutoff δ τ (F ∘ c.e) u q
  have hext := hcomp.indicator_of_support c.openU c.closedS c.supportU (by positivity) hz
  convert hext using 1 <;> (try simp only [FreeBudget.slowSize, FreeBudget.seedConstant]) <;> first | rfl | ring

end ClosedSurfaceR4.RealModes

end

end OAI
