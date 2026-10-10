import OAI.Geometry.Immersion.ClosedSurface.RootMean
import OAI.Geometry.Immersion.ClosedSurface.FiniteMean
import OAI.Geometry.Immersion.ClosedSurface.CoordinateBounds

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.RootMean ClosedSurfaceR4.WeightedEstimates
open Set



abbrev Tensor := Fin 3 → ℝ

def firstDirection : Fin 3 → Base := ![dx, dx, dy]
def secondDirection : Fin 3 → Base := ![dx, dy, dy]

lemma firstDirection_norm (i : Fin 3) : ‖firstDirection i‖ ≤ 1 := by
  fin_cases i <;> norm_num [firstDirection, dx, dy, Prod.norm_def]
lemma secondDirection_norm (i : Fin 3) : ‖secondDirection i‖ ≤ 1 := by
  fin_cases i <;> norm_num [secondDirection, dx, dy, Prod.norm_def]

def evaluate (A : Tensor) (v w : Base) : ℝ :=
  A 0 * v.1 * w.1 + A 1 * (v.1 * w.2 + v.2 * w.1) + A 2 * v.2 * w.2


def pullback (J : Base →L[ℝ] Base) : Tensor →L[ℝ] Tensor :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A i => evaluate A (J (firstDirection i)) (J (secondDirection i))
    map_add' := by intro A B; ext i; simp only [evaluate, Pi.add_apply]; ring
    map_smul' := by intro c A; ext i; simp only [evaluate, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

def pullbackField (χ : Base → Base) (p : Base) : Tensor →L[ℝ] Tensor :=
  pullback (fderiv ℝ χ p)


def meanTensor (δ τ : ℝ) (F : RField 4) (b : Base → ℝ) (q : ℕ) : Base → Tensor :=
  fun p i => normalizedMeanError δ τ F b q (firstDirection i) (secondDirection i) p

lemma contDiffOn_meanTensor {V : Set Base} {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F V) {b : Base → ℝ} (hb : ContDiffOn ℝ ∞ b V)
    (δ τ : ℝ) (q : ℕ) : ContDiffOn ℝ ∞ (meanTensor δ τ F b q) V := by
  apply contDiffOn_pi.mpr
  intro i
  have hv := freeSeed_isFree hF h δ τ hb
  exact (contDiffOn_modeMeanError τ (h.complexDomain hF) hv.smooth hv.smooth q
    (firstDirection i) (secondDirection i)).const_smul ((δ ^ 2)⁻¹)

lemma weighted_meanTensor {V : Set Base} {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F V) {b : Base → ℝ} (hb : ContDiffOn ℝ ∞ b V)
    {δ τ s K C B : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s)
    (hs1 : s ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C) (hB : 0 ≤ B) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F p)) V s (m + q + 2) K)
    (hbb : WeightedBound V s (m + q + 2) C b)
    (hbN : WeightedBound V s (m + q + 2) B (freeNormal F)) :
    WeightedBound V s m
      (meanErrorConstant 4 m K q * (Real.sqrt 2 * 2 ^ (m + q + 2) * C * B) ^ 2 * (τ / s))
      (meanTensor δ τ F b q) := by
  have hm := contDiffOn_meanTensor hF h hb δ τ q
  have hM := meanErrorConstant_nonneg 4 m q hK
  apply WeightedBound.pi h.isOpen.uniqueDiffOn hs (by positivity)
    (fun i => contDiffOn_pi.mp hm i)
  intro i
  exact weighted_normalizedMeanError hF h hδ hτ hs hτs hs1 hK hC hB hb q m hc hbb hbN
    (firstDirection i) (secondDirection i) (firstDirection_norm i) (secondDirection_norm i)

lemma weighted_meanTensor_difference {V : Set Base} {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F V) {b c : Base → ℝ} (hb : ContDiffOn ℝ ∞ b V)
    (hcs : ContDiffOn ℝ ∞ c V) {δ τ s K C D B : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B) (q m : ℕ)
    (hc : ReconstructionCoefficientBound (fun p => complexify (F p)) V s (m + q + 2) K)
    (hbb : WeightedBound V s (m + q + 2) C b)
    (hbc : WeightedBound V s (m + q + 2) C c)
    (hbD : WeightedBound V s (m + q + 2) D (fun p => b p - c p))
    (hbN : WeightedBound V s (m + q + 2) B (freeNormal F)) :
    WeightedBound V s m (2 * meanErrorConstant 4 m K q *
      (Real.sqrt 2 * 2 ^ (m + q + 2) * B) ^ 2 * C * D * (τ / s))
      (fun p => meanTensor δ τ F b q p - meanTensor δ τ F c q p) := by
  have hM := meanErrorConstant_nonneg 4 m q hK
  have hm := (contDiffOn_meanTensor hF h hb δ τ q).sub
    (contDiffOn_meanTensor hF h hcs δ τ q)
  apply WeightedBound.pi h.isOpen.uniqueDiffOn hs (by positivity)
    (fun i => contDiffOn_pi.mp hm i)
  intro i
  exact weighted_normalizedMeanError_difference hF h hδ hτ hs hτs hs1 hK hC hD hB hb hcs q m
    hc hbb hbc hbD hbN (firstDirection i) (secondDirection i)
    (firstDirection_norm i) (secondDirection_norm i)



def coefficient (Q : Base → Tensor →L[ℝ] ℝ) (e : Base → Base) (A : Base → Tensor) : Base → ℝ :=
  fun p => Q p (A (e p))



def meanTerm (δ s : ℝ) (F : RField 4) (ψ : Base → ℝ)
    (Q : Base → Tensor →L[ℝ] ℝ) (χ e : Base → Base) (q : ℕ)
    (η : ℝ) (A : Base → Tensor) : Base → Tensor :=
  fun p => pullbackField χ p
    (meanTensor δ (η * s) F (phaseAmplitude ψ (coefficient Q e A)) q (χ p))

end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set

lemma contDiffOn_coefficient {U V : Set Base} {Q : Base → Tensor →L[ℝ] ℝ}
    {e : Base → Base} {A : Base → Tensor} (hQ : ContDiffOn ℝ ∞ Q V)
    (he : ContDiffOn ℝ ∞ e V) (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (coefficient Q e A) V :=
  hQ.clm_apply (hA.comp he heU)

lemma weighted_coefficient {U V : Set Base} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {Q : Base → Tensor →L[ℝ] ℝ} {e : Base → Base} {A : Base → Tensor}
    {s J P C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hP : 0 ≤ P)
    (hC : 0 ≤ C) (hQ : ContDiffOn ℝ ∞ Q V) (he : ContDiffOn ℝ ∞ e V)
    (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U)
    (heB : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ J)
    (hQB : WeightedBound V s m P Q) (hAB : WeightedBound U s m C A) :
    WeightedBound V s m ((2 ^ m * P * (m.factorial : ℝ) * J ^ m) * C)
      (coefficient Q e A) := by
  have hAe := hAB.comp_coordinates hV hU hs hs1 hJ hC he hA heU heB
  have hh := hQB.clm_apply hV hs.le hP (by positivity) hQ (hA.comp he heU) hAe
  convert hh using 1 <;> try rfl
  ring

lemma weighted_coefficient_difference {U V : Set Base} (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V)
    {Q : Base → Tensor →L[ℝ] ℝ} {e : Base → Base} {A B : Base → Tensor}
    {s J P D : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hP : 0 ≤ P)
    (hD : 0 ≤ D) (hQ : ContDiffOn ℝ ∞ Q V) (he : ContDiffOn ℝ ∞ e V)
    (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (heB : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ J)
    (hQB : WeightedBound V s m P Q) (hAB : WeightedBound U s m D (A - B)) :
    WeightedBound V s m ((2 ^ m * P * (m.factorial : ℝ) * J ^ m) * D)
      (fun p => coefficient Q e A p - coefficient Q e B p) := by
  apply (weighted_coefficient hU hV hs hs1 hJ hP hD hQ he heU (hA.sub hB) heB hQB hAB).congr
  intro p hp
  exact (map_sub (Q p) (A (e p)) (B (e p))).symm




lemma coefficient_trial_range {U V : Set Base} {Q : Base → Tensor →L[ℝ] ℝ}
    {e : Base → Base} {reference A : Base → Tensor} {r ρ R : ℝ}
    (heU : MapsTo e V U)
    (hmargin : ∀ p ∈ V, ρ + ‖Q p‖ * r ≤ coefficient Q e reference p ∧
      coefficient Q e reference p ≤ R - ‖Q p‖ * r)
    (hA : InTrialBall U reference r A) : MapsTo (coefficient Q e A) V (Icc ρ R) := by
  intro p hp
  have hnorm : ‖coefficient Q e A p - coefficient Q e reference p‖ ≤ ‖Q p‖ * r := by
    rw [coefficient, coefficient, ← map_sub]
    exact (ContinuousLinearMap.le_opNorm (Q p) _).trans
      (mul_le_mul_of_nonneg_left (hA (e p) (heU hp)).le (norm_nonneg _))
  have hb := abs_le.mp (show |coefficient Q e A p - coefficient Q e reference p| ≤ ‖Q p‖ * r by
    simpa only [Real.norm_eq_abs] using hnorm)
  obtain ⟨hl, hu⟩ := hmargin p hp
  constructor <;> linarith

end ClosedSurfaceR4.PhaseMean

end

end OAI
