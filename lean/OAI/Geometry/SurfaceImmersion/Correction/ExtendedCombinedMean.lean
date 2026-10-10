import OAI.Geometry.SurfaceImmersion.Correction.LocalCombinedMeanBounds

namespace OAI

/-! Extend the actual local combined mean through its fixed compact support. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes WeightedEstimates FiniteMean
open JetPolynomial (SupportedField)
open JetPolynomial.Perturbation (modeSupport)

variable {n : ℕ} {U V : Set Base} {s r ρ R₀ : ℝ} {reference : Base → Tensor}
  {F : RField 4} {K : Compacts JetPolynomial.Base}
  {ψ : SupportedField (F := ℝ) (modeSupport K)}
  {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

def extendedCombinedMean (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (modeSupport K : Set Base) ⊆ V)
    (P : Fin 3 → Fin n → JetPolynomial.Expression) (G : JetPolynomial.Base → JetPolynomial.Space)
    (δ τ ε : ℝ) (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q : ℕ) (A : Base → Tensor) : Base → Tensor :=
  U.indicator (localCombinedMean h hρ hKV P G δ τ ε R q A)

lemma extendedCombinedMean_smooth (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (modeSupport K : Set Base) ⊆ V)
    {S : Set Base} (hS : IsClosed S) (hSU : S ⊆ U)
    (hsp : ∀ x ∈ U, χ x ∈ (modeSupport K : Set Base) → x ∈ S)
    {P : Fin 3 → Fin n → JetPolynomial.Expression} {J : Set JetPolynomial.Base}
    {O : Set JetPolynomial.LowJet} (hJ : IsOpen J) (hO : IsOpen O)
    (hP : ∀ i l, (P i l).SmoothCoeffs O) {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (hGQ : Set.MapsTo (JetPolynomial.lowJet G) J O)
    (hKJ : (K : Set JetPolynomial.Base) ⊆ J)
    (δ τ ε : ℝ) (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q : ℕ) (A : Base → Tensor) :
    ContDiff ℝ ∞ (extendedCombinedMean h hρ hKV P G δ τ ε R q A) :=
  contDiff_indicator_of_support h.openU hS hSU
    (localCombinedMean_smooth h hρ hKV hJ hO hP hG hGQ hKJ δ τ ε R q A)
    (localCombinedMean_vanishes h hρ hKV hsp P G δ τ ε R q A)

lemma extendedCombinedMean_value (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (modeSupport K : Set Base) ⊆ V)
    {S : Set Base} (hS : IsClosed S) (hSU : S ⊆ U)
    (hsp : ∀ x ∈ U, χ x ∈ (modeSupport K : Set Base) → x ∈ S)
    (P : Fin 3 → Fin n → JetPolynomial.Expression) (G : JetPolynomial.Base → JetPolynomial.Space)
    (δ τ ε : ℝ) (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q : ℕ) (A : Base → Tensor)
    {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C (localCombinedMean h hρ hKV P G δ τ ε R q A)) :
    WeightedBound Set.univ s m C (extendedCombinedMean h hρ hKV P G δ τ ε R q A) :=
  hb.indicator_of_support h.openU hS hSU hC (localCombinedMean_vanishes h hρ hKV hsp P G δ τ ε R q A)

lemma extendedCombinedMean_difference (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (modeSupport K : Set Base) ⊆ V)
    {S : Set Base} (hS : IsClosed S) (hSU : S ⊆ U)
    (hsp : ∀ x ∈ U, χ x ∈ (modeSupport K : Set Base) → x ∈ S)
    (P : Fin 3 → Fin n → JetPolynomial.Expression) (G : JetPolynomial.Base → JetPolynomial.Space)
    (δ τ ε : ℝ) (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q : ℕ) (A B : Base → Tensor)
    {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C (localCombinedMean h hρ hKV P G δ τ ε R q A -
      localCombinedMean h hρ hKV P G δ τ ε R q B)) :
    WeightedBound Set.univ s m C (extendedCombinedMean h hρ hKV P G δ τ ε R q A -
      extendedCombinedMean h hρ hKV P G δ τ ε R q B) := by
  have hz : ∀ x ∈ U, x ∉ S → (localCombinedMean h hρ hKV P G δ τ ε R q A -
      localCombinedMean h hρ hKV P G δ τ ε R q B) x = 0 := by
    intro x hx hs
    rw [Pi.sub_apply, localCombinedMean_vanishes h hρ hKV hsp P G δ τ ε R q A x hx hs,
      localCombinedMean_vanishes h hρ hKV hsp P G δ τ ε R q B x hx hs, sub_self]
  have hh := hb.indicator_of_support h.openU hS hSU hC hz
  apply hh.congr
  intro x _
  by_cases hx : x ∈ U
  · simp only [extendedCombinedMean, Set.indicator_of_mem hx, Pi.sub_apply]
  · simp only [extendedCombinedMean, Set.indicator_of_notMem hx, Pi.sub_apply, sub_self]

end ClosedSurfaceR4.PhaseMean

end

end OAI
