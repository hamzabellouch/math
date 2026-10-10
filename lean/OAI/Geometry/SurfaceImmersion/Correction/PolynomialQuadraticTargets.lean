import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticFamily

namespace OAI

/-! Smooth supported tensor targets for every polynomial quadratic phase. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma quadraticFamilyPhase_smooth {ι : Type*} {φ : ι → Base → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (l : RealModes.QuadraticLabel ι) :
    ContDiff ℝ ∞ (quadraticFamilyPhase φ l) := by
  rcases l with i | ⟨i,j,b⟩
  · exact (contDiff_const (c := (2 : ℝ))).mul (hφ i)
  · cases b
    · exact (hφ i).add (hφ j)
    · exact (hφ i).sub (hφ j)

lemma quadraticFamilyCoefficient_smooth {n : ℕ} {ι : Type*}
    {P : Fin n → Expression} {U : Set Base} {O : Set LowJet}
    (hO : IsOpen O) (hP : ∀ j, (P j).SmoothCoeffs O) {G : Base → Space}
    {φ : ι → Base → ℝ} {H : ι → Base → Fin 4 → ℂ}
    (hG : ContDiff ℝ ∞ G) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (hQ : Set.MapsTo (lowJet G) U O)
    (ε τ t : ℝ) (l : RealModes.QuadraticLabel ι) :
    ContDiffOn ℝ ∞ (quadraticFamilyCoefficient P ε G φ H τ t l) U := by
  rcases l with i | ⟨i,j,b⟩
  · exact quadraticPhaseCoefficient_smooth hO hP hG (hφ i) (hφ i) (hH i) (hH i) hQ ε τ t
  · cases b
    · exact quadraticPhaseCoefficient_smooth hO hP hG (hφ i) (hφ j) (hH i) (hH j) hQ ε τ t
    · exact quadraticPhaseCoefficient_smooth hO hP hG (hφ i) (hφ j).neg
        (hH i) (starField_smooth (hH j)) hQ ε τ t

def quadraticFamilyTensor {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ)
    (l : RealModes.QuadraticLabel ι) : Base → Fin 3 → ℂ :=
  fun x k => quadraticFamilyCoefficient (P k) ε G φ H τ t l x

lemma quadraticFamilyTensor_tsupport {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ)
    {S : ι → Set Base} (hS : ∀ i, IsClosed (S i)) (hH : ∀ i, tsupport (H i) ⊆ S i)
    (l : RealModes.QuadraticLabel ι) :
    tsupport (quadraticFamilyTensor P ε G φ H τ t l) ⊆ quadraticFamilySupport S l := by
  have hclosed : IsClosed (quadraticFamilySupport S l) := by
    rcases l with i | ⟨i,j,b⟩
    · exact hS i
    · exact (hS i).inter (hS j)
  apply closure_minimal _ hclosed
  intro x hx
  by_contra hn
  apply hx
  funext k
  change quadraticFamilyCoefficient (P k) ε G φ H τ t l x = 0
  exact image_eq_zero_of_notMem_tsupport (fun hp => hn
    (quadraticFamilyCoefficient_tsupport (P k) ε G φ H τ t hH l hp))

def polynomialQuadraticTarget {n : ℕ} {ι : Type*}
    {P : Fin 3 → Fin n → Expression} {U : Set Base} {O : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hP : ∀ k j, (P k j).SmoothCoeffs O)
    {G : Base → Space} {φ : ι → Base → ℝ} {H : ι → Base → Fin 4 → ℂ}
    (hG : ContDiff ℝ ∞ G) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (hQ : Set.MapsTo (lowJet G) U O)
    {S : ι → Set Base} (hS : ∀ i, IsClosed (S i)) (hHS : ∀ i, tsupport (H i) ⊆ S i)
    (l : RealModes.QuadraticLabel ι) (C : Compacts Base) (hCU : (C : Set Base) ⊆ U)
    (hSC : quadraticFamilySupport S l ⊆ C) (ε τ t : ℝ) :
    SupportedField (F := Fin 3 → ℂ) C :=
  let ht := (quadraticFamilyTensor_tsupport P ε G φ H τ t hS hHS l).trans hSC
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset hU (ht.trans hCU)
      (contDiffOn_pi.mpr fun k => quadraticFamilyCoefficient_smooth hO (hP k) hG hφ hH hQ ε τ t l))
    (subset_closure.trans ht)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
