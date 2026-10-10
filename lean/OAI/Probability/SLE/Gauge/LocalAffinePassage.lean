import OAI.Probability.SLE.Gauge.RibbonPassageScaling
import OAI.Probability.SLE.Gauge.RibbonCoordinateLimit

namespace OAI

/-! Affine transport uses the progress coordinate only on the successful
physical envelope. This avoids imposing any condition on the arbitrary
off-image values of `coordinateInverse`. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open FirstFrontPassage PassageSuccess FrontSuccessMeasurability RibbonCoordinates
open RibbonPassageScaling

theorem frontSuccess_mass_eq_of_eqOn
    {Ω : Type*} (η : ℕ → Ω → ℝ≥0 → ℂ) (p p' : ℕ → ℂ → ℝ)
    (σ : Ω → ℝ≥0) (V : ℕ → Set ℂ) (a : ℕ → ℂ) (ε : ℝ) (n : ℕ)
    (hpeq : EqOn (p n) (p' n) (V n)) (κ v c : ℝ) (R : Set ℂ) :
    {ω | ω ∈ FrontSuccess η p σ V a ε n ∧ ENNReal.ofReal c ≤
      segmentSausageCharge κ (η n ω) (σ ω)
        (frontTime (fun t => p n (η n ω t)) 1) v R} =
    {ω | ω ∈ FrontSuccess η p' σ V a ε n ∧ ENNReal.ofReal c ≤
      segmentSausageCharge κ (η n ω) (σ ω)
        (frontTime (fun t => p' n (η n ω t)) 1) v R} := by
  have heq := frontSuccess_eq_of_eqOn η p p' σ V a ε n hpeq
  ext ω
  by_cases hω : ω ∈ FrontSuccess η p σ V a ε n
  · have hω' := heq ▸ hω
    have hs := hω
    obtain ⟨hfirst, hhit, _, hpath, _⟩ := hω
    have hfirst' := firstFrontTime_eq_of_prefix _ _ 1 _ hfirst hhit
      (fun t ht => hpeq (hpath ht))
    have ht : frontTime (fun t => p' n (η n ω t)) 1 =
        frontTime (fun t => p n (η n ω t)) 1 := by
      simp only [frontTime, hfirst', WithTop.untopD_coe]
    simp only [mem_ofPred_eq, hs, hω', true_and, ht]
  · have hω' : ω ∉ FrontSuccess η p' σ V a ε n := by
      simpa only [← heq] using hω
    simp only [mem_ofPred_eq, hω, hω', false_and]

def affineInverse (a : ℂ) (ell : ℝ) (z : ℂ) : ℂ := (z - a) / (ell : ℂ)

theorem affineInverse_left (a : ℂ) {ell : ℝ} (hell : 0 < ell) (z : ℂ) :
    affineInverse a ell (affine a ell z) = z := by
  simp only [affineInverse, affine, add_sub_cancel_left]
  exact mul_div_cancel_left₀ z (Complex.ofReal_ne_zero.mpr hell.ne')

theorem frontSuccess_mass_probability_affine_local
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (η : ℕ → Ω → ℝ≥0 → ℂ) (p p' : ℕ → ℂ → ℝ)
    (σ : Ω → ℝ≥0) (V : ℕ → Set ℂ) (b : ℕ → ℂ) (ε : ℝ)
    (a : ℂ) {ell : ℝ} (hell : 0 < ell) (n : ℕ)
    (hp : ∀ z ∈ V n, p' n (affine a ell z) = p n z)
    (κ : ℝ) (R : Set ℂ) {v : ℝ} (hv : 0 < v) (c : ℝ) :
    P {ω | ω ∈ FrontSuccess (fun j ω t => affine a ell (η j ω t)) p' σ
          (fun j => affine a ell '' V j) (fun j => affine a ell (b j)) (ell * ε) n ∧
        ENNReal.ofReal (c * ell ^ dimension κ) ≤
          segmentSausageCharge κ (fun t => affine a ell (η n ω t)) (σ ω)
            (frontTime (fun t => p' n (affine a ell (η n ω t))) 1)
            (ell * v) (affine a ell '' R)} =
      P {ω | ω ∈ FrontSuccess η p σ V b ε n ∧ ENNReal.ofReal c ≤
        segmentSausageCharge κ (η n ω) (σ ω)
          (frontTime (fun t => p n (η n ω t)) 1) v R} := by
  let pp := fun j z => p j (affineInverse a ell z)
  have heq : EqOn (pp n) (p' n) (affine a ell '' V n) := by
    rintro z ⟨w, hw, rfl⟩
    dsimp only [pp]
    rw [affineInverse_left a hell]
    exact (hp w hw).symm
  rw [← frontSuccess_mass_eq_of_eqOn
    (fun j ω t => affine a ell (η j ω t)) pp p' σ
    (fun j => affine a ell '' V j) (fun j => affine a ell (b j)) (ell * ε) n
    heq κ (ell * v) (c * ell ^ dimension κ) (affine a ell '' R)]
  exact frontSuccess_mass_probability_affine P η p pp σ V b ε a hell n
    (fun z => by dsimp only [pp]; rw [affineInverse_left a hell]) κ R hv c

theorem longitudinalCoordinate_affine_on_image
    (P : ℂ → ℂ) (K : Set ℂ) (hiP : InjOn P K) (a : ℂ)
    {ell : ℝ} (hell : 0 < ell) (k : ℝ) :
    ∀ z ∈ P '' K,
      longitudinalCoordinate (fun w => affine a ell (P w)) K k (affine a ell z) =
        longitudinalCoordinate P K k z := by
  have hi : InjOn (fun w => affine a ell (P w)) K :=
    (affine_bijective a hell).1.injOn.comp hiP (mapsTo_univ _ _)
  rintro z ⟨w, hw, rfl⟩
  simp only [longitudinalCoordinate, coordinateInverse_left hi hw,
    coordinateInverse_left hiP hw]

end SLEExactGauge

end

end OAI
