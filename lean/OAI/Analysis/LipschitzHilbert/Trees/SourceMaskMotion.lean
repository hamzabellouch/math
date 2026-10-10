import OAI.Analysis.LipschitzHilbert.Fourier.SincMaskMotion
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledMotion
import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketScaling

namespace OAI

/-! The actual top mask preserves interval motion.  Only absolute mask
differences occur, so no nonvanishing hypothesis is imposed on the mask. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert
open PhaseCombinatorics

variable {κ : Type} [Fintype κ]

/-- The common diagonal carrier as a complex linear isometry. -/
def diagonalModulationIsometry (frequency : κ → ℝ) (t : ℝ) :
    EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ where
  toFun a := diagonalModulation frequency a t
  map_add' a b := by
    ext k
    simp only [diagonalModulation, WithLp.ofLp_toLp, PiLp.add_apply]
    ring
  map_smul' c a := by
    ext k
    simp only [diagonalModulation, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring
  norm_map' a := norm_diagonalModulation frequency a t

@[simp]
theorem diagonalModulationIsometry_apply (frequency : κ → ℝ) (t : ℝ)
    (a : EuclideanSpace ℂ κ) :
    diagonalModulationIsometry frequency t a = diagonalModulation frequency a t := rfl

def diagonalModulationRealIsometry (frequency : κ → ℝ) (t : ℝ) :
    EuclideanSpace ℂ κ →ₗᵢ[ℝ] EuclideanSpace ℂ κ where
  toLinearMap := (diagonalModulationIsometry frequency t).toLinearMap.restrictScalars ℝ
  norm_map' a := norm_diagonalModulation frequency a t

@[simp]
theorem diagonalModulationRealIsometry_apply (frequency : κ → ℝ) (t : ℝ)
    (a : EuclideanSpace ℂ κ) :
    diagonalModulationRealIsometry frequency t a = diagonalModulation frequency a t := rfl

theorem masked_isometry_motion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E →ₗᵢ[ℝ] E) (v₁ v₀ : E) (q₁ q₀ B ε δ : ℝ)
    (hq : |q₁| ≤ 1) (hδ : 0 ≤ δ) (hmask : |q₁-q₀| ≤ δ)
    (hbase : ‖v₀‖ ≤ B) (hmove : ‖v₁-U v₀‖ ≤ ε) :
    ‖q₁ • v₁-U (q₀ • v₀)‖ ≤ ε+δ*B := by
  have heq : q₁ • v₁-U (q₀ • v₀) =
      q₁ • (v₁-U v₀)+(q₁-q₀) • U v₀ := by
    rw [U.map_smul, smul_sub, sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖q₁ • (v₁-U v₀)‖+‖(q₁-q₀) • U v₀‖ := norm_add_le _ _
    _ = |q₁| * ‖v₁-U v₀‖+|q₁-q₀| * ‖v₀‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, U.norm_map]
    _ ≤ 1*ε+δ*B := add_le_add
      (mul_le_mul hq hmove (norm_nonneg _) zero_le_one)
      (mul_le_mul hmask hbase (norm_nonneg _) hδ)
    _ = _ := by ring

namespace SlopeBox

theorem mask_slope_coordinates_motion (T : SlopeBox) (L A x₀ x₁ y₀ y₁ : ℝ)
    (hL : 0 < L) :
    |T.mask L A (x₁,y₁+T.slope*x₁)-T.mask L A (x₀,y₀+T.slope*x₀)| ≤
      (2*(⌈L⌉₊:ℝ)/L^A)*(|x₁-x₀|/T.length+|y₁-y₀|/T.width) := by
  have h := T.mask_motion L A hL (x₁,y₁+T.slope*x₁) (x₀,y₀+T.slope*x₀)
  have heq : (y₁+T.slope*x₁)-(y₀+T.slope*x₀)-T.slope*(x₁-x₀) = y₁-y₀ := by ring
  simpa only [heq, abs_div, abs_of_pos T.length_pos, abs_of_pos T.width_pos] using h

end SlopeBox

namespace SourceLabeledLattice

variable {N : ℕ} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [∀ j l, Fintype (Item j l)]

theorem rawInterval_coeff_smul (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q : ℝ) (jet : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    P.rawInterval (fun j l u => q • coeff j l u) jet lower upper x y =
      q • P.rawInterval coeff jet lower upper x y := by
  exact planarPacketInterval_coeff_smul (ι := fun j => Σ l : P.labels j, Item j l)
    (fun j p => coeff j p.1 p.2) (fun j p k t s => P.raw jet j p.1 p.2 k t s)
    q lower upper x y

/-- Original physical coefficients, the original top carrier, and the
mask evaluated at each endpoint.  The only pointwise estimate used is the
already established interval concentration on the snapshot vertical line. -/
theorem source_labeled_masked_interval_motion (p : ℝ) (D B : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (B : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 1 ≤ K → SourceLabeledTopGeometry P T K D →
      ∀ (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ x₀ x₁ y₀ y₁ A maskExponent : ℝ,
      |x₁-x₀| ≤ T.length → |y₁-y₀| ≤ T.width →
      let F := (P.withProfile alt hAlt).rawInterval
        (P.physicalCoefficient T.slope cutoff v g) 0 lower upper
      let w₀ := (T.weight K (D:ℝ) (x₀,y₀+T.slope*x₀))^8
      (∀ y, |y-y₀| ≤ T.width → ‖F x₀ y‖+T.width*
        ‖covariantSignal P.frequency (fun k t => F x₀ t k) y‖ ≤ A*w₀) →
      ‖T.mask L maskExponent (x₁,y₁+T.slope*x₁) • F x₁ y₁-
        diagonalModulation P.frequency
          (T.mask L maskExponent (x₀,y₀+T.slope*x₀) • F x₀ y₀) (y₁-y₀)‖ ≤
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
          (|x₁-x₀|/T.length+|y₁-y₀|/T.width)*A)*w₀ := by
  obtain ⟨L0,hL0,hB,hmotion⟩ := source_labeled_interval_motion p D B
  refine ⟨L0,hL0,hB,?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK G cutoff v hv g hg hg1
    lower upper hlu r hr hs x₀ x₁ y₀ y₁ A maskExponent hx hy
  dsimp only
  intro hc
  let F := (P.withProfile alt hAlt).rawInterval
    (P.physicalCoefficient T.slope cutoff v g) 0 lower upper
  let w₀ := (T.weight K (D:ℝ) (x₀,y₀+T.slope*x₀))^8
  have hL : 0 < L := zero_lt_one.trans_le (hL0.trans hLL)
  have hm := hmotion L hLL N κ Label Item P hcard hP alt hAlt T K hK G
    cutoff v hv g hg hg1 lower upper hlu r hr hs x₀ x₁ y₀ y₁ A hx hy hc
  have hbase : ‖F x₀ y₀‖ ≤ A*w₀ := by
    have hb := hc y₀ (by simp [T.width_pos.le])
    have hn := mul_nonneg T.width_pos.le
      (norm_nonneg (covariantSignal P.frequency (fun k t => F x₀ t k) y₀))
    change ‖F x₀ y₀‖+_ ≤ A*w₀ at hb
    linarith
  have hq : |T.mask L maskExponent (x₁,y₁+T.slope*x₁)| ≤ 1 := by
    change |topSincMask L maskExponent _ _| ≤ 1
    rw [abs_of_nonneg (topSincMask_nonneg _ _ _ _)]
    exact topSincMask_le_one _ _ _ _
  have hlength := T.length_pos
  have hwidth := T.width_pos
  have h := masked_isometry_motion
    (diagonalModulationRealIsometry P.frequency (y₁-y₀))
    (F x₁ y₁) (F x₀ y₀)
    (T.mask L maskExponent (x₁,y₁+T.slope*x₁))
    (T.mask L maskExponent (x₀,y₀+T.slope*x₀)) (A*w₀)
    (((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|)*w₀)
    ((2*(⌈L⌉₊:ℝ)/L^maskExponent)*(|x₁-x₀|/T.length+|y₁-y₀|/T.width))
    hq (by positivity) (T.mask_slope_coordinates_motion L maskExponent x₀ x₁ y₀ y₁ hL)
    hbase hm
  have heq :
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|)*w₀+
        ((2*(⌈L⌉₊:ℝ)/L^maskExponent)*(|x₁-x₀|/T.length+|y₁-y₀|/T.width))*(A*w₀) =
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*(|x₁-x₀|/T.length+|y₁-y₀|/T.width)*A)*w₀ := by
    ring
  rw [heq] at h
  simpa only [diagonalModulationRealIsometry_apply] using h

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
