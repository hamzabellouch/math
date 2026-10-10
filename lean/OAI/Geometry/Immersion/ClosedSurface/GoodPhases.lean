import OAI.Geometry.Immersion.ClosedSurface.GoodDirections
import OAI.Geometry.Immersion.ClosedSurface.PositiveBasis

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma good_weighted {n : ℕ} {B : Fin 3 → RVec n} {t w : ℝ}
    (hw : w ≠ 0) (ht : secondQuadratic B (-t, 1) ≠ 0) : Good B (w, w*t) := by
  constructor
  · intro hz
    exact hw (congrArg Prod.fst hz)
  · have he : (-(w*t), w) = w • (-t, (1 : ℝ)) := by
      ext <;> simp
    rw [he, secondQuadratic_smul]
    exact smul_ne_zero (pow_ne_zero 2 hw) ht



theorem positive_good_slopes {n : ℕ} {B : Fin 3 → RVec n} (hB : B ≠ 0)
    {H : PhaseMean.Tensor} (h₀ : 0 < H 0) (hdet : 0 < H 0 * H 2 - (H 1)^2) :
    ∃ t₀ t₁ t₂ : ℝ, t₀ < t₁ ∧ t₁ < t₂ ∧
      0 < basisCoefficient t₀ t₁ t₂ H ∧ 0 < basisCoefficient t₁ t₀ t₂ H ∧
      0 < basisCoefficient t₂ t₀ t₁ H ∧
      secondQuadratic B (-t₀, 1) ≠ 0 ∧ secondQuadratic B (-t₁, 1) ≠ 0 ∧
      secondQuadratic B (-t₂, 1) ≠ 0 ∧
      secondQuadratic B (-((t₀ + 2*t₁)/3), 1) ≠ 0 ∧
      secondQuadratic B (-(2*t₁-t₀), 1) ≠ 0 ∧
      secondQuadratic B (-((t₀ + 4*t₂)/5), 1) ≠ 0 ∧
      secondQuadratic B (-((4*t₂-t₀)/3), 1) ≠ 0 ∧
      secondQuadratic B (-((t₁ + 2*t₂)/3), 1) ≠ 0 ∧
      secondQuadratic B (-(2*t₂-t₁), 1) ≠ 0 := by
  obtain ⟨β, r, hr, h₁, h₂⟩ := positive_center_parameters h₀ hdet
  let T : Set ℝ := (fun x : ℝ => r*x + β) ⁻¹' {t : ℝ | secondQuadratic B (-t, 1) = 0}
  have hT : T.Finite := finite_affine_preimage (finite_bad_slopes hB) hr.ne'
  obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, hn₀, hn₁, hn₂, hn₃, hn₄, hn₅, hn₆, hn₇, hn₈⟩ :=
    choose_three_avoiding hT (show (-3 : ℝ) < -2 by norm_num)
      (show (-(1/4) : ℝ) < 1/4 by norm_num) (show (2 : ℝ) < 3 by norm_num)
  have hn : ∀ {x : ℝ}, x ∉ T → secondQuadratic B (-(β+r*x), 1) ≠ 0 := by
    intro x hx
    simpa only [T, mem_preimage, mem_ofPred_eq, add_comm] using hx
  have hpos := shifted_basis_positive h₀ hr h₁ h₂ hx₀ hx₁ hx₂
  refine ⟨β+r*x₀, β+r*x₁, β+r*x₂, ?_, ?_, hpos.1, hpos.2.1, hpos.2.2,
    hn hn₀, hn hn₁, hn hn₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [hx₀.2, hx₁.1]
  · nlinarith [hx₁.2, hx₂.1]
  · convert hn hn₃ using 1
    congr 2
    ring
  · convert hn hn₄ using 1
    congr 2
    ring
  · convert hn hn₅ using 1
    congr 2
    ring
  · convert hn hn₆ using 1
    congr 2
    ring
  · convert hn hn₇ using 1
    congr 2
    ring
  · convert hn hn₈ using 1
    congr 2
    ring

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma good_neg {n : ℕ} {B : Fin 3 → RVec n} {ξ : Base} (h : Good B ξ) : Good B (-ξ) := by
  constructor
  · exact neg_ne_zero.mpr h.1
  · have he : (-(-ξ).2, (-ξ).1) = (-1 : ℝ) • (-ξ.2, ξ.1) := by ext <;> simp
    rw [he, secondQuadratic_smul]
    simpa using h.2



theorem positive_good_phase_data {n : ℕ} {B : Fin 3 → RVec n} (hB : B ≠ 0)
    {H₀ : PhaseMean.Tensor} (h₀ : 0 < H₀ 0) (hdet : 0 < H₀ 0 * H₀ 2 - (H₀ 1)^2) :
    ∃ (ξ : Fin 3 → Base) (Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ),
      (∀ H, ∑ i : Fin 3, Q i H • covectorSquare (ξ i) = H) ∧
      (∀ i, 0 < Q i H₀) ∧ (∀ i, Good B (ξ i)) ∧
      (∀ i j, i ≠ j → Good B (ξ i + ξ j) ∧ Good B (ξ i - ξ j)) := by
  obtain ⟨t₀, t₁, t₂, h01, h12, hp₀, hp₁, hp₂, hg₀, hg₁, hg₂, hg₃, hg₄, hg₅, hg₆, hg₇, hg₈⟩ :=
    positive_good_slopes hB h₀ hdet
  let ξ : Fin 3 → Base := ![(1, t₀), (2, 2*t₁), (4, 4*t₂)]
  let Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ :=
    ![basisCoefficient t₀ t₁ t₂, (1/4 : ℝ) • basisCoefficient t₁ t₀ t₂,
      (1/16 : ℝ) • basisCoefficient t₂ t₀ t₁]
  have hξ₁ : ξ 1 = (2 : ℝ) • (1, t₁) := by ext <;> simp [ξ]
  have hξ₂ : ξ 2 = (4 : ℝ) • (1, t₂) := by ext <;> simp [ξ]
  have h03 : Good B (ξ 0 + ξ 1) := by
    convert good_weighted (B := B) (w := 3) (by norm_num) hg₃ using 1
    ext <;> simp [ξ] <;> ring
  have h04 : Good B (ξ 1 - ξ 0) := by
    convert good_weighted (B := B) (w := 1) (by norm_num) hg₄ using 1
    ext <;> simp [ξ]
    ring
  have h05 : Good B (ξ 0 + ξ 2) := by
    convert good_weighted (B := B) (w := 5) (by norm_num) hg₅ using 1
    ext <;> simp [ξ] <;> ring
  have h06 : Good B (ξ 2 - ξ 0) := by
    convert good_weighted (B := B) (w := 3) (by norm_num) hg₆ using 1
    ext <;> simp [ξ] <;> ring
  have h07 : Good B (ξ 1 + ξ 2) := by
    convert good_weighted (B := B) (w := 6) (by norm_num) hg₇ using 1
    ext <;> simp [ξ] <;> ring
  have h08 : Good B (ξ 2 - ξ 1) := by
    convert good_weighted (B := B) (w := 2) (by norm_num) hg₈ using 1
    ext <;> simp [ξ] <;> ring
  refine ⟨ξ, Q, ?_, ?_, ?_, ?_⟩
  · intro H
    rw [Fin.sum_univ_three, hξ₁, hξ₂, covectorSquare_smul, covectorSquare_smul]
    convert three_slope_decomposition h01.ne (h01.trans h12).ne h12.ne H using 1
    ext i
    simp [Q, ξ, Pi.smul_apply, smul_smul, smul_eq_mul]
    ring
  · intro i
    fin_cases i <;> simp [Q]
    · exact hp₀
    · positivity
    · positivity
  · intro i
    fin_cases i
    · simpa [ξ] using good_weighted (w := 1) (by norm_num) hg₀
    · simpa [ξ] using good_weighted (w := 2) (by norm_num) hg₁
    · simpa [ξ] using good_weighted (w := 4) (by norm_num) hg₂
  · intro i j hij
    have h40 := good_neg h04
    have h60 := good_neg h06
    have h80 := good_neg h08
    simp only [neg_sub] at h40 h60 h80
    fin_cases i <;> fin_cases j <;> simp_all [add_comm]

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma continuous_secondQuadratic {n : ℕ} :
    Continuous (fun z : (Fin 3 → RVec n) × Base => secondQuadratic z.1 z.2) := by
  unfold secondQuadratic
  fun_prop

lemma isOpen_good {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {ξ : X → Base} (hB : Continuous B) (hξ : Continuous ξ) :
    IsOpen {p : X | Good (B p) (ξ p)} := by
  change IsOpen ({p : X | ξ p ≠ 0} ∩
    {p : X | secondQuadratic (B p) (-(ξ p).2, (ξ p).1) ≠ 0})
  apply (isOpen_ne_fun hξ continuous_const).inter
  apply isOpen_ne_fun _ continuous_const
  exact continuous_secondQuadratic.comp (hB.prodMk ((hξ.snd.neg).prodMk hξ.fst))



theorem positive_good_local_data {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {H₀ : X → PhaseMean.Tensor} (hB : Continuous B)
    (hH : Continuous H₀) (p : X) (hpB : B p ≠ 0)
    (hpH : 0 < H₀ p 0) (hpdet : 0 < H₀ p 0 * H₀ p 2 - (H₀ p 1)^2) :
    ∃ (ξ : Fin 3 → Base) (Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ) (U : Set X),
      IsOpen U ∧ p ∈ U ∧
      (∀ H, ∑ i : Fin 3, Q i H • covectorSquare (ξ i) = H) ∧
      (∀ x ∈ U, (∀ i, 0 < Q i (H₀ x)) ∧ (∀ i, Good (B x) (ξ i)) ∧
        (∀ i j, i ≠ j → Good (B x) (ξ i + ξ j) ∧ Good (B x) (ξ i - ξ j))) := by
  obtain ⟨ξ, Q, hdec, hpos, hgood, hcross⟩ := positive_good_phase_data hpB hpH hpdet
  let U : Set X := {x | (∀ i, 0 < Q i (H₀ x)) ∧ (∀ i, Good (B x) (ξ i)) ∧
    (∀ i j, i ≠ j → Good (B x) (ξ i + ξ j) ∧ Good (B x) (ξ i - ξ j))}
  have hU : IsOpen U := by
    apply IsOpen.and
    · simp only [ofPred_forall]
      apply isOpen_iInter_of_finite
      intro i
      exact isOpen_lt continuous_const ((Q i).continuous.comp hH)
    apply IsOpen.and
    · simp only [ofPred_forall]
      apply isOpen_iInter_of_finite
      intro i
      exact isOpen_good hB continuous_const
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro hij
    exact (isOpen_good hB continuous_const).and (isOpen_good hB continuous_const)
  exact ⟨ξ, Q, U, hU, ⟨hpos, hgood, hcross⟩, hdec, fun _ hx => hx⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
