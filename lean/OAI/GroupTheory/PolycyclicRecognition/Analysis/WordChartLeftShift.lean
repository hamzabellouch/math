import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartTranslations
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WordChartHeight
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartSmallProducts

namespace OAI

/-! # Exact changes of basepoint in nilpotent exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
open Module LieModule
open scoped Manifold

variable {L E G W I : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]

/-- Coordinates use the given global exponential chart and the actual
chosen basis; no topology on the abstract Lie algebra is needed. -/
def exponentialCoordinates {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (b : Basis (Fin n) ℝ L) : (Fin n → ℝ) ≃ₜ G :=
  (b.map e.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart

omit [IsTopologicalGroup G] in
@[simp] theorem exponentialCoordinates_apply {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (b : Basis (Fin n) ℝ L) (z : Fin n → ℝ) :
    exponentialCoordinates e chart b z = chart (e (b.equivFun.symm z)) := rfl

/-- The chart change determined by left multiplication by `k⁻¹`. -/
def wordChartLeftShift {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (source target : Basis (Fin n) ℝ L) (k : G) :
    C((Fin n → ℝ), (Fin n → ℝ)) where
  toFun z := (exponentialCoordinates e chart target).symm
    (k⁻¹ * exponentialCoordinates e chart source z)
  continuous_toFun := (exponentialCoordinates e chart target).symm.continuous.comp
    (continuous_const.mul (exponentialCoordinates e chart source).continuous)

theorem wordChartLeftShift_point {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (source target : Basis (Fin n) ℝ L) (k : G) (z : Fin n → ℝ) :
    exponentialCoordinates e chart target (wordChartLeftShift e chart source target k z) =
      k⁻¹ * exponentialCoordinates e chart source z :=
  (exponentialCoordinates e chart target).apply_symm_apply _

theorem wordChartLeftShift_change_basis {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (source target : Basis (Fin n) ℝ L) (k : G) (z : Fin n → ℝ) :
    wordChartLeftShift e chart source target k z =
      target.equivFun (source.equivFun.symm (wordChartLeftShift e chart source source k z)) := by
  apply (exponentialCoordinates e chart target).injective
  rw [wordChartLeftShift_point]
  simp only [exponentialCoordinates_apply, LinearEquiv.symm_apply_apply]
  exact (wordChartLeftShift_point e chart source source k z).symm

section NormBound

variable [Fintype I] [DecidableEq I]

/-- The exact group-defined shift satisfies the polynomial chart bound. -/
theorem exists_wordChartLeftShift_norm_bound
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    (X : I → L) {d : ℕ} (hd : lowerCentralSeries ℝ L L d = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : WordBasisSelections X (boundedBracketWords d))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (e (finiteDynkinPolynomial a ![x, y])) = Exp (e x) * Exp (e y))
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ h : L,
      let br := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) β)
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
      ‖br.equivFun h‖ ≤ 1 → ∀ z : Fin (finrank ℝ L) → ℝ, ‖z‖ ≤ R →
      ‖wordChartLeftShift e chart br br (Exp (e h)) z - z‖ ≤ C * ‖br.equivFun h‖ := by
  have hinj : Function.Injective Exp := funext hchart ▸ chart.injective
  obtain ⟨C, hC, hbound⟩ := exists_uniform_word_chart_translation_bound e Exp hExp hinj
    X hd b₀ β hβ a hm R
  refine ⟨C, hC, ?_⟩
  intro r hr h
  dsimp only
  let br := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) β)
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
  intro hh z hz
  have he : wordChartLeftShift e chart br br (Exp (e h)) z =
      br.equivFun (finiteDynkinPolynomial a ![-h, br.equivFun.symm z]) := by
    apply (exponentialCoordinates e chart br).injective
    rw [wordChartLeftShift_point]
    simp only [exponentialCoordinates_apply, LinearEquiv.symm_apply_apply, hchart, hm,
      map_neg, hExp.map_neg]
  rw [he]
  exact hbound r hr h hh z hz

/-- A fixed smaller ball is carried into the prescribed chart ball when
the normalized Cartan shift is small and the scales differ by at most two. -/
theorem exists_wordChartLeftShift_ball
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ v, chart v = Exp v)
    (X : I → L) {d : ℕ} (hd : lowerCentralSeries ℝ L L d = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : WordBasisSelections X (boundedBracketWords d))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (e (finiteDynkinPolynomial a ![x, y])) = Exp (e x) * Exp (e y))
    {R : ℝ} (hR : 0 < R) :
    ∃ ρ η : ℝ, 0 < ρ ∧ 0 < η ∧ ∀ r s : ℝ, 1 ≤ r → 0 < s → r ≤ 2 * s →
      ∀ h : L,
      let b := WordBasisSelections.basis X (boundedBracketWords d) β
      let br := exponentialRescaleBasis b
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
      let bs := exponentialRescaleBasis b
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log s)
      ‖br.equivFun h‖ ≤ η → ∀ z : Fin (finrank ℝ L) → ℝ, ‖z‖ ≤ ρ →
      ‖wordChartLeftShift e chart br bs (Exp (e h)) z‖ ≤ R := by
  let p := Finset.univ.sup (fun j => bracketWordLength (β.val j : FreeMagma I))
  have hp j : bracketWordExponent (fun _ : I => 1) (β.val j) ≤ (p : ℝ) := by
    rw [bracketWordExponent_one]
    exact_mod_cast Finset.le_sup (f := fun j => bracketWordLength (β.val j : FreeMagma I))
      (Finset.mem_univ j)
  let D : ℝ := 2 ^ p
  have hD : 0 < D := by dsimp [D]; positivity
  let ρ := R / (2 * D)
  have hρ : 0 < ρ := div_pos hR (by positivity)
  obtain ⟨C, hC, hbound⟩ := exists_wordChartLeftShift_norm_bound e Exp hExp chart hchart
    X hd b₀ β hβ a hm ρ
  let η := min 1 (ρ / (C + 1))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hρ (by linarith))
  refine ⟨ρ, η, hρ, hη, ?_⟩
  intro r s hr hs hrs h
  dsimp only
  let b := WordBasisSelections.basis X (boundedBracketWords d) β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let br := exponentialRescaleBasis b cost (Real.log r)
  let bs := exponentialRescaleBasis b cost (Real.log s)
  intro hh z hz
  have hh1 : ‖br.equivFun h‖ ≤ 1 := hh.trans (min_le_left _ _)
  have hhm : (C + 1) * ‖br.equivFun h‖ ≤ ρ := by
    have ht := (le_div_iff₀ (by linarith : 0 < C + 1)).mp (hh.trans (min_le_right _ _))
    simpa only [mul_comm] using ht
  have hshift := hbound r hr h hh1 z hz
  have hsmall : ‖wordChartLeftShift e chart br br (Exp (e h)) z‖ ≤ 2 * ρ := by
    have ht := norm_le_norm_sub_add (wordChartLeftShift e chart br br (Exp (e h)) z) z
    nlinarith [norm_nonneg (br.equivFun h)]
  rw [wordChartLeftShift_change_basis]
  have hc := norm_word_chart_change_le b cost p
    (fun j => by dsimp [cost]; rw [bracketWordExponent_one]; positivity)
    hp (by linarith) hs hrs
    (br.equivFun.symm (wordChartLeftShift e chart br br (Exp (e h)) z))
  calc
    _ ≤ D * ‖wordChartLeftShift e chart br br (Exp (e h)) z‖ :=
      hc.trans_eq (congrArg (fun v => D * ‖v‖)
        (br.equivFun.apply_symm_apply (wordChartLeftShift e chart br br (Exp (e h)) z)))
    _ ≤ D * (2 * ρ) := mul_le_mul_of_nonneg_left hsmall hD.le
    _ = R := by dsimp [ρ]; field_simp

end NormBound

variable [Fintype I] [DecidableEq I] [AddCommGroup W] [Module ℝ W]

/-- Height under this change of basepoint is exactly affine, at the two
physical scales. This identity is separate from metric compatibility. -/
theorem wordChartLeftShift_height
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (π : G →* Multiplicative W) (height : L →ₗ[ℝ] W)
    (hheight : ∀ v, (π (chart (e v))).toAdd = height v)
    (hkill : ∀ x y : L, height ⁅x, y⁆ = 0)
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (k : G)
    (z : Fin (finrank ℝ L) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let br := exponentialRescaleBasis b
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)
    let bs := exponentialRescaleBasis b
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log s)
    s • height (b.equivFun.symm (wordChartLeftShift e chart br bs k z)) =
      r • height (b.equivFun.symm z) - (π k).toAdd := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let br := exponentialRescaleBasis b
    (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)
  let bs := exponentialRescaleBasis b
    (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log s)
  have hp := congrArg (fun g => (π g).toAdd) (wordChartLeftShift_point e chart br bs k z)
  simp only [exponentialCoordinates_apply, hheight, map_mul, map_inv,
    toAdd_mul, toAdd_inv] at hp
  rw [word_length_chart_height X S β height hkill hs,
    word_length_chart_height X S β height hkill hr] at hp
  exact hp.trans (by abel)

end PolycyclicRecognition

end

end OAI
