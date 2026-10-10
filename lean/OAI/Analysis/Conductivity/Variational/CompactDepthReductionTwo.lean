import Mathlib
import OAI.Analysis.Conductivity.Branching.JoinHull
import OAI.Analysis.Conductivity.Variational.ConjugateDiagonal
import OAI.Analysis.Conductivity.Variational.CompactCompatibleReplacement

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem exists_compact_depth_reduction_two
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    {p : Coord3} (hpU : p ∈ U)
    (hD : Function.Surjective (fderiv ℝ u p)) {n : ℕ}
    (hp : A p ∈ spectralExtension (depthClass T (n+1)))
    (hn : A p ∉ spectralExtension (depthClass T n)) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ R : CompactTwoFieldReplacement μ O u A,
        (∀ x ∈ O, R.tensor x ∈ matrixFiniteLaminate a b) ∧
        μ {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} ≤ ENNReal.ofReal ε := by
  obtain ⟨Q, hQ, d, hd, hrep⟩ := hp
  have hdn : d ∉ depthClass T n := fun h => hn ⟨Q, hQ, d, h, hrep⟩
  obtain ⟨i, θ, α, β, hθ, hθ1, hα, hβ, he, _⟩ := depthClass_plan hsub hd hdn
  have hre : conjugateDiagonal Q (coordinateJoin i θ α β) = A p := by
    apply Subtype.ext
    simpa only [conjugateDiagonal, he] using hrep.symm
  obtain ⟨v, L, B, η, c, m, C, hLv, hB, hBn, hη, hη1, hm, hpath, hC, hCs,
    hdet, hconst, hCG, hCa, hCb⟩ := spectral_join_plan ha
      (depthClass_subset_laminate hsub n) i hα hβ hθ hθ1 hQ
  rw [hre] at hconst
  have hTo : IsOpen (spectralExtension (depthClass T n)) :=
    isOpen_spectralExtension (isOpen_depthClass ha hT hsub n) (depthClass_permute hperm n)
  let G := endpointGraph (-η) (1-η) (matrixFiniteLaminate a b)
    (spectralExtension (depthClass T n)) (spectralExtension (depthClass T n))
  have hGo : IsOpen G := isOpen_endpointGraph _ _ (isOpen_matrixFiniteLaminate ha) hTo hTo
  have hGC : ∀ z ∈ Icc (-η) (1-η), (z, C z) ∈ G :=
    path_mem_endpointGraph _ _ C hCG hCa hCb
  obtain ⟨W, hW, hpW, hWU, hWc, hop⟩ := exists_locally_smooth_compact_split μ u A
    hU hUb hpU hu hA hdiv hD v L hLv B hB hBn hη hη1 hm hpath C hC hCs hdet hconst hGo hGC
  refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
  intro O hO hOW ε hε
  obtain ⟨R, q, _, _, hqG, hqm⟩ := hop O hO hOW ε hε
  refine ⟨R, fun x hx => (hqG x hx).1, le_trans (measure_mono ?_) hqm⟩
  intro x hx
  refine ⟨hx.1, ?_, ?_⟩
  · exact (hqG x hx.1).2.1.resolve_right hx.2
  · exact (hqG x hx.1).2.2.resolve_right hx.2

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

theorem exists_compact_depth_reduction_selected
    (J : Set (Fin 2))
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j ∈ J, ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    {p : Coord3} (hpU : p ∈ U)
    (hD : Function.Surjective (fderiv ℝ u p)) {n : ℕ}
    (hp : A p ∈ spectralExtension (depthClass T (n+1)))
    (hn : A p ∉ spectralExtension (depthClass T n)) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ R : CompactSelectedReplacement J μ O u A,
        (∀ x ∈ O, R.tensor x ∈ matrixFiniteLaminate a b) ∧
        μ {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} ≤ ENNReal.ofReal ε := by
  obtain ⟨Q, hQ, d, hd, hrep⟩ := hp
  have hdn : d ∉ depthClass T n := fun h => hn ⟨Q, hQ, d, h, hrep⟩
  obtain ⟨i, θ, α, β, hθ, hθ1, hα, hβ, he, _⟩ := depthClass_plan hsub hd hdn
  have hre : conjugateDiagonal Q (coordinateJoin i θ α β) = A p := by
    apply Subtype.ext
    simpa only [conjugateDiagonal, he] using hrep.symm
  obtain ⟨v, L, B, η, c, m, C, hLv, hB, hBn, hη, hη1, hm, hpath, hC, hCs,
    hdet, hconst, hCG, hCa, hCb⟩ := spectral_join_plan ha
      (depthClass_subset_laminate hsub n) i hα hβ hθ hθ1 hQ
  rw [hre] at hconst
  have hTo : IsOpen (spectralExtension (depthClass T n)) :=
    isOpen_spectralExtension (isOpen_depthClass ha hT hsub n) (depthClass_permute hperm n)
  let G := endpointGraph (-η) (1-η) (matrixFiniteLaminate a b)
    (spectralExtension (depthClass T n)) (spectralExtension (depthClass T n))
  have hGo : IsOpen G := isOpen_endpointGraph _ _ (isOpen_matrixFiniteLaminate ha) hTo hTo
  have hGC : ∀ z ∈ Icc (-η) (1-η), (z, C z) ∈ G :=
    path_mem_endpointGraph _ _ C hCG hCa hCb
  obtain ⟨W, hW, hpW, hWU, hWc, hop⟩ := exists_locally_smooth_selected_split J μ u A
    hU hUb hpU hu hA hdiv hD v L hLv B hB hBn hη hη1 hm hpath C hC hCs hdet hconst hGo hGC
  refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
  intro O hO hOW ε hε
  obtain ⟨R, q, _, _, hqG, hqm⟩ := hop O hO hOW ε hε
  refine ⟨R, fun x hx => (hqG x hx).1, le_trans (measure_mono ?_) hqm⟩
  intro x hx
  refine ⟨hx.1, ?_, ?_⟩
  · exact (hqG x hx.1).2.1.resolve_right hx.2
  · exact (hqG x hx.1).2.2.resolve_right hx.2

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma gradientColumns_surjective {m : Type*} [Fintype m] [DecidableEq m]
    (D : Coord3 →L[ℝ] (m → ℝ))
    (hD : LinearIndependent ℝ (gradientColumns D).col) : Function.Surjective D := by
  let E := gradientColumns D
  have hh : Eᵀ * (((Eᵀ * E)⁻¹ * Eᵀ)ᵀ) = 1 := by
    rw [← Matrix.transpose_mul, gram_leftInverse E hD, Matrix.transpose_one]
  have hs := Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨_, hh⟩
  intro y
  obtain ⟨x, hx⟩ := hs y
  exact ⟨x, (gradientColumns_apply D x).symm.trans hx⟩

lemma exists_independent_pairedPotential_at {u : Coord3 → ℝ} {p : Coord3}
    (hu : DifferentiableAt ℝ u p) (hp : fderiv ℝ u p ≠ 0) :
    ∃ j : Fin 3, Function.Surjective (fderiv ℝ (pairedPotential u j) p) := by
  obtain ⟨i, hi⟩ := exists_coordinate_nonzero hp
  obtain ⟨j, hji⟩ := exists_ne i
  refine ⟨j, ?_⟩
  rw [(pairedPotential_hasFDerivAt hu.hasFDerivAt j).fderiv]
  exact pairedFunctional_surjective hi hji.symm

lemma pairedPotential_contDiffOn {u : Coord3 → ℝ} {O : Set Coord3}
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u O) (j : Fin 3) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (pairedPotential u j) O := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact hu
  · exact (contDiff_apply ℝ ℝ j).contDiffOn

lemma column_derivative_ne_zero_of_independent {O : Set Coord3} (hO : IsOpen O)
    {v : Coord3 → Fin 2 → ℝ} (hv : DifferentiableOn ℝ v O)
    {x : Coord3} (hx : x ∈ O)
    (hr : LinearIndependent ℝ (gradientColumns (fderiv ℝ v x)).col) (j : Fin 2) :
    fderiv ℝ (fun y => v y j) x ≠ 0 := by
  intro hz
  have hh := ((ContinuousLinearMap.proj j).hasFDerivAt.comp x
    ((hv x hx).differentiableAt (hO.mem_nhds hx)).hasFDerivAt).fderiv
  have hzero : (gradientColumns (fderiv ℝ v x)).col j = 0 := by
    ext i
    have h := congrArg (fun L : Coord3 →L[ℝ] ℝ => L (Pi.single i 1)) (hh.symm.trans hz)
    exact h
  exact (hr.ne_zero j) hzero

lemma conductivityFlux_affine_column {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {l κ : Fin 2 → ℝ} (A : Coord3 → Symmetric3)
    (he : ∀ x ∈ O, ∀ j, u x j = l j * v x 0 + κ j)
    (hv : DifferentiableOn ℝ v O) {x : Coord3} (hx : x ∈ O) (j : Fin 2) :
    (conductivityFlux u A x).col j = l j • (conductivityFlux v A x).col 0 := by
  ext i
  change (∑ k, (A x).val i k * gradientColumns (fderiv ℝ u x) k j) =
    l j * ∑ k, (A x).val i k * gradientColumns (fderiv ℝ v x) k 0
  simp_rw [gradientColumns_affine_column hO he hv hx]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma active_flux_harmonic_of_affine
    (μ : Measure Coord3) {O : Set Coord3} (hO : IsOpen O)
    {u v : Coord3 → Fin 2 → ℝ} {l κ : Fin 2 → ℝ} (A : Coord3 → Symmetric3)
    (he : ∀ x ∈ O, ∀ j, u x j = l j * v x 0 + κ j)
    (hv : DifferentiableOn ℝ v O) {j : Fin 2} (hj : l j ≠ 0)
    (hdiv : ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ O → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0) :
    ∀ (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ O → (∫ x, fderiv ℝ ψ x ((conductivityFlux v A x).col 0) ∂μ) = 0 := by
  intro ψ hψ hc hs
  have heq : (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) =
      l j * ∫ x, fderiv ℝ ψ x ((conductivityFlux v A x).col 0) ∂μ := by
    rw [derivative_test_integral_congr μ ψ _
      (fun x => l j • (conductivityFlux v A x).col 0)
      (fun x hx => conductivityFlux_affine_column hO A he hv (hs hx) j)]
    simp_rw [map_smul, smul_eq_mul]
    exact integral_const_mul _ _
  exact (mul_eq_zero.mp (heq.symm.trans (hdiv ψ hψ hc hs))).resolve_left hj

def TwoFieldRankRegular (u : Coord3 → Fin 2 → ℝ) (O : Set Coord3) : Prop :=
  (∀ x ∈ O, LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col) ∨
  (∃ (v : Coord3 → ℝ) (l κ : Fin 2 → ℝ),
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) v O ∧ (∃ j, l j ≠ 0) ∧
    (∀ x ∈ O, fderiv ℝ v x ≠ 0) ∧
    (∀ x ∈ O, ∀ j, u x j = l j * v x + κ j)) ∨
  ∃ κ : Fin 2 → ℝ, ∀ x ∈ O, u x = κ

lemma TwoFieldRankRegular.mono {u : Coord3 → Fin 2 → ℝ} {O W : Set Coord3}
    (h : TwoFieldRankRegular u O) (hW : W ⊆ O) : TwoFieldRankRegular u W := by
  rcases h with h | h | ⟨κ, hκ⟩
  · exact Or.inl (fun x hx => h x (hW hx))
  · obtain ⟨v, l, κ, hv, hl, hd, he⟩ := h
    exact Or.inr (Or.inl ⟨v, l, κ, hv.mono hW, hl, fun x hx => hd x (hW hx),
      fun x hx => he x (hW hx)⟩)
  · exact Or.inr (Or.inr ⟨κ, fun x hx => hκ x (hW hx)⟩)

end ScalarConductivity

end

end OAI
