import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactDepthReductionTwo

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

lemma exists_precompact_open_inside {U : Set Coord3} (hU : IsOpen U)
    {p : Coord3} (hp : p ∈ U) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) := by
  obtain ⟨K, hpK, hKU, hK⟩ := local_compact_nhds (hU.mem_nhds hp)
  have he : closure (interior K) ⊆ K := hK.isClosed.closure_subset_iff.mpr interior_subset
  exact ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.mpr hpK,
    he.trans hKU, hK.of_isClosed_subset isClosed_closure he⟩

def CompactCompatibleReplacement.unchanged
    (μ : Measure Coord3) (O : Set Coord3) (u : Coord3 → Fin 2 → ℝ)
    (A : Coord3 → Symmetric3)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) O) :
    CompactCompatibleReplacement μ O u A where
  du := 0
  dF := 0
  tensor := A
  smooth_du := contDiff_const
  compact_du := by simp [HasCompactSupport]
  support_du := by simp
  smooth_dF := contDiff_const
  compact_dF := by simp [HasCompactSupport]
  support_dF := by simp
  cauchy_dF := by
    intro j ψ _
    change (∫ x, fderiv ℝ ψ x (0 : Coord3) ∂μ) = 0
    simp
  smooth_tensor := hA
  constitutive := by intro x _; simp only [Pi.zero_apply, add_zero, conductivityFlux]

lemma gradientColumns_zero_fderiv_of_constant {O : Set Coord3} (hO : IsOpen O)
    {u : Coord3 → Fin 2 → ℝ} {κ : Fin 2 → ℝ}
    (he : ∀ x ∈ O, u x = κ) {x : Coord3} (hx : x ∈ O) :
    gradientColumns (fderiv ℝ u x) = 0 := by
  rw [fderiv_eq_of_eqOn_open hO he hx]
  have hz : fderiv ℝ (fun _ : Coord3 => κ) x = 0 := congrFun (fderiv_const (𝕜 := ℝ) κ) x
  rw [hz]
  rfl

def CompactCompatibleReplacement.constantRank
    (μ : Measure Coord3) {O : Set Coord3} (hO : IsOpen O)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {κ : Fin 2 → ℝ} (he : ∀ x ∈ O, u x = κ) (S : Symmetric3) :
    CompactCompatibleReplacement μ O u A where
  du := 0
  dF := 0
  tensor := fun _ => S
  smooth_du := contDiff_const
  compact_du := by simp [HasCompactSupport]
  support_du := by simp
  smooth_dF := contDiff_const
  compact_dF := by simp [HasCompactSupport]
  support_dF := by simp
  cauchy_dF := by
    intro j ψ _
    change (∫ x, fderiv ℝ ψ x (0 : Coord3) ∂μ) = 0
    simp
  smooth_tensor := contDiffOn_const
  constitutive := by
    intro x hx
    simp only [Pi.zero_apply, add_zero, conductivityFlux,
      gradientColumns_zero_fderiv_of_constant hO he hx, Matrix.mul_zero]

lemma spectral_depth_subset {a b : ℝ} {T : Set DiagonalTriple}
    (hsub : ∀ d ∈ T, IsFiniteLaminate a b d) (n : ℕ) :
    spectralExtension (depthClass T n) ⊆ matrixFiniteLaminate a b := by
  rintro S ⟨Q, hQ, d, hd, hre⟩
  exact ⟨Q, hQ, d, depthClass_subset_laminate hsub n d hd, hre⟩

theorem exists_compact_depth_reduction_regular_nontrivial
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞)) u U)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => (A x).val) U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hr : TwoFieldRankRegular u U)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    {p : Coord3} (hpU : p ∈ U) {n : ℕ}
    (hp : A p ∈ spectralExtension (depthClass T (n+1)))
    (hn : A p ∉ spectralExtension (depthClass T n))
    (hsc : (spectralExtension (depthClass T n)).Nonempty) :
    ∃ W : Set Coord3, IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ ε : ℝ, 0 < ε →
      ∃ R : CompactCompatibleReplacement μ O u A,
        TwoFieldRankRegular (fun x => u x+R.du x) O ∧
        (∀ x ∈ O, R.tensor x ∈ matrixFiniteLaminate a b) ∧
        μ {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} ≤ ENNReal.ofReal ε := by
  rcases hr with hr | hr | ⟨κ, hκ⟩
  · obtain ⟨W, hW, hpW, hWU, hWc, hop⟩ := exists_compact_depth_reduction_two μ u A
      hU hUb hu hA hdiv ha hT hsub hperm hpU
      (gradientColumns_surjective _ (hr p hpU)) hp hn
    refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
    intro O hO hOW ε hε
    obtain ⟨R, hRG, hbad⟩ := hop O hO hOW ε hε
    exact ⟨R.forgetRank, Or.inl R.rank, hRG, hbad⟩
  · obtain ⟨v, l, κ, hv, ⟨j, hj⟩, hvd, he⟩ := hr
    obtain ⟨i, hi⟩ := exists_independent_pairedPotential_at
      ((hv.differentiableOn (by simp) p hpU).differentiableAt (hU.mem_nhds hpU)) (hvd p hpU)
    let V := pairedPotential v i
    have hV : ContDiffOn ℝ (↑(⊤ : ℕ∞)) V U := pairedPotential_contDiffOn hv i
    have heV : ∀ x ∈ U, ∀ j, u x j = l j * V x 0 + κ j := he
    have hdivV : ∀ k ∈ ({0} : Set (Fin 2)), ∀ (ψ : Coord3 → ℝ),
        ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        (∫ x, fderiv ℝ ψ x ((conductivityFlux V A x).col k) ∂μ) = 0 := by
      intro k hk
      have hk0 : k = 0 := Set.mem_singleton_iff.mp hk
      subst k
      exact active_flux_harmonic_of_affine μ hU A heV (hV.differentiableOn (by simp)) hj (hdiv j)
    obtain ⟨W, hW, hpW, hWU, hWc, hop⟩ := exists_compact_depth_reduction_selected {0} μ V A
      hU hUb hV hA hdivV ha hT hsub hperm hpU hi hp hn
    refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
    intro O hO hOW ε hε
    obtain ⟨R, hRG, hbad⟩ := hop O hO hOW ε hε
    have hOU := hOW.trans (subset_closure.trans hWU)
    have hVO := hV.mono hOU
    have heO : ∀ x ∈ O, ∀ j, u x j = l j * V x 0 + κ j := fun x hx => heV x (hOU hx)
    let P := R.affineTransfer hO heO hVO
    refine ⟨P, Or.inr (Or.inl ⟨fun x => (V x+R.du x) 0, l, κ,
      contDiffOn_pi.mp (hVO.add R.smooth_du.contDiffOn) 0, ⟨j, hj⟩, ?_, ?_⟩), hRG, hbad⟩
    · intro x hx
      exact column_derivative_ne_zero_of_independent hO
        ((hVO.add R.smooth_du.contDiffOn).differentiableOn (by simp)) hx (R.rank x hx) 0
    · exact R.affineTransfer_relation hO heO hVO
  · obtain ⟨W, hW, hpW, hWU, hWc⟩ := exists_precompact_open_inside hU hpU
    obtain ⟨S, hS⟩ := hsc
    refine ⟨W, hW, hpW, hWU, hWc, ?_⟩
    intro O hO hOW ε _
    have hOU := hOW.trans (subset_closure.trans hWU)
    let R := CompactCompatibleReplacement.constantRank μ hO u A
      (fun x hx => hκ x (hOU hx)) S
    refine ⟨R, ?_, fun _ _ => spectral_depth_subset hsub n hS, ?_⟩
    · exact Or.inr (Or.inr ⟨κ, fun x hx => by
        change u x + 0 = κ
        rw [add_zero, hκ x (hOU hx)]⟩)
    · have he : {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} = ∅ := by
        ext x
        simp only [R, CompactCompatibleReplacement.constantRank, hS, not_true_eq_false,
          and_false, mem_ofPred_eq, mem_empty_iff_false]
      rw [he, measure_empty]
      exact bot_le

end ScalarConductivity

end

end OAI
