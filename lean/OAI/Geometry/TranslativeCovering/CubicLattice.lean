import OAI.Geometry.TranslativeCovering.Periodization

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace CubicLattice
open Module Set MeasureTheory TranslativeCovering
open scoped ENNReal BigOperators Classical
noncomputable def basis (n : ℕ) (L : ℝ) (hL : 0<L) : Basis (Fin n) ℝ (Space n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.isUnitSMul (fun _ => isUnit_iff_ne_zero.mpr (by positivity : (2*L:ℝ)≠0))
lemma basis_apply {n : ℕ} {L : ℝ} (hL : 0<L) (i : Fin n) :
    basis n L hL i = (2*L) • (EuclideanSpace.basisFun (Fin n) ℝ) i := by
  exact Basis.isUnitSMul_apply _ i
lemma volume_domain {n : ℕ} {L : ℝ} (hL : 0<L) :
    volume (ZSpan.fundamentalDomain (basis n L hL)) = ENNReal.ofReal ((2*L)^n) := by
  let b₀ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hv : volume (ZSpan.fundamentalDomain b₀)=1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀ volume)]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).volume_parallelepiped
  rw [ZSpan.measure_fundamentalDomain (basis n L hL) volume b₀,hv,mul_one]
  congr 1
  have he : (basis n L hL : Fin n → Space n) = fun i => (2*L) • b₀ i := funext (basis_apply hL)
  rw [he,AlternatingMap.map_smul_univ,Basis.det_self]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  exact abs_of_nonneg (pow_nonneg (by positivity) _)

lemma period_mem {n : ℕ} {L : ℝ} (hL : 0<L) (z : Fin n → ℤ) :
    cubePeriod L z ∈ Submodule.span ℤ (Set.range (basis n L hL)) := by
  have he : cubePeriod L z = ∑ i,(z i) • basis n L hL i := by
    ext j
    simp [cubePeriod,basis_apply,EuclideanSpace.basisFun_apply,
      Pi.single_apply,mul_ite]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

lemma covering {n : ℕ} {K : Set (Space n)} (P : CubicCover K) :
    ∀ y,∃ (i : P.centers) (l : Submodule.span ℤ (Set.range (basis n P.L P.positive))),
      y-i.val-l.val ∈ K := by
  intro y
  obtain ⟨x,hx,hy⟩ := P.covers y
  obtain ⟨s,hs,z,rfl⟩ := hx
  refine ⟨⟨s,hs⟩,⟨cubePeriod P.L z,period_mem P.positive z⟩,?_⟩
  simpa only [sub_add_eq_sub_sub] using hy
end CubicLattice

end OAI
