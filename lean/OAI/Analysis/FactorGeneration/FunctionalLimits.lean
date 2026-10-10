import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.MetricSpace.ProperSpace
import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

noncomputable section

namespace Generator

/-! A functional bounded by a Hilbert-valued linear map factors through one
inner product. The proof uses the actual range, Hahn--Banach, and Riesz. -/
namespace Tracial

section
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem exists_inner_factor_of_bound (F : E →ₗ[ℂ] V) (φ : E →ₗ[ℂ] ℂ)
    (C : ℝ) (hb : ∀ x : E, ‖φ x‖ ≤ C*‖F x‖) :
    ∃ η : V, ∀ x : E, φ x=inner ℂ η (F x) := by
  classical
  have hfiber {x y : E} (h : F x=F y) : φ x=φ y := by
    have hb' := hb (x-y)
    rw [map_sub,map_sub,h,sub_self,norm_zero,mul_zero] at hb'
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb' (norm_nonneg _)))
  have hex (z : LinearMap.range F) : ∃ x : E, F x=z.val := z.property
  choose a ha using hex
  let L : LinearMap.range F →ₗ[ℂ] ℂ :=
    { toFun := fun z => φ (a z)
      map_add' := by
        intro z w
        calc φ (a (z+w)) = φ (a z+a w) := hfiber (by rw [ha,map_add,ha,ha]; rfl)
          _ = φ (a z)+φ (a w) := map_add φ _ _
      map_smul' := by
        intro c z
        calc φ (a (c • z)) = φ (c • a z) := hfiber (by rw [ha,map_smul,ha]; rfl)
          _ = c • φ (a z) := map_smul φ _ _ }
  have hL (x : E) : L ⟨F x,LinearMap.mem_range_self F x⟩=φ x := hfiber (ha _)
  let l : LinearMap.range F →L[ℂ] ℂ := L.mkContinuous C (fun z => by
    have h := hb (a z)
    rw [ha] at h
    exact h)
  obtain ⟨g,hg,_⟩ := exists_extension_norm_eq (LinearMap.range F) l
  refine ⟨(InnerProductSpace.toDual ℂ V).symm g,?_⟩
  intro x
  rw [InnerProductSpace.toDual_symm_apply]
  exact ((hg ⟨F x,LinearMap.mem_range_self F x⟩).trans (hL x)).symm

end

/-! Pointwise ultrafilter limits of uniformly bounded complex functionals.
Compactness is used only for scalar closed balls, with no separability premise. -/
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_bounded_functional_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (f : ι → E →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) :
    ∃ φ : E →L[ℂ] ℂ, ‖φ‖ ≤ C ∧
      ∀ x : E, Tendsto (fun i => f i x) (ω : Filter ι) (𝓝 (φ x)) := by
  have hex (x : E) : ∃ z : ℂ, ‖z‖ ≤ C*‖x‖ ∧
      Tendsto (fun i => f i x) (ω : Filter ι) (𝓝 z) := by
    obtain ⟨z,hz,ht⟩ := (isCompact_closedBall (0 : ℂ) (C*‖x‖)).ultrafilter_le_nhds
      (ω.map (fun i => f i x)) (by
        apply le_principal_iff.mpr
        change ∀ᶠ i in (ω : Filter ι), f i x ∈ Metric.closedBall 0 (C*‖x‖)
        exact Eventually.of_forall (fun i => by
          simpa only [Metric.mem_closedBall,dist_zero_right] using
            (f i).le_of_opNorm_le (hf i) x))
    exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz,ht⟩
  choose v hv ht using hex
  have hadd (x y : E) : v (x+y)=v x+v y := by
    apply tendsto_nhds_unique (ht (x+y))
    simpa only [map_add] using (ht x).add (ht y)
  have hsmul (c : ℂ) (x : E) : v (c • x)=c • v x := by
    apply tendsto_nhds_unique (ht (c • x))
    simpa only [map_smul,smul_eq_mul] using (ht x).const_mul c
  let φ : E →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := v, map_add' := hadd, map_smul' := hsmul } C hv
  exact ⟨φ,φ.opNorm_le_bound hC hv,ht⟩

end Tracial

/-! A separable normed space has a countable family of bounded linear
functionals separating its points. All functionals are constructed by
Hahn--Banach at a countable dense family of vectors. -/
section
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace.SeparableSpace E]

theorem exists_countable_total_dual :
    ∃ g : ℕ → StrongDual ℂ E, (∀ n, ‖g n‖ ≤ 1) ∧
      ∀ x : E, (∀ n, g n x = 0) → x = 0 := by
  choose g hg he using fun n => exists_dual_vector'' ℂ (TopologicalSpace.denseSeq E n)
  refine ⟨g, hg, fun x hx => ?_⟩
  by_contra hzero
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hzero
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq E).exists_dist_lt x
    (by positivity : 0 < ‖x‖ / 3)
  have hb : ‖TopologicalSpace.denseSeq E n‖ ≤ ‖TopologicalSpace.denseSeq E n - x‖ := by
    calc
      ‖TopologicalSpace.denseSeq E n‖ =
          ‖g n (TopologicalSpace.denseSeq E n - x)‖ := by
        simp only [map_sub, hx, sub_zero, he, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖g n‖ * ‖TopologicalSpace.denseSeq E n - x‖ := (g n).le_opNorm _
      _ ≤ ‖TopologicalSpace.denseSeq E n - x‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hg n) (norm_nonneg _)
  have ht := norm_le_norm_add_norm_sub (TopologicalSpace.denseSeq E n) x
  rw [norm_sub_rev] at ht
  rw [dist_eq_norm] at hn
  rw [norm_sub_rev] at hb
  linarith

end

/-! Hermitian symmetrization and complex polarization for bounded functionals.
No tracial functional or finite factor is supplied to these algebraic lemmas. -/
open scoped CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance polarizationCStar : CStarAlgebra M.toStarSubalgebra := {}

def conjugateFunctional (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    M.toStarSubalgebra →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => star (φ (star x))
      map_add' := by intros; simp only [star_add,map_add]
      map_smul' := by intros; simp only [star_smul,map_smul,star_star,RingHom.id_apply] }
    ‖φ‖ (fun x => by
      change ‖star (φ (star x))‖ ≤ ‖φ‖*‖x‖
      simpa only [norm_star] using φ.le_opNorm (star x))

theorem conjugateFunctional_apply (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) : conjugateFunctional φ x=star (φ (star x)) := rfl

theorem conjugateFunctional_norm_le (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    ‖conjugateFunctional φ‖ ≤ ‖φ‖ := by
  apply (conjugateFunctional φ).opNorm_le_bound (norm_nonneg φ)
  intro x
  simpa only [conjugateFunctional_apply,norm_star] using φ.le_opNorm (star x)

def hermitianFunctional (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    M.toStarSubalgebra →L[ℂ] ℂ := (1/2 : ℂ) • (φ+conjugateFunctional φ)

theorem hermitianFunctional_apply (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) : hermitianFunctional φ x=(φ x+star (φ (star x)))/2 := by
  simp only [hermitianFunctional,smul_apply,add_apply,
    conjugateFunctional_apply,smul_eq_mul]
  ring

theorem hermitianFunctional_norm_le (φ : M.toStarSubalgebra →L[ℂ] ℂ) :
    ‖hermitianFunctional φ‖ ≤ ‖φ‖ := by
  change ‖(1/2 : ℂ) • (φ+conjugateFunctional φ)‖ ≤ _
  rw [norm_smul]
  have h := norm_add_le φ (conjugateFunctional φ)
  have h' := conjugateFunctional_norm_le φ
  norm_num
  linarith

theorem hermitianFunctional_star (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) : hermitianFunctional φ (star x)=star (hermitianFunctional φ x) := by
  simp only [hermitianFunctional_apply,star_star,star_div₀,star_add,star_ofNat]
  rw [add_comm]

theorem hermitianFunctional_selfAdjoint (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    hermitianFunctional φ x=((φ x).re : ℂ) := by
  rw [hermitianFunctional_apply,hx.star_eq]
  exact (Complex.re_eq_add_conj _).symm

theorem hermitianFunctional_one (φ : M.toStarSubalgebra →L[ℂ] ℂ) (hφ : φ 1=1) :
    hermitianFunctional φ 1=1 := by
  rw [hermitianFunctional_selfAdjoint φ 1 (IsSelfAdjoint.one _),hφ]
  rfl

/-- Equality of complex quadratic values polarizes to the full trace identity. -/
theorem functional_trace_of_quadratic (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hφ : ∀ x : M.toStarSubalgebra, φ (star x*x)=φ (x*star x))
    (x y : M.toStarSubalgebra) : φ (x*y)=φ (y*x) := by
  have hp := hφ (x+star y)
  have hi := hφ (x+Complex.I • star y)
  simp only [star_add,star_star,add_mul,mul_add,map_add] at hp
  simp only [star_add,star_smul,star_star,add_mul,mul_add,smul_mul_assoc,
    mul_smul_comm,map_add,map_smul,smul_eq_mul] at hi
  rw [hφ x,← hφ y] at hp hi
  simp only [show star Complex.I = -Complex.I from Complex.conj_I] at hi
  linear_combination (norm := ring_nf) -(1/2 : ℂ)*hp - (Complex.I/2)*hi
  simp only [Complex.I_sq]
  ring

theorem hermitianFunctional_trace (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hφ : ∀ x : M.toStarSubalgebra, (φ (star x*x)).re=(φ (x*star x)).re)
    (x y : M.toStarSubalgebra) : hermitianFunctional φ (x*y)=hermitianFunctional φ (y*x) := by
  apply functional_trace_of_quadratic
  intro z
  rw [hermitianFunctional_selfAdjoint φ _ (IsSelfAdjoint.star_mul_self z),
    hermitianFunctional_selfAdjoint φ _ (IsSelfAdjoint.mul_star_self z),hφ z]

end Tracial

end Generator

end

end OAI
