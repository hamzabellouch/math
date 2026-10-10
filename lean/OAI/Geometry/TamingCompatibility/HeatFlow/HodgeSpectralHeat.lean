import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeResolventParameters

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include D hD in

theorem hodgeSpectralSum : IsHilbertSum ℝ
    (fun x : ℝ => Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x)
    (fun x => (Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal _ (hodgeResolvent_symmetric A J α hs ht 1).orthogonalFamily_eigenspaces
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    hodgeResolvent_eigenspaces_total A J α hs ht D hD]
  simp

def hodgeSpectralRate (x : ℝ) : ℝ := max 0 (x⁻¹-1)

def hodgeHeatMultiplier (t x : ℝ) : ℝ := Real.exp (-(max t 0) * hodgeSpectralRate x)

lemma hodgeHeatMultiplier_pos (t x : ℝ) : 0 < hodgeHeatMultiplier t x := Real.exp_pos _
lemma hodgeHeatMultiplier_le_one (t x : ℝ) : hodgeHeatMultiplier t x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_max_right _ _)) (le_max_left _ _)

lemma hodgeHeatMultiplier_add (t s x : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    hodgeHeatMultiplier (t+s) x = hodgeHeatMultiplier t x * hodgeHeatMultiplier s x := by
  simp only [hodgeHeatMultiplier, max_eq_left ht, max_eq_left hs, max_eq_left (add_nonneg ht hs)]
  rw [show -(t+s)*hodgeSpectralRate x = -t*hodgeSpectralRate x + -s*hodgeSpectralRate x by ring,
    Real.exp_add]

def hodgeHeatDiagonal (t : ℝ) :
    lp (fun x : ℝ => Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x) 2 →L[ℝ]
    lp (fun x : ℝ => Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x) 2 :=
  lp.mapCLM 2 (fun x => hodgeHeatMultiplier t x • ContinuousLinearMap.id ℝ _) zero_le_one (by
    intro x
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp only [smul_apply, ContinuousLinearMap.id_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (hodgeHeatMultiplier_pos t x), one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hodgeHeatMultiplier_le_one t x))

lemma hodgeHeatDiagonal_apply (t : ℝ)
    (f : lp (fun x : ℝ => Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x) 2)
    (x : ℝ) : hodgeHeatDiagonal A J α hs ht t f x = hodgeHeatMultiplier t x • f x := rfl

def hodgeSpectralHeat (t : ℝ) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  E.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((hodgeHeatDiagonal A J α hs ht t).comp E.toContinuousLinearEquiv.toContinuousLinearMap)

lemma hodgeSpectralHeat_repr (t : ℝ) (f : L2 A J α hs ht true) (x : ℝ) :
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
      (hodgeSpectralHeat A J α hs ht D hD t f) x = hodgeHeatMultiplier t x •
        (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv f x := by
  change ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
    ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv.symm
      (hodgeHeatDiagonal A J α hs ht t
        ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv f)))) x = _
  rw [LinearIsometryEquiv.apply_symm_apply, hodgeHeatDiagonal_apply]

lemma hodgeSpectralHeat_zero : hodgeSpectralHeat A J α hs ht D hD 0 = 1 := by
  ext f
  apply (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv.injective
  ext x
  rw [hodgeSpectralHeat_repr]
  simp only [hodgeHeatMultiplier, max_self, neg_zero, zero_mul, Real.exp_zero, one_smul,
    one_apply_eq_self]

lemma hodgeSpectralHeat_add (t s : ℝ) (ht' : 0 ≤ t) (hs' : 0 ≤ s) :
    hodgeSpectralHeat A J α hs ht D hD (t+s) =
      hodgeSpectralHeat A J α hs ht D hD t * hodgeSpectralHeat A J α hs ht D hD s := by
  ext f
  apply (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv.injective
  ext x
  simp only [mul_apply_eq_comp, hodgeSpectralHeat_repr,
    hodgeHeatMultiplier_add t s x ht' hs', mul_smul]

lemma hodgeSpectralHeat_norm_le (t : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeSpectralHeat A J α hs ht D hD t f‖ ≤ ‖f‖ := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  rw [← E.norm_map (hodgeSpectralHeat A J α hs ht D hD t f), ← E.norm_map f]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro x
  rw [hodgeSpectralHeat_repr, norm_smul, Real.norm_eq_abs,
    abs_of_pos (hodgeHeatMultiplier_pos t x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hodgeHeatMultiplier_le_one t x)

lemma hodgeSpectralHeat_eigenvector (t x : ℝ) (f : L2 A J α hs ht true)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    hodgeSpectralHeat A J α hs ht D hD t f = hodgeHeatMultiplier t x • f := by
  classical
  let v : Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x :=
    ⟨f, Module.End.mem_eigenspace_iff.mpr hx⟩
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  have hv : E.symm (lp.single 2 x v) = f :=
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv_symm_apply_single v
  have hv' : E f = lp.single 2 x v := by rw [← hv, E.apply_symm_apply]
  apply E.injective
  apply lp.ext
  funext y
  change E (hodgeSpectralHeat A J α hs ht D hD t f) y = E (hodgeHeatMultiplier t x • f) y
  rw [hodgeSpectralHeat_repr, map_smul]
  change hodgeHeatMultiplier t y • E f y = hodgeHeatMultiplier t x • E f y
  rw [hv']
  by_cases hy : y = x
  · subst y; rfl
  · simp [lp.single_apply, hy]

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeHeatMultiplier_continuous (x : ℝ) : Continuous (fun t => hodgeHeatMultiplier t x) := by
  exact ((continuous_id.max continuous_const).neg.mul continuous_const).rexp

lemma hodgeSpectralHeat_continuous (f : L2 A J α hs ht true) :
    Continuous (fun t => hodgeSpectralHeat A J α hs ht D hD t f) := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  let v := E f
  let F := fun t => hodgeHeatDiagonal A J α hs ht t v
  have hc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro t₀
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsq (t : ℝ) : ‖F t - F t₀‖^2 =
        ∑' x : ℝ, ‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖^2 := by
      have hh := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (F t-F t₀)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hh
      rw [hh]
      congr 1
      funext x
      change ‖hodgeHeatMultiplier t x • v x - hodgeHeatMultiplier t₀ x • v x‖^2 = _
      rw [← sub_smul]
    have hsum : Summable (fun x : ℝ => ‖v x‖^2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal)
    have hb (x t : ℝ) :
        ‖‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖^2‖ ≤ ‖v x‖^2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have ha : |hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x| ≤ 1 := by
        apply abs_le.mpr
        have h1 := hodgeHeatMultiplier_pos t x
        have h2 := hodgeHeatMultiplier_pos t₀ x
        have h3 := hodgeHeatMultiplier_le_one t x
        have h4 := hodgeHeatMultiplier_le_one t₀ x
        constructor <;> linarith
      have hn : ‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖ ≤ ‖v x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) ha
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hcts : Continuous (fun t => ∑' x : ℝ,
        ‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖^2) :=
      continuous_tsum (fun x => (((hodgeHeatMultiplier_continuous x).sub continuous_const).smul
        continuous_const).norm.pow 2) hsum hb
    have hlim := (Real.continuous_sqrt.comp hcts).tendsto t₀
    have hh : (fun t => Real.sqrt (∑' x : ℝ,
        ‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖^2)) =
        (fun t => ‖F t-F t₀‖) := by
      funext t
      rw [← hsq t, Real.sqrt_sq (norm_nonneg _)]
    change Tendsto (fun t => Real.sqrt (∑' x : ℝ,
      ‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖^2)) _ _ at hlim
    rw [hh] at hlim
    change Tendsto (fun t => ‖F t-F t₀‖) (𝓝 t₀) (𝓝 (Real.sqrt
      (∑' x : ℝ, ‖(hodgeHeatMultiplier t₀ x-hodgeHeatMultiplier t₀ x) • v x‖^2))) at hlim
    simpa using hlim
  exact E.symm.continuous.comp hc

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
