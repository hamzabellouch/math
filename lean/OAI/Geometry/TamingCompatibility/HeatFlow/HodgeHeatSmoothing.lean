import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeSpectralHeat

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def hodgeBoundedSpectralMultiplier (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  E.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun x => m x • ContinuousLinearMap.id ℝ _) hK (by
      intro x
      apply ContinuousLinearMap.opNorm_le_bound _ hK
      intro v
      simp only [smul_apply, ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hm x) (norm_nonneg _))).comp
      E.toContinuousLinearEquiv.toContinuousLinearMap)

lemma hodgeBoundedSpectralMultiplier_repr (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (f : L2 A J α hs ht true) (x : ℝ) :
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
      (hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f) x =
      m x • (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv f x := by
  change ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
    ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv.symm _)) x = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma hodgeBoundedSpectralMultiplier_eigenvector (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (x : ℝ) (f : L2 A J α hs ht true)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f = m x • f := by
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
  change E (hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f) y = E (m x • f) y
  rw [hodgeBoundedSpectralMultiplier_repr, map_smul]
  change m y • E f y = m x • E f y
  rw [hv']
  by_cases hy : y = x
  · subst y; rfl
  · simp [lp.single_apply, hy]

lemma hodgeBoundedSpectralMultiplier_norm_le (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (f : L2 A J α hs ht true) :
    ‖hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f‖ ≤ K * ‖f‖ := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  calc
    _ = ‖E (hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f)‖ :=
      (E.norm_map _).symm
    _ ≤ ‖K • E f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro x
      rw [hodgeBoundedSpectralMultiplier_repr]
      change ‖m x • E f x‖ ≤ ‖K • E f x‖
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hK]
      exact mul_le_mul_of_nonneg_right (hm x) (norm_nonneg _)
    _ = K * ‖f‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hK, E.norm_map]

lemma hodgeBoundedSpectralMultiplier_symmetric (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (f g : L2 A J α hs ht true) :
    ⟪hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f,g⟫ =
      ⟪f,hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm g⟫ := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  rw [← E.inner_map_map (hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f) g,
    ← E.inner_map_map f (hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm g),
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  rw [hodgeBoundedSpectralMultiplier_repr, hodgeBoundedSpectralMultiplier_repr]
  change ⟪m x • (E f x).val, (E g x).val⟫ = ⟪(E f x).val, m x • (E g x).val⟫
  exact (real_inner_smul_left (E f x).val (E g x).val (m x)).trans
    (real_inner_smul_right (E f x).val (E g x).val (m x)).symm

lemma heat_boost_bound (y : ℝ) (hy : 0 ≤ y) :
    |(1+y)^3 * Real.exp (-y)| ≤ 6 * Real.exp 1 := by
  have hp : 0 ≤ 1+y := by linarith
  have he := Real.pow_div_factorial_le_exp (1+y) hp 3
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at he
  have he' : (1+y)^3 ≤ 6 * Real.exp (1+y) := by linarith
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg hp _) (Real.exp_pos _).le)]
  calc
    _ ≤ (6 * Real.exp (1+y)) * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right he' (Real.exp_pos _).le
    _ = 6 * Real.exp 1 := by rw [mul_assoc, ← Real.exp_add]; ring_nf

def hodgeHeatBoost (r : ℝ) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  hodgeBoundedSpectralMultiplier A J α hs ht D hD
    (fun x => (1+r^2*hodgeSpectralRate x)^3 * Real.exp (-(r^2*hodgeSpectralRate x)))
    (6 * Real.exp 1) (by positivity)
    (fun x => heat_boost_bound _ (mul_nonneg (sq_nonneg _) (le_max_left _ _)))

lemma hodgeSpectralHeat_factor (r : ℝ) (hr : 0 < r) :
    hodgeSpectralHeat A J α hs ht D hD (r^2) =
      hodgeRegularization A J α hs ht r * hodgeHeatBoost A J α hs ht D hD r := by
  let L := hodgeSpectralHeat A J α hs ht D hD (r^2) -
    hodgeRegularization A J α hs ht r * hodgeHeatBoost A J α hs ht D hD r
  have hi : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x) ≤ L.ker := by
    apply iSup_le
    intro x f hf
    have hx := Module.End.mem_eigenspace_iff.mp hf
    change L f = 0
    by_cases hzero : f = 0
    · subst f; exact map_zero L
    obtain ⟨hx0,hx1⟩ := hodgeResolvent_eigenvalue_positive_le_one A J α hs ht f hzero x hx
    have hxinv : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).mpr hx1
    have hrate : hodgeSpectralRate x = x⁻¹-1 := max_eq_right (sub_nonneg.mpr hxinv)
    have hden : 0 < 1+r^2*hodgeSpectralRate x := by
      have hp := mul_nonneg (sq_nonneg r) (le_max_left 0 (x⁻¹-1))
      dsimp [hodgeSpectralRate]; linarith
    have hdpos : 0 < r^2+(1-r^2)*x := by
      have hp := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hx1)
      nlinarith
    have heq : x/(r^2+(1-r^2)*x) = (1+r^2*hodgeSpectralRate x)⁻¹ := by
      rw [hrate] at hden ⊢
      field_simp [ne_of_gt hx0, ne_of_gt hden, ne_of_gt hdpos]
      ring
    have he := hodgeResolvent_eigenvector_parameter A J α hs ht r hr f x hx0.le hx1 hx
    rw [heq] at he
    have hp (n : ℕ) : (hodgeResolvent A J α hs ht r ^ n) f =
        ((1+r^2*hodgeSpectralRate x)⁻¹)^n • f := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', mul_apply_eq_comp, ih, map_smul, he, smul_smul]
        congr 1
    have hb := hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D hD
      (fun x => (1+r^2*hodgeSpectralRate x)^3 * Real.exp (-(r^2*hodgeSpectralRate x)))
      (6*Real.exp 1) (by positivity)
      (fun x => heat_boost_bound _ (mul_nonneg (sq_nonneg _) (le_max_left _ _))) x f hx
    change hodgeHeatBoost A J α hs ht D hD r f = _ at hb
    dsimp [L]
    rw [sub_apply, mul_apply_eq_comp,
      hodgeSpectralHeat_eigenvector A J α hs ht D hD _ x f hx, hb, map_smul]
    change hodgeHeatMultiplier (r^2) x • f - _ • (hodgeResolvent A J α hs ht r ^ 3) f = 0
    rw [hp 3, smul_smul]
    have hc : ((1+r^2*hodgeSpectralRate x)^3 * Real.exp (-(r^2*hodgeSpectralRate x))) *
        ((1+r^2*hodgeSpectralRate x)⁻¹)^3 = hodgeHeatMultiplier (r^2) x := by
      simp only [hodgeHeatMultiplier, max_eq_left (sq_nonneg r), neg_mul]
      field_simp [ne_of_gt hden]
    rw [hc, sub_self]
  have hcl : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,
      hodgeResolvent_eigenspaces_total A J α hs ht D hD]
    simp
  have htop : ⊤ ≤ L.ker := by
    rw [← hcl]
    exact Submodule.topologicalClosure_minimal _ hi (ContinuousLinearMap.isClosed_ker L)
  ext f
  have hf : L f = 0 := htop (Submodule.mem_top)
  exact sub_eq_zero.mp hf

lemma hodgeHeatBoost_norm_le (r : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeHeatBoost A J α hs ht D hD r f‖ ≤ (6 * Real.exp 1) * ‖f‖ :=
  hodgeBoundedSpectralMultiplier_norm_le A J α hs ht D hD _ _ _ _ f

end TamingCompatibility.GeometricHilbert

end

end OAI
