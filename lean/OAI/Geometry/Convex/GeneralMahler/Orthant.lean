import OAI.Geometry.Convex.GeneralMahler.Transform

namespace OAI
/-! Full-dimensional simplicial cones, coordinates and Laplace integrals. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real WithLp Module
open scoped RealInnerProductSpace ENNReal Topology
namespace GeneralMahler
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ}

section Orthant

variable (b : Basis (Fin m) ℝ E)

def orthant : ProperCone ℝ E where
  carrier := {p | ∀ i, 0 ≤ b.equivFun p i}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i
    simpa using add_nonneg (hx i) (hy i)
  smul_mem' := by
    rintro ⟨r,hr⟩ x hx i
    change 0 ≤ b.equivFun (r • x) i
    simpa using mul_nonneg hr (hx i)
  isClosed' := by
    simp_rw [ofPred_forall]
    apply isClosed_iInter; intro i
    apply isClosed_le continuous_const
    exact (continuous_apply i).comp b.equivFun.toContinuousLinearEquiv.continuous

@[simp] theorem mem_orthant {p : E} :
    p ∈ orthant b ↔ ∀ i, 0 ≤ b.equivFun p i := Iff.rfl

theorem basis_mem_orthant (i) : b i ∈ orthant b := by
  rw [mem_orthant]
  intro j
  simp
  split <;> norm_num

lemma mem_interior_orthant {p : E} :
    p ∈ interior (orthant b:Set E) ↔ ∀ i, 0 < b.equivFun p i := by
  constructor
  · intro hp i
    by_contra hn
    push Not at hn
    let f : ℝ → E := fun r => p - r • b i
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hv : ∀ᶠ r in 𝓝[>] (0:ℝ), f r ∈ (orthant b:Set E) :=
      nhdsWithin_le_nhds ((hf.tendsto 0) (by simpa [f] using mem_interior_iff_mem_nhds.mp hp))
    obtain ⟨r,hr,hm⟩ := hv.and (show ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r from self_mem_nhdsWithin)
      |>.exists
    have hh := (mem_orthant b).mp hr i
    simp [f] at hh hn
    linarith
  · intro h
    apply mem_interior_iff_mem_nhds.mpr
    change ∀ᶠ x in 𝓝 p, x ∈ (orthant b : Set E)
    have he : ∀ i, ∀ᶠ x in 𝓝 p, 0 < b.equivFun x i :=
      fun i => ((continuous_apply i).comp b.equivFun.toContinuousLinearEquiv.continuous).tendsto p
        (Ioi_mem_nhds (h i))
    filter_upwards [eventually_all.mpr he] with x hx
    exact (mem_orthant b).mpr fun i => (hx i).le

/-- Simplifying two bases via coefficient equivalence. -/
def rebase (a : Basis (Fin m) ℝ E) : E ≃ₗ[ℝ] E :=
  b.equivFun.trans a.equivFun.symm

lemma pushCone_rebase (a : Basis (Fin m) ℝ E) :
    pushCone (rebase b a) (orthant b) = orthant a := by
  ext x
  rw [mem_pushCone, mem_orthant, mem_orthant]
  change (∀ i, 0 ≤ b.equivFun (b.equivFun.symm _) i) ↔ _
  rw [LinearEquiv.apply_symm_apply]
  rfl

omit [FiniteDimensional ℝ E] in
lemma rebase_apply_basis (a : Basis (Fin m) ℝ E) (i : Fin m) :
    rebase b a (b i) = a i := by
  apply a.equivFun.injective
  change a.equivFun (a.equivFun.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  ext j; simp

/-- Exact cone equality class in the proof: image of a coordinate orthant
by an invertible linear map. Basis vectors serve as generating rays. -/
def IsLinearOrthant (m : ℕ) (C : ProperCone ℝ E) :=
  ∃ a : Basis (Fin m) ℝ E, C = orthant a

end Orthant

variable (b : OrthonormalBasis (Fin m) ℝ E)
local notation "C" => orthant b.toBasis

omit [FiniteDimensional ℝ E] in
lemma eq_basis_ip (x : E) (i : Fin m) :
    b.toBasis.equivFun x i = ⟪b i, x⟫ := by
  simpa using b.repr_apply_apply x i

omit [FiniteDimensional ℝ E] in
lemma ip_onb (x y : E) :
    ⟪x,y⟫ = ∑ i, b.toBasis.equivFun x i * b.toBasis.equivFun y i := by
  have he : (∑ i, b.toBasis.equivFun x i • b i) = x := by
    simpa only [Basis.equivFun_apply, OrthonormalBasis.coe_toBasis] using b.toBasis.sum_repr x
  conv_lhs => rw [← he, sum_inner]
  simp_rw [real_inner_smul_left, eq_basis_ip]

lemma orthant_self_dual : posDual C = C := by
  ext x; rw [mem_posDual,mem_orthant]
  constructor
  · intro h i
    rw [eq_basis_ip]
    exact h (basis_mem_orthant _ _)
  · intro h y hy
    rw [ip_onb b]
    apply Finset.sum_nonneg ; intro i hi
    exact mul_nonneg ((mem_orthant _).mp hy i) (h i)

-- Work with canonical Euclidean volumes.
variable [MeasurableSpace E] [BorelSpace E]

theorem chi_orthant {V : E} (h : V ∈ interior (C : Set E)) :
    chi C V = ∏ i, (b.toBasis.equivFun V i)⁻¹ := by
  classical
  let a := b.toBasis.equivFun
  have ha (i : Fin m) : 0 < a V i := (mem_interior_orthant _).mp h i
  let T : E ≃ᵐ (Fin m → ℝ) :=
    b.measurableEquiv.trans (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm
  have hT : MeasurePreserving T :=
    MeasurePreserving.trans b.measurePreserving_measurableEquiv
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _)
  have hta (x : E) : T x = a x := by
    ext i
    change b.repr x i = _
    simp [a]
  let g (i : Fin m) : ℝ → ℝ :=
    (Ici 0).indicator fun t => exp (-(a V i) * t)
  let p (v : Fin m → ℝ) := ∏ i, g i (v i)
  have hip (i : Fin m) : (∫ t : ℝ, g i t) = (a V i)⁻¹ := by
    rw [show (∫ t : ℝ, g i t) = ∫ t : ℝ in Ici 0, exp (-(a V i) * t) from
      integral_indicator measurableSet_Ici,
      integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (neg_neg_of_pos (ha i))]
    ring_nf
    simp
  unfold chi
  rw [← integral_indicator (orthant b.toBasis).isClosed.measurableSet]
  have heq (x : E) :
      (C : Set E).indicator (fun x => exp (-⟪V,x⟫)) x = p (T x) := by
    rw [hta]
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx, ip_onb b, ← Finset.sum_neg_distrib, Real.exp_sum]
      apply Finset.prod_congr rfl; intro i hi
      have hn : 0 ≤ a x i := (mem_orthant _).mp hx i
      change exp (-(a V i * a x i)) = g i (a x i)
      rw [show g i (a x i) = _ from indicator_of_mem (mem_Ici.mpr hn) _]
      rw [neg_mul]
    · rw [indicator_of_notMem hx]
      rw [mem_orthant] at hx
      push Not at hx
      obtain ⟨i,hi⟩ := hx
      have hn : a x i ∉ Ici 0 := hi.not_ge
      exact Eq.symm (Finset.prod_eq_zero (Finset.mem_univ i)
        (indicator_of_notMem hn _))
  simp_rw [heq]
  rw [hT.integral_comp']
  exact (integral_fin_nat_prod_volume_eq_prod ..).trans (Finset.prod_congr rfl fun i _ => hip i)
end GeneralMahler

end

end OAI
