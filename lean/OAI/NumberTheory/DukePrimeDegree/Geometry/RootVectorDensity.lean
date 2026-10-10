import OAI.NumberTheory.DukePrimeDegree.Dynamics.ConjugationOrbit
import OAI.NumberTheory.PrimePackets.RootRelations

namespace OAI

/-!
# Fixed vectors on finite-volume root orbits

A finite distribution invariant under a root shear is supported on the
fixed hyperplane of that shear. Recurrence proves this directly. Applied
to the vector orbit map, it shows that a vector fixed by the actual
lattice stabilizer is fixed by every root group in the orbit group.
This is the fixed-vector part of the density argument used to exclude
singleton root blocks.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rootVectorAction {n : ℕ} (i j : Fin n) (t : ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  v ᵥ* Matrix.transvection i j t

lemma continuous_rootVectorAction {n : ℕ} (i j : Fin n) (t : ℝ) :
    Continuous (rootVectorAction i j t) := by
  apply continuous_pi
  intro k
  simp only [rootVectorAction, vecMul_transvection_apply]
  split_ifs <;> fun_prop

lemma rootVectorAction_iterate {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (v : Fin n → ℝ) (m : ℕ) (k : Fin n) :
    (rootVectorAction i j 1)^[m] v k =
      v k + if j = k then (m : ℝ) * v i else 0 := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    simp only [rootVectorAction, vecMul_transvection_apply]
    rw [ih k, ih i]
    simp only [ite_eq_right hij.symm, add_zero, mul_one, Nat.cast_add, Nat.cast_one]
    split_ifs <;> ring

theorem ae_rootVector_fixed_of_map_eq {n : ℕ}
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν]
    (i j : Fin n) (hij : i ≠ j)
    (hinv : ν.map (rootVectorAction i j 1) = ν) : ∀ᵐ v ∂ν, v i = 0 := by
  let f := rootVectorAction i j 1
  have hf : MeasurePreserving f ν ν := ⟨(continuous_rootVectorAction i j 1).measurable, hinv⟩
  filter_upwards [hf.conservative.ae_frequently_mem_of_mem_nhds] with v hv
  by_contra hvi
  let U : Set (Fin n → ℝ) := {w | |w j - v j| < 1}
  have hU : U ∈ 𝓝 v := by
    apply (isOpen_lt ((continuous_apply j).sub continuous_const).abs continuous_const).mem_nhds
    change |v j - v j| < 1
    simp
  have hrec := hv U hU
  have hgrowth : Tendsto (fun m : ℕ => (m : ℝ) * |v i|) atTop atTop :=
    Filter.Tendsto.atTop_mul_const (abs_pos.mpr hvi) tendsto_natCast_atTop_atTop
  obtain ⟨m, hmU, hmB⟩ := (hrec.and_eventually (hgrowth.eventually_ge_atTop 1)).exists
  have he : |(f^[m] v) j - v j| = (m : ℝ) * |v i| := by
    rw [rootVectorAction_iterate i j hij v m j]
    simp only [ite_true, add_sub_cancel_left, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m)]
  change |(f^[m] v) j - v j| < 1 at hmU
  rw [he] at hmU
  exact (not_lt_of_ge hmB) hmU

def fixedVectorOrbitMap {n : ℕ} (g : G n) (H : Subgroup (G n))
    (v : Fin n → ℝ)
    (hfixed : ∀ s : pointOrbitStabilizer g H, v ᵥ* s.val.val = v) :
    LatticeOrbitQuotient g H → (Fin n → ℝ) :=
  Quotient.lift (fun h : H => v ᵥ* h.val.val) (by
    intro a b hab
    change QuotientGroup.rightRel (pointOrbitStabilizer g H) a b at hab
    rw [QuotientGroup.rightRel_apply] at hab
    have hs := hfixed ⟨b * a⁻¹, hab⟩
    have he := congrArg (fun w : Fin n → ℝ => w ᵥ* a.val.val) hs
    simpa only [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right] using he.symm)

lemma continuous_fixedVectorOrbitMap {n : ℕ} (g : G n) (H : Subgroup (G n))
    (v : Fin n → ℝ)
    (hfixed : ∀ s : pointOrbitStabilizer g H, v ᵥ* s.val.val = v) :
    Continuous (fixedVectorOrbitMap g H v hfixed) := by
  apply continuous_quot_lift
  fun_prop

lemma fixedVectorOrbitMap_rightAction {n : ℕ} (g : G n) (H : Subgroup (G n))
    (v : Fin n → ℝ)
    (hfixed : ∀ s : pointOrbitStabilizer g H, v ᵥ* s.val.val = v)
    (x : LatticeOrbitQuotient g H) (h : H) :
    fixedVectorOrbitMap g H v hfixed (latticeOrbitRightAction g H x h) =
      fixedVectorOrbitMap g H v hfixed x ᵥ* h.val.val := by
  induction x using Quotient.inductionOn with
  | h a => exact (Matrix.vecMul_vecMul v a.val.val h.val.val).symm

theorem fixedVector_root_coordinate_zero_of_finite_orbit {n : ℕ}
    (g : G n) (H : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g H)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : H, μ.map (fun x => latticeOrbitRightAction g H x h) = μ)
    (v : Fin n → ℝ)
    (hfixed : ∀ s : pointOrbitStabilizer g H, v ᵥ* s.val.val = v)
    (i j : Fin n) (hij : i ≠ j)
    (hroot : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ H) : v i = 0 := by
  let F := fixedVectorOrbitMap g H v hfixed
  let h : H := ⟨Matrix.SpecialLinearGroup.transvection hij (1 : ℝ), hroot⟩
  have hF : Continuous F := continuous_fixedVectorOrbitMap g H v hfixed
  have hpush : (μ.map F).map (rootVectorAction i j 1) = μ.map F := by
    calc
      _ = μ.map (rootVectorAction i j 1 ∘ F) :=
        Measure.map_map (continuous_rootVectorAction i j 1).measurable hF.measurable
      _ = μ.map (F ∘ fun x => latticeOrbitRightAction g H x h) := by
        congr 1
        funext x
        exact (fixedVectorOrbitMap_rightAction g H v hfixed x h).symm
      _ = (μ.map (fun x => latticeOrbitRightAction g H x h)).map F :=
        (Measure.map_map hF.measurable (continuous_latticeOrbitRightAction g H h).measurable).symm
      _ = μ.map F := by rw [hinv h]
  have hzero : ∀ᵐ x ∂μ, F x i = 0 := ae_of_ae_map hF.measurable.aemeasurable
    (ae_rootVector_fixed_of_map_eq (μ.map F) i j hij hpush)
  have hs : μ.support ⊆ {x | F x i = 0} :=
    Measure.support_subset_of_isClosed
      (isClosed_eq ((continuous_apply i).comp hF) continuous_const) hzero
  have hmem : (Quotient.mk _ (1 : H) : LatticeOrbitQuotient g H) ∈ μ.support := by
    rw [latticeOrbit_support_eq_univ g H μ hμ hinv]
    trivial
  have he := hs hmem
  change (v ᵥ* (1 : G n).val) i = 0 at he
  simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one] using he

end DukePrimeDegree

end

end OAI
