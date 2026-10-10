import OAI.Geometry.HeilbronnTriangle.SuccessiveBox

namespace OAI


namespace Problem355.SuccessiveBox

open MeasureTheory Set Module InnerProductSpace
open scoped BigOperators

theorem gramSchmidt_coordinate_zero_of_mem_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hdim : finrank ℝ E = Fintype.card (Fin n))
    (v : Fin n → E) (j : Fin n) {x : E}
    (hx : x ∈ Submodule.span ℝ (v '' Set.Iio j)) :
    (gramSchmidtOrthonormalBasis hdim v).repr x j = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact gramSchmidtOrthonormalBasis_inv_triangular' hdim v hi
  | zero => simp
  | add x y hx hy hx' hy' => simp [map_add, hx', hy']
  | smul a x hx hx' => simp [map_smul, hx']

theorem successive_norm_product_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (hn : 0 < n) (hdim : finrank ℝ E = Fintype.card (Fin n))
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : Fin n → E) (hpositive : ∀ i, 0 < ‖v i‖)
    (hmono : Monotone (fun i => ‖v i‖))
    (hmin : ∀ j (x : E), x ∈ L → x ∉ Submodule.span ℝ (v '' Set.Iio j) →
      ‖v j‖ ≤ ‖x‖) :
    (∏ i, ‖v i‖) ≤ Real.sqrt n ^ n * ZLattice.covolume L := by
  classical
  let b := gramSchmidtOrthonormalBasis hdim v
  let f : (Fin n → ℝ) ≃L[ℝ] E :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.trans b.repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f :=
    b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp (Fin n))
  let L' := ZLattice.comap ℝ L f.toLinearMap
  let b' := IsZLattice.basis L'
  let : Countable L'.toAddSubgroup := b'.equivFun.injective.countable
  let F := ZSpan.fundamentalDomain (b'.ofZLatticeBasis ℝ)
  have hF : IsAddFundamentalDomain L'.toAddSubgroup F volume :=
    ZLattice.isAddFundamentalDomain b' volume
  have hfinite : volume F ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (b'.ofZLatticeBasis ℝ)).measure_lt_top.ne
  have hlen : ∀ (x : L'.toAddSubgroup) (j : Fin n), (x : Fin n → ℝ) j ≠ 0 →
      (∀ i, j < i → (x : Fin n → ℝ) i = 0) →
      ‖v j‖ ^ 2 ≤ ∑ i, (x : Fin n → ℝ) i ^ 2 := by
    intro x j hxj _
    have hxmem : f (x : Fin n → ℝ) ∈ L := x.property
    have hcoord : b.repr (f (x : Fin n → ℝ)) j = (x : Fin n → ℝ) j := by
      simp [f]
    have hout : f (x : Fin n → ℝ) ∉ Submodule.span ℝ (v '' Set.Iio j) := by
      intro h
      have hz := gramSchmidt_coordinate_zero_of_mem_span hdim v j h
      change b.repr (f (x : Fin n → ℝ)) j = 0 at hz
      exact hxj (hcoord.symm.trans hz)
    have hle := hmin j _ hxmem hout
    have hnorm : ‖f (x : Fin n → ℝ)‖ ^ 2 = ∑ i, (x : Fin n → ℝ) i ^ 2 := by
      calc
        ‖f (x : Fin n → ℝ)‖ ^ 2 = ‖b.repr (f (x : Fin n → ℝ))‖ ^ 2 := by simp
        _ = ∑ i, ‖b.repr (f (x : Fin n → ℝ)) i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
        _ = ∑ i, (x : Fin n → ℝ) i ^ 2 := by simp [f, Real.norm_eq_abs, sq_abs]
    rw [← hnorm]
    exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hle
  have hresult := successive_product_le hn L'.toAddSubgroup F hF hfinite
    (fun i => ‖v i‖) hpositive hmono hlen
  have hcov : volume.real F = ZLattice.covolume L := by
    rw [← ZLattice.covolume_eq_measure_fundamentalDomain L' volume
      (ZLattice.isAddFundamentalDomain b' volume)]
    exact ZLattice.covolume_comap L volume volume hf
  rwa [hcov] at hresult

end Problem355.SuccessiveBox

end OAI
