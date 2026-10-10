import OAI.Geometry.HeilbronnTriangle.LatticeLowerProduct
import OAI.Geometry.HeilbronnTriangle.SuccessiveTransport
import OAI.Geometry.HeilbronnTriangle.SuccessiveVectors

namespace OAI


noncomputable section

open Module Submodule
open scoped BigOperators

namespace Problem355.SuccessiveEstimates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem monotone_norm_of_minimizing_basis (L : Submodule ℤ E)
    (b : Basis (Fin n) ℝ E) (hb : ∀ i, b i ∈ L)
    (hmin : ∀ j (x : E), x ∈ L → x ∉ Submodule.span ℝ (b '' Set.Iio j) →
      ‖b j‖ ≤ ‖x‖) : Monotone (fun i => ‖b i‖) := by
  intro i j hij
  apply hmin i (b j) (hb j)
  rw [b.self_mem_span_image]
  exact not_lt_of_ge hij

theorem successive_basis_estimates (hn : 0 < n) (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin n) ℝ E) (hb : ∀ i, b i ∈ L)
    (hmin : ∀ j (x : E), x ∈ L → x ∉ Submodule.span ℝ (b '' Set.Iio j) →
      ‖b j‖ ≤ ‖x‖) :
    ZLattice.covolume L ≤ ∏ i, ‖b i‖ ∧
      (∏ i, ‖b i‖) ≤ Real.sqrt n ^ n * ZLattice.covolume L ∧
      ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≤
        Real.sqrt n ^ n := by
  have hpositive : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.mpr (b.ne_zero i)
  have hupper := SuccessiveBox.successive_norm_product_le hn
    (Module.finrank_eq_card_basis b) L b hpositive
    (monotone_norm_of_minimizing_basis L b hb hmin) hmin
  refine ⟨LatticeLowerProduct.covolume_le_prod_norm L b hb, hupper, ?_⟩
  calc
    ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≤
        (∏ i, ‖b i‖) / ZLattice.covolume L :=
      LatticeLowerProduct.relIndex_span_basis_le L b hb
    _ ≤ Real.sqrt n ^ n := (div_le_iff₀ (ZLattice.covolume_pos L)).mpr hupper

theorem exists_successive_basis_estimates (hdim : 0 < Module.finrank ℝ E)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ b : Basis (Fin (Module.finrank ℝ E)) ℝ E,
      SuccessiveVectors.IsSuccessive L b ∧
      ZLattice.covolume L ≤ ∏ i, ‖b i‖ ∧
      (∏ i, ‖b i‖) ≤ Real.sqrt (Module.finrank ℝ E) ^ Module.finrank ℝ E *
        ZLattice.covolume L ∧
      ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≤
        Real.sqrt (Module.finrank ℝ E) ^ Module.finrank ℝ E := by
  obtain ⟨b, hb⟩ := SuccessiveVectors.exists_successive_basis L
  refine ⟨b, hb, ?_⟩
  exact successive_basis_estimates hdim L b hb.mem_lattice hb.minimal

theorem relIndex_le_five (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin 3) ℝ E) (hb : ∀ i, b i ∈ L)
    (hmin : ∀ j (x : E), x ∈ L → x ∉ Submodule.span ℝ (b '' Set.Iio j) →
      ‖b j‖ ≤ ‖x‖) :
    (Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≤ 5 := by
  have hbound := (successive_basis_estimates (by norm_num : 0 < 3) L b hb hmin).2.2
  have hsqrt : Real.sqrt (3 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hcub : Real.sqrt (3 : ℝ) ^ 3 < 6 := by
    calc
      Real.sqrt (3 : ℝ) ^ 3 = 3 * Real.sqrt (3 : ℝ) := by
        rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      _ < 6 := by linarith
  have hlt : ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) < 6 :=
    hbound.trans_lt hcub
  have hint : (Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup < 6 := by
    exact_mod_cast hlt
  omega

end Problem355.SuccessiveEstimates

end

end OAI
