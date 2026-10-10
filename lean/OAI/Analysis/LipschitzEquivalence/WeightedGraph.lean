import OAI.Analysis.LipschitzEquivalence.NullSequences

namespace OAI

universe uA uH uB uJ

noncomputable section
namespace LipschitzCounterexample

namespace WeightedGraph
open scoped ENNReal NNReal Topology
open Filter

variable {A : Type uA} {H : Type uH} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

abbrev L1 (A : Type uA) [NormedAddCommGroup A] := lp (fun _ : ℕ => A) 1
abbrev C0 (H : Type uH) [NormedAddCommGroup H] := NullSequences.C0 (H := H)

def weight (i : ℕ) : ℝ := (1 / 2) ^ (i + 1)

theorem weight_pos (i : ℕ) : 0 < weight i := pow_pos (by norm_num) _
theorem weight_ne_zero (i : ℕ) : weight i ≠ 0 := (weight_pos i).ne'
theorem weight_nonneg (i : ℕ) : 0 ≤ weight i := (weight_pos i).le

theorem hasSum_weight : HasSum weight 1 := by
  change HasSum (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1)) 1
  simpa [pow_succ, mul_comm] using
    hasSum_geometric_two.mul_left (1 / 2 : ℝ)

omit [NormedSpace ℝ A] in
theorem norm_l1 (x : L1 A) : ‖x‖ = ∑' i, ‖x i‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x

instance [TopologicalSpace.SeparableSpace A] : TopologicalSpace.SeparableSpace (L1 A) := by
  let S : Set (L1 A) := ⋃ i : ℕ, Set.range (lp.single (E := fun _ : ℕ => A) 1 i)
  have hs : TopologicalSpace.IsSeparable S :=
    TopologicalSpace.IsSeparable.iUnion (fun i =>
      TopologicalSpace.isSeparable_range (lp.isometry_single i).continuous)
  have hd : Dense (Submodule.span ℝ S : Set (L1 A)) := by
    intro s
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by simp) s).tendsto_sum_nat
    apply Eventually.of_forall
    intro n
    apply subset_closure
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.subset_span
    exact Set.mem_iUnion.2 ⟨i, ⟨s i, rfl⟩⟩
  exact hd.isSeparable_iff.mp hs.span

def graphSubmodule (Q : A →L[ℝ] H) : Submodule ℝ (L1 A × C0 H) where
  carrier := { s | ∀ i, Q (s.1 i) = weight i • s.2 i }
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i
    change Q (x.1 i + y.1 i) = weight i • (x.2 i + y.2 i)
    rw [map_add, hx, hy, smul_add]
  smul_mem' := by
    intro c x hx i
    change Q (c • x.1 i) = weight i • (c • x.2 i)
    rw [map_smul, hx, smul_comm]

theorem isClosed_graphSubmodule (Q : A →L[ℝ] H) :
    IsClosed (graphSubmodule Q : Set (L1 A × C0 H)) := by
  change IsClosed {s : L1 A × C0 H | ∀ i, Q (s.1 i) = weight i • s.2 i}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_eq
  · exact Q.continuous.comp ((lp.evalCLM ℝ (fun _ : ℕ => A) 1 i).continuous.comp continuous_fst)
  · exact ((NullSequences.evalCLM (H := H) i).continuous.comp continuous_snd).const_smul _

def Space (Q : A →L[ℝ] H) : Type _ := graphSubmodule Q

instance (Q : A →L[ℝ] H) : NormedAddCommGroup (Space Q) :=
  inferInstanceAs (NormedAddCommGroup (graphSubmodule Q))
instance (Q : A →L[ℝ] H) : NormedSpace ℝ (Space Q) :=
  inferInstanceAs (NormedSpace ℝ (graphSubmodule Q))
instance (Q : A →L[ℝ] H) [CompleteSpace A] [CompleteSpace H] : CompleteSpace (Space Q) :=
  (isClosed_graphSubmodule Q).isComplete.completeSpace_coe

instance (Q : A →L[ℝ] H) [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace H] : TopologicalSpace.SeparableSpace (Space Q) :=
  inferInstanceAs (TopologicalSpace.SeparableSpace (graphSubmodule Q))

variable (Q : A →L[ℝ] H)

def inclusion : Space Q →ₗᵢ[ℝ] L1 A × C0 H where
  toFun := fun s => s.1
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  norm_map' := fun _ => rfl

def coord (s : Space Q) (i : ℕ) : A := (weight i)⁻¹ • s.1.1 i

def output : Space Q →L[ℝ] C0 H :=
  (ContinuousLinearMap.snd ℝ (L1 A) (C0 H)).comp (inclusion Q).toContinuousLinearMap

@[simp] theorem output_apply (s : Space Q) (i : ℕ) : output Q s i = s.1.2 i := rfl

theorem map_coord (s : Space Q) (i : ℕ) : Q (coord Q s i) = output Q s i := by
  simp only [coord, map_smul, s.2 i, smul_smul, inv_mul_cancel₀ (weight_ne_zero i), one_smul]
  rfl

theorem weight_smul_coord (s : Space Q) (i : ℕ) : weight i • coord Q s i = s.1.1 i := by
  rw [coord, smul_smul, mul_inv_cancel₀ (weight_ne_zero i), one_smul]

theorem norm_output_le (s : Space Q) : ‖output Q s‖ ≤ ‖s‖ :=
  le_max_right _ _

theorem norm_coord_le (s : Space Q) (i : ℕ) : ‖coord Q s i‖ ≤ (weight i)⁻¹ * ‖s‖ := by
  rw [coord, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (weight_nonneg i))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (weight_nonneg i))
  exact (lp.norm_apply_le_norm (by norm_num) s.1.1 i).trans (le_max_left _ _)

def coordCLM (i : ℕ) : Space Q →L[ℝ] A :=
  ({ toFun := fun s => coord Q s i
     map_add' := by
       intro s t
       change (weight i)⁻¹ • (s.1.1 i + t.1.1 i) = _
       exact smul_add _ _ _
     map_smul' := by
       intro c s
       change (weight i)⁻¹ • (c • s.1.1 i) = c • ((weight i)⁻¹ • s.1.1 i)
       exact smul_comm _ _ _ } : Space Q →ₗ[ℝ] A).mkContinuous
    (weight i)⁻¹ (fun s => norm_coord_le Q s i)

theorem norm_eq (s : Space Q) :
    ‖s‖ = max (∑' i, weight i * ‖coord Q s i‖) ‖output Q s‖ := by
  change max ‖s.1.1‖ ‖s.1.2‖ = _
  rw [norm_l1]
  congr 1
  apply tsum_congr
  intro i
  rw [← weight_smul_coord Q s i, norm_smul, Real.norm_of_nonneg (weight_nonneg i)]

theorem summable_weighted_norm (s : Space Q) : Summable (fun i => weight i * ‖coord Q s i‖) := by
  have h := (lp.hasSum_norm (by norm_num : 0 < (1 : ℝ≥0∞).toReal) s.1.1).summable
  simpa only [ENNReal.toReal_one, Real.rpow_one, ← weight_smul_coord Q s,
    norm_smul, Real.norm_of_nonneg (weight_nonneg _)] using h

def ofSequence (s : ℕ → A) (hs : Summable (fun i => weight i * ‖s i‖))
    (hq : Tendsto (fun i => Q (s i)) atTop (𝓝 0)) : Space Q :=
  ⟨(⟨fun i => weight i • s i, memℓp_gen (by
      simpa only [ENNReal.toReal_one, Real.rpow_one, norm_smul,
        Real.norm_of_nonneg (weight_nonneg _)] using hs)⟩,
    NullSequences.ofTendsto (fun i => Q (s i)) hq), by
    intro i
    exact Q.map_smul _ _⟩

@[simp] theorem coord_ofSequence (s : ℕ → A) (hs) (hq) (i : ℕ) :
    coord Q (ofSequence Q s hs hq) i = s i := by
  simp [coord, ofSequence, smul_smul, weight_ne_zero]

@[ext] theorem ext {s t : Space Q} (h : ∀ i, coord Q s i = coord Q t i) : s = t := by
  apply Subtype.ext
  apply Prod.ext
  · apply lp.ext
    funext i
    rw [← weight_smul_coord Q s i, ← weight_smul_coord Q t i, h i]
  · ext i
    rw [← output_apply, ← output_apply, ← map_coord, ← map_coord, h i]

@[simp] theorem coord_zero (i : ℕ) : coord Q 0 i = 0 := by
  change (weight i)⁻¹ • (0 : A) = 0
  exact smul_zero _
@[simp] theorem coord_sub (s t : Space Q) (i : ℕ) :
    coord Q (s - t) i = coord Q s i - coord Q t i :=
  (coordCLM Q i).map_sub s t

variable {B : Type uB} {J : Type uJ} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup J] [NormedSpace ℝ J]
variable (R : B →L[ℝ] J) (F : A → B) (g : H → J)
  {K L : ℝ≥0} (hF : LipschitzWith K F) (hg : LipschitzWith L g)
  (hF0 : F 0 = 0) (hg0 : g 0 = 0) (hdiag : ∀ x, R (F x) = g (Q x))

def lift (s : Space Q) : Space R :=
  ofSequence R (fun i => F (coord Q s i))
    (Summable.of_nonneg_of_le (fun i => mul_nonneg (weight_nonneg i) (norm_nonneg _))
      (fun i => by
        have h := hF.norm_sub_le (coord Q s i) 0
        simp only [hF0, sub_zero] at h
        calc
          weight i * ‖F (coord Q s i)‖ ≤ weight i * (K * ‖coord Q s i‖) :=
            mul_le_mul_of_nonneg_left h (weight_nonneg i)
          _ = K * (weight i * ‖coord Q s i‖) := by ring)
      ((summable_weighted_norm Q s).mul_left (K : ℝ)))
    (by
      simp_rw [hdiag, map_coord]
      change Tendsto (g ∘ output Q s) atTop (𝓝 0)
      rw [← hg0]
      exact (hg.continuous.tendsto 0).comp (NullSequences.tendsto_zero (output Q s)))

@[simp] theorem coord_lift (s : Space Q) (i : ℕ) :
    coord R (lift Q R F g hF hg hF0 hg0 hdiag s) i = F (coord Q s i) :=
  coord_ofSequence ..

 theorem lipschitz_lift : LipschitzWith (max K L) (lift Q R F g hF hg hF0 hg0 hdiag) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro s t
  rw [norm_eq]
  apply max_le
  · calc
      (∑' i, weight i * ‖coord R (lift Q R F g hF hg hF0 hg0 hdiag s -
        lift Q R F g hF hg hF0 hg0 hdiag t) i‖) ≤
          ∑' i, (K : ℝ) * (weight i * ‖coord Q (s - t) i‖) := by
            apply Summable.tsum_le_tsum
            · intro i
              simp only [coord_sub, coord_lift]
              calc
                _ ≤ weight i * (K * ‖coord Q s i - coord Q t i‖) :=
                  mul_le_mul_of_nonneg_left (hF.norm_sub_le _ _) (weight_nonneg i)
                _ = _ := by ring
            · exact summable_weighted_norm R _
            · exact (summable_weighted_norm Q _).mul_left _
      _ = K * (∑' i, weight i * ‖coord Q (s - t) i‖) := tsum_mul_left
      _ ≤ K * ‖s - t‖ := by
        apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
        rw [norm_eq]
        exact le_max_left _ _
      _ ≤ (max K L : ℝ≥0) * ‖s - t‖ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K L) (norm_nonneg _)
  · apply le_trans _ (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right K L) (norm_nonneg (s - t)))
    apply (NullSequences.norm_le (mul_nonneg L.coe_nonneg (norm_nonneg (s - t)))).2
    intro i
    rw [← map_coord, coord_sub, map_sub, coord_lift, coord_lift, hdiag, hdiag]
    apply (hg.norm_sub_le _ _).trans
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    rw [map_coord, map_coord]
    change ‖(output Q s - output Q t) i‖ ≤ ‖s - t‖
    rw [← map_sub]
    exact (NullSequences.norm_apply_le _ i).trans (norm_output_le Q _)

end WeightedGraph

end LipschitzCounterexample
end

end OAI
