import OAI.Analysis.LipschitzFree.Coordinates

namespace OAI

/-!
# Absolutely summable coefficients of bounded separated Lipschitz-free spaces
-/

noncomputable section
open scoped BigOperators ENNReal Classical

namespace DiscreteFree

namespace Coefficients

variable {ι M : Type*} [MetricSpace M] (o : M)
variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)
variable (e : ι ≃ {x : M // x ≠ o})

abbrev L1 (ι : Type*) := lp (fun _ : ι => ℝ) (1 : ENNReal)

theorem norm_eq_tsum (c : L1 ι) : ‖c‖ = ∑' i, |c i| := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) c

theorem summable_abs (c : L1 ι) : Summable (fun i => |c i|) := by
  simpa using (lp.memℓp c).summable (by norm_num : 0 < (1 : ENNReal).toReal)

theorem sum_abs_le (u : FreeSpace o) (s : Finset ι) :
    ∑ i ∈ s, |coordinate o sep (e i).val u| ≤ 2 * ‖u‖ := by
  let j : ι ↪ M := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  simpa only [Finset.sum_map, j, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Function.Embedding.coeFn_mk] using sum_abs_coordinate_le o sep (s.map j) u

def analysisLinear : FreeSpace o →ₗ[ℝ] L1 ι where
  toFun u := ⟨fun i => coordinate o sep (e i).val u, memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      summable_of_sum_le (fun i => abs_nonneg (coordinate o sep (e i).val u))
        (sum_abs_le o sep e u))⟩
  map_add' u v := by apply lp.ext; funext i; exact map_add _ u v
  map_smul' r u := by apply lp.ext; funext i; exact map_smul _ r u

@[simp] theorem analysisLinear_apply (u : FreeSpace o) (i : ι) :
    analysisLinear o sep e u i = coordinate o sep (e i).val u := rfl

theorem analysis_bound (u : FreeSpace o) : ‖analysisLinear o sep e u‖ ≤ 2 * ‖u‖ := by
  rw [norm_eq_tsum]
  exact Real.tsum_le_of_sum_le (fun i => abs_nonneg _) (sum_abs_le o sep e u)

def analysis : FreeSpace o →L[ℝ] L1 ι :=
  (analysisLinear o sep e).mkContinuous 2 (analysis_bound o sep e)

@[simp] theorem analysis_apply (u : FreeSpace o) (i : ι) :
    analysis o sep e u i = coordinate o sep (e i).val u := rfl

variable (B : ℝ) (hb : ∀ x, dist x o ≤ B)
include hb

theorem term_bound (c : L1 ι) (i : ι) :
    ‖c i • delta o (e i).val‖ ≤ |c i| * B := by
  rw [norm_smul, Real.norm_eq_abs, delta_norm]
  exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)

theorem summable_term_norm (c : L1 ι) :
    Summable (fun i => ‖c i • delta o (e i).val‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_bound o e B hb c)
    ((summable_abs c).mul_right B)

theorem summable_term (c : L1 ι) : Summable (fun i => c i • delta o (e i).val) :=
  (summable_term_norm o e B hb c).of_norm

def synthesisLinear : L1 ι →ₗ[ℝ] FreeSpace o where
  toFun c := ∑' i, c i • delta o (e i).val
  map_add' c d := by
    simp only [lp.coeFn_add, Pi.add_apply, add_smul]
    exact Summable.tsum_add (summable_term o e B hb c) (summable_term o e B hb d)
  map_smul' r c := by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_assoc, RingHom.id_apply]
    exact (summable_term o e B hb c).tsum_const_smul r

theorem synthesis_bound (c : L1 ι) :
    ‖synthesisLinear o e B hb c‖ ≤ B * ‖c‖ := by
  change ‖∑' i, c i • delta o (e i).val‖ ≤ B * ‖c‖
  calc
    _ ≤ ∑' i, ‖c i • delta o (e i).val‖ :=
      norm_tsum_le_tsum_norm (summable_term_norm o e B hb c)
    _ ≤ ∑' i, |c i| * B := Summable.tsum_le_tsum (term_bound o e B hb c)
      (summable_term_norm o e B hb c) ((summable_abs c).mul_right B)
    _ = B * ‖c‖ := by rw [tsum_mul_right, norm_eq_tsum, mul_comm]

def synthesis : L1 ι →L[ℝ] FreeSpace o :=
  (synthesisLinear o e B hb).mkContinuous B (synthesis_bound o e B hb)

@[simp] theorem synthesis_apply (c : L1 ι) :
    synthesis o e B hb c = ∑' i, c i • delta o (e i).val := rfl

@[simp] theorem synthesis_single (i : ι) (r : ℝ) :
    synthesis o e B hb (lp.single 1 i r) = r • delta o (e i).val := by
  rw [synthesis_apply]
  simp only [lp.single_apply, Pi.single_apply, ite_smul, zero_smul]
  exact tsum_ite_eq i (fun j => r • delta o (e j).val)

omit hb in
@[simp] theorem analysis_delta (i : ι) :
    analysis o sep e (delta o (e i).val) = lp.single 1 i 1 := by
  apply lp.ext
  funext j
  have heq : (e i).val = (e j).val ↔ i = j := by
    constructor
    · intro h
      exact e.injective (Subtype.ext h)
    · rintro rfl
      rfl
  simp [analysis_apply, coordinate_delta, (e j).property, heq,
    lp.single_apply, Pi.single_apply, eq_comm]

@[simp] theorem analysis_synthesis (c : L1 ι) :
    analysis o sep e (synthesis o e B hb c) = c := by
  apply lp.ext
  funext i
  rw [analysis_apply, synthesis_apply,
    (coordinate o sep (e i).val).map_tsum (summable_term o e B hb c)]
  have heq (j : ι) : (e j).val = (e i).val ↔ j = i := by
    constructor
    · intro h
      exact e.injective (Subtype.ext h)
    · rintro rfl
      rfl
  simp [map_smul, coordinate_delta, (e i).property, heq, smul_eq_mul]

@[simp] theorem synthesis_analysis (u : FreeSpace o) :
    synthesis o e B hb (analysis o sep e u) = u := by
  let A := (synthesis o e B hb).comp (analysis o sep e)
  change A u = u
  refine freeSpace_induction (fun v => A v = v)
    (isClosed_eq A.continuous continuous_id) ?_ ?_ ?_ ?_ u
  · exact map_zero A
  · intro v w hv hw
    simp only [map_add, hv, hw]
  · intro r v hv
    simp only [map_smul, hv]
  · intro x
    by_cases hx : x = o
    · subst x
      simp [A]
    · obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      have hix : (e i).val = x := congrArg Subtype.val hi
      rw [← hix]
      change synthesis o e B hb (analysis o sep e (delta o (e i).val)) = _
      rw [analysis_delta, synthesis_single, one_smul]

def equiv : L1 ι ≃L[ℝ] FreeSpace o where
  toLinearEquiv :=
    { (synthesis o e B hb).toLinearMap with
      invFun := analysis o sep e
      left_inv := analysis_synthesis o sep e B hb
      right_inv := synthesis_analysis o sep e B hb }
  continuous_toFun := (synthesis o e B hb).continuous
  continuous_invFun := (analysis o sep e).continuous

@[simp] theorem equiv_apply (c : L1 ι) :
    equiv o sep e B hb c = ∑' i, c i • delta o (e i).val := rfl

theorem equiv_bounds (c : L1 ι) :
    (1 / 2 : ℝ) * ‖c‖ ≤ ‖equiv o sep e B hb c‖ ∧
    ‖equiv o sep e B hb c‖ ≤ B * ‖c‖ := by
  constructor
  · have h := analysis_bound o sep e (synthesis o e B hb c)
    change ‖analysis o sep e (synthesis o e B hb c)‖ ≤
      2 * ‖synthesis o e B hb c‖ at h
    rw [analysis_synthesis] at h
    change (1 / 2 : ℝ) * ‖c‖ ≤ ‖synthesis o e B hb c‖
    linarith
  · exact synthesis_bound o e B hb c

end Coefficients

end DiscreteFree
end

end OAI
