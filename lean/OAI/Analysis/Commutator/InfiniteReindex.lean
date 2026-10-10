import Mathlib
import OAI.Analysis.Commutator.InfiniteAmplification

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace ENNReal

namespace Kadison.InfiniteAmplification

variable {ι κ : Type*}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma norm_sq (x : Space ι H) : ‖x‖^2=∑' i,‖x i‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) x

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma extend_sq (e : ι ↪ κ) (x : ι → H) (k : κ) :
    ‖Function.extend e x 0 k‖^2=Function.extend e (fun i => ‖x i‖^2) 0 k := by
  classical
  by_cases hk : k∈Set.range e
  · obtain ⟨i,rfl⟩ := hk
    simp only [e.injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ hk,Function.extend_apply' _ _ _ hk]
    simp

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma reindex_mem (e : ι ↪ κ) (x : Space ι H) : Memℓp (Function.extend e x 0) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,extend_sq]
  apply (summable_extend_zero e.injective).mpr
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (lp.memℓp x).summable
    (by norm_num : 0<(2:ℝ≥0∞).toReal)

def reindex (e : ι ↪ κ) : Space ι H →ₗᵢ[ℂ] Space κ H where
  toFun x := ⟨Function.extend e x 0,reindex_mem e x⟩
  map_add' x y := by
    classical
    ext k
    by_cases hk : k∈Set.range e
    · obtain ⟨i,rfl⟩ := hk
      simp only [e.injective.extend_apply,lp.coeFn_add,Pi.add_apply]
    · simp only [lp.coeFn_add,Pi.add_apply,Function.extend_apply' _ _ _ hk,Pi.zero_apply,add_zero]
  map_smul' c x := by
    classical
    ext k
    by_cases hk : k∈Set.range e
    · obtain ⟨i,rfl⟩ := hk
      simp only [e.injective.extend_apply,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply]
    · simp only [lp.coeFn_smul,Pi.smul_apply,Function.extend_apply' _ _ _ hk,Pi.zero_apply,smul_zero]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,norm_sq]
    change (∑' k,‖Function.extend e x 0 k‖^2)=∑' i,‖x i‖^2
    simp only [extend_sq]
    exact tsum_extend_zero e.injective (fun i => ‖x i‖^2)

omit [CompleteSpace H] in
@[simp] lemma reindex_apply (e : ι ↪ κ) (x : Space ι H) (i : ι) : reindex e x (e i)=x i :=
  e.injective.extend_apply _ _ _

omit [CompleteSpace H] in
lemma reindex_intertwines (e : ι ↪ κ) (T : H →L[ℂ] H) (x : Space ι H) :
    reindex e (map T x)=map T (reindex e x) := by
  classical
  ext k
  by_cases hk : k∈Set.range e
  · obtain ⟨i,rfl⟩ := hk
    simp only [reindex_apply,map_apply]
  · change Function.extend e (map T x) 0 k=T (Function.extend e x 0 k)
    rw [Function.extend_apply' _ _ _ hk,Function.extend_apply' _ _ _ hk]
    exact (map_zero T).symm

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma flatten_mem (x : Space ι (Space κ H)) : Memℓp (fun p : ι×κ => x p.1 p.2) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  apply (summable_prod_of_nonneg (fun p => sq_nonneg ‖x p.1 p.2‖)).mpr
  constructor
  · intro i
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (lp.memℓp (x i)).summable
      (by norm_num : 0<(2:ℝ≥0∞).toReal)
  · simp only [←norm_sq]
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (lp.memℓp x).summable
      (by norm_num : 0<(2:ℝ≥0∞).toReal)

def flatten : Space ι (Space κ H) →ₗᵢ[ℂ] Space (ι×κ) H where
  toFun x := ⟨fun p => x p.1 p.2,flatten_mem x⟩
  map_add' x y := by ext p; rfl
  map_smul' c x := by ext p; rfl
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,norm_sq]
    have hs : Summable (fun p : ι×κ => ‖x p.1 p.2‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (flatten_mem x).summable
        (by norm_num : 0<(2:ℝ≥0∞).toReal)
    change (∑' p : ι×κ,‖x p.1 p.2‖^2)=∑' i,‖x i‖^2
    rw [hs.tsum_prod]
    exact tsum_congr (fun i => (norm_sq (x i)).symm)

omit [CompleteSpace H] in
@[simp] lemma flatten_apply (x : Space ι (Space κ H)) (p : ι×κ) : flatten x p=x p.1 p.2 := rfl

end Kadison.InfiniteAmplification

end

end
end

end OAI
