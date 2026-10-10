import OAI.Analysis.LipschitzFree.Evaluation

namespace OAI

/-!
# Contractive linearization of pointed Lipschitz maps
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
variable {M N : Type*} [MetricSpace M] [MetricSpace N]

def lipPullback (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) : Lip0 b →L[ℝ] Lip0 o :=
  LinearMap.mkContinuous
    { toFun := fun g => Lip0.ofBound o (fun x => g (f x)) (by simp [hbase])
        ‖g‖ (norm_nonneg _) (fun x y => (Lip0.sub_le g (f x) (f y)).trans
          (mul_le_mul_of_nonneg_left (by simpa using hf.dist_le_mul x y) (norm_nonneg _)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun g => by
      rw [one_mul]
      apply (Lip0.norm_le_iff _ (norm_nonneg _)).mpr
      intro x y
      exact (Lip0.sub_le g (f x) (f y)).trans
        (mul_le_mul_of_nonneg_left (by simpa using hf.dist_le_mul x y) (norm_nonneg _)))

@[simp] theorem lipPullback_apply (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) (g : Lip0 b) (x : M) :
    lipPullback o b f hbase hf g x = g (f x) := rfl

theorem lipPullback_bound (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) : ‖lipPullback o b f hbase hf‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro g
  rw [one_mul]
  apply (Lip0.norm_le_iff _ (norm_nonneg _)).mpr
  intro x y
  exact (Lip0.sub_le g (f x) (f y)).trans
    (mul_le_mul_of_nonneg_left (by simpa using hf.dist_le_mul x y) (norm_nonneg _))

theorem pullback_mem_free (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) (u : FreeSpace o) :
    u.val.comp (lipPullback o b f hbase hf) ∈ freeSubmodule b := by
  let L : FreeSpace o →L[ℝ] (Lip0 b →L[ℝ] ℝ) :=
    ((ContinuousLinearMap.compL ℝ (Lip0 b) (Lip0 o) ℝ).flip
      (lipPullback o b f hbase hf)).comp (freeSubmodule o).subtypeL
  change L u ∈ freeSubmodule b
  apply freeSpace_induction (fun v => L v ∈ freeSubmodule b)
    ((Submodule.isClosed_topologicalClosure _).preimage L.continuous)
    (by simp) (fun v w hv hw => by simpa using (freeSubmodule b).add_mem hv hw)
    (fun c v hv => by simpa using (freeSubmodule b).smul_mem c hv) (fun x => ?_) u
  change evaluation b (f x) ∈ freeSubmodule b
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self _))

def freeMap (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) : FreeSpace o →L[ℝ] FreeSpace b :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨u.val.comp (lipPullback o b f hbase hf), pullback_mem_free o b f hbase hf u⟩
      map_add' := fun u v => by apply Subtype.ext; ext g; rfl
      map_smul' := fun c u => by apply Subtype.ext; ext g; rfl }
    1 (fun u => by
      change ‖u.val.comp (lipPullback o b f hbase hf)‖ ≤ 1*‖u‖
      calc
        _ ≤ ‖u.val‖*‖lipPullback o b f hbase hf‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖u.val‖*1 := mul_le_mul_of_nonneg_left (lipPullback_bound o b f hbase hf) (norm_nonneg _)
        _ = _ := by simp; rfl)

@[simp] theorem freeMap_delta (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) (x : M) :
    freeMap o b f hbase hf (delta o x) = delta b (f x) := rfl

theorem freeMap_bound (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) : ‖freeMap o b f hbase hf‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  change ‖u.val.comp (lipPullback o b f hbase hf)‖ ≤ 1*‖u‖
  calc
    _ ≤ ‖u.val‖*‖lipPullback o b f hbase hf‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖u.val‖*1 := mul_le_mul_of_nonneg_left (lipPullback_bound o b f hbase hf) (norm_nonneg _)
    _ = _ := by simp; rfl

theorem freeMap_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (o : M)
    {T U : FreeSpace o →L[ℝ] E} (h : ∀ x, T (delta o x) = U (delta o x)) : T = U := by
  ext u
  exact freeSpace_induction (fun u => T u = U u) (isClosed_eq T.continuous U.continuous)
    (by simp) (fun u v hu hv => by simp [hu,hv])
    (fun c u hu => by simp [hu]) h u

end DiscreteFree
end

end

end OAI
