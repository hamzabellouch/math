import Mathlib
import OAI.Analysis.BoundedHochschild.Cochains

namespace OAI

/-! Weak-star cochain limits, averaging operators and preadjoints. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 

def PredualTendsto (a : I → M) (l : Filter I) (b : M) : Prop :=
  ∀ z : X, Tendsto (fun i => e.symm (a i) z) l (𝓝 (e.symm b z))

lemma predual_tendsto_unique {a : I → M} {l : Filter I} [l.NeBot] {b c : M}
    (hb : PredualTendsto e a l b) (hc : PredualTendsto e a l c) : b = c := by
  apply e.symm.injective
  ext z
  exact tendsto_nhds_unique (hb z) (hc z)

lemma predual_tendsto_const (m : M) (l : Filter I) :
    PredualTendsto e (fun _ => m) l m := fun _ => tendsto_const_nhds

lemma predual_tendsto_add {a b : I → M} {l : Filter I} {c d : M}
    (ha : PredualTendsto e a l c) (hb : PredualTendsto e b l d) :
    PredualTendsto e (fun i => a i+b i) l (c+d) := by
  intro z
  simpa only [map_add,add_apply] using (ha z).add (hb z)

lemma predual_tendsto_smul {a : I → M} {l : Filter I} {b : M}
    (ha : PredualTendsto e a l b) (c : ℂ) :
    PredualTendsto e (fun i => c • a i) l (c • b) := by
  intro z
  simpa only [LinearIsometryEquiv.map_smulₛₗ,smul_apply,smul_eq_mul]
    using (ha z).const_mul (starRingEnd ℂ c)

lemma exists_predual_ultralimit (u : Ultrafilter I) (a : I → M) (C : ℝ)
    (hb : ∀ i, ‖a i‖ ≤ C) :
    ∃ b : M, ‖b‖ ≤ C ∧ PredualTendsto e a u b := by
  let j : I → WeakDual ℂ X := fun i => StrongDual.toWeakDual (e.symm (a i))
  have hmem : (u.map j : Filter (WeakDual ℂ X)) ≤
      𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) C) := by
    rw [Ultrafilter.coe_map,Filter.map_le_iff_le_comap, Filter.comap_principal]
    apply Filter.le_principal_iff.mpr
    exact Filter.Eventually.of_forall fun i => by
      simpa [j,Metric.mem_closedBall] using hb i
  obtain ⟨b,hb',ht⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) C).ultrafilter_le_nhds (u.map j) hmem
  refine ⟨e (WeakDual.toStrongDual b),?_,?_⟩
  · simpa only [LinearIsometryEquiv.norm_map,Set.mem_preimage,
      Metric.mem_closedBall,dist_zero_right] using hb'
  · intro z
    have hjt : Tendsto j (u : Filter I) (𝓝 b) := by
      simpa only [Ultrafilter.coe_map, Filter.Tendsto] using ht
    have hz := (WeakDual.eval_continuous z).tendsto b |>.comp hjt
    change Tendsto (fun i => e.symm (a i) z) (u : Filter I) (𝓝 (b z)) at hz
    simpa only [LinearIsometryEquiv.symm_apply_apply, WeakDual.toStrongDual_apply] using hz

 

theorem bounded_cochain_ultralimit {n : ℕ} (u : Ultrafilter I)
    (F : I → Cochain M n) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ i, ‖F i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C ∧
      ∀ x, PredualTendsto e (fun i => F i x) u (G x) := by
  classical
  have hex (x : Fin n → M) : ∃ b : M, ‖b‖ ≤ C * ∏ k, ‖x k‖ ∧
      PredualTendsto e (fun i => F i x) u b :=
    exists_predual_ultralimit e u (fun i => F i x) _ (fun i =>
      (F i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hF i)
        (Finset.prod_nonneg (fun k _ => norm_nonneg (x k)))))
  choose b hb ht using hex
  let G₀ : MultilinearMap ℂ (fun _ : Fin n => M) M :=
    { toFun := b
      map_update_add' := fun x k a c => by
        apply predual_tendsto_unique e (ht (Function.update x k (a+c)))
        simpa only [ContinuousMultilinearMap.map_update_add] using
          predual_tendsto_add e (ht (Function.update x k a)) (ht (Function.update x k c))
      map_update_smul' := fun x k c a => by
        apply predual_tendsto_unique e (ht (Function.update x k (c • a)))
        simpa only [ContinuousMultilinearMap.map_update_smul] using
          predual_tendsto_smul e (ht (Function.update x k a)) c }
  exact ⟨G₀.mkContinuous C hb, G₀.mkContinuous_norm_le hC hb, ht⟩

end BoundedHochschild

 

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

noncomputable def translateLastCLM {n : ℕ} (u : unitary M) :
    Cochain M (n+1) →L[ℂ] Cochain M (n+1) :=
  LinearMap.mkContinuous
    { toFun := fun f => translateLast f u
      map_add' := fun f g => translateLast_add f g u
      map_smul' := fun c f => translateLast_smul c f u }
    1 (fun f => by change ‖translateLast f u‖ ≤ 1 * ‖f‖; simpa only [one_mul] using norm_translateLast_le f u)

@[simp] theorem translateLast_one {n : ℕ} (f : Cochain M (n+1)) :
    translateLast f 1 = f := by
  ext x
  simp only [translateLast_apply,Submonoid.coe_one,star_one,mul_one]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem translateLast_mul {n : ℕ} (f : Cochain M (n+1)) (u v : unitary M) :
    translateLast (translateLast f v) u = translateLast f (u*v) := by
  ext x
  simp only [translateLast_apply,Fin.snoc_last,Fin.snoc_castSucc,Submonoid.coe_mul,
    star_mul,mul_assoc]

noncomputable def averageLastCLM {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) :
    Cochain M (n+1) →L[ℂ] Cochain M (n+1) :=
  LinearMap.mkContinuous
    { toFun := averageLast p u
      map_add' := fun f g => by
        simp only [averageLast,translateLast_add,smul_add]
        exact Summable.tsum_add (summable_averageLast p u hp hs.summable f)
          (summable_averageLast p u hp hs.summable g)
      map_smul' := fun c f => by
        simp only [averageLast,translateLast_smul,smul_comm (p _ : ℂ) c,
          tsum_const_smul'',RingHom.id_apply] }
    1 (fun f => by change ‖averageLast p u f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using norm_averageLast_le p u hp hs f)

@[simp] theorem averageLastCLM_apply {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) (f : Cochain M (n+1)) :
    averageLastCLM p u hp hs f = averageLast p u f := rfl

 

noncomputable def residualCLM {n : ℕ} (x : Fin (n+1) → M) : Cochain M (n+1) →L[ℂ] M :=
  (ContinuousLinearMap.mul ℂ M (x 0)).comp
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M
        (Fin.snoc (fun i : Fin n => x i.succ) 1)) +
    ∑ j : Fin n, ((-1:ℂ)^(j.val+1)) •
      ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M
        (Fin.snoc (mergeInputs x j) 1) +
    ((-1:ℂ)^(n+1)) • ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M x

@[simp] theorem residualCLM_apply {n : ℕ} (x : Fin (n+1) → M) (F : Cochain M (n+1)) :
    residualCLM x F =
      x 0 * F (Fin.snoc (fun i : Fin n => x i.succ) 1) +
        ∑ j : Fin n, ((-1:ℂ)^(j.val+1)) • F (Fin.snoc (mergeInputs x j) 1) +
        ((-1:ℂ)^(n+1)) • F x := by
  simp [residualCLM]

lemma residual_eq_differential {n : ℕ} (x : Fin (n+1) → M) (F : Cochain M (n+1)) :
    residualCLM x F = differentialValue (insertLast F 1) x +
      ((-1:ℂ)^(n+1)) •
        (F x - insertLast F 1 (fun i : Fin n => x i.castSucc) * x (Fin.last n)) := by
  simp only [residualCLM_apply,differentialValue,insertLast_apply,smul_sub]
  abel

lemma insertLast_translateLast {n : ℕ} (f : Cochain M (n+1)) (u : unitary M) :
    insertLast (translateLast f u) 1 = lastHomotopy f (u:M) (star (u:M)) := by
  ext x
  simp [translateLast_apply]

lemma residual_translate_cocycle {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x = 0)
    (u : unitary M) (x : Fin (n+1) → M) :
    residualCLM x (translateLast f u) = ((-1:ℂ)^(n+1)) • f x := by
  rw [residual_eq_differential,insertLast_translateLast,
    lastHomotopy_cocycle f hf (u:M) (star (u:M)) (Unitary.mul_star_self_of_mem u.property)]
  simp only [translateLast_apply,smul_add,smul_sub]
  abel

 

lemma residual_average_invariant {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) (F : Cochain M (n+1))
    (c : (Fin (n+1) → M) → M)
    (hF : ∀ v x, residualCLM x (translateLast F v) = c x) :
    ∀ v x, residualCLM x (translateLast (averageLast p u F) v) = c x := by
  intro v x
  let L : Cochain M (n+1) →L[ℂ] M := (residualCLM x).comp (translateLastCLM v)
  have he : L (averageLast p u F) = ∑' i, (p i : ℂ) • c x := by
    rw [averageLast,L.map_tsum (summable_averageLast p u hp hs.summable F)]
    congr 1
    funext i
    simp only [map_smul,L,ContinuousLinearMap.comp_apply]
    change (p i:ℂ) • residualCLM x (translateLast (translateLast F (u i)) v) = _
    rw [translateLast_mul,hF]
  change L (averageLast p u F) = _
  rw [he]
  have hsc : HasSum (fun i => (p i : ℂ)) 1 := by simpa only [Complex.ofReal_one] using Complex.hasSum_ofReal.mpr hs
  simpa only [one_smul] using (hsc.smul_const (c x)).tsum_eq

lemma residual_iterate {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x = 0) (j : ℕ) :
    ∀ v x, residualCLM x (translateLast ((averageLastCLM p u hp hs)^[j] f) v) =
      ((-1:ℂ)^(n+1)) • f x := by
  induction j with
  | zero => exact fun v x => residual_translate_cocycle f hf v x
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact residual_average_invariant p u hp hs _ _ ih

end BoundedHochschild

 

open Filter Topology
namespace BoundedHochschild
variable {M X I J : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_of_norm {a : I → M} {l : Filter I} {b : M}
    (h : Tendsto a l (𝓝 b)) : PredualTendsto e a l b := by
  intro z
  exact (((ContinuousLinearMap.apply ℂ ℂ) z).continuous.tendsto _).comp
    (e.symm.continuous.tendsto _ |>.comp h)

lemma predual_tendsto_neg {a : I → M} {l : Filter I} {b : M}
    (h : PredualTendsto e a l b) : PredualTendsto e (fun i => -a i) l (-b) := by
  intro z
  simpa only [map_neg,neg_apply] using (h z).neg

lemma predual_tendsto_sub {a b : I → M} {l : Filter I} {c d : M}
    (ha : PredualTendsto e a l c) (hb : PredualTendsto e b l d) :
    PredualTendsto e (fun i => a i-b i) l (c-d) := by
  simpa only [sub_eq_add_neg] using predual_tendsto_add e ha (predual_tendsto_neg e hb)

lemma predual_tendsto_sum {a : I → J → M} {b : J → M} (l : Filter I) (s : Finset J)
    (h : ∀ j ∈ s, PredualTendsto e (fun i => a i j) l (b j)) :
    PredualTendsto e (fun i => ∑ j ∈ s, a i j) l (∑ j ∈ s, b j) := by
  intro z
  simpa only [map_sum,sum_apply] using
    tendsto_finsetSum s (fun j hj => h j hj z)

lemma predual_norm_le {a : I → M} {l : Filter I} [l.NeBot] {b : M} (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C) (h : PredualTendsto e a l b) : ‖b‖ ≤ C := by
  rw [← e.symm.norm_map b]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro z
  apply le_of_tendsto (h z).norm
  filter_upwards [ha] with i hi
  calc
    ‖e.symm (a i) z‖ ≤ ‖e.symm (a i)‖ * ‖z‖ := (e.symm (a i)).le_opNorm z
    _ ≤ C * ‖z‖ := mul_le_mul_of_nonneg_right (by simpa using hi) (norm_nonneg _)

lemma predual_tendsto_tsum [CompleteSpace M] {a : I → J → M} {b : J → M}
    {l : Filter I} [l.NeBot] (C : J → ℝ) (hC : Summable C)
    (ha : ∀ i j, ‖a i j‖ ≤ C j)
    (h : ∀ j, PredualTendsto e (fun i => a i j) l (b j)) :
    PredualTendsto e (fun i => ∑' j, a i j) l (∑' j, b j) := by
  have hCb (j : J) : ‖b j‖ ≤ C j :=
    predual_norm_le e (C j) (by obtain ⟨i,_⟩ := (Eventually.of_forall (fun _i : I => True.intro) : ∀ᶠ _i in l, True).exists; exact (norm_nonneg (a i j)).trans (ha i j))
      (Eventually.of_forall fun i => ha i j) (h j)
  have hsa (i : I) : Summable (a i) := hC.of_norm_bounded (ha i)
  have hsb : Summable b := hC.of_norm_bounded hCb
  intro z
  let ev : M →L⋆[ℂ] ℂ := ((ContinuousLinearMap.apply ℂ ℂ) z).comp
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  change Tendsto (fun i => ev (∑' j, a i j)) l (𝓝 (ev (∑' j, b j)))
  simp_rw [ev.map_tsum (hsa _),ev.map_tsum hsb]
  apply tendsto_tsum_of_dominated_convergence (hC.mul_right ‖z‖) (fun j => h j z)
  exact Eventually.of_forall fun i j => calc
    ‖ev (a i j)‖ ≤ ‖e.symm (a i j)‖ * ‖z‖ := (e.symm (a i j)).le_opNorm z
    _ ≤ C j * ‖z‖ := mul_le_mul_of_nonneg_right (by simpa using ha i j) (norm_nonneg _)

 

def HasPreadjoint (L : M →L[ℂ] M) : Prop :=
  ∀ z : X, ∃ z' : X, ∀ a : M, e.symm (L a) z = e.symm a z'

lemma HasPreadjoint.tendsto {L : M →L[ℂ] M} (hL : HasPreadjoint e L)
    {a : I → M} {l : Filter I} {b : M} (h : PredualTendsto e a l b) :
    PredualTendsto e (fun i => L (a i)) l (L b) := by
  intro z
  obtain ⟨z',hz'⟩ := hL z
  simpa only [hz'] using h z'

end BoundedHochschild
end

end OAI
