import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevTraceChain

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma h1_limit_ae_closed {u : ℕ → H1} {w : H1}
    (hu : Tendsto u atTop (𝓝 w)) (K : R3 → Set JetFiber)
    (hK : ∀ x, IsClosed (K x)) (hm : ∀ n, ∀ᵐ x ∂ballMeasure, (u n).val x∈K x) :
    ∀ᵐ x ∂ballMeasure, w.val x∈K x := by
  have ht : Tendsto (fun n => (u n).val) atTop (𝓝 w.val) :=
    continuous_subtype_val.continuousAt.tendsto.comp hu
  obtain ⟨φ,hφ,hφae⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  filter_upwards [hφae,ae_all_iff.mpr hm] with x hx hy
  exact (hK x).mem_of_tendsto hx (Eventually.of_forall (fun n => hy (φ n)))

lemma h1_limit_bounded {u : ℕ → H1} {w : H1} {M : ℝ}
    (hu : Tendsto u atTop (𝓝 w))
    (hm : ∀ n, ∀ᵐ x ∂ballMeasure, |weakValue (u n) x|≤M) :
    ∀ᵐ x ∂ballMeasure, |weakValue w x|≤M := by
  exact h1_limit_ae_closed hu (fun _ => {z | |jetValue z|≤M})
    (fun _ => isClosed_le (jetValue.continuous.abs) continuous_const) hm

lemma h1_limit_supported {u : ℕ → H1} {w : H1} {r : ℝ}
    (hu : Tendsto u atTop (𝓝 w))
    (hm : ∀ n, ∀ᵐ x ∂ballMeasure, r<‖x‖ →
      weakValue (u n) x=0 ∧ weakGradient (u n) x=0) :
    ∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0 := by
  exact h1_limit_ae_closed hu
    (fun x => {z | r<‖x‖ → jetValue z=0 ∧ jetGradient z=0})
    (fun x => by
      by_cases hx : r<‖x‖
      · simpa only [hx,true_implies,Set.inter_def,Set.mem_ofPred_eq] using
          (isClosed_eq jetValue.continuous continuous_const).inter
            (isClosed_eq jetGradient.continuous continuous_const)
      · simp only [hx,IsEmpty.forall_iff,Set.ofPred_true]
        exact isClosed_univ) hm

lemma weakValue_sum (s : Finset ℕ) (u : ℕ → H1) :
    weakValue (∑ n∈s, u n) =ᵐ[ballMeasure] fun x => ∑ n∈s, weakValue (u n) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx
    change jetValue ((0:JetSpace) x)=0
    rw [hx,Pi.zero_apply,map_zero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [weakValue_add (u a) (∑ i∈s,u i),ih] with x hx hy
    simpa only [Pi.add_apply,hy] using hx

lemma weakGradient_sum (s : Finset ℕ) (u : ℕ → H1) :
    weakGradient (∑ n∈s, u n) =ᵐ[ballMeasure] fun x => ∑ n∈s, weakGradient (u n) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx
    change jetGradient ((0:JetSpace) x)=0
    rw [hx,Pi.zero_apply,map_zero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [weakGradient_add (u a) (∑ i∈s,u i),ih] with x hx hy
    simpa only [Pi.add_apply,hy] using hx

theorem source_series_limit (Z : ℕ → H1) (b : ℕ → ℝ)
    (hnorm : Summable (fun n => ‖Z n‖)) (hb : Summable b)
    (hb0 : ∀ n, 0≤b n) (hZ : ∀ n, Z n∈H10)
    (hbound : ∀ n, ∀ᵐ x ∂ballMeasure, |weakValue (Z n) x|≤b n)
    (r : ℝ) (hsupp : ∀ n, ∀ᵐ x ∂ballMeasure, r<‖x‖ →
      weakValue (Z n) x=0 ∧ weakGradient (Z n) x=0) :
    ∃ w : H1, w∈H10 ∧
      Tendsto (fun N => ∑ n∈Finset.range N, Z n) atTop (𝓝 w) ∧
      (∀ᵐ x ∂ballMeasure, |weakValue w x|≤∑' n,b n) ∧
      (∀ᵐ x ∂ballMeasure, r<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0) := by
  classical
  have hsum : Summable Z := hnorm.of_norm
  refine ⟨∑' n,Z n,?_,hsum.hasSum.tendsto_sum_nat,?_,?_⟩
  · exact H10_isClosed.mem_of_tendsto hsum.hasSum.tendsto_sum_nat
      (Eventually.of_forall (fun N => H10.sum_mem (fun n _ => hZ n)))
  · apply h1_limit_bounded hsum.hasSum.tendsto_sum_nat
    intro N
    filter_upwards [weakValue_sum (Finset.range N) Z,ae_all_iff.mpr hbound] with x hx hy
    rw [hx]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun n _ => hy n)).trans (Summable.sum_le_tsum _ (fun n _ => hb0 n) hb))
  · apply h1_limit_supported hsum.hasSum.tendsto_sum_nat
    intro N
    filter_upwards [weakValue_sum (Finset.range N) Z,weakGradient_sum (Finset.range N) Z,
      ae_all_iff.mpr hsupp] with x hv hg hx
    intro hr
    simp only [hv,hg]
    exact ⟨Finset.sum_eq_zero (fun n _ => (hx n hr).1),Finset.sum_eq_zero (fun n _ => (hx n hr).2)⟩

end ScalarConductivity

end
end

end OAI
