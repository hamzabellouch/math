import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.EnsembleMoments
import OAI.Analysis.CoulombRadii.Screening.AtomicCapRaw
import OAI.Analysis.CoulombRadii.RandomFields.EnsembleCauchy

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma sliceExpectation_localCount_le {m k : ℕ} (u : H1Vector (m+k))
    {A : Set Space} (hA : MeasurableSet A) :
    sliceExpectation u (fun _ x => localCount A x) ≤ (m:ℝ)*mass u := by
  rw [←integral_mass_coreSlice u,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_const_mul]
  apply integral_mono
  · simpa only [pow_one] using sliceCount_weight_integrable u hA s 1
  · exact (mass_coreSlice_integrable u s).const_mul _
  · intro x
    dsimp only
    nlinarith [mul_le_mul_of_nonneg_left (localCount_le A x) (mass_nonneg (u.coreSlice s x))]

lemma sliceExpectation_count_cap_addback {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {a : ℝ} (ha : 0<a) (y : Space)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-y‖) :
    sliceExpectation u (fun s x => localCount (Metric.closedBall y a) x*
      (localFarCap S (u.coreSlice s x).normalized x y a+(m:ℝ)/(3*a))) ≤
    sliceExpectation u (fun s x => localCount (Metric.closedBall y a) x*
      localFarCap S (u.coreSlice s x).normalized x y a)+(m:ℝ)^2/(3*a)*mass u := by
  have hc (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*
      (localCount (Metric.closedBall y a) x*localFarCap S (u.coreSlice s x).normalized x y a)) := by
    simpa only [mul_assoc] using sliceCount_cap_weight_integrable S u measurableSet_closedBall s ha y hnuc
  have hn (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*
      ((m:ℝ)/(3*a)*localCount (Metric.closedBall y a) x)) := by
    have h : Integrable (fun x => mass (u.coreSlice s x)*localCount (Metric.closedBall y a) x) := by
      simpa only [pow_one] using sliceCount_weight_integrable u measurableSet_closedBall s 1
    simpa only [mul_left_comm (mass _) ((m:ℝ)/(3*a))] using h.const_mul ((m:ℝ)/(3*a))
  have he : sliceExpectation u (fun s x => localCount (Metric.closedBall y a) x*
      (localFarCap S (u.coreSlice s x).normalized x y a+(m:ℝ)/(3*a))) =
      sliceExpectation u (fun s x => localCount (Metric.closedBall y a) x*
        localFarCap S (u.coreSlice s x).normalized x y a)+
      (m:ℝ)/(3*a)*sliceExpectation u (fun _ x => localCount (Metric.closedBall y a) x) := by
    rw [←sliceExpectation_const_mul,←sliceExpectation_add u _ _ hc hn]
    congr 1
    funext s x
    ring
  rw [he]
  have H := mul_le_mul_of_nonneg_left (sliceExpectation_localCount_le u (A:=Metric.closedBall y a) measurableSet_closedBall)
    (show 0 ≤ (m:ℝ)/(3*a) by positivity)
  have heq : (m:ℝ)/(3*a)*((m:ℝ)*mass u)=(m:ℝ)^2/(3*a)*mass u := by ring
  rw [heq] at H
  exact add_le_add le_rfl H

theorem conditionalOutCost_ensemble_cover_lower {P C : Type*} [Fintype P] [Fintype C] {J : ℕ}
    (S : Nuclei J) (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    (y : C → Space) (a : C → ℝ) (ha : ∀ c, 0<a c)
    (hnuc : ∀ c j, 4*a c ≤ ‖S.position j-y c‖)
    (hsupp : ∀ p s, ∀ᵐ x, mass ((u p).coreSlice s x) ≠0 → ∀ i, ∃ c, ‖position x i-y c‖ ≤ a c) :
    -(∑ c, (Real.sqrt ((∑ p, sliceExpectation (u p) (fun _ x => (localCount (Metric.closedBall (y c) (a c)) x)^2))*
      (∑ p, sliceExpectation (u p) (fun s x => (localFarCap S ((u p).coreSlice s x).normalized x (y c) (a c))^2)))+
      (∑ p, (m p:ℝ)^2*mass (u p))/(3*a c))) ≤ ∑ p, conditionalOutCost S (u p) := by
  let F := fun c p (s : Spins (m p)) (x : Configuration (m p)) =>
    localCount (Metric.closedBall (y c) (a c)) x*(localFarCap S ((u p).coreSlice s x).normalized x (y c) (a c)+(m p:ℝ)/(3*a c))
  have hlow := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => conditionalOutCost_lower_cover S (u p) y a ha hnuc (hsupp p))
  change (∑ p, -(∑ c, sliceExpectation (u p) (F c p))) ≤ _ at hlow
  rw [Finset.sum_neg_distrib,Finset.sum_comm] at hlow
  refine (neg_le_neg (Finset.sum_le_sum (fun c (_ : c∈Finset.univ) => ?_))).trans hlow
  have hcs := slice_ensemble_mul_le_sqrt m k u
    (fun _ _ x => localCount (Metric.closedBall (y c) (a c)) x)
    (fun p s x => localFarCap S ((u p).coreSlice s x).normalized x (y c) (a c))
    (fun p s => sliceCount_weight_integrable (u p) measurableSet_closedBall s 2)
    (fun p s => localFarCap_weight_integrable S (u p) s (ha c) (y c) (hnuc c) 2)
    (fun p s => by simpa only [mul_assoc] using sliceCount_cap_weight_integrable S (u p) measurableSet_closedBall s (ha c) (y c) (hnuc c))
  have hsum := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => sliceExpectation_count_cap_addback S (u p) (ha c) (y c) (hnuc c))
  rw [Finset.sum_add_distrib] at hsum
  have he : (∑ p, (m p:ℝ)^2/(3*a c)*mass (u p))=(∑ p, (m p:ℝ)^2*mass (u p))/(3*a c) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [he] at hsum
  exact hsum.trans (add_le_add hcs le_rfl)

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb
namespace RecordedEnsemble

theorem atomic_cost_lower {n J : ℕ} {C : Type*} [Fintype C]
    (S : Nuclei J) (hatom : ∀ j, S.position j=0) (ψ : H1Vector n)
    (T : RecordedEnsemble n) (hT : T.Conserves ψ) (z : C → Space) (hz : ∀ c, z c≠0)
    (hcover : ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 →
      ∀ i, ∃ c, ‖position x i-z c‖≤atomicCellScale (z c))
    {H : ℝ}
    (hraw : ∀ c v, ‖v-z c‖≤2*atomicCellScale (z c) → T.rawSquare S v (atomicCellScale v)≤H) :
    -(∑ c, (Real.sqrt (localCountSecondMoment ψ (Metric.closedBall (z c) (atomicCellScale (z c)))*(8*H))+
      ((Fintype.card C:ℝ)*(∑ d, localCountSecondMoment ψ (Metric.closedBall (z d) (atomicCellScale (z d)))))/
        (3*atomicCellScale (z c)))) ≤ ∑ p, conditionalOutCost S (T.vector p) := by
  let a := fun c => atomicCellScale (z c)
  have ha (c) : 0<a c := atomicCellScale_pos (hz c)
  have hnuc (c) (j) : 4*a c≤‖S.position j-z c‖ := by
    rw [hatom j]
    exact atomicCellScale_nucleus_far _
  have HC := conditionalOutCost_ensemble_cover_lower S T.out T.core T.vector z a ha hnuc hcover
  have hcap (c) : (∑ p, sliceExpectation (T.vector p) (fun s x =>
      (localFarCap S ((T.vector p).coreSlice s x).normalized x (z c) (a c))^2))≤8*H :=
    atomic_cap_sq_le_of_raw_bound S T.out T.core T.vector (hz c) (hnuc c) (hraw c)
  have hcount := out_square_cover hT (fun c => Metric.closedBall (z c) (a c))
    (fun _ => measurableSet_closedBall)
    (fun p s => by
      filter_upwards [hcover p s] with x hx
      intro hm i
      obtain ⟨c,hc⟩ := hx hm i
      exact ⟨c,by simpa only [Metric.mem_closedBall,dist_eq_norm] using hc⟩)
  refine (neg_le_neg (Finset.sum_le_sum (fun c _ => ?_))).trans HC
  apply add_le_add
  · apply Real.sqrt_le_sqrt
    apply mul_le_mul (hT.recorded_secondMoment measurableSet_closedBall) (hcap c)
    · exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun s _ => integral_nonneg
        (fun x => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
    · exact localCountSecondMoment_nonneg ψ _
  · exact div_le_div_of_nonneg_right hcount (mul_nonneg (by norm_num) (ha c).le)

lemma patches_cover {n : ℕ} {I : Type*} [Fintype I]
    (T : RecordedEnsemble n) (target : I → Space) (htarget : ∀ i, target i≠0)
    (hsupp : T.OutSupported (⋃ i, Metric.closedBall (target i) (80*atomicCellScale (target i)))) :
    ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 →
      ∀ j, ∃ c : I × {v : Space // v∈atomicPatchMesh},
        ‖position x j-atomicMeshCenter (target c.1) c.2.val‖≤
          atomicCellScale (atomicMeshCenter (target c.1) c.2.val) := by
  intro p s
  filter_upwards [(hsupp p).recorded_positions s] with x hx
  intro hm j
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hx hm j)
  obtain ⟨v,hv,hclose⟩ := atomicMesh_cover (htarget i) (position x j)
    (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hi)
  exact ⟨(i,⟨v,hv⟩),hclose⟩

end RecordedEnsemble
end Coulomb

end

end OAI
