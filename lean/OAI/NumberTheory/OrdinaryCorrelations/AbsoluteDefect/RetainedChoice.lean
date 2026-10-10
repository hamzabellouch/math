import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumDvdDilateComplex

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff

namespace OrdinaryAnalyticCentering
open Finset OrdinaryCorrelations OrdinaryTwistWidth OrdinaryAnalyticCutoff
noncomputable def retainedChoice (q:Σ_:ℕ,Finset ℕ) : ℕ := retained q.1 q.2
noncomputable def removedChoice (q:Σ_:ℕ,Finset ℕ) : ℕ := removed q.2
noncomputable def retainedSet (B:ℝ) (D:Finset ℕ) : Finset ℕ := (choices B D).image retainedChoice
noncomputable def choiceFiber (B:ℝ) (D:Finset ℕ) (u:ℕ) : Finset (Σ_:ℕ,Finset ℕ) :=
  (choices B D).filter (fun q=>retainedChoice q=u)
noncomputable def shiftSet (B:ℝ) (D:Finset ℕ) (u:ℕ) : Finset ℕ :=
  (choiceFiber B D u).image removedChoice
noncomputable def fiberCoeff (a:ℕ→ℂ) (u w:ℕ) : ℂ := a (u*w)*(-1/4:ℂ)^w.primeFactors.card
noncomputable def fiberSum (phi:ℝ→ℝ) (B:ℝ) (D:Finset ℕ)
    (a f g:ℕ→ℂ) (h u:ℕ) (Y:ℝ) : ℂ :=
  ∑v∈Icc 1 ⌊Y⌋₊,∑w∈shiftSet B D u,(fiberCoeff a u w/(w:ℂ))*
    f (u*v)*g (u*(v+h*w))*cut phi B u v*cut phi B u (v+h*w)

lemma choice_primes {B:ℝ} {D:Finset ℕ} {q:Σ_:ℕ,Finset ℕ}
    (hq:q∈choices B D) : ∀p∈q.2,p.Prime := by
  intro p hp
  exact center_prime B (mem_filter.mp ((mem_choices.mp hq).2.2 hp)).1
lemma fiber_reconstruct {B:ℝ} {D:Finset ℕ} (hD:∀d∈D,Squarefree d ∧ d≠0)
    {u:ℕ} {q:Σ_:ℕ,Finset ℕ} (hq:q∈choiceFiber B D u) : u*removedChoice q=q.1 := by
  obtain ⟨hq,hret⟩:=mem_filter.mp hq
  obtain ⟨hd,hnW,hW⟩:=mem_choices.mp hq
  have he:=retained_mul_removed q.1 (hD _ hd).1 q.2 (hW.trans (centralPrimes_subset B (hD _ hd).2))
  simpa only [←hret,retainedChoice,removedChoice] using he
lemma fiber_removed_inj (B:ℝ) (D:Finset ℕ) (hD:∀d∈D,Squarefree d ∧ d≠0) (u:ℕ) :
    Set.InjOn removedChoice (choiceFiber B D u : Set (Σ_:ℕ,Finset ℕ)) := by
  intro q hq r hr he
  have hd:q.1=r.1 := by rw [←fiber_reconstruct hD hq,←fiber_reconstruct hD hr,he]
  have hW:q.2=r.2 := by
    have hp:=congrArg Nat.primeFactors he
    rw [show removedChoice q=removed q.2 from rfl,show removedChoice r=removed r.2 from rfl,
      removed_factors q.2 (choice_primes (mem_filter.mp hq).1),
      removed_factors r.2 (choice_primes (mem_filter.mp hr).1)] at hp
    exact hp
  cases q with
  | mk d W =>
    cases r with
    | mk e V =>
      dsimp at hd hW
      subst e
      subst V
      rfl

lemma sum_fiber_eq (phi:ℝ→ℝ) (B:ℝ) (D:Finset ℕ)
    (hD:∀d∈D,Squarefree d ∧ d≠0) (a f g:ℕ→ℂ) (h u:ℕ) (X:ℝ) (hX:0≤X) :
    (∑q∈choiceFiber B D u,choiceTerm phi B a f g h X q)=
      (divisorWeight B u:ℂ)*fiberSum phi B D a f g h u (X/u) := by
  unfold fiberSum shiftSet
  rw [mul_sum]
  simp_rw [sum_image (fiber_removed_inj B D hD u),mul_sum]
  rw [Finset.sum_comm (s:=Icc 1 ⌊X/u⌋₊)]
  apply sum_congr rfl
  intro q hq
  obtain ⟨hqC,hret⟩:=mem_filter.mp hq
  obtain ⟨hd,hnW,hW⟩:=mem_choices.mp hqC
  have he:=choiceTerm_dilate phi B (hD _ hd).1 (hD _ hd).2 q.2 hW a f g h X hX
  change retained q.1 q.2=u at hret
  rw [hret,mul_sum] at he
  rw [he]
  apply sum_congr rfl
  intro v hv
  simp only [removedChoice,fiberCoeff,removed_factors q.2 (choice_primes hqC)]

lemma regroup_centered (phi:ℝ→ℝ) (B:ℝ) (D:Finset ℕ)
    (hD:∀d∈D,Squarefree d ∧ d≠0 ∧ d.primeFactors⊆core B∪center B)
    (a f g:ℕ→ℂ) (h:ℕ) (X:ℝ) (hX:0≤X) :
    centeredSum phi B D a f g h X=rawSum phi B D a f g h X+
      ∑u∈retainedSet B D,(divisorWeight B u:ℂ)*fiberSum phi B D a f g h u (X/u) := by
  rw [centered_eq_raw_add phi B D hD]
  congr 1
  rw [←sum_fiberwise_of_maps_to (fun q hq=>mem_image_of_mem retainedChoice hq)
    (choiceTerm phi B a f g h X)]
  apply sum_congr rfl
  intro u hu
  exact sum_fiber_eq phi B D (fun d hd=>⟨(hD d hd).1,(hD d hd).2.1⟩) a f g h u X hX
end OrdinaryAnalyticCentering

end

end OAI
