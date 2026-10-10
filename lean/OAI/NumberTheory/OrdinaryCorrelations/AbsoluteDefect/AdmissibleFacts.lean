import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MeanC
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.RetainedChoice

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
open Finset Filter OrdinaryCorrelations OrdinaryTwistWidth OrdinaryAnalyticCutoff

lemma admissible_facts {B C₀ τ H:ℝ} {D:Finset ℕ} (hD:Admissible B C₀ τ H D) :
    ∀d∈D,Squarefree d ∧ d≠0 ∧ d.primeFactors⊆core B∪center B := by
  intro d hd
  have h:=hD.2.2 d hd
  exact ⟨h.1,by omega,h.2.1⟩
lemma retained_properties {B C₀ τ H:ℝ} {D:Finset ℕ} (hD:Admissible B C₀ τ H D)
    {u:ℕ} (hu:u∈retainedSet B D) :
    0<u ∧ u.primeFactors⊆core B∪center B ∧ u.primeFactors.card≤J C₀ B ∧
      (∏p∈u.primeFactors,p)=u := by
  obtain ⟨q,hq,rfl⟩:=mem_image.mp hu
  obtain ⟨hd,hnW,hW⟩:=mem_choices.mp hq
  have h:=hD.2.2 q.1 hd
  dsimp [retainedChoice]
  refine ⟨retained_pos _ _,?_,?_,?_⟩
  · rw [retained_factors];exact sdiff_subset.trans h.2.1
  · rw [retained_factors];exact (Finset.card_le_card Finset.sdiff_subset).trans h.2.2.2.2.2
  · rw [retained_factors];rfl

lemma shift_properties {B C₀ τ H:ℝ} {D:Finset ℕ} (hB:1≤B)
    (hD:Admissible B C₀ τ H D) {u:ℕ} (hu:u∈retainedSet B D)
    {w:ℕ} (hw:w∈shiftSet B D u) :
    0<w ∧ P₀ B<(w:ℝ) ∧ H/u<(w:ℝ) ∧ (w:ℝ)≤τ*(H/u) ∧
      SourceRoughFourier.IsRough (P₀ B) w ∧ u*w∈D := by
  obtain ⟨q,hq,he⟩:=mem_image.mp hw
  obtain ⟨hqC,hret⟩:=mem_filter.mp hq
  obtain ⟨hd,hnW,hW⟩:=mem_choices.mp hqC
  have hpr:=choice_primes hqC
  have hrecon:=fiber_reconstruct (fun d hd=>⟨(admissible_facts hD d hd).1,
    (admissible_facts hD d hd).2.1⟩) hq
  have hwpos : 0<w := by
    rw [←he]
    exact prod_pos (fun p hp=>(hpr p hp).pos)
  have hfac : w.primeFactors=q.2 := by
    rw [←he]
    exact removed_factors q.2 hpr
  have hprod : u*w=q.1 := by rw [←he];exact hrecon
  have hwp : P₀ B<(w:ℝ) := by
    obtain ⟨p,hp⟩:=nonempty_iff_ne_empty.mpr hnW
    have hpd : p∣w := by rw [←he];exact dvd_prod_of_mem (fun p=>p) hp
    have hpW : p∈center B := (mem_filter.mp (hW hp)).1
    have hp0:=prime_lower B hB (mem_union_right (core B) hpW)
    exact hp0.trans_le (by exact_mod_cast Nat.le_of_dvd hwpos hpd)
  have hu0 : (0:ℝ)<u := by exact_mod_cast (retained_properties hD hu).1
  have hprodR : (u:ℝ)*(w:ℝ)=(q.1:ℝ) := by exact_mod_cast hprod
  have hf:=hD.2.2 q.1 hd
  refine ⟨hwpos,hwp,?_,?_,?_,?_⟩
  · apply (div_lt_iff₀ hu0).mpr
    nlinarith [hf.2.2.2.1]
  · rw [←mul_div_assoc]
    apply (le_div_iff₀ hu0).mpr
    nlinarith [hf.2.2.2.2.1]
  · intro p hp hpB hpd
    have hpF : p∈w.primeFactors:=Nat.mem_primeFactors.mpr ⟨hp,hpd,hwpos.ne'⟩
    rw [hfac] at hpF
    have hpc:=prime_lower B hB (mem_union_right (core B) (mem_filter.mp (hW hpF)).1)
    exact (not_lt_of_ge hpB) hpc
  · rwa [hprod]

lemma retained_scale {B C₀ τ H:ℝ} {D:Finset ℕ} (hB:1≤B) (hτ:0<τ)
    (hD:Admissible B C₀ τ H D) {u:ℕ} (hu:u∈retainedSet B D) : P₀ B/τ≤H/u := by
  obtain ⟨q,hq,hret⟩:=mem_image.mp hu
  have hqF : q∈choiceFiber B D u := mem_filter.mpr ⟨hq,hret⟩
  have hyr : removedChoice q∈shiftSet B D u := mem_image_of_mem _ hqF
  have hs:=shift_properties hB hD hu hyr
  apply (div_le_iff₀ hτ).mpr
  nlinarith [hs.2.1,hs.2.2.2.1]

lemma fiberCoeff_norm {B C₀ τ H:ℝ} {D:Finset ℕ} (hB:1≤B)
    (hD:Admissible B C₀ τ H D) (a:ℕ→ℂ) (ha:∀d∈D,‖a d‖≤1)
    {u:ℕ} (hu:u∈retainedSet B D) {w:ℕ} (hw:w∈shiftSet B D u) : ‖fiberCoeff a u w‖≤1 := by
  have hd:=(shift_properties hB hD hu hw).2.2.2.2.2
  rw [fiberCoeff,norm_mul,norm_pow]
  have hc : ‖(-1/4:ℂ)‖≤1 := by norm_num
  exact (mul_le_mul (ha _ hd) (pow_le_one₀ (norm_nonneg _) hc) (by positivity) (by positivity)).trans_eq (by ring)
end OrdinaryAnalyticCentering

end

end OAI
