import OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFourier
import OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic
namespace SevenEighths.InverseInitialOverlapIdealFourier
open InverseMoment InverseInitialOverlapFourier
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def activeIndices (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (c : Ideal Eis) : Finset ι := (I.biUnion L).filter (fun p=>primes p∣c)

omit [DecidableEq σ] in
theorem activeIndices_mem (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (c : Ideal Eis) {i : σ} (hi : i∈I) {p : ι} (hp : p∈L i) :
    p∈activeIndices primes I L c ↔ primes p∣c := by
  simp only [activeIndices,Finset.mem_filter]
  exact and_iff_right (Finset.mem_biUnion.mpr ⟨i,hi,hp⟩)

theorem indexed_mark_active (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (c : Ideal Eis) :
    indexedIdealMark primes I L a c=primeMark I L a (activeIndices primes I L c) := by
  unfold indexedIdealMark primeMark primeSlot
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro p hp
  simp only [activeIndices_mem primes I L c hi hp]

theorem indexed_overlap_separation (g : 𝓢(ℝ,ℂ))
    (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (c : Ideal Eis) (xj xc : ℝ) :
    (∑p∈I.pi L,(∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)*
      g (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*logPhase t xc*
        indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c := by
  simp_rw [indexed_mark_active]
  rw [←overlap_tuple_separation]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [activeIndices_mem primes I L c i.property ((Finset.mem_pi.mp hp) i.val i.property)]

theorem indexed_overlap_integrable (g : 𝓢(ℝ,ℂ))
    (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (c : Ideal Eis) (xj xc : ℝ) :
    Integrable (fun t:ℝ=>density g xj t*logPhase t xc*
      indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c) := by
  simp_rw [indexed_mark_active]
  exact overlap_mode_integrable g I L a y _ xj xc

omit [DecidableEq σ] [DecidableEq ι] in
theorem tuple_gate_product (primes : ι→Ideal Eis) (I : Finset σ)
    (a : σ→ι→ℂ) (p : ∀i∈I,ι) (c : Ideal Eis)
    (hc : Pairwise (Function.onFun IsCoprime (fun i:I=>primes (p i.val i.property)))) :
    (∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)=
      if (∏i∈I.attach,primes (p i.val i.property))∣c then
        ∏i∈I.attach,a i.val (p i.val i.property) else 0 := by
  by_cases h : (∏i∈I.attach,primes (p i.val i.property))∣c
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i hi
    exact ite_eq_left ((Finset.dvd_prod_of_mem (fun i:I=>primes (p i.val i.property)) hi).trans h)
  · rw [ite_eq_right h]
    have hn : ∃i:I,¬primes (p i.val i.property)∣c := by
      by_contra hn
      push Not at hn
      apply h
      exact Finset.prod_dvd_of_coprime (hc.set_pairwise _) (fun i _=>hn i)
    obtain ⟨i,hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_attach _ i) (ite_eq_right hi)

theorem finite_ideal_overlap_separation (g : 𝓢(ℝ,ℂ))
    (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (C : Finset (Ideal Eis))
    (coefficient : Ideal Eis→ℂ) (xj : ℝ) (xc : Ideal Eis→ℝ) :
    (∑c∈C,coefficient c*
      ∑p∈I.pi L,(∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)*
        g (xj+xc c-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*
        ∑c∈C,coefficient c*logPhase t (xc c)*
          indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c := by
  simp_rw [indexed_overlap_separation]
  simp only [Finset.mul_sum]
  have hi (c:Ideal Eis) : Integrable (fun t:ℝ=>coefficient c*
      (density g xj t*logPhase t (xc c)*indexedIdealMark primes I L
        (fun i p=>a i p*logPhase (-t) (y i p)) c)) :=
    (indexed_overlap_integrable g primes I L a y c xj (xc c)).const_mul _
  have he (c:Ideal Eis) (t:ℝ) : density g xj t*(coefficient c*logPhase t (xc c)*
      indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c)=
      coefficient c*(density g xj t*logPhase t (xc c)*
      indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c) := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun c _=>hi c)]
  simp only [integral_const_mul]

end SevenEighths.InverseInitialOverlapIdealFourier

end

end OAI
