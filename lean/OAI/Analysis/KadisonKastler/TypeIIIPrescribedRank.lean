import OAI.Analysis.KadisonKastler.TypeIIISpectralMatrix

namespace OAI

/-! # Prescribed finite matrix ranks for type III projections

Every nonzero projection splits into any positive finite number of
nonzero pieces. Consequently a nontrivial projection can occupy either
chosen positive block size in a unital full matrix algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_proper_subprojection (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (hp : p.val ≠ 0) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ q.val ≠ 0 ∧ q.val ≠ p.val := by
  have hn : ¬ FiniteProjectionIn M p.val := fun h => hp (hM.purelyInfinite p.val p.property h)
  simp only [FiniteProjectionIn] at hn
  push Not at hn
  obtain ⟨v,hv,hpv,hproper⟩ := hn
  let w : PartialIsometry M := ⟨p,v,hv⟩
  refine ⟨w.target,?_,?_,hproper⟩
  · change p.val * (v * star v) = v * star v
    rw [← mul_assoc,hpv]
  · intro hz
    have hv0 : v = 0 := by
      have he := w.target_mul
      change (v * star v) * v = v at he
      rw [show v * star v = 0 from hz,zero_mul] at he
      exact he.symm
    apply hp
    rw [← hv,hv0,star_zero,zero_mul]

theorem TypeIIIFactor.exists_nonzero_fin_partition (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (n : ℕ) :
    ∃ q : Fin (n+1) → AlgebraProjection M,
      (∀ i, (q i).val ≠ 0) ∧
      (∀ i j, i ≠ j → (q i).val * (q j).val = 0) ∧
      (∑ i, (q i).val) = p.val ∧ (∀ i, q i ≤ p) := by
  induction n generalizing p with
  | zero =>
    refine ⟨fun _ => p,fun _ => hp,?_,?_,fun _ => le_rfl⟩
    · intro i j hij
      exact (hij (Fin.ext (by omega))).elim
    · simp
  | succ n ih =>
    obtain ⟨q,hqp,hq0,hqpne⟩ := hM.exists_proper_subprojection p hp
    let r : AlgebraProjection M := ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property hqp⟩
    have hr0 : r.val ≠ 0 := fun h => hqpne (sub_eq_zero.mp h).symm
    have hrp : r ≤ p := by
      change p.val * (p.val-q.val) = p.val-q.val
      rw [mul_sub,p.property.isIdempotentElem.eq,hqp]
    have hqr : q.val*r.val = 0 := by
      change q.val * (p.val-q.val) = 0
      rw [mul_sub,projection_mul_of_le hqp,q.property.isIdempotentElem.eq,sub_self]
    obtain ⟨f,hf0,hforth,hft,hfr⟩ := ih r hr0
    refine ⟨Fin.cons q f,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hq0
      · exact hf0 j
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact orthogonal_subprojections hqr le_rfl (hfr j)
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          exact PartialIsometry.orthogonal_reverse _ _
            (orthogonal_subprojections hqr le_rfl (hfr i))
        | succ j => exact hforth i j (fun he => hij (congrArg Fin.succ he))
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
      rw [hft]
      change q.val + (p.val-q.val) = p.val
      abel
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hqp
      · exact (hfr j).trans hrp

theorem TypeIIIFactor.exists_matrixUnits_prescribed_projection_rank
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (hp0 : p.val ≠ 0) (hp1 : p.val ≠ 1)
    (r s : ℕ) :
    ∃ E : MatrixUnitSystem (Fin (r+1) ⊕ Fin (s+1)) (Algebra M),
      (∑ i, E.entry (Sum.inl i) (Sum.inl i)) = p.val := by
  let q : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  have hq0 : q.val ≠ 0 := fun h => hp1 (sub_eq_zero.mp h).symm
  obtain ⟨a,ha0,haorth,hat,hap⟩ := hM.exists_nonzero_fin_partition p hp0 r
  obtain ⟨b,hb0,hborth,hbt,hbq⟩ := hM.exists_nonzero_fin_partition q hq0 s
  let f : Fin (r+1) ⊕ Fin (s+1) → AlgebraProjection M := Sum.elim a b
  have hpq : p.val * q.val = 0 := p.property.mul_one_sub_self
  have horth : ∀ i j, i ≠ j → (f i).val * (f j).val = 0 := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact haorth i j (fun he => hij (congrArg Sum.inl he))
      | inr j => exact orthogonal_subprojections hpq (hap i) (hbq j)
    | inr i =>
      cases j with
      | inl j =>
        exact PartialIsometry.orthogonal_reverse _ _
          (orthogonal_subprojections hpq (hap j) (hbq i))
      | inr j => exact hborth i j (fun he => hij (congrArg Sum.inr he))
  have htotal : (∑ i, (f i).val) = 1 := by
    rw [Fintype.sum_sum_type]
    change (∑ i, (a i).val) + (∑ i, (b i).val) = 1
    rw [hat,hbt]
    change p.val+(1-p.val) = 1
    abel
  obtain ⟨E,hE⟩ := hM.exists_matrixUnits_of_partition f
    (fun i => by cases i with | inl i => exact ha0 i | inr i => exact hb0 i)
    horth htotal
  exact ⟨E,(Finset.sum_congr rfl (fun i _ => hE (Sum.inl i))).trans hat⟩

end

end KadisonKastler

end OAI
