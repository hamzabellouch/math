import OAI.Analysis.FactorGeneration.Dimension

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace AlgebraProjection

/-- Actual least upper bounds for arbitrary nonempty directed projection nets. -/
theorem exists_isLUB_monotone
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q) :
    ∃ p : AlgebraProjection M, IsLUB (Set.range q) p := by
  obtain ⟨v,hv,hs,_⟩ := PartialIsometry.traceFree_monotone_least_supports
    (fun i => PartialIsometry.onProjection (q i)) (fun _ _ h => hq h)
  refine ⟨v.support,?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact PartialIsometry.support_mono (hv i)
  · intro p hp
    exact hs p (fun i => hp ⟨i,rfl⟩)

end AlgebraProjection
namespace PartialIsometry

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hfinite in
/-- Extend a given embedding to a larger source while keeping its target in r. -/
theorem exists_extension_of_subequivalent (v : PartialIsometry M)
    (p r : AlgebraProjection M) (hp : v.support ≤ p) (hr : v.target ≤ r)
    (hpr : p.Subequivalent r) :
    ∃ w : PartialIsometry M, v ≤ w ∧ w.support=p ∧ w.target ≤ r := by
  obtain ⟨u,hu,ht⟩ := AlgebraProjection.remainder_subequivalent hfinite hfactor hp hr
    (show v.support.Equivalent v.target from ⟨v,rfl,rfl⟩) hpr
  have hi : v.support.val*u.support.val=0 := by
    rw [hu]
    exact AlgebraProjection.remainder_orthogonal _ _ hp
  have ho : v.target.val*u.target.val=0 :=
    projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal _ _ hr) le_rfl ht
  refine ⟨v.patch u hi ho,v.le_patch u hi ho,?_,?_⟩
  · apply Subtype.ext
    change v.support.val+u.support.val=p.val
    rw [hu]
    change v.support.val+(p.val-v.support.val)=p.val
    abel
  · have he : (v.patch u hi ho).target=orthogonalSum v.target u.target ho :=
      Subtype.ext (v.patch_target u hi ho)
    rw [he]
    exact orthogonalSum_le ho hr (ht.trans (AlgebraProjection.remainder_le _ _ hr))

include hfactor hfinite in
/-- A sequence of comparable sources admits compatible actual embeddings. -/
theorem exists_monotone_embeddings (q : ℕ → AlgebraProjection M) (hq : Monotone q)
    (r : AlgebraProjection M) (hr : ∀ n, (q n).Subequivalent r) :
    ∃ a : ℕ → PartialIsometry M, Monotone a ∧
      (∀ n, (a n).support=q n) ∧ (∀ n, (a n).target ≤ r) := by
  classical
  obtain ⟨v,hv,ht⟩ := hr 0
  let step (n : ℕ) (w : {w : PartialIsometry M // w.support=q n ∧ w.target ≤ r}) :=
    exists_extension_of_subequivalent hfactor hfinite w.val (q (n+1)) r
      (by rw [w.property.1]; exact hq (Nat.le_succ n)) w.property.2 (hr (n+1))
  let a : (n : ℕ) → {w : PartialIsometry M // w.support=q n ∧ w.target ≤ r} :=
    Nat.rec ⟨v,hv,ht⟩ (fun n w => ⟨(step n w).choose,(step n w).choose_spec.2⟩)
  refine ⟨fun n => (a n).val,?_,fun n => (a n).property.1,fun n => (a n).property.2⟩
  apply monotone_nat_of_le_succ
  intro n
  exact (step n (a n)).choose_spec.1

end PartialIsometry
namespace AlgebraProjection

/-- Sequential increasing-union comparison, with a constructed compatible
partial-isometry limit. No dimension-continuity premise occurs. -/
theorem isLUB_subequivalent_of_sequence
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (q : ℕ → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p)
    (r : AlgebraProjection M) (hr : ∀ n, (q n).Subequivalent r) :
    p.Subequivalent r := by
  obtain ⟨a,ha,hs,ht⟩ := PartialIsometry.exists_monotone_embeddings hfactor hfinite q hq r hr
  obtain ⟨v,hv,hvs,hvt⟩ := PartialIsometry.traceFree_monotone_least_supports a ha
  refine ⟨v,le_antisymm (hvs p (fun n => by rw [hs]; exact hp.1 ⟨n,rfl⟩)) ?_,hvt r ht⟩
  apply hp.2
  rintro _ ⟨n,rfl⟩
  rw [← hs n]
  exact PartialIsometry.support_mono (hv n)

end AlgebraProjection
end

/-! Continuity of the constructed dimension on arbitrary increasing projection
nets. Compatible sequential embeddings are proved first; dimension approximation
then constructs a countable subfamily with the same projection supremum. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem traceFreeDimension_range_bddAbove {I : Type*} (q : I → AlgebraProjection M) :
    BddAbove (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) :=
  ⟨1,by rintro _ ⟨i,rfl⟩; exact traceFreeDimension_le_one hfactor hdiff (q i)⟩

include hfinite in
/-- Continuity on sequences follows from compatible embeddings into each
concrete dyadic upper approximant of the real supremum. -/
theorem traceFreeDimension_isLUB_sequence
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (q : ℕ → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    traceFreeDimension hfactor hdiff p =
      sSup (Set.range (fun n => traceFreeDimension hfactor hdiff (q n))) := by
  let c := sSup (Set.range (fun n => traceFreeDimension hfactor hdiff (q n)))
  have hb := traceFreeDimension_range_bddAbove hfactor hdiff q
  have hne := Set.range_nonempty (fun n => traceFreeDimension hfactor hdiff (q n))
  have hqc (n : ℕ) : traceFreeDimension hfactor hdiff (q n) ≤ c := le_csSup hb ⟨n,rfl⟩
  have hc : 0 ≤ c := (traceFreeDimension_nonneg hfactor hdiff (q 0)).trans (hqc 0)
  have hc1 : c ≤ 1 := csSup_le hne (by
    rintro _ ⟨n,rfl⟩; exact traceFreeDimension_le_one hfactor hdiff (q n))
  apply le_antisymm ?_ (csSup_le hne (by
    rintro _ ⟨n,rfl⟩
    exact traceFreeDimension_mono hfactor hdiff (hp.1 ⟨n,rfl⟩)))
  apply le_of_all_dyadic_errors
  intro n
  obtain ⟨r,hcr,hrc⟩ := traceFreeDimension_exists_upper hfactor hdiff hfinite hunit c hc hc1 n
  have hqr (k : ℕ) : (q k).Subequivalent r :=
    (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit _ _).mp
      ((hqc k).trans hcr)
  exact (traceFreeDimension_subequivalent hfactor hdiff
    (AlgebraProjection.isLUB_subequivalent_of_sequence hfactor hfinite q hq p hp r hqr)).trans hrc

/-- Every countable family in a directed preorder has an increasing majorant
above a specified index. This is not countable cofinality of the preorder. -/
theorem exists_monotone_dominating_from
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] (f : ℕ → I) (i : I) :
    ∃ a : ℕ → I, Monotone a ∧ (∀ n, f n ≤ a n) ∧ (∀ n, i ≤ a n) := by
  classical
  let upper (x y : I) := (exists_ge_ge x y).choose
  have hl (x y : I) : x ≤ upper x y := (exists_ge_ge x y).choose_spec.1
  have hr (x y : I) : y ≤ upper x y := (exists_ge_ge x y).choose_spec.2
  let a : ℕ → I := Nat.rec (upper i (f 0)) (fun n j => upper j (f (n+1)))
  have ha : Monotone a := monotone_nat_of_le_succ (fun n => hl (a n) (f (n+1)))
  refine ⟨a,ha,?_,fun n => (hl i (f 0)).trans (ha (Nat.zero_le n))⟩
  intro n
  cases n with
  | zero => exact hr i (f 0)
  | succ n => exact hr (a n) (f (n+1))

include hfinite in
/-- Construct an increasing countable subfamily whose supremum dimension is
the real supremum of the entire directed family. No countability is assumed. -/
theorem traceFreeDimension_exists_exhausting_sequence
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q) :
    ∃ (a : ℕ → I) (s : AlgebraProjection M), Monotone a ∧
      IsLUB (Set.range (fun n => q (a n))) s ∧
      traceFreeDimension hfactor hdiff s =
        sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  classical
  let c := sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i)))
  have hb := traceFreeDimension_range_bddAbove hfactor hdiff q
  have hqc (i : I) : traceFreeDimension hfactor hdiff (q i) ≤ c := le_csSup hb ⟨i,rfl⟩
  have hex (n : ℕ) : ∃ i, c-1/2^n < traceFreeDimension hfactor hdiff (q i) := by
    have hn : c-1/2^n<c := sub_lt_self c (by positivity)
    obtain ⟨_,⟨i,rfl⟩,hi⟩ := exists_lt_of_lt_csSup
      (Set.range_nonempty (fun i => traceFreeDimension hfactor hdiff (q i))) hn
    exact ⟨i,hi⟩
  choose f hf using hex
  obtain ⟨a,ha,hfa,_⟩ := exists_monotone_dominating_from f (Classical.choice ‹Nonempty I›)
  obtain ⟨s,hs⟩ := AlgebraProjection.exists_isLUB_monotone (fun n => q (a n)) (hq.comp ha)
  refine ⟨a,s,ha,hs,le_antisymm ?_ ?_⟩
  · rw [traceFreeDimension_isLUB_sequence hfactor hdiff hfinite hunit _ (hq.comp ha) s hs]
    exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨n,rfl⟩; exact hqc (a n))
  · apply le_of_all_dyadic_errors
    intro n
    have hfq := traceFreeDimension_mono hfactor hdiff (hq (hfa n))
    have hqs := traceFreeDimension_mono hfactor hdiff (hs.1 ⟨n,rfl⟩)
    have hfn := hf n
    linarith

include hfinite in
/-- The constructed countable supremum bounds the entire net: adjoining any
one index cannot increase its dimension, so strict increase forces equality. -/
theorem traceFreeDimension_exists_isLUB
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q) :
    ∃ p : AlgebraProjection M, IsLUB (Set.range q) p ∧
      traceFreeDimension hfactor hdiff p =
        sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  obtain ⟨a,s,ha,hs,hd⟩ := traceFreeDimension_exists_exhausting_sequence
    hfactor hdiff hfinite hunit q hq
  have hupper (i : I) : q i ≤ s := by
    obtain ⟨b,hb,hab,hib⟩ := exists_monotone_dominating_from a i
    obtain ⟨t,ht⟩ := AlgebraProjection.exists_isLUB_monotone (fun n => q (b n)) (hq.comp hb)
    have hst : s ≤ t := hs.2 (by
      rintro _ ⟨n,rfl⟩; exact (hq (hab n)).trans (ht.1 ⟨n,rfl⟩))
    have htd : traceFreeDimension hfactor hdiff t ≤ traceFreeDimension hfactor hdiff s := by
      rw [hd,traceFreeDimension_isLUB_sequence hfactor hdiff hfinite hunit _ (hq.comp hb) t ht]
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨n,rfl⟩
      exact le_csSup (traceFreeDimension_range_bddAbove hfactor hdiff q) ⟨b n,rfl⟩
    have he : s=t := by
      by_contra hne
      exact (not_lt_of_ge htd) (traceFreeDimension_strictMono hfactor hdiff hfinite hunit
        (lt_of_le_of_ne hst hne))
    rw [he]
    exact (hq (hib 0)).trans (ht.1 ⟨0,rfl⟩)
  refine ⟨s,⟨?_,?_⟩,hd⟩
  · rintro _ ⟨i,rfl⟩; exact hupper i
  · intro p hp
    exact hs.2 (by rintro _ ⟨n,rfl⟩; exact hp ⟨a n,rfl⟩)

include hfinite in
/-- Order continuity on arbitrary nonempty directed projection nets. -/
theorem traceFreeDimension_isLUB_monotone
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    traceFreeDimension hfactor hdiff p =
      sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  obtain ⟨s,hs,hd⟩ := traceFreeDimension_exists_isLUB hfactor hdiff hfinite hunit q hq
  have he : p=s := le_antisymm (hp.2 hs.1) (hs.2 hp.1)
  rw [he]
  exact hd

end Tracial

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/
section
universe v
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}

/-- Arbitrary increasing-union comparison, now a consequence of the constructed
dimension continuity and exact classification of comparison. -/
theorem traceFree_isLUB_subequivalent
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p)
    (r : AlgebraProjection M) (hr : ∀ i, (q i).Subequivalent r) :
    p.Subequivalent r := by
  apply (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit p r).mp
  rw [traceFreeDimension_isLUB_monotone hfactor hdiff hfinite hunit q hq p hp]
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨i,rfl⟩
  exact traceFreeDimension_subequivalent hfactor hdiff (hr i)

end Tracial

/-- The same actual dimension satisfies all finite laws and arbitrary-directed
supremum continuity under exactly the original IsII1Factor hypothesis. -/
theorem isII1Factor_projection_dimension_orderContinuous
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S) :
    ∃ D : Tracial.AlgebraProjection (vonNeumannOfWOTClosed S hS.weaklyClosed) → ℝ,
      D ⟨1,IsStarProjection.one _⟩=1 ∧
      (∀ q, 0 ≤ D q ∧ D q ≤ 1) ∧
      (∀ q, D q=0 ↔ q.val=0) ∧
      (∀ q r, D q ≤ D r ↔ q.Subequivalent r) ∧
      (∀ q r, D q=D r ↔ q.Equivalent r) ∧
      (∀ q r (ho : q.val*r.val=0), D (Tracial.orthogonalSum q r ho)=D q+D r) ∧
      (∀ (I : Type v) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
        (q : I → Tracial.AlgebraProjection (vonNeumannOfWOTClosed S hS.weaklyClosed)),
        Monotone q → ∃ p, IsLUB (Set.range q) p ∧
          D p=sSup (Set.range (fun i => D (q i)))) := by
  let M := vonNeumannOfWOTClosed S hS.weaklyClosed
  have hf : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    obtain ⟨z,hz⟩ := hS.factor c hc
    exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z)⟩
  let p : Tracial.AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  have hp : p.val≠0 := by
    intro h
    exact hS.nonzero (congrArg Subtype.val h).symm
  have hle (q : Tracial.AlgebraProjection M) : q ≤ p := one_mul _
  refine ⟨Tracial.traceFreeDimension hf hS.diffuse,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Tracial.traceFreeDyadicSup_self hf hS.diffuse p
  · intro q
    exact ⟨Tracial.traceFreeDimension_nonneg hf hS.diffuse q,
      Tracial.traceFreeDimension_le_one hf hS.diffuse q⟩
  · intro q
    exact Tracial.traceFreeDyadicSup_eq_zero_iff hf hS.diffuse hS.finite p q hp
  · intro q r
    exact Tracial.traceFreeDimension_le_iff_subequivalent hf hS.diffuse hS.finite hp q r
  · intro q r
    exact Tracial.traceFreeDyadicSup_eq_iff_equivalent hf hS.diffuse hS.finite p q r hp (hle q) (hle r)
  · intro q r ho
    exact Tracial.traceFreeDyadicSup_orthogonal_add hf hS.diffuse hS.finite p q r hp (hle q) (hle r) ho
  · intro I _ _ _ q hq
    exact Tracial.traceFreeDimension_exists_isLUB hf hS.diffuse hS.finite hp q hq

end

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_exists_small_subprojection
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (hp : p.val≠0) (ε : ℝ) (hε : 0<ε) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ 0 < traceFreeDimension hfactor hdiff q ∧
      traceFreeDimension hfactor hdiff q < ε := by
  classical
  have hpD : 0 < traceFreeDimension hfactor hdiff p :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite _ p hp
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (lt_min hε hpD) (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hn0 : (0 : ℝ)<1/2^n := by positivity
  have hi : Nonempty (DyadicIndex n) := Fintype.card_pos_iff.mp (by
    rw [card_dyadicIndex]; positivity)
  let i : DyadicIndex n := Classical.choice hi
  let e := (traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset {i}
  have heD : traceFreeDimension hfactor hdiff e=1/2^n := by
    change traceFreeDyadicSup hfactor hdiff ⟨1,IsStarProjection.one _⟩
      ((traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset {i})=1/2^n
    rw [traceFreeDyadicSup_subset hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ hunit]
    simp only [dyadicWeight,Finset.card_singleton,Nat.cast_one]
  obtain ⟨v,hv,ht⟩ := (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit e p).mp
    (by rw [heD]; exact (lt_min_iff.mp hn).2.le)
  have he : traceFreeDimension hfactor hdiff v.target=1/2^n := by
    have h := traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
      (show e.Equivalent v.target from ⟨v,hv,rfl⟩)
    exact h.symm.trans heD
  exact ⟨v.target,ht,by rw [he]; exact hn0,by rw [he]; exact (lt_min_iff.mp hn).1⟩

include hfinite in
theorem traceFreeDimension_bounded_chain
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Set (AlgebraProjection M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p : AlgebraProjection M) (d : ℝ)
    (hp : ∀ q ∈ c, q ≤ p) (hd : ∀ q ∈ c, traceFreeDimension hfactor hdiff q ≤ d) :
    ∃ q : AlgebraProjection M, (∀ r ∈ c, r ≤ q) ∧ q ≤ p ∧
      traceFreeDimension hfactor hdiff q ≤ d := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v,h,le_rfl⟩
    · exact ⟨u,le_rfl,h⟩⟩
  obtain ⟨q,hq,hD⟩ := traceFreeDimension_exists_isLUB hfactor hdiff hfinite hunit
    (fun r : c => r.val) (fun _ _ h => h)
  refine ⟨q,fun r hr => hq.1 ⟨⟨r,hr⟩,rfl⟩,?_,?_⟩
  · exact hq.2 (by rintro _ ⟨r,rfl⟩; exact hp r.val r.property)
  · rw [hD]
    exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨r,rfl⟩; exact hd r.val r.property)

include hfinite in
theorem traceFreeDimension_exists_maximal_below
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (d : ℝ) (hd : 0 ≤ d) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ traceFreeDimension hfactor hdiff q ≤ d ∧
      ∀ r : AlgebraProjection M, r ≤ p → traceFreeDimension hfactor hdiff r ≤ d →
        q ≤ r → r ≤ q := by
  let S : Set (AlgebraProjection M) := {q | q ≤ p ∧ traceFreeDimension hfactor hdiff q ≤ d}
  obtain ⟨q,hq⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨q,hcq,hqp,hqd⟩ := traceFreeDimension_bounded_chain hfactor hdiff hfinite hunit
        c hchain hne p d (fun q hq => (hc hq).1) (fun q hq => (hc hq).2)
      exact ⟨q,⟨hqp,hqd⟩,hcq⟩
    · refine ⟨⟨0,IsStarProjection.zero _⟩,⟨mul_zero _,?_⟩,?_⟩
      · have hz := traceFreeDyadicSup_zero hfactor hdiff ⟨1,IsStarProjection.one _⟩
          ⟨0,IsStarProjection.zero _⟩ hunit rfl
        exact hz.le.trans hd
      · intro r hr
        exact (hne ⟨r,hr⟩).elim)
  exact ⟨q,hq.1.1,hq.1.2,fun r hr hrd hqr => hq.2 ⟨hr,hrd⟩ hqr⟩

include hfinite in
/-- Every dimension between zero and D(p) is realized inside p. -/
theorem traceFreeDimension_exists_subprojection
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (d : ℝ) (hd : 0 ≤ d)
    (hdp : d ≤ traceFreeDimension hfactor hdiff p) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ traceFreeDimension hfactor hdiff q=d := by
  obtain ⟨q,hqp,hqd,hmax⟩ := traceFreeDimension_exists_maximal_below
    hfactor hdiff hfinite hunit p d hd
  refine ⟨q,hqp,le_antisymm hqd ?_⟩
  by_contra hnot
  have hlt : traceFreeDimension hfactor hdiff q < d := lt_of_not_ge hnot
  let r := AlgebraProjection.remainder q p hqp
  have hr : r.val≠0 := by
    change p.val-q.val≠0
    intro hz
    have he : p=q := Subtype.ext (sub_eq_zero.mp hz)
    rw [he] at hdp
    exact (not_lt_of_ge hdp) hlt
  obtain ⟨s,hs,hpos,hsmall⟩ := traceFreeDimension_exists_small_subprojection
    hfactor hdiff hfinite hunit r hr (d-traceFreeDimension hfactor hdiff q) (sub_pos.mpr hlt)
  have ho : q.val*s.val=0 :=
    projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal q p hqp) le_rfl hs
  let t := orthogonalSum q s ho
  have htp : t ≤ p := orthogonalSum_le ho hqp (hs.trans (AlgebraProjection.remainder_le q p hqp))
  have htD : traceFreeDimension hfactor hdiff t=
      traceFreeDimension hfactor hdiff q+traceFreeDimension hfactor hdiff s :=
    traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ q s
      hunit (one_mul _) (one_mul _) ho
  have htd : traceFreeDimension hfactor hdiff t ≤ d := by rw [htD]; linarith
  have hle : t ≤ q := hmax t htp htd (le_orthogonalSum_left _ _ ho)
  have hmono := traceFreeDimension_mono hfactor hdiff hle
  rw [htD] at hmono
  linarith

end

/-! Finite partitions with prescribed dimensions, and actual equivalent
partitions of arbitrary positive finite size in every corner. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_remainder
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (q p : AlgebraProjection M) (hq : q ≤ p) :
    traceFreeDimension hfactor hdiff (AlgebraProjection.remainder q p hq)=
      traceFreeDimension hfactor hdiff p-traceFreeDimension hfactor hdiff q := by
  have h := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
    ⟨1,IsStarProjection.one _⟩ q (AlgebraProjection.remainder q p hq)
    hunit (one_mul _) (one_mul _) (AlgebraProjection.remainder_orthogonal q p hq)
  rw [AlgebraProjection.orthogonalSum_remainder] at h
  change traceFreeDimension hfactor hdiff p=
    traceFreeDimension hfactor hdiff q+
      traceFreeDimension hfactor hdiff (AlgebraProjection.remainder q p hq) at h
  linarith

include hfinite in
/-- Every prescribed finite list of nonnegative dimensions summing to D(p)
is realized by pairwise orthogonal actual projections summing to p. -/
theorem traceFreeDimension_exists_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (p : AlgebraProjection M) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hsum : ∑ i, d i=traceFreeDimension hfactor hdiff p) :
    ∃ q : Fin n → AlgebraProjection M, (∀ i, q i ≤ p) ∧
      (∀ i j, i≠j → (q i).val*(q j).val=0) ∧
      (∑ i, (q i).val)=p.val ∧ (∀ i, traceFreeDimension hfactor hdiff (q i)=d i) := by
  induction n generalizing p with
  | zero =>
    have hpD : traceFreeDimension hfactor hdiff p=0 := by simpa using hsum.symm
    have hpz : p.val=0 := (traceFreeDyadicSup_eq_zero_iff hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p hunit).mp hpD
    refine ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_,fun i => Fin.elim0 i⟩
    simpa using hpz.symm
  | succ n ih =>
    have hsum' : d 0+∑ i : Fin n, d i.succ=traceFreeDimension hfactor hdiff p := by
      simpa only [Fin.sum_univ_succ] using hsum
    have hdp : d 0 ≤ traceFreeDimension hfactor hdiff p := by
      have hh : 0 ≤ ∑ i : Fin n, d i.succ := Finset.sum_nonneg (fun i _ => hd i.succ)
      linarith
    obtain ⟨q,hqp,hqd⟩ := traceFreeDimension_exists_subprojection
      hfactor hdiff hfinite hunit p (d 0) (hd 0) hdp
    let r := AlgebraProjection.remainder q p hqp
    have hrD : traceFreeDimension hfactor hdiff r=
        traceFreeDimension hfactor hdiff p-d 0 := by
      rw [traceFreeDimension_remainder hfactor hdiff hfinite hunit q p hqp,hqd]
    obtain ⟨b,hbr,hbo,hbs,hbd⟩ := ih r (fun i => d i.succ) (fun i => hd i.succ) (by
      rw [hrD]; linarith)
    let a : Fin (n+1) → AlgebraProjection M := Fin.cons q b
    have hqb (i : Fin n) : q.val*(b i).val=0 :=
      projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal q p hqp) le_rfl (hbr i)
    refine ⟨a,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases hqp (fun j => ?_) i
      exact (hbr j).trans (AlgebraProjection.remainder_le q p hqp)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro k
        refine Fin.cases ?_ (fun l => ?_) k
        · intro h; exact (h rfl).elim
        · intro _; exact hqb l
      · intro k
        refine Fin.cases ?_ (fun l => ?_) k
        · intro _; exact PartialIsometry.orthogonal_reverse q (b j) (hqb j)
        · intro h
          exact hbo j l (fun he => h (congrArg Fin.succ he))
    · rw [Fin.sum_univ_succ]
      change q.val+(∑ i, (b i).val)=p.val
      rw [hbs]
      change q.val+(p.val-q.val)=p.val
      abel
    · intro i
      exact Fin.cases hqd hbd i

include hfinite in
/-- A finite corner partition into n equal dimensions, for every n>0. -/
theorem traceFreeDimension_exists_uniform_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (hn : 0<n) (p : AlgebraProjection M) :
    ∃ q : Fin n → AlgebraProjection M, (∀ i, q i ≤ p) ∧
      (∀ i j, i≠j → (q i).val*(q j).val=0) ∧
      (∑ i, (q i).val)=p.val ∧
      (∀ i, traceFreeDimension hfactor hdiff (q i)=traceFreeDimension hfactor hdiff p/n) := by
  apply traceFreeDimension_exists_partition hfactor hdiff hfinite hunit n p
    (fun _ => traceFreeDimension hfactor hdiff p/n)
  · intro i
    exact div_nonneg (traceFreeDimension_nonneg hfactor hdiff p) (Nat.cast_nonneg n)
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp

include hfactor hdiff hfinite in
/-- Actual matrix-unit legs for a partition of every positive finite size. -/
theorem traceFreeDimension_exists_equivalent_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (hn : 0<n) (p : AlgebraProjection M) :
    Nonempty (EquivalentPartition p (Fin n)) := by
  classical
  obtain ⟨q,hqp,hqo,hqs,hqd⟩ := traceFreeDimension_exists_uniform_partition
    hfactor hdiff hfinite hunit n hn p
  let i₀ : Fin n := ⟨0,hn⟩
  have he (i : Fin n) : (q i₀).Equivalent (q i) :=
    (traceFreeDyadicSup_eq_iff_equivalent hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩
      (q i₀) (q i) hunit (one_mul _) (one_mul _)).mp ((hqd i₀).trans (hqd i).symm)
  choose v hv ht using he
  exact ⟨{
    base := q i₀
    leg := v
    initial := hv
    cross := fun i j hij => (v i).adjoint.mul_eq_zero (v j) (by
      change (v i).target.val*(v j).target.val=0
      rw [ht i,ht j]; exact hqo i j hij)
    total := by simpa only [ht] using hqs
    bound := fun i => by rw [ht]; exact hqp i }⟩

end Tracial

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace AlgebraProjection

/-- The original Hilbert-space vector functional on actual projections. -/
def vectorValue (ξ : H) (p : AlgebraProjection M) : ℝ :=
  (inner ℂ ξ (p.val.val ξ)).re

theorem vectorValue_eq_norm_sq (ξ : H) (p : AlgebraProjection M) :
    vectorValue ξ p = ‖p.val.val ξ‖^2 := by
  have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  have hi : p.val.val (p.val.val ξ)=p.val.val ξ :=
    congrArg (fun a : M.toStarSubalgebra => a.val ξ) p.property.isIdempotentElem.eq
  have he : inner ℂ (p.val.val ξ) (p.val.val ξ)=inner ℂ ξ (p.val.val ξ) := by
    rw [← ContinuousLinearMap.adjoint_inner_right p.val.val]
    rw [← ContinuousLinearMap.star_eq_adjoint,hs,hi]
  rw [vectorValue,← he,inner_self_eq_norm_sq_to_K]
  norm_cast

theorem vectorValue_nonneg (ξ : H) (p : AlgebraProjection M) : 0 ≤ vectorValue ξ p := by
  rw [vectorValue_eq_norm_sq]
  positivity

theorem vectorValue_remainder (ξ : H) (p q : AlgebraProjection M) (h : p ≤ q) :
    vectorValue ξ (remainder p q h)=vectorValue ξ q-vectorValue ξ p := by
  change (inner ℂ ξ (q.val.val ξ-p.val.val ξ)).re=_
  rw [inner_sub_right,Complex.sub_re]
  rfl

theorem vectorValue_mono (ξ : H) : Monotone (vectorValue (M := M) ξ) := by
  intro p q hpq
  have h := vectorValue_nonneg ξ (remainder p q hpq)
  rw [vectorValue_remainder] at h
  linarith

/-- Retains the matrix-coefficient limit of the concrete projection supremum.
The ultrafilter is the fixed extension of atTop, not a countable subsequence. -/
theorem exists_isLUB_monotone_vector_limit
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a) :
    ∃ p : AlgebraProjection M, IsLUB (Set.range a) p ∧
      ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x))
        ((Ultrafilter.of atTop : Ultrafilter ι) : Filter ι) (𝓝 (inner ℂ y (p.val.val x))) := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => ((a i).val : H →L[ℂ] H)) 1 (by norm_num)
    (fun i => (a i).property.norm_le)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb (x y : H) : Tendsto (fun i => inner ℂ y (((a i).val : H →L[ℂ] H) x))
    (ω : Filter ι) (𝓝 (inner ℂ y ((b : H →L[ℂ] H) x))) := ht x y
  have hadj (i : ι) (x y : H) :
      inner ℂ x (((a i).val : H →L[ℂ] H) y) =
      inner ℂ (((a i).val : H →L[ℂ] H) x) y := by
    have hs : star (((a i).val : H →L[ℂ] H)) = ((a i).val : H →L[ℂ] H) :=
      congrArg Subtype.val (a i).property.isSelfAdjoint.star_eq
    calc inner ℂ x (((a i).val : H →L[ℂ] H) y) =
          inner ℂ x (star (((a i).val : H →L[ℂ] H)) y) := by rw [hs]
         _ = inner ℂ (((a i).val : H →L[ℂ] H) x) y := by
           rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hself : star b = b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    have hh := (hb y x).star
    change Tendsto (fun i => (starRingEnd ℂ) (inner ℂ x (((a i).val : H →L[ℂ] H) y)))
      (ω : Filter ι) (𝓝 ((starRingEnd ℂ) (inner ℂ x ((b : H →L[ℂ] H) y)))) at hh
    simp only [inner_conj_symm] at hh
    have eq := tendsto_nhds_unique (hb x y) (hh.congr (fun i => (hadj i y x).symm))
    change inner ℂ y (star (b : H →L[ℂ] H) x) = inner ℂ y ((b : H →L[ℂ] H) x)
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact eq.symm
  have hba (i : ι) : b * (a i).val = (a i).val := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (hb (((a i).val : H →L[ℂ] H) x) y)
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y ((z : H →L[ℂ] H) x)) (ha hj)).symm
  have hab (i : ι) : (a i).val * b = (a i).val := by
    have h := congrArg star (hba i)
    simpa only [star_mul, hself, (a i).property.isSelfAdjoint.star_eq] using h
  have hid : b * b = b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (hb ((b : H →L[ℂ] H) x) y)
    exact (hb x y).congr (fun i =>
      (congrArg (fun z : M.toStarSubalgebra => inner ℂ y ((z : H →L[ℂ] H) x)) (hab i)).symm)
  refine ⟨⟨b,⟨hid,hself⟩⟩,⟨?_,?_⟩,hb⟩
  · rintro _ ⟨i,rfl⟩
    exact hba i
  · intro p hp
    change p.val*b=b
    apply wot_limit_unique (fun i => p.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    have hpa (i : ι) : p.val*(a i).val=(a i).val := hp ⟨i,rfl⟩
    simpa only [hpa] using hb

/-- The vector functional preserves any directed projection supremum. -/
theorem vectorValue_isLUB_monotone
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range a) p) (ξ : H) :
    IsLUB (Set.range (fun i => vectorValue ξ (a i))) (vectorValue ξ p) := by
  obtain ⟨q,hq,ht⟩ := exists_isLUB_monotone_vector_limit a ha
  have he : q=p := le_antisymm (hq.2 hp.1) (hp.2 hq.1)
  subst q
  refine ⟨?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact vectorValue_mono ξ (hp.1 ⟨i,rfl⟩)
  · intro r hr
    exact le_of_tendsto ((Complex.continuous_re.tendsto _).comp (ht ξ ξ))
      (Eventually.of_forall (fun i => hr ⟨i,rfl⟩))

theorem vectorValue_tendsto_monotone
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range a) p) (ξ : H) :
    Tendsto (fun i => vectorValue ξ (a i)) atTop (𝓝 (vectorValue ξ p)) :=
  tendsto_atTop_isLUB ((vectorValue_mono ξ).comp ha)
    (vectorValue_isLUB_monotone a ha p hp ξ)

end AlgebraProjection
end Tracial

end Generator

end

end OAI
