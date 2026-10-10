import Mathlib.Data.Finset.Max
import OAI.Analysis.FactorGeneration.DyadicComparison

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Follow the false child at every level of the actual coherent dyadic system. -/
def dyadicFalseIndex : (n : ℕ) → DyadicIndex n
  | 0 => ()
  | n+1 => (dyadicFalseIndex n,false)

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

def traceFreeDyadicReference (p : AlgebraProjection M) (n : ℕ) : AlgebraProjection M :=
  ((traceFreeDyadicPartition hfactor hdiff p n).leg (dyadicFalseIndex n)).target

def traceFreeDyadicSibling (p : AlgebraProjection M) (n : ℕ) : AlgebraProjection M :=
  ((traceFreeDyadicPartition hfactor hdiff p (n+1)).leg (dyadicFalseIndex n,true)).target

theorem traceFreeDyadicReference_zero (p : AlgebraProjection M) :
    traceFreeDyadicReference hfactor hdiff p 0=p :=
  PartialIsometry.onProjection_target p

theorem traceFreeDyadic_child_le (p : AlgebraProjection M) (n : ℕ)
    (i : DyadicIndex n) (b : Bool) :
    ((traceFreeDyadicPartition hfactor hdiff p (n+1)).leg (i,b)).target ≤
      ((traceFreeDyadicPartition hfactor hdiff p n).leg i).target :=
  PartialIsometry.compose_target_le _ _ (by
    rw [EquivalentPartition.initial]
    exact EquivalentPartition.bound _ b)

theorem traceFreeDyadicReference_antitone (p : AlgebraProjection M) :
    Antitone (traceFreeDyadicReference hfactor hdiff p) := by
  apply antitone_nat_of_succ_le
  intro n
  exact traceFreeDyadic_child_le hfactor hdiff p n (dyadicFalseIndex n) false

theorem traceFreeDyadicSibling_le (p : AlgebraProjection M) (n : ℕ) :
    traceFreeDyadicSibling hfactor hdiff p n ≤ traceFreeDyadicReference hfactor hdiff p n :=
  traceFreeDyadic_child_le hfactor hdiff p n (dyadicFalseIndex n) true

theorem traceFreeDyadicReference_sibling_orthogonal (p : AlgebraProjection M) (n : ℕ) :
    (traceFreeDyadicReference hfactor hdiff p (n+1)).val*
      (traceFreeDyadicSibling hfactor hdiff p n).val=0 := by
  apply EquivalentPartition.orthogonal
  exact fun h => Bool.false_ne_true (congrArg Prod.snd h)

theorem traceFreeDyadicSibling_orthogonal (p : AlgebraProjection M) (i j : ℕ) (hij : i≠j) :
    (traceFreeDyadicSibling hfactor hdiff p i).val*
      (traceFreeDyadicSibling hfactor hdiff p j).val=0 := by
  have hlt (i j : ℕ) (h : i<j) :
      (traceFreeDyadicSibling hfactor hdiff p i).val*
        (traceFreeDyadicSibling hfactor hdiff p j).val=0 := by
    apply projection_orthogonal_of_le
      (PartialIsometry.orthogonal_reverse _ _
        (traceFreeDyadicReference_sibling_orthogonal hfactor hdiff p i)) le_rfl
    exact (traceFreeDyadicSibling_le hfactor hdiff p j).trans
      (traceFreeDyadicReference_antitone hfactor hdiff p (by omega))
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact PartialIsometry.orthogonal_reverse _ _ (hlt j i h)

theorem traceFreeDyadicReference_equivalent_sibling (p : AlgebraProjection M) (n : ℕ) :
    (traceFreeDyadicReference hfactor hdiff p (n+1)).Equivalent
      (traceFreeDyadicSibling hfactor hdiff p n) := by
  let E := traceFreeDyadicPartition hfactor hdiff p (n+1)
  exact ⟨E.link (dyadicFalseIndex (n+1)) (dyadicFalseIndex n,true),
    E.link_support _ _,E.link_target _ _⟩

theorem traceFreeDyadicReference_ne_zero (p : AlgebraProjection M) (hp : p.val≠0) (n : ℕ) :
    (traceFreeDyadicReference hfactor hdiff p n).val≠0 :=
  EquivalentPartition.target_ne_zero _ hp _

/-- A projection that embeds in every dyadic reference corner must be zero.
Finiteness is used through the constructed infinite shift, not through a trace. -/
theorem traceFree_dyadic_archimedean
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M)
    (h : ∀ n, r.Subequivalent (traceFreeDyadicReference hfactor hdiff p n)) : r.val=0 := by
  apply traceFree_finite_subequivalent_orthogonal_eq_zero hfinite r
    (traceFreeDyadicSibling hfactor hdiff p)
    (traceFreeDyadicSibling_orthogonal hfactor hdiff p)
  intro n
  exact AlgebraProjection.subequivalent_trans (h (n+1))
    (traceFreeDyadicReference_equivalent_sibling hfactor hdiff p n).subequivalent

/-- Archimedean comparison with explicit partial-isometry witnesses. -/
theorem traceFree_dyadic_archimedean_witnesses
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M)
    (h : ∀ n, ∃ v : PartialIsometry M, v.support=r ∧
      v.target ≤ traceFreeDyadicReference hfactor hdiff p n) : r.val=0 :=
  traceFree_dyadic_archimedean hfactor hdiff hfinite p r h

/-- Every nonzero projection eventually fails to fit into the dyadic corners. -/
theorem traceFree_exists_dyadic_obstruction
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M) (hr : r.val≠0) :
    ∃ n, ¬r.Subequivalent (traceFreeDyadicReference hfactor hdiff p n) := by
  by_contra hn
  exact hr (traceFree_dyadic_archimedean hfactor hdiff hfinite p r
    (by simpa only [not_exists,not_not] using hn))

/-- Every nonzero projection contains an equivalent copy of every sufficiently
small dyadic reference piece. This supplies the positivity input for dimension. -/
theorem traceFree_eventually_dyadic_subequivalent
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M) (hr : r.val≠0) :
    ∃ n, ∀ m, n ≤ m → (traceFreeDyadicReference hfactor hdiff p m).Subequivalent r := by
  obtain ⟨n,hn⟩ := traceFree_exists_dyadic_obstruction hfactor hdiff hfinite p r hr
  have he : (traceFreeDyadicReference hfactor hdiff p n).Subequivalent r :=
    (AlgebraProjection.subequivalent_total hfactor r _).resolve_left hn
  refine ⟨n,fun m hm => ?_⟩
  exact AlgebraProjection.subequivalent_trans (AlgebraProjection.subequivalent_of_le
    (traceFreeDyadicReference_antitone hfactor hdiff p hm)) he

end Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The unchanged original finite diffuse factor has a decreasing sequence
of nonzero dyadic reference projections satisfying Archimedean comparison. -/
theorem isII1Factor_archimedean_reference
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S) :
    ∃ e : ℕ → Tracial.AlgebraProjection (vonNeumannOfWOTClosed S hS.weaklyClosed),
      (e 0).val=1 ∧ Antitone e ∧ (∀ n, (e n).val≠0) ∧
      ∀ r : Tracial.AlgebraProjection (vonNeumannOfWOTClosed S hS.weaklyClosed),
        (∀ n, r.Subequivalent (e n)) → r.val=0 := by
  let M := vonNeumannOfWOTClosed S hS.weaklyClosed
  have hf : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    obtain ⟨z,hz⟩ := hS.factor c hc
    exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z)⟩
  let p : Tracial.AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  refine ⟨Tracial.traceFreeDyadicReference hf hS.diffuse p,?_,
    Tracial.traceFreeDyadicReference_antitone hf hS.diffuse p,?_,?_⟩
  · exact congrArg Subtype.val (Tracial.traceFreeDyadicReference_zero hf hS.diffuse p)
  · intro n
    apply Tracial.traceFreeDyadicReference_ne_zero hf hS.diffuse p _ n
    intro h
    exact hS.nonzero (congrArg Subtype.val h).symm
  · intro r hr
    exact Tracial.traceFree_dyadic_archimedean hf hS.diffuse hS.finite p r hr

end

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem exists_maximal_fitting_subset (E : EquivalentPartition p ι) (q : AlgebraProjection M) :
    ∃ s : Finset ι, (E.subset s).Subequivalent q ∧
      ∀ t : Finset ι, (E.subset t).Subequivalent q → t.card ≤ s.card := by
  classical
  let F : Finset (Finset ι) := Finset.univ.filter (fun s => (E.subset s).Subequivalent q)
  have h0 : (E.subset ∅).Subequivalent q := AlgebraProjection.subequivalent_of_le (by
    change q.val*(E.subset ∅).val=(E.subset ∅).val
    rw [E.subset_empty,mul_zero])
  have hF : F.Nonempty := ⟨∅,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h0⟩⟩
  obtain ⟨s,hs,hmax⟩ := F.exists_max_image Finset.card hF
  exact ⟨s,(Finset.mem_filter.mp hs).2,fun t ht =>
    hmax t (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)⟩

/-- A further piece in the remainder would enlarge the fitting subset. -/
theorem maximal_remainder_not_subequivalent (E : EquivalentPartition p ι)
    (q : AlgebraProjection M) (s : Finset ι)
    (hmax : ∀ t : Finset ι, (E.subset t).Subequivalent q → t.card ≤ s.card)
    (v : PartialIsometry M) (hv : v.support=E.subset s) (ht : v.target ≤ q)
    (i : ι) (hi : i ∉ s) :
    ¬(E.leg i).target.Subequivalent (AlgebraProjection.remainder v.target q ht) := by
  classical
  intro h
  obtain ⟨w,hw,hwr⟩ := h
  have ho₁ : v.support.val*w.support.val=0 := by
    rw [hv,hw]
    exact E.subset_mul_piece_of_not_mem s i hi
  have ho₂ : v.target.val*w.target.val=0 :=
    projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal v.target q ht)
      le_rfl hwr
  let u := v.patch w ho₁ ho₂
  have hus : u.support=E.subset (insert i s) := Subtype.ext (by
    change v.support.val+w.support.val=_
    rw [hv,hw,E.subset_insert s i hi])
  have hut : u.target ≤ q := by
    have he : u.target=orthogonalSum v.target w.target ho₂ :=
      Subtype.ext (v.patch_target w ho₁ ho₂)
    rw [he]
    exact orthogonalSum_le ho₂ ht (hwr.trans (AlgebraProjection.remainder_le _ _ ht))
  have hc := hmax (insert i s) ⟨u,hus,hut⟩
  rw [Finset.card_insert_of_notMem hi] at hc
  omega

/-- Every projection inside the partition unit lies between subset sums whose
cardinalities differ by at most one. This is operator comparison, not a trace
estimate and not an assumed dimension rounding law. -/
theorem exists_subset_rounding
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (E : EquivalentPartition p ι) (q : AlgebraProjection M) (hqp : q ≤ p) :
    ∃ s t : Finset ι, s ⊆ t ∧ t.card ≤ s.card+1 ∧
      (E.subset s).Subequivalent q ∧ q.Subequivalent (E.subset t) ∧
      ∀ a : Finset ι, (E.subset a).Subequivalent q → a.card ≤ s.card := by
  classical
  obtain ⟨s,hs,hmax⟩ := E.exists_maximal_fitting_subset q
  by_cases hsall : s=Finset.univ
  · refine ⟨s,s,Finset.Subset.refl _,Nat.le_succ _,hs,?_,hmax⟩
    rw [hsall,E.subset_univ]
    exact AlgebraProjection.subequivalent_of_le hqp
  · obtain ⟨i,hi⟩ : ∃ i : ι, i ∉ s := by
      by_contra h
      apply hsall
      ext i
      simp only [Finset.mem_univ,iff_true]
      exact Classical.not_not.mp (fun hi => h ⟨i,hi⟩)
    obtain ⟨v,hv,ht⟩ := hs
    let r := AlgebraProjection.remainder v.target q ht
    have hr : r.Subequivalent (E.leg i).target :=
      (AlgebraProjection.subequivalent_total hfactor (E.leg i).target r).resolve_left
        (E.maximal_remainder_not_subequivalent q s hmax v hv ht i hi)
    have hv' : v.target.Equivalent (E.subset s) := ⟨v.adjoint,rfl,v.adjoint_target.trans hv⟩
    have ho := E.subset_mul_piece_of_not_mem s i hi
    have hupper := AlgebraProjection.subequivalent_orthogonalSum
      (AlgebraProjection.remainder_orthogonal v.target q ht) ho hv'.subequivalent hr
    rw [AlgebraProjection.orthogonalSum_remainder] at hupper
    have he : orthogonalSum (E.subset s) (E.leg i).target ho=E.subset (insert i s) :=
      Subtype.ext (E.subset_insert s i hi).symm
    rw [he] at hupper
    exact ⟨s,insert i s,Finset.subset_insert _ _,by rw [Finset.card_insert_of_notMem hi],
      ⟨v,hv,ht⟩,hupper,hmax⟩

end EquivalentPartition

/-! The dyadic lower cut on projections below p and its normalized faithful monotone supremum, capped at one. -/

def dyadicWeight (n : ℕ) (s : Finset (DyadicIndex n)) : ℝ := (s.card : ℝ)/2^n

theorem dyadicWeight_nonneg (n : ℕ) (s : Finset (DyadicIndex n)) : 0 ≤ dyadicWeight n s :=
  div_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos (by norm_num) _))

theorem dyadicWeight_le_one (n : ℕ) (s : Finset (DyadicIndex n)) : dyadicWeight n s ≤ 1 := by
  apply (div_le_one (pow_pos (by norm_num : (0 : ℝ)<2) n)).mpr
  have h : s.card ≤ 2^n := (Finset.card_le_univ s).trans_eq (card_dyadicIndex n)
  exact_mod_cast h

theorem dyadicWeight_univ (n : ℕ) : dyadicWeight n Finset.univ=1 := by
  unfold dyadicWeight
  rw [Finset.card_univ,card_dyadicIndex,Nat.cast_pow,Nat.cast_ofNat]
  exact div_self (ne_of_gt (pow_pos (by norm_num : (0 : ℝ)<2) n))

theorem dyadicWeight_children (n : ℕ) (s : Finset (DyadicIndex n)) :
    dyadicWeight (n+1) (s ×ˢ (Finset.univ : Finset Bool))=dyadicWeight n s := by
  change ((s ×ˢ (Finset.univ : Finset Bool)).card : ℝ)/2^(n+1)=(s.card : ℝ)/2^n
  rw [Finset.card_product,Finset.card_univ,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
  exact mul_div_mul_right _ _ (by norm_num : (2 : ℝ)≠0)

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-- Membership contains an actual partial-isometry witness through Subequivalent. -/
def traceFreeDyadicCut (p q : AlgebraProjection M) : Set ℝ :=
  {x | ∃ n, ∃ s : Finset (DyadicIndex n),
    ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q ∧
      x=dyadicWeight n s}

def traceFreeDyadicSup (p q : AlgebraProjection M) : ℝ :=
  sSup (traceFreeDyadicCut hfactor hdiff p q)

theorem traceFreeDyadicCut_zero_mem (p q : AlgebraProjection M) :
    0 ∈ traceFreeDyadicCut hfactor hdiff p q := by
  refine ⟨0,∅,AlgebraProjection.subequivalent_of_le ?_,?_⟩
  · change q.val*((traceFreeDyadicPartition hfactor hdiff p 0).subset ∅).val=_
    rw [EquivalentPartition.subset_empty,mul_zero]
  · simp only [dyadicWeight,Finset.card_empty,Nat.cast_zero,zero_div]

theorem traceFreeDyadicCut_bddAbove (p q : AlgebraProjection M) :
    BddAbove (traceFreeDyadicCut hfactor hdiff p q) := by
  refine ⟨1,?_⟩
  rintro x ⟨n,s,_,rfl⟩
  exact dyadicWeight_le_one n s

theorem traceFreeDyadicSup_nonneg (p q : AlgebraProjection M) :
    0 ≤ traceFreeDyadicSup hfactor hdiff p q :=
  le_csSup (traceFreeDyadicCut_bddAbove hfactor hdiff p q)
    (traceFreeDyadicCut_zero_mem hfactor hdiff p q)

theorem traceFreeDyadicSup_le_one (p q : AlgebraProjection M) :
    traceFreeDyadicSup hfactor hdiff p q ≤ 1 := by
  apply csSup_le ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p q⟩
  rintro x ⟨n,s,_,rfl⟩
  exact dyadicWeight_le_one n s

theorem traceFreeDyadicSup_lower_bound (p q : AlgebraProjection M) (n : ℕ)
    (s : Finset (DyadicIndex n))
    (h : ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q) :
    dyadicWeight n s ≤ traceFreeDyadicSup hfactor hdiff p q :=
  le_csSup (traceFreeDyadicCut_bddAbove hfactor hdiff p q) ⟨n,s,h,rfl⟩

theorem traceFreeDyadicCut_mono (p : AlgebraProjection M) {q r : AlgebraProjection M}
    (h : q.Subequivalent r) :
    traceFreeDyadicCut hfactor hdiff p q ⊆ traceFreeDyadicCut hfactor hdiff p r := by
  rintro x ⟨n,s,hs,hx⟩
  exact ⟨n,s,AlgebraProjection.subequivalent_trans hs h,hx⟩

theorem traceFreeDyadicSup_mono (p : AlgebraProjection M) {q r : AlgebraProjection M}
    (h : q.Subequivalent r) :
    traceFreeDyadicSup hfactor hdiff p q ≤ traceFreeDyadicSup hfactor hdiff p r :=
  csSup_le_csSup (traceFreeDyadicCut_bddAbove hfactor hdiff p r)
    ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p q⟩
    (traceFreeDyadicCut_mono hfactor hdiff p h)

theorem traceFreeDyadicSup_equivalent (p : AlgebraProjection M) {q r : AlgebraProjection M}
    (h : q.Equivalent r) :
    traceFreeDyadicSup hfactor hdiff p q=traceFreeDyadicSup hfactor hdiff p r :=
  le_antisymm (traceFreeDyadicSup_mono hfactor hdiff p h.subequivalent)
    (traceFreeDyadicSup_mono hfactor hdiff p (AlgebraProjection.equivalent_symm h).subequivalent)

theorem traceFreeDyadicSup_self (p : AlgebraProjection M) :
    traceFreeDyadicSup hfactor hdiff p p=1 := by
  apply le_antisymm (traceFreeDyadicSup_le_one hfactor hdiff p p)
  rw [← dyadicWeight_univ 0]
  apply traceFreeDyadicSup_lower_bound hfactor hdiff p p 0 Finset.univ
  rw [EquivalentPartition.subset_univ]
  exact AlgebraProjection.subequivalent_refl p

/-- Refining to all children preserves both the actual projection and weight. -/
theorem traceFreeDyadicCut_refine (p q : AlgebraProjection M) (n : ℕ)
    (s : Finset (DyadicIndex n))
    (h : ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q) :
    ((traceFreeDyadicPartition hfactor hdiff p (n+1)).subset
      (s ×ˢ (Finset.univ : Finset Bool))).Subequivalent q ∧
      dyadicWeight (n+1) (s ×ˢ (Finset.univ : Finset Bool))=dyadicWeight n s := by
  refine ⟨?_,dyadicWeight_children n s⟩
  change (((traceFreeDyadicPartition hfactor hdiff p n).refine _).subset _).Subequivalent q
  rw [EquivalentPartition.subset_refine]
  exact h

theorem traceFreeDyadicSup_zero (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q.val=0) :
    traceFreeDyadicSup hfactor hdiff p q=0 := by
  apply le_antisymm ?_ (traceFreeDyadicSup_nonneg hfactor hdiff p q)
  apply csSup_le ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p q⟩
  rintro x ⟨n,s,⟨v,hv,ht⟩,rfl⟩
  have htz : v.target.val=0 := by
    change q.val*v.target.val=v.target.val at ht
    rw [hq,zero_mul] at ht
    exact ht.symm
  have hvz : v.val=0 := by
    have h := v.target_mul
    rw [htz,zero_mul] at h
    exact h.symm
  have hsz : ((traceFreeDyadicPartition hfactor hdiff p n).subset s).val=0 := by
    rw [← hv,← v.initial,hvz,star_zero,zero_mul]
  have hs : s ⊆ ∅ :=
    ((traceFreeDyadicPartition hfactor hdiff p n).subset_le_subset_iff hp s ∅).mp (by
      change ((traceFreeDyadicPartition hfactor hdiff p n).subset ∅).val*
        ((traceFreeDyadicPartition hfactor hdiff p n).subset s).val=_
      rw [hsz,mul_zero])
  have he : s=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => Finset.notMem_empty i (hs hi))
  simp only [he,dyadicWeight,Finset.card_empty,Nat.cast_zero,zero_div,le_refl]

/-- Archimedean comparison makes the supremum strictly positive on nonzero projections. -/
theorem traceFreeDyadicSup_pos
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p q : AlgebraProjection M) (hq : q.val≠0) :
    0 < traceFreeDyadicSup hfactor hdiff p q := by
  obtain ⟨n,hn⟩ := traceFree_eventually_dyadic_subequivalent hfactor hdiff hfinite p q hq
  have h := hn n le_rfl
  have he : ((traceFreeDyadicPartition hfactor hdiff p n).subset {dyadicFalseIndex n}).Subequivalent q := by
    rw [EquivalentPartition.subset_singleton]
    exact h
  apply lt_of_lt_of_le ?_ (traceFreeDyadicSup_lower_bound hfactor hdiff p q n _ he)
  simp only [dyadicWeight,Finset.card_singleton,Nat.cast_one]
  exact div_pos zero_lt_one (pow_pos (by norm_num) _)

theorem traceFreeDyadicSup_eq_zero_iff
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p q : AlgebraProjection M) (hp : p.val≠0) :
    traceFreeDyadicSup hfactor hdiff p q=0 ↔ q.val=0 := by
  constructor
  · intro h
    by_contra hq
    have hh := traceFreeDyadicSup_pos hfactor hdiff hfinite p q hq
    rw [h] at hh
    exact lt_irrefl _ hh
  · exact traceFreeDyadicSup_zero hfactor hdiff p q hp

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem dyadicWeight_le_iff (n : ℕ) (s t : Finset (DyadicIndex n)) :
    dyadicWeight n s ≤ dyadicWeight n t ↔ s.card ≤ t.card := by
  unfold dyadicWeight
  rw [div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ)<2) n)]
  exact Nat.cast_le

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

theorem traceFreeDyadic_exists_refined_subset (p : AlgebraProjection M) (n m : ℕ)
    (hnm : n ≤ m) (s : Finset (DyadicIndex n)) :
    ∃ t : Finset (DyadicIndex m),
      (traceFreeDyadicPartition hfactor hdiff p m).subset t=
        (traceFreeDyadicPartition hfactor hdiff p n).subset s ∧
      dyadicWeight m t=dyadicWeight n s := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨s,rfl,rfl⟩
  | succ m _ ih =>
    obtain ⟨t,ht,hw⟩ := ih
    refine ⟨t ×ˢ (Finset.univ : Finset Bool),?_,(dyadicWeight_children m t).trans hw⟩
    change ((traceFreeDyadicPartition hfactor hdiff p m).refine _).subset _=_
    rw [EquivalentPartition.subset_refine,ht]

/-- Comparison between any two levels agrees with the real dyadic weights. -/
theorem traceFreeDyadic_comparison_iff_weight
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p : AlgebraProjection M) (hp : p.val≠0) (n m : ℕ)
    (s : Finset (DyadicIndex n)) (t : Finset (DyadicIndex m)) :
    ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent
      ((traceFreeDyadicPartition hfactor hdiff p m).subset t) ↔
        dyadicWeight n s ≤ dyadicWeight m t := by
  obtain ⟨s',hs',hws⟩ := traceFreeDyadic_exists_refined_subset hfactor hdiff p n (max n m)
    (le_max_left _ _) s
  obtain ⟨t',ht',hwt⟩ := traceFreeDyadic_exists_refined_subset hfactor hdiff p m (max n m)
    (le_max_right _ _) t
  rw [← hs',← ht',← hws,← hwt]
  rw [EquivalentPartition.subset_subequivalent_iff_card_le hfinite _ hp,dyadicWeight_le_iff]

theorem traceFreeDyadicSup_subset
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p : AlgebraProjection M) (hp : p.val≠0) (n : ℕ) (s : Finset (DyadicIndex n)) :
    traceFreeDyadicSup hfactor hdiff p ((traceFreeDyadicPartition hfactor hdiff p n).subset s)=
      dyadicWeight n s := by
  apply le_antisymm ?_ (traceFreeDyadicSup_lower_bound hfactor hdiff p _ n s
    (AlgebraProjection.subequivalent_refl _))
  apply csSup_le ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p _⟩
  rintro x ⟨m,t,h,rfl⟩
  exact (traceFreeDyadic_comparison_iff_weight hfactor hdiff hfinite p hp m n t s).mp h

/-- At every level the cut supremum has actual lower and upper operator
witnesses, with a numerical gap at most 2^(-n). -/
theorem traceFreeDyadicSup_rounding
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q ≤ p) (n : ℕ) :
    ∃ s t : Finset (DyadicIndex n), s ⊆ t ∧ t.card ≤ s.card+1 ∧
      ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q ∧
      q.Subequivalent ((traceFreeDyadicPartition hfactor hdiff p n).subset t) ∧
      dyadicWeight n s ≤ traceFreeDyadicSup hfactor hdiff p q ∧
      traceFreeDyadicSup hfactor hdiff p q ≤ dyadicWeight n t ∧
      dyadicWeight n t ≤ dyadicWeight n s+1/2^n := by
  obtain ⟨s,t,hst,hcard,hs,ht,_⟩ :=
    (traceFreeDyadicPartition hfactor hdiff p n).exists_subset_rounding hfactor q hq
  refine ⟨s,t,hst,hcard,hs,ht,traceFreeDyadicSup_lower_bound hfactor hdiff p q n s hs,?_,?_⟩
  · have h := traceFreeDyadicSup_mono hfactor hdiff p ht
    rwa [traceFreeDyadicSup_subset hfactor hdiff hfinite p hp] at h
  · change (t.card : ℝ)/2^n ≤ (s.card : ℝ)/2^n+1/2^n
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ)<2) n)).mpr
    exact_mod_cast hcard

end

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem subset_complement [DecidableEq ι] (E : EquivalentPartition p ι) (s : Finset ι) :
    E.subset (Finset.univ \ s)=AlgebraProjection.remainder (E.subset s) p (E.subset_le s) := by
  classical
  apply Subtype.ext
  change (∑ i ∈ Finset.univ \ s, (E.leg i).target.val)=p.val-(E.subset s).val
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ s),E.total]
  rfl

theorem exists_disjoint_card (s t : Finset ι) (h : s.card+t.card ≤ Fintype.card ι) :
    ∃ u : Finset ι, Disjoint s u ∧ u.card=t.card := by
  classical
  have hc : t.card ≤ (Finset.univ \ s).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s),Finset.card_univ]
    omega
  obtain ⟨u,hu,huc⟩ := Finset.exists_subset_card_eq hc
  refine ⟨u,Finset.disjoint_left.mpr ?_,huc⟩
  intro i hi hui
  exact (Finset.mem_sdiff.mp (hu hui)).2 hi

/-- Two orthogonal fitting projections cannot use more pieces than the unit. -/
theorem orthogonal_fitting_card_bound
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (E : EquivalentPartition p ι) (hp : p.val≠0)
    (q r : AlgebraProjection M) (hqp : q ≤ p) (hrp : r ≤ p) (ho : q.val*r.val=0)
    (s t : Finset ι) (hs : (E.subset s).Subequivalent q) (ht : (E.subset t).Subequivalent r) :
    s.card+t.card ≤ Fintype.card ι := by
  classical
  obtain ⟨v,hv,hvr⟩ := ht
  have hvp := hvr.trans hrp
  have hqv : q.val*v.target.val=0 := projection_orthogonal_of_le ho le_rfl hvr
  have hqr : q ≤ AlgebraProjection.remainder v.target p hvp := by
    change (p.val-v.target.val)*q.val=q.val
    rw [sub_mul,hqp,PartialIsometry.orthogonal_reverse _ _ hqv,sub_zero]
  have he : v.target.Equivalent (E.subset t) := ⟨v.adjoint,rfl,v.adjoint_target.trans hv⟩
  have hc := AlgebraProjection.remainder_equivalent hfinite hfactor hvp (E.subset_le t)
    he (AlgebraProjection.equivalent_refl p)
  rw [← E.subset_complement t] at hc
  have hh : (E.subset s).Subequivalent (E.subset (Finset.univ \ t)) :=
    AlgebraProjection.subequivalent_trans hs (AlgebraProjection.subequivalent_trans
      (AlgebraProjection.subequivalent_of_le hqr) hc.subequivalent)
  have hn := (E.subset_subequivalent_iff_card_le hfinite hp s _).mp hh
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ t)
  rw [Finset.card_univ] at hcard
  omega

/-- Disjoint replacement of one collection lets the actual witnesses be added. -/
theorem orthogonal_fitting_union
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (E : EquivalentPartition p ι) (hp : p.val≠0)
    (q r : AlgebraProjection M) (hqp : q ≤ p) (hrp : r ≤ p) (ho : q.val*r.val=0)
    (s t : Finset ι) (hs : (E.subset s).Subequivalent q) (ht : (E.subset t).Subequivalent r) :
    ∃ u : Finset ι, u.card=s.card+t.card ∧
      (E.subset u).Subequivalent (orthogonalSum q r ho) := by
  classical
  obtain ⟨t',hst,hct⟩ := exists_disjoint_card s t
    (E.orthogonal_fitting_card_bound hfinite hfactor hp q r hqp hrp ho s t hs ht)
  have ht' : (E.subset t').Subequivalent r := AlgebraProjection.subequivalent_trans
    (E.subset_equivalent_of_card_eq t' t hct).subequivalent ht
  refine ⟨s ∪ t',by rw [Finset.card_union_of_disjoint hst,hct],?_⟩
  rw [E.subset_union s t' hst]
  exact AlgebraProjection.subequivalent_orthogonalSum
    (E.subset_orthogonal_of_disjoint s t' hst) ho hs ht'

theorem orthogonal_upper_union
    (E : EquivalentPartition p ι) (q r : AlgebraProjection M) (ho : q.val*r.val=0)
    (s t : Finset ι) (hs : q.Subequivalent (E.subset s)) (ht : r.Subequivalent (E.subset t))
    (hcard : s.card+t.card ≤ Fintype.card ι) :
    ∃ u : Finset ι, u.card=s.card+t.card ∧
      (orthogonalSum q r ho).Subequivalent (E.subset u) := by
  classical
  obtain ⟨t',hst,hct⟩ := exists_disjoint_card s t hcard
  have ht' : r.Subequivalent (E.subset t') := AlgebraProjection.subequivalent_trans ht
    (E.subset_equivalent_of_card_eq t t' hct.symm).subequivalent
  refine ⟨s ∪ t',by rw [Finset.card_union_of_disjoint hst,hct],?_⟩
  rw [E.subset_union s t' hst]
  exact AlgebraProjection.subequivalent_orthogonalSum ho
    (E.subset_orthogonal_of_disjoint s t' hst) hs ht'

end EquivalentPartition
end

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem eq_of_all_dyadic_errors (a b : ℝ) (h : ∀ n : ℕ, |a-b| ≤ 2/2^n) : a=b := by
  by_contra hab
  have hp : 0 < |a-b|/2 := div_pos (abs_pos.mpr (sub_ne_zero.mpr hab)) (by norm_num)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hh := h n
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring] at hh
  linarith

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDyadicSup_lower_add
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) (hrp : r ≤ p)
    (ho : q.val*r.val=0) (n : ℕ) (s t : Finset (DyadicIndex n))
    (hs : ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q)
    (ht : ((traceFreeDyadicPartition hfactor hdiff p n).subset t).Subequivalent r) :
    dyadicWeight n s+dyadicWeight n t ≤
      traceFreeDyadicSup hfactor hdiff p (orthogonalSum q r ho) := by
  obtain ⟨u,huc,hu⟩ := (traceFreeDyadicPartition hfactor hdiff p n).orthogonal_fitting_union
    hfinite hfactor hp q r hqp hrp ho s t hs ht
  have h := traceFreeDyadicSup_lower_bound hfactor hdiff p _ n u hu
  simpa only [dyadicWeight,huc,Nat.cast_add,add_div] using h

include hfinite in
theorem traceFreeDyadicSup_upper_add
    (p q r : AlgebraProjection M) (hp : p.val≠0) (ho : q.val*r.val=0)
    (n : ℕ) (s t : Finset (DyadicIndex n))
    (hs : q.Subequivalent ((traceFreeDyadicPartition hfactor hdiff p n).subset s))
    (ht : r.Subequivalent ((traceFreeDyadicPartition hfactor hdiff p n).subset t)) :
    traceFreeDyadicSup hfactor hdiff p (orthogonalSum q r ho) ≤
      dyadicWeight n s+dyadicWeight n t := by
  by_cases hc : s.card+t.card ≤ Fintype.card (DyadicIndex n)
  · obtain ⟨u,huc,hu⟩ := (traceFreeDyadicPartition hfactor hdiff p n).orthogonal_upper_union
      q r ho s t hs ht hc
    have h := traceFreeDyadicSup_mono hfactor hdiff p hu
    rw [traceFreeDyadicSup_subset hfactor hdiff hfinite p hp] at h
    simpa only [dyadicWeight,huc,Nat.cast_add,add_div] using h
  · apply le_trans (traceFreeDyadicSup_le_one hfactor hdiff p _)
    have hn : 2^n ≤ s.card+t.card := by rw [card_dyadicIndex] at hc; omega
    change 1 ≤ (s.card : ℝ)/2^n+(t.card : ℝ)/2^n
    rw [← add_div]
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ)<2) n)).mpr
    simp only [one_mul]
    exact_mod_cast hn

include hfinite in
/-- The dyadic supremum is additive on actual orthogonal projections below p. -/
theorem traceFreeDyadicSup_orthogonal_add
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) (hrp : r ≤ p)
    (ho : q.val*r.val=0) :
    traceFreeDyadicSup hfactor hdiff p (orthogonalSum q r ho)=
      traceFreeDyadicSup hfactor hdiff p q+traceFreeDyadicSup hfactor hdiff p r := by
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨s,t,_,_,hs,ht,hql,hqu,hqe⟩ :=
    traceFreeDyadicSup_rounding hfactor hdiff hfinite p q hp hqp n
  obtain ⟨a,b,_,_,ha,hb,hrl,hru,hre⟩ :=
    traceFreeDyadicSup_rounding hfactor hdiff hfinite p r hp hrp n
  have hlo := traceFreeDyadicSup_lower_add hfactor hdiff hfinite p q r hp hqp hrp ho n s a hs ha
  have hhi := traceFreeDyadicSup_upper_add hfactor hdiff hfinite p q r hp ho n t b ht hb
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
  apply abs_le.mpr
  constructor <;> linarith

include hfinite in
theorem traceFreeDyadicSup_remainder
    (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q ≤ p) :
    traceFreeDyadicSup hfactor hdiff p (AlgebraProjection.remainder q p hq)=
      1-traceFreeDyadicSup hfactor hdiff p q := by
  have h := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite p q
    (AlgebraProjection.remainder q p hq) hp hq (AlgebraProjection.remainder_le q p hq)
    (AlgebraProjection.remainder_orthogonal q p hq)
  rw [AlgebraProjection.orthogonalSum_remainder,traceFreeDyadicSup_self] at h
  linarith

include hfinite in
/-- Faithfulness and additivity give strict increase along proper inclusion. -/
theorem traceFreeDyadicSup_strictMono
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hrp : r ≤ p) (hqr : q < r) :
    traceFreeDyadicSup hfactor hdiff p q < traceFreeDyadicSup hfactor hdiff p r := by
  have hle : q ≤ r := le_of_lt hqr
  let s := AlgebraProjection.remainder q r hle
  have hs : s.val≠0 := by
    change r.val-q.val≠0
    intro h
    exact (ne_of_lt hqr) (Subtype.ext (sub_eq_zero.mp h).symm)
  have hpos := traceFreeDyadicSup_pos hfactor hdiff hfinite p s hs
  have he := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite p q s hp
    (hle.trans hrp) ((AlgebraProjection.remainder_le q r hle).trans hrp)
    (AlgebraProjection.remainder_orthogonal q r hle)
  rw [AlgebraProjection.orthogonalSum_remainder] at he
  linarith

end Tracial

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFree_target_eq_of_dimension_le
    (p q : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p)
    (v : PartialIsometry M) (ht : v.target ≤ q)
    (hd : traceFreeDyadicSup hfactor hdiff p q ≤ traceFreeDyadicSup hfactor hdiff p v.support) :
    v.target=q := by
  by_contra he
  have hlt := traceFreeDyadicSup_strictMono hfactor hdiff hfinite p v.target q hp hqp
    (lt_of_le_of_ne ht he)
  have heq := traceFreeDyadicSup_equivalent hfactor hdiff p
    (show v.support.Equivalent v.target from ⟨v,rfl,rfl⟩)
  linarith

include hfinite in
/-- Real-valued comparison is exactly witnessed projection subequivalence. -/
theorem traceFreeDyadicSup_le_iff_subequivalent
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) :
    traceFreeDyadicSup hfactor hdiff p q ≤ traceFreeDyadicSup hfactor hdiff p r ↔
      q.Subequivalent r := by
  refine ⟨fun hd => ?_,traceFreeDyadicSup_mono hfactor hdiff p⟩
  rcases AlgebraProjection.subequivalent_total hfactor q r with h | h
  · exact h
  · obtain ⟨v,hv,ht⟩ := h
    have he : v.target=q := traceFree_target_eq_of_dimension_le hfactor hdiff hfinite
      p q hp hqp v ht (by rw [hv]; exact hd)
    exact ⟨v.adjoint,he,le_of_eq (v.adjoint_target.trans hv)⟩

include hfinite in
theorem traceFreeDyadicSup_eq_iff_equivalent
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) (hrp : r ≤ p) :
    traceFreeDyadicSup hfactor hdiff p q=traceFreeDyadicSup hfactor hdiff p r ↔
      q.Equivalent r := by
  constructor
  · intro h
    exact AlgebraProjection.equivalent_of_mutual_subequivalent hfinite
      ((traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite p q r hp hqp).mp (le_of_eq h))
      ((traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite p r q hp hrp).mp (le_of_eq h.symm))
  · exact traceFreeDyadicSup_equivalent hfactor hdiff p

/-- The same constructed lower cut, now normalized at the algebra identity. -/
def traceFreeDimension (q : AlgebraProjection M) : ℝ :=
  traceFreeDyadicSup hfactor hdiff ⟨1,IsStarProjection.one _⟩ q

end Tracial

/-- The original nonzero finite diffuse factor has a normalized faithful
finitely additive dimension on its actual projections. The comparison
equivalences use actual partial isometries, not a supplied dimension oracle. -/
theorem isII1Factor_projection_dimension
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S) :
    ∃ D : Tracial.AlgebraProjection (vonNeumannOfWOTClosed S hS.weaklyClosed) → ℝ,
      D ⟨1,IsStarProjection.one _⟩=1 ∧
      (∀ q, 0 ≤ D q ∧ D q ≤ 1) ∧
      (∀ q, D q=0 ↔ q.val=0) ∧
      (∀ q r, D q ≤ D r ↔ q.Subequivalent r) ∧
      (∀ q r, D q=D r ↔ q.Equivalent r) ∧
      (∀ q r (ho : q.val*r.val=0), D (Tracial.orthogonalSum q r ho)=D q+D r) := by
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
  have hle (q : Tracial.AlgebraProjection M) : q ≤ p := by
    change 1*q.val=q.val
    exact one_mul _
  refine ⟨Tracial.traceFreeDimension hf hS.diffuse,?_,?_,?_,?_,?_,?_⟩
  · exact Tracial.traceFreeDyadicSup_self hf hS.diffuse p
  · intro q
    exact ⟨Tracial.traceFreeDyadicSup_nonneg hf hS.diffuse p q,
      Tracial.traceFreeDyadicSup_le_one hf hS.diffuse p q⟩
  · intro q
    exact Tracial.traceFreeDyadicSup_eq_zero_iff hf hS.diffuse hS.finite p q hp
  · intro q r
    exact Tracial.traceFreeDyadicSup_le_iff_subequivalent hf hS.diffuse hS.finite p q r hp (hle q)
  · intro q r
    exact Tracial.traceFreeDyadicSup_eq_iff_equivalent hf hS.diffuse hS.finite p q r hp (hle q) (hle r)
  · intro q r ho
    exact Tracial.traceFreeDyadicSup_orthogonal_add hf hS.diffuse hS.finite p q r hp (hle q) (hle r) ho

end

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem traceFreeDimension_nonneg (q : AlgebraProjection M) :
    0 ≤ traceFreeDimension hfactor hdiff q :=
  traceFreeDyadicSup_nonneg hfactor hdiff _ q

theorem traceFreeDimension_le_one (q : AlgebraProjection M) :
    traceFreeDimension hfactor hdiff q ≤ 1 :=
  traceFreeDyadicSup_le_one hfactor hdiff _ q

theorem traceFreeDimension_subequivalent {q r : AlgebraProjection M}
    (h : q.Subequivalent r) :
    traceFreeDimension hfactor hdiff q ≤ traceFreeDimension hfactor hdiff r :=
  traceFreeDyadicSup_mono hfactor hdiff _ h

theorem traceFreeDimension_mono : Monotone (traceFreeDimension hfactor hdiff) :=
  fun _ _ h => traceFreeDimension_subequivalent hfactor hdiff
    (AlgebraProjection.subequivalent_of_le h)

include hfinite in
theorem traceFreeDimension_le_iff_subequivalent
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (q r : AlgebraProjection M) :
    traceFreeDimension hfactor hdiff q ≤ traceFreeDimension hfactor hdiff r ↔
      q.Subequivalent r :=
  traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite _ q r hunit (one_mul _)

include hfinite in
theorem traceFreeDimension_strictMono (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    StrictMono (traceFreeDimension hfactor hdiff) :=
  fun _ _ h => traceFreeDyadicSup_strictMono hfactor hdiff hfinite _ _ _ hunit (one_mul _) h

/-- A subset of the n-th reference partition with weight in [c,c+2^(-n)]. -/
theorem exists_dyadicWeight_upper (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    ∃ s : Finset (DyadicIndex n), c ≤ dyadicWeight n s ∧ dyadicWeight n s ≤ c+1/2^n := by
  classical
  have hn : (0 : ℝ)<2^n := pow_pos (by norm_num) n
  have hk : Nat.ceil (c*2^n) ≤ Fintype.card (DyadicIndex n) := by
    rw [card_dyadicIndex,Nat.ceil_le]
    push_cast
    nlinarith
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (DyadicIndex n))) (n := Nat.ceil (c*2^n))
    (by simpa only [Finset.card_univ] using hk)
  refine ⟨s,?_,?_⟩
  · change c ≤ (s.card : ℝ)/2^n
    rw [hs,le_div_iff₀ hn]
    exact Nat.le_ceil _
  · change (s.card : ℝ)/2^n ≤ c+1/2^n
    rw [hs,div_le_iff₀ hn]
    have h := (Nat.ceil_lt_add_one (mul_nonneg hc hn.le)).le
    calc (Nat.ceil (c*2^n) : ℝ) ≤ c*2^n+1 := h
         _ = (c+1/2^n)*2^n := by field_simp

include hfinite in
/-- Actual projection upper approximants for every real c in [0,1]. -/
theorem traceFreeDimension_exists_upper
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    ∃ r : AlgebraProjection M, c ≤ traceFreeDimension hfactor hdiff r ∧
      traceFreeDimension hfactor hdiff r ≤ c+1/2^n := by
  obtain ⟨s,hs,ht⟩ := exists_dyadicWeight_upper c hc hc1 n
  refine ⟨(traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset s,?_,?_⟩
  · simpa only [traceFreeDimension,traceFreeDyadicSup_subset hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ hunit] using hs
  · simpa only [traceFreeDimension,traceFreeDyadicSup_subset hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ hunit] using ht

theorem le_of_all_dyadic_errors (a b : ℝ) (h : ∀ n : ℕ, a ≤ b+1/2^n) : a ≤ b := by
  by_contra hab
  have hp : 0 < a-b := sub_pos.mpr (lt_of_not_ge hab)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hh := h n
  linarith

end Tracial

end Generator

end

end OAI
