import OAI.Combinatorics.ContingencyTables.Rooted.ForestCountIdentification
import OAI.Combinatorics.ContingencyTables.Transport.SliceFactorial
import OAI.Combinatorics.ContingencyTables.Transport.TwoLiftStates
import OAI.Combinatorics.ContingencyTables.Transport.NestedReindex

namespace OAI

/-!
# The companion's literal completion count gives both labelled factorial signatures

The labels below are actual copies of the retained small cells. Their
fiber cardinalities are the capacities, so the original first and dual
factorial displays and the W² chain-state comparison have no abstract
signature or completion hypothesis.
-/

namespace ContingencyTables.CompanionFactorialApplication

open scoped BigOperators Classical Matrix
open SimpleGraph CommonBasesFPRAS
open ForestCapacity GraphIntegralCompletion ForestCountIdentification
open LargePairEnumeration BalancedBox LabelledFactorial

variable (I J : Type*) [Fintype I] [Fintype J]

/-- Actual tightened bounded margins, a maximum large-cell forest, and
one feasible baseline table determine the completion counts and
factorial signatures. -/
structure Instance where
  small : I → J → Bool
  b : I → J → ℕ
  T : SimpleGraph (I⊕J)
  hTG : T≤cellGraph small
  hT : T.IsAcyclic
  hmax : ∀ F : SimpleGraph (I⊕J), F≤cellGraph small → F.IsAcyclic →
    MaximumForest.weight F (capacity b)≤MaximumForest.weight T (capacity b)
  r : I → ℤ
  c : J → ℤ
  X : I → J → ℤ
  d : ℕ
  W : ℕ
  hd : 1≤d
  hcard : Fintype.card I*Fintype.card J≤d
  hW : 2≤W
  hlarge : ∀ i j, small i j=false → W≤b i j ∧ 1≤b i j
  hsmall : ∀ i j, small i j=true → b i j<W
  hX : ∀ i j, 0≤X i j ∧ X i j≤b i j
  hXr : ∀ i, (∑ j, X i j)=r i
  hXc : ∀ j, (∑ i, X i j)=c j

variable {I J}

@[reducible] def SmallCell (A : Instance I J) := {a : I×J // A.small a.1 a.2=true}

@[reducible] def View (A : Instance I J) := SmallCell A×Bool

def bounds (A : Instance I J) (u : View A) : ℕ := A.b u.1.val.1 u.1.val.2

noncomputable def h (A : Instance I J) (alpha : ℝ) (z : View A → ℕ) : ℝ :=
  sourceMarginal A.small A.T A.d A.b A.r A.c alpha z

lemma h_positive (A : Instance I J) (alpha : ℝ) (z : View A → ℕ) : 0<h A alpha z :=
  sourceMarginal_positive A.small A.T A.d A.b A.r A.c alpha z

private lemma large_width (A : Instance I J) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2)) (k : Fin n) :
    2≤ForestLiteralCount.width A.T A.d A.b (e k).val.1 (e k).val.2 := by
  have hb := (A.hlarge _ _ (e k).property).2
  by_cases ht : A.T.Adj (.inl (e k).val.1) (.inr (e k).val.2)
  · simp only [ForestLiteralCount.width,ht,ite_true]
    have hd := A.hd
    have hdb : 0<A.d*A.b (e k).val.1 (e k).val.2 := Nat.mul_pos (by omega) (by omega)
    nlinarith
  · simp only [ForestLiteralCount.width,ht,ite_false]
    exact A.hW.trans (A.hlarge _ _ (e k).property).1

private lemma count_identity (A : Instance I J) (alpha : ℝ) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2)) (z : View A → ℕ)
    (hz : InBox (bounds A) z) :
    h A alpha z=ForestLargeMarginal.largeMarginal (fun a : I×J => A.small a.1 a.2) A.T A.b
      (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b)
      A.r A.c alpha e z :=
  sourceMarginal_eq_largeMarginal A.small A.b A.T A.hTG A.hT A.hmax A.r A.c A.X A.d A.W alpha
    A.hd A.hcard A.hlarge A.hsmall A.hX A.hXr A.hXc e z hz

/-- The original free-assignment count has its actual raw removal slice. -/
theorem h_removal (A : Instance I J) (alpha : ℝ) (ha : 0≤alpha) (R : ℕ) :
    RemovalSlice (h A alpha) (bounds A) R := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => A.small a.1 a.2))).symm
  have hs := ForestLargeMarginal.largeMarginal_removal
    (fun a : I×J => A.small a.1 a.2) A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
    (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha e (bounds A) R ha (large_width A e)
  intro z hz ht
  rw [NestedReindex.removal_congr_box _ _ (bounds A) z hz (count_identity A alpha e)]
  convert hs z hz ht using 1

/-- The globally reflected count supplies the dual addition input. -/
theorem h_reflected (A : Instance I J) (alpha : ℝ) (ha : 0≤alpha) (R : ℕ) :
    RemovalSlice (fun z => h A alpha (IntegerReflection.reflect (bounds A) z)) (bounds A) R := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => A.small a.1 a.2))).symm
  have hs := ForestLargeMarginal.largeMarginal_reflected
    (fun a : I×J => A.small a.1 a.2) A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
    (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha e (bounds A) R ha (large_width A e)
  intro z hz ht
  rw [NestedReindex.removal_congr_box _ _ (bounds A) z hz (by
    intro x _
    apply count_identity A alpha e
    intro u
    exact Nat.sub_le _ _)]
  convert hs z hz ht using 1

@[reducible] def Labels (A : Instance I J) := Σ s : SmallCell A, Fin (A.b s.val.1 s.val.2)

@[reducible] def labelCell (A : Instance I J) (p : Labels A) : SmallCell A := p.1

lemma label_width (A : Instance I J) (s : SmallCell A) :
    TwoLiftStates.width (labelCell A) s=A.b s.val.1 s.val.2 := by
  rw [TwoLiftStates.width_eq_sum]
  rw [Fintype.sum_sigma]
  have hinner (x : SmallCell A) :
      (∑ k : Fin (A.b x.val.1 x.val.2), if labelCell A ⟨x,k⟩=s then 1 else 0)=
        if x=s then A.b x.val.1 x.val.2 else 0 := by
    by_cases hx : x=s
    · subst x
      have he : ∀ k : Fin (A.b s.val.1 s.val.2), labelCell A ⟨s,k⟩=s := fun _ => rfl
      simp [he]
    · have he : ∀ k : Fin (A.b x.val.1 x.val.2), labelCell A ⟨x,k⟩≠s := fun _ => hx
      simp [he,hx]
  convert (show (∑ x : SmallCell A, if x=s then A.b x.val.1 x.val.2 else 0)=
      A.b s.val.1 s.val.2 by simp) using 1
  apply Finset.sum_congr rfl
  intro x _
  convert hinner x using 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : labelCell A ⟨x,k⟩=s <;> simp [hk]

lemma label_capacity (A : Instance I J) :
    groupCount (TwoLiftStates.group (labelCell A)) Set.univ=bounds A := by
  funext u
  rcases u with ⟨s,t⟩
  rw [TwoLiftStates.groupCount_eq_viewCount]
  unfold TwoLiftStates.viewCount
  simp only [Set.mem_univ,and_true]
  have he : (∑ p : Labels A, if labelCell A p=s then 1 else 0)=
      TwoLiftStates.width (labelCell A) s := by
    rw [TwoLiftStates.width_eq_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : labelCell A p=s <;> simp [hp]
  exact he.trans (label_width A s)

noncomputable def denominator (A : Instance I J) := TwoLiftStates.denominator (labelCell A)

lemma denominator_positive (A : Instance I J) : 0<denominator A := by
  apply Finset.prod_pos
  intro s _
  exact Nat.cast_pos.mpr (Nat.factorial_pos _)

noncomputable def f (A : Instance I J) (alpha : ℝ) : Set (Labels A×Bool) → ℝ :=
  firstLift (TwoLiftStates.group (labelCell A)) (h A alpha) (denominator A)

noncomputable def g (A : Instance I J) (alpha : ℝ) : Set (Labels A×Bool) → ℝ :=
  secondLift (TwoLiftStates.group (labelCell A)) (h A alpha) (denominator A)

/-- The manuscript's actual factorial lift is positive on its degree and
has its omission signature, derived from the literal count. -/
theorem first_properties (A : Instance I J) (alpha : ℝ) (ha : 0≤alpha) :
    BinaryContraction.DegreePositive (f A alpha) (Fintype.card (Labels A)) ∧
      BinaryContraction.OmissionProperty (f A alpha) (Fintype.card (Labels A)) := by
  change BinaryContraction.DegreePositive
      (firstLift (TwoLiftStates.group (labelCell A)) (h A alpha) (denominator A)) _ ∧
    BinaryContraction.OmissionProperty
      (firstLift (TwoLiftStates.group (labelCell A)) (h A alpha) (denominator A)) _
  constructor
  · exact SliceFactorial.firstLift_degreePositive (TwoLiftStates.group (labelCell A))
      (h A alpha) (denominator A) (Fintype.card (Labels A)) (denominator_positive A)
      (fun z _ _ => h_positive A alpha z)
  · have hs : @RemovalSlice (View A) _ (Classical.decEq _)
        (h A alpha) (groupCount (TwoLiftStates.group (labelCell A)) Set.univ)
        (Fintype.card (Labels A)) := by
      rw [label_capacity]
      convert h_removal A alpha ha _ using 1
    convert SliceFactorial.firstLift_omission_slice (TwoLiftStates.group (labelCell A))
      (h A alpha) (denominator A) (Fintype.card (Labels A)) (denominator_positive A)
      (fun z => (h_positive A alpha z).le) hs using 1

/-- The dual factorial lift retains positivity and has its actual
addition signature from the globally reflected raw count. -/
theorem second_properties (A : Instance I J) (alpha : ℝ) (ha : 0≤alpha) :
    BinaryContraction.DegreePositive (g A alpha) (Fintype.card (Labels A)) ∧
      BinaryContraction.AdditionProperty (g A alpha) (Fintype.card (Labels A)) := by
  change BinaryContraction.DegreePositive
      (secondLift (TwoLiftStates.group (labelCell A)) (h A alpha) (denominator A)) _ ∧
    BinaryContraction.AdditionProperty
      (secondLift (TwoLiftStates.group (labelCell A)) (h A alpha) (denominator A)) _
  constructor
  · intro S _
    exact div_pos
      (mul_pos (h_positive A alpha _) (FactorialSignatures.factorialProduct_positive _))
      (denominator_positive A)
  · have hs : @RemovalSlice (View A) _ (Classical.decEq _)
        (fun z => h A alpha (IntegerReflection.reflect
          (groupCount (TwoLiftStates.group (labelCell A)) Set.univ) z))
        (groupCount (TwoLiftStates.group (labelCell A)) Set.univ)
        (Fintype.card (Labels A×Bool)-Fintype.card (Labels A)) := by
      rw [label_capacity]
      convert h_reflected A alpha ha _ using 1
    convert ReflectedSlices.secondLift_addition_reflected_slice (TwoLiftStates.group (labelCell A))
      (h A alpha) (denominator A) (Fintype.card (Labels A))
      (by simp only [Fintype.card_prod,Fintype.card_bool]; omega)
      (denominator_positive A) (fun z => (h_positive A alpha z).le) hs using 1

/-- The actual paired-label chain has the required pointwise q=W²
comparison, with the source count appearing identically in both lifts. -/
theorem chain_comparison (A : Instance I J) (alpha : ℝ) (S : Set (Labels A×Bool))
    (hS : CommonBasesFPRAS.ChainState TwoLiftStates.pairs S) :
    (1/(A.W:ℝ)^2)*f A alpha S≤g A alpha S ∧ g A alpha S≤(A.W:ℝ)^2*f A alpha S := by
  apply TwoLiftStates.chain_lifts_compare (labelCell A) (h A alpha) S hS A.W
    (by have hW := A.hW; omega)
  · intro s
    rw [label_width]
    exact A.hsmall _ _ s.property
  · exact (h_positive A alpha _).le

end ContingencyTables.CompanionFactorialApplication

end OAI
