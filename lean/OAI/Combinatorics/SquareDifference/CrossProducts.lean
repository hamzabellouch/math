import OAI.Combinatorics.SquareDifference.AffineTuples

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

lemma crossEdges_factor {I J : Type*} [Fintype I] [Fintype J]
    {p : ℕ} [Fact p.Prime] (E : Finset ((I⊕J)×(I⊕J)))
    (hnoopp : ∀e∈E, (e.2,e.1)∉E) (x : I → ZMod p) (y : J → ZMod p) :
    listKernel (crossEdges E) (crossDir E) x y =
      (∏i, ∏j, if (Sum.inl i,Sum.inr j)∈E then squareIndicator (y j-x i) else 1)*
      (∏j, ∏i, if (Sum.inr j,Sum.inl i)∈E then squareIndicator (x i-y j) else 1) := by
  classical
  rw [listKernel, ← Fintype.prod_ite_mem, ← univ_product_univ, prod_product]
  rw [prod_comm (f := fun j i => if (Sum.inr j,Sum.inl i)∈E then squareIndicator (x i-y j) else 1)]
  rw [← prod_mul_distrib]
  apply prod_congr rfl; intro i _
  rw [← prod_mul_distrib]
  apply prod_congr rfl; intro j _
  by_cases h : (Sum.inl i,Sum.inr j)∈E
  · have h' := hnoopp _ h
    simp [crossEdges, crossDir, h, h']
  · by_cases h' : (Sum.inr j,Sum.inl i)∈E <;> simp [crossEdges, crossDir, h, h']

lemma graphValidity_singleton_cut {J : Type*} [Fintype J]
    {p : ℕ} [Fact p.Prime] (E : Finset ((Unit⊕J)×(Unit⊕J)))
    (hnoopp : ∀e∈E, (e.2,e.1)∉E) (hloop : (Sum.inl (),Sum.inl ())∉E)
    (x : Unit → ZMod p) (y : J → ZMod p) :
    graphValidity E (Sum.elim x y)=
      (∏i, ∏j, if (Sum.inr i,Sum.inr j)∈E then squareIndicator (y j-y i) else 1)*
        listKernel (crossEdges E) (crossDir E) x y := by
  classical
  rw [graphValidity_all, Fintype.prod_sum_type]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, prod_mul_distrib]
  rw [crossEdges_factor E hnoopp]
  simp only [Fintype.prod_unique, show (default : Unit)=() from rfl, ite_eq_right hloop, one_mul]
  ring

noncomputable def tupleZeroIndex : TupleListIndex ∅ :=
  ⟨0, by simp only [card_empty, pow_zero]; decide⟩

instance tupleEmptyIndexSubsingleton : Subsingleton (TupleListIndex ∅) where
  allEq i j := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    simp only [card_empty, pow_zero] at hi hj
    omega

noncomputable def tupleLeadingEntry : TupleVertex ≃ TupleListEntry ∅ where
  toFun v := (tupleProjection ∅ v, tupleZeroIndex)
  invFun u b := u.1 ⟨b, by simp⟩
  left_inv v := rfl
  right_inv u := by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _

noncomputable def tupleLeadingGraph : Finset (TupleVertex×TupleVertex) :=
  graphPullback tupleLeadingEntry (tupleListEdges ∅)

lemma graphPullback_no_opp {I K : Type*} [Fintype I] (e : I ≃ K)
    (E : Finset (K×K)) (hE : ∀u∈E, (u.2,u.1)∉E) :
    ∀u∈graphPullback e E, (u.2,u.1)∉graphPullback e E := by
  intro u hu hn
  have h1 : (e u.1,e u.2)∈E := (mem_filter.mp hu).2
  have h2 : (e u.2,e u.1)∈E := (mem_filter.mp hn).2
  exact hE (e u.1,e u.2) h1 h2

lemma graphPullback_no_loop {I K : Type*} [Fintype I] (e : I ≃ K)
    (E : Finset (K×K)) (hE : ∀u∈E, u.1≠u.2) (v : I) :
    (v,v)∉graphPullback e E := by
  intro hv
  exact hE (e v,e v) (mem_filter.mp hv).2 rfl

lemma tupleLeadingGraph_no_opp : ∀e∈tupleLeadingGraph, (e.2,e.1)∉tupleLeadingGraph :=
  graphPullback_no_opp tupleLeadingEntry (tupleListEdges ∅) (tupleListEdges_no_opp ∅)

lemma tupleLeadingGraph_no_loop (v : TupleVertex) : (v,v)∉tupleLeadingGraph :=
  graphPullback_no_loop tupleLeadingEntry (tupleListEdges ∅) (tupleListEdges_no_loop ∅) v

lemma tupleComponent_leading_integral {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) :
    tupleComponent ∅ F=𝔼 z, graphValidity tupleLeadingGraph z*F z := by
  classical
  have ho (Y : TupleListEntry ∅ → ZMod p) (j : TupleVertex → TupleListIndex ∅) :
      tupleOutput ∅ Y j=Y ∘ tupleLeadingEntry := by
    funext v
    change Y (tupleProjection ∅ v, j v)=Y (tupleProjection ∅ v,tupleZeroIndex)
    rw [Subsingleton.elim (j v) tupleZeroIndex]
  simp only [tupleComponent, tupleWeight_empty, mul_one, ho, Fintype.expect_const]
  rw [expect_precompose tupleLeadingEntry.symm]
  apply expect_congr rfl; intro z _
  have he : (z ∘ tupleLeadingEntry.symm) ∘ tupleLeadingEntry=z := by ext v; simp
  rw [he]
  change graphValidity (tupleListEdges ∅) (z ∘ tupleLeadingEntry.symm)*F z=_
  rw [← graphValidity_pullback tupleLeadingEntry (tupleListEdges ∅) (z ∘ tupleLeadingEntry.symm)]
  rw [he]
  rfl

noncomputable def graphCondConstant {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V×V)) (v : V) : ℝ :=
  let m := (crossEdges (graphPullback (splitIndex v) E)).card
  (2/(1/2 : ℝ)^m+4/((1/2 : ℝ)^m)^2)*((32*m : ℝ)^((1:ℝ)/4))^2

lemma graphCondConstant_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V×V)) (v : V) : 0 ≤ graphCondConstant E v := by
  unfold graphCondConstant; positivity

lemma mem_graphPullback {I K : Type*} [Fintype I] (e : I ≃ K)
    (E : Finset (K×K)) (u : I×I) : u∈graphPullback e E ↔ (e u.1,e u.2)∈E := by
  simp only [graphPullback, mem_filter, mem_univ, true_and]

noncomputable def graphRest {J : Type*} [Fintype J] {p : ℕ} [Fact p.Prime]
    (E : Finset ((Unit⊕J)×(Unit⊕J))) (y : J → ZMod p) : ℝ :=
  ∏i, ∏j, if (Sum.inr i,Sum.inr j)∈E then squareIndicator (y j-y i) else 1

lemma graphRest_le_one {J : Type*} [Fintype J] {p : ℕ} [Fact p.Prime]
    (E : Finset ((Unit⊕J)×(Unit⊕J))) (y : J → ZMod p) : graphRest E y≤1 := by
  unfold graphRest
  apply prod_le_one₀
  · intro i _; apply prod_nonneg; intro j _; split <;> first | exact squareIndicator_nonneg _ | norm_num
  · intro i _; apply prod_le_one₀
    · intro j _; split <;> first | exact squareIndicator_nonneg _ | norm_num
    · intro j _; split <;> first | exact squareIndicator_le_one _ | norm_num

lemma split_merge {V X : Type*} [DecidableEq V] (v : V)
    (x : Unit → X) (y : {w : V // w≠v} → X) :
    ((Equiv.funSplitAt v X).symm (x (),y)) ∘ splitIndex v=Sum.elim x y := by
  funext i
  cases i with
  | inl i => cases i; simp [Equiv.funSplitAt, Equiv.piSplitAt, splitIndex]
  | inr i => simp [Equiv.funSplitAt, Equiv.piSplitAt, splitIndex, i.property]

lemma graphValidity_singleton_reindex {V : Type*} [Fintype V] [DecidableEq V]
    {p : ℕ} [Fact p.Prime] (E : Finset (V×V)) (hE : ∀u∈E, (u.2,u.1)∉E)
    (hl : ∀v, (v,v)∉E) (v : V) (x : Unit → ZMod p) (y : {w : V // w≠v} → ZMod p) :
    graphValidity E ((Equiv.funSplitAt v (ZMod p)).symm (x (),y))=
      graphRest (graphPullback (splitIndex v) E) y*
        listKernel (crossEdges (graphPullback (splitIndex v) E))
          (crossDir (graphPullback (splitIndex v) E)) x y := by
  rw [← graphValidity_pullback (splitIndex v) E ((Equiv.funSplitAt v (ZMod p)).symm (x (),y)),
    split_merge]
  apply graphValidity_singleton_cut
  · exact graphPullback_no_opp (splitIndex v) E hE
  · intro h
    exact hl v ((mem_graphPullback (splitIndex v) E _).mp h)

lemma singleton_list_conditional_mixing {J : Type*} [Fintype J] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p≠2)
    (E : Finset (Unit × J)) (dir : Unit → J → Bool)
    (L : (J → ZMod p) → ℝ) (hL : ∀y, L y≤1)
    (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (fun x y => L y*listKernel E dir (fun _ => x) y) f ≤
      ((2/(1/2 : ℝ)^E.card+4/((1/2 : ℝ)^E.card)^2)*
      ((32*E.card : ℝ)^((1:ℝ)/4))^2)*(p : ℝ)^(-(1:ℝ)/4)*(𝔼 x, f x^2) := by
  have hex (g : ZMod p → ℝ) : (𝔼 x : Unit → ZMod p, g (x ()))=𝔼 x, g x :=
    Fintype.expect_equiv (Equiv.funUnique Unit (ZMod p)) _ _ (fun _ => rfl)
  have hfun (x : Unit → ZMod p) : (fun _ : Unit => x ())=x := by ext i; cases i; rfl
  have hh := list_conditional_mixing hp E dir L hL (fun x => f (x ())) (by rw [hex, hf])
  have hpow : ((p : ℝ)^(-(1:ℝ)/8))^2=(p : ℝ)^(-(1:ℝ)/4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1; norm_num
  have hid := conditionalEnergy_equiv (Equiv.funUnique Unit (ZMod p))
    (Equiv.refl (J → ZMod p)) (fun x y => L y*listKernel E dir (fun _ => x) y) f
  simp only [Equiv.funUnique_apply, Equiv.refl_apply, hfun] at hid
  rw [← hid]
  have hx : (𝔼 x : Unit → ZMod p, f (x ())^2)=𝔼 x, f x^2 := hex (fun x => f x^2)
  simpa only [hx, mul_pow, hpow, mul_assoc] using hh

lemma graph_conditional_mixing {V : Type*} [Fintype V] [DecidableEq V]
    {p : ℕ} [Fact p.Prime] (hp : p≠2)
    (E : Finset (V×V)) (hE : ∀u∈E, (u.2,u.1)∉E)
    (hl : ∀v, (v,v)∉E) (v : V) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (fun x y => graphValidity E ((Equiv.funSplitAt v (ZMod p)).symm (x,y))) f ≤
      graphCondConstant E v*(p : ℝ)^(-(1:ℝ)/4)*(𝔼 x, f x^2) := by
  classical
  let E' := graphPullback (splitIndex v) E
  have hd (x : ZMod p) (y : {w : V // w≠v} → ZMod p) :
      graphValidity E ((Equiv.funSplitAt v (ZMod p)).symm (x,y))=
        graphRest E' y*listKernel (crossEdges E') (crossDir E') (fun _ => x) y :=
    graphValidity_singleton_reindex E hE hl v (fun _ => x) y
  simp only [hd]
  exact singleton_list_conditional_mixing hp (crossEdges E') (crossDir E')
    (graphRest E') (graphRest_le_one E') f hf

lemma tupleLeading_conditional_mixing {p : ℕ} [Fact p.Prime] (hp : p≠2)
    (v : TupleVertex) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (jointDensity (tupleComponentMap ∅) (Equiv.funSplitAt v (ZMod p))) f ≤
      graphCondConstant tupleLeadingGraph v*(p : ℝ)^(-(1:ℝ)/4)*(𝔼 x, f x^2) := by
  have he x y : jointDensity (tupleComponentMap (p := p) ∅) (Equiv.funSplitAt v (ZMod p)) x y=
      graphValidity tupleLeadingGraph ((Equiv.funSplitAt v (ZMod p)).symm (x,y)) :=
    jointDensity_uniform (tupleComponentMap ∅) _ (graphValidity tupleLeadingGraph)
      (tupleComponent_leading_integral) x y
  rw [show jointDensity (tupleComponentMap (p := p) ∅) (Equiv.funSplitAt v (ZMod p))=
      (fun x y => graphValidity tupleLeadingGraph ((Equiv.funSplitAt v (ZMod p)).symm (x,y)))
    from funext fun x => funext fun y => he x y]
  exact graph_conditional_mixing hp tupleLeadingGraph tupleLeadingGraph_no_opp
    tupleLeadingGraph_no_loop v f hf

lemma tupleComponent_marginal {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleComponent S (fun z => f (z v))=tupleComponent (p := p) S (fun _ => 1)*(𝔼 x, f x) := by
  apply invariant_marginal_uniform (tupleComponentMap S) _ v f
  intro a F
  change tupleComponent S (fun z => F (fun v => z v+a))=tupleComponent S F
  simpa only [one_pow, one_mul] using tupleComponent_affine S 1 a one_ne_zero F

lemma tupleComponent_conditional_contraction {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (v : TupleVertex) (f : ZMod p → ℝ) :
    conditionalEnergy (jointDensity (tupleComponentMap S) (Equiv.funSplitAt v (ZMod p))) f ≤
      tupleComponent (p := p) S (fun _ => 1)*(𝔼 x, f x^2) := by
  apply conditionalEnergy_uniform _ f
    (jointDensity_nonneg (tupleComponentMap S) _ (tupleComponent_nonneg S))
  intro x
  apply jointDensity_marginal
  intro g
  exact tupleComponent_marginal S v g

lemma jointDensity_smul {Ω X Y : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y) (c : ℝ) :
    jointDensity (c • L) e=fun x y => c*jointDensity L e x y := by
  funext x y
  simp only [jointDensity, lawDensity, LinearMap.smul_apply, smul_eq_mul]
  ring

lemma jointDensity_sum {Ω X Y I : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : I → (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y) (s : Finset I) :
    jointDensity (∑i∈s, L i) e=fun x y => ∑i∈s, jointDensity (L i) e x y := by
  funext x y
  simp only [jointDensity, lawDensity, LinearMap.sum_apply, mul_sum]

lemma conditionalEnergy_sum_le {X Y I : Type*} [Fintype X] [Fintype Y]
    (s : Finset I) (W : I → X → Y → ℝ) (f : X → ℝ)
    (hW : ∀i∈s, ∀x y, 0≤W i x y) :
    conditionalEnergy (fun x y => ∑i∈s, W i x y) f ≤
      ∑i∈s, conditionalEnergy (W i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [conditionalEnergy]
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact (conditionalEnergy_add_le _ _ f (hW i (mem_insert_self _ _))
      (fun x y => sum_nonneg fun j hj => hW j (mem_insert_of_mem hj) x y)).trans
      (add_le_add_right (ih fun j hj => hW j (mem_insert_of_mem hj)) _)

noncomputable def tupleSubmixture {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) : ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ :=
  ∑S∈D, tupleMixtureWeight p S • tupleComponentMap S

lemma tupleSubmixture_apply {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) (F : (TupleVertex → ZMod p) → ℝ) :
    tupleSubmixture D F=∑S∈D, tupleMixtureWeight p S*tupleComponent S F := by
  simp only [tupleSubmixture, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

lemma tupleSubmixture_nonneg {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) (F : (TupleVertex → ZMod p) → ℝ)
    (hF : ∀z, 0≤F z) : 0≤tupleSubmixture D F := by
  rw [tupleSubmixture_apply]
  exact sum_nonneg fun S _ => mul_nonneg (tupleMixtureWeight_nonneg p S)
    (tupleComponent_nonneg S F hF)

lemma tupleSubmixture_mass_lower {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (D : Finset (Finset (Fin tupleBlocks))) (hD : ∅∈D) :
    tupleLeadingMassLower≤tupleSubmixture (p := p) D (fun _ => 1) := by
  refine (tupleLeading_mass_lower hp).trans ?_
  rw [tupleSubmixture_apply]
  have h := single_le_sum (s := D) (fun S _ => mul_nonneg (tupleMixtureWeight_nonneg p S)
    (tupleComponent_nonneg (p := p) S (fun _ => 1) (fun _ => by norm_num))) hD
  simpa [tupleMixtureWeight] using h

lemma tupleSubmixture_marginal {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleSubmixture D (fun z => f (z v))=tupleSubmixture (p := p) D (fun _ => 1)*(𝔼 x, f x) := by
  simp only [tupleSubmixture_apply, tupleComponent_marginal, sum_mul, mul_assoc]

noncomputable def tupleSubLaw {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) : ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ :=
  (tupleSubmixture (p := p) D (fun _ => 1))⁻¹ • tupleSubmixture D

lemma tupleSubLaw_probability {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (D : Finset (Finset (Fin tupleBlocks))) (hD : ∅∈D) :
    tupleSubLaw (p := p) D (fun _ => 1)=1 := by
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos (tupleSubmixture_mass_lower hp D hD)
  simp only [tupleSubLaw, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hm.ne']

lemma tupleSubLaw_nonneg {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) (F : (TupleVertex → ZMod p) → ℝ)
    (hF : ∀z, 0≤F z) : 0≤tupleSubLaw D F :=
  mul_nonneg (inv_nonneg.mpr (tupleSubmixture_nonneg D _ (fun _ => by norm_num)))
    (tupleSubmixture_nonneg D F hF)

lemma tupleSubLaw_marginal {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold≤(p : ℝ)) (D : Finset (Finset (Fin tupleBlocks))) (hD : ∅∈D)
    (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleSubLaw D (fun z => f (z v))=𝔼 x, f x := by
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos (tupleSubmixture_mass_lower hp D hD)
  simp only [tupleSubLaw, LinearMap.smul_apply, smul_eq_mul, tupleSubmixture_marginal,
    ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]

lemma tupleMixtureWeight_small {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hS : S≠∅) :
    tupleMixtureWeight p S≤(p : ℝ)^(-(1:ℝ)/16) := by
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have hc : (1 : ℝ)≤S.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS).card_ne_zero
  linarith

lemma le_univ_sum_real {I : Type*} [Fintype I] (f : I → ℝ)
    (hf : ∀i, 0≤f i) (i : I) : f i≤∑j, f j :=
  single_le_sum (fun j _ => hf j) (mem_univ i)

noncomputable def tupleConditionalNumerator : ℝ :=
  (∑v : TupleVertex, graphCondConstant tupleLeadingGraph v)+
    ((univ : Finset (Finset (Fin tupleBlocks))).card : ℝ)*tupleWeightBound

lemma tupleConditionalNumerator_nonneg : 0≤tupleConditionalNumerator := by
  apply add_nonneg (sum_nonneg fun v _ => graphCondConstant_nonneg _ _)
  exact mul_nonneg (Nat.cast_nonneg _) tupleWeightBound_pos.le

lemma tupleSubmixture_conditional {p : ℕ} [Fact p.Prime] (hp : p≠2)
    (D : Finset (Finset (Fin tupleBlocks))) (hD : ∀S∈D, S.card≤tupleT+1)
    (v : TupleVertex) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (jointDensity (tupleSubmixture D) (Equiv.funSplitAt v (ZMod p))) f ≤
      tupleConditionalNumerator*(p : ℝ)^(-(1:ℝ)/16)*(𝔼 x, f x^2) := by
  let R := (p : ℝ)^(-(1:ℝ)/16)
  let A := ∑v : TupleVertex, graphCondConstant tupleLeadingGraph v
  let W := fun S => jointDensity (tupleComponentMap (p := p) S) (Equiv.funSplitAt v (ZMod p))
  have hR : 0≤R := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA : 0≤A := sum_nonneg fun v _ => graphCondConstant_nonneg _ _
  have hf2 : 0≤𝔼 x, f x^2 := expect_nonneg fun x _ => sq_nonneg _
  have hlead : conditionalEnergy (W ∅) f≤A*R*(𝔼 x, f x^2) := by
    refine (tupleLeading_conditional_mixing hp v f hf).trans ?_
    apply mul_le_mul_of_nonneg_right _ hf2
    apply mul_le_mul
    · exact le_univ_sum_real (graphCondConstant tupleLeadingGraph)
        (graphCondConstant_nonneg tupleLeadingGraph) v
    · exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (Fact.out : p.Prime).one_lt.le) (by norm_num)
    · exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    · exact hA
  have hterm (S) (hS : S∈D) : tupleMixtureWeight p S*conditionalEnergy (W S) f≤
      ((if S=∅ then A else 0)+tupleWeightBound)*R*(𝔼 x, f x^2) := by
    by_cases hs : S=∅
    · subst S
      simpa only [tupleMixtureWeight, card_empty, Nat.cast_zero, neg_zero, zero_div,
        Real.rpow_zero, one_mul, ite_true] using hlead.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right tupleWeightBound_pos.le) hR) hf2)
    · rw [ite_eq_right hs, zero_add]
      exact (mul_le_mul_of_nonneg_left (tupleComponent_conditional_contraction S v f)
        (tupleMixtureWeight_nonneg p S)).trans (by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ hf2
          calc
            _ ≤ R*tupleWeightBound := mul_le_mul (tupleMixtureWeight_small S hs)
              (tupleComponent_mass_le S (hD S hS))
              (tupleComponent_nonneg S _ (fun _ => by norm_num)) hR
            _ = _ := mul_comm _ _)
  have hsum : (∑S∈D, ((if S=∅ then A else 0)+tupleWeightBound))≤tupleConditionalNumerator := by
    rw [sum_add_distrib, sum_ite_eq', sum_const, nsmul_eq_mul]
    apply add_le_add
    · by_cases hd : (∅ : Finset (Fin tupleBlocks))∈D
      · rw [ite_eq_left hd]
      · rw [ite_eq_right hd]; exact hA
    · apply mul_le_mul_of_nonneg_right _ tupleWeightBound_pos.le
      exact_mod_cast card_le_card (subset_univ D)
  unfold tupleSubmixture
  rw [jointDensity_sum]
  simp only [jointDensity_smul]
  refine (conditionalEnergy_sum_le D (fun S x y => tupleMixtureWeight p S*W S x y) f
    (fun S _ x y => mul_nonneg (tupleMixtureWeight_nonneg p S)
      (jointDensity_nonneg _ _ (tupleComponent_nonneg S) x y))).trans ?_
  simp only [conditionalEnergy_smul]
  calc
    _ ≤ ∑S∈D, ((if S=∅ then A else 0)+tupleWeightBound)*R*(𝔼 x, f x^2) := sum_le_sum hterm
    _ = (∑S∈D, ((if S=∅ then A else 0)+tupleWeightBound))*R*(𝔼 x, f x^2) := by rw [sum_mul, sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum hR) hf2

noncomputable def tupleConditionalConstant : ℝ := tupleConditionalNumerator/tupleLeadingMassLower

noncomputable def tupleConditionalThreshold : ℝ :=
  max tupleMassThreshold (max 3 (tupleConditionalConstant^32))

lemma rpow_absorb_32 {C p : ℝ} (hC : 0≤C) (hp : 0<p) (h : C^32≤p) :
    C*p^(-(1:ℝ)/16)≤p^(-(1:ℝ)/32) := by
  have hh := Real.rpow_le_rpow (pow_nonneg hC 32) h (by norm_num : 0≤(1:ℝ)/32)
  have he : (C^32)^((1:ℝ)/32)=C := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC]
    norm_num
  rw [he] at hh
  have hmul := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hp.le (-(1:ℝ)/16))
  rw [← Real.rpow_add hp] at hmul
  norm_num only [show (1:ℝ)/32 + -(1:ℝ)/16=-(1:ℝ)/32 by norm_num] at hmul
  simpa only [neg_div] using hmul

lemma tupleSubLaw_conditional {p : ℕ} [Fact p.Prime]
    (hp : tupleConditionalThreshold≤(p : ℝ))
    (D : Finset (Finset (Fin tupleBlocks))) (hD0 : ∅∈D)
    (hD : ∀S∈D, S.card≤tupleT+1) (v : TupleVertex) (f : ZMod p → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (jointDensity (tupleSubLaw D) (Equiv.funSplitAt v (ZMod p))) f ≤
      (p : ℝ)^(-(1:ℝ)/32)*(𝔼 x, f x^2) := by
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos
    (tupleSubmixture_mass_lower ((le_max_left _ _).trans hp) D hD0)
  have hp3 : (3 : ℝ)≤p := (le_max_left _ _).trans ((le_max_right _ _).trans hp)
  have hp2 : p≠2 := by intro h; subst p; norm_num at hp3
  have hf2 : 0≤𝔼 x, f x^2 := expect_nonneg fun x _ => sq_nonneg _
  rw [tupleSubLaw, jointDensity_smul, conditionalEnergy_smul]
  calc
    _ ≤ (tupleSubmixture D (fun _ => 1))⁻¹*
        (tupleConditionalNumerator*(p : ℝ)^(-(1:ℝ)/16)*(𝔼 x, f x^2)) :=
      mul_le_mul_of_nonneg_left (tupleSubmixture_conditional hp2 D hD v f hf) (inv_nonneg.mpr hm.le)
    _ ≤ tupleLeadingMassLower⁻¹*
        (tupleConditionalNumerator*(p : ℝ)^(-(1:ℝ)/16)*(𝔼 x, f x^2)) := by
      apply mul_le_mul_of_nonneg_right
      · exact inv_anti₀ tupleLeadingMassLower_pos (tupleSubmixture_mass_lower ((le_max_left _ _).trans hp) D hD0)
      · exact mul_nonneg (mul_nonneg tupleConditionalNumerator_nonneg
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hf2
    _ = (tupleConditionalConstant*(p : ℝ)^(-(1:ℝ)/16))*(𝔼 x, f x^2) := by unfold tupleConditionalConstant; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (rpow_absorb_32
      (div_nonneg tupleConditionalNumerator_nonneg tupleLeadingMassLower_pos.le)
      (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)
      ((le_max_right _ _).trans ((le_max_right _ _).trans hp))) hf2

lemma linearMap_expect {Ω I : Type*} [Fintype I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (F : I → Ω → ℝ) :
    L (fun z => 𝔼 i, F i z)=𝔼 i, L (F i) := by
  rw [show (fun z => 𝔼 i, F i z)=(𝔼 i, F i) from (funext fun z =>
    (expect_apply univ F z).symm)]
  exact map_expect (L.restrictScalars ℚ≥0) F univ

noncomputable def squarePairAverage {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F → F → ℝ) : ℝ := 𝔼 q : Fˣ, 𝔼 x, g x (x+(q : F)^2)

lemma square_affine_pair_average {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F → F → ℝ) (x y : F) (hxy : y-x≠0 ∧ IsSquare (y-x)) :
    (𝔼 q : Fˣ, 𝔼 a : F, g ((q : F)^2*x+a) ((q : F)^2*y+a))=squarePairAverage g := by
  classical
  obtain ⟨r, hr⟩ := hxy.2
  have hr0 : r≠0 := by intro hz; simp [hz] at hr; exact hxy.1 hr
  have h1 (q : Fˣ) : (𝔼 a : F, g ((q : F)^2*x+a) ((q : F)^2*y+a))=
      𝔼 a : F, g a (a+((q : F)*r)^2) := by
    apply Fintype.expect_equiv (Equiv.addLeft ((q : F)^2*x))
    intro a
    congr 1
    have h : y=x+r*r := by linear_combination hr
    rw [h]
    simp only [Equiv.coe_addLeft]
    ring
  simp only [h1]
  unfold squarePairAverage
  apply Fintype.expect_equiv (Equiv.mulRight (Units.mk0 r hr0))
  intro q
  simp only [Equiv.coe_mulRight, Units.val_mul, Units.val_mk0]

lemma tupleComponent_pair_congr {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hS : S.card≤tupleT) (k : ℕ)
    (F G : ZMod p → ZMod p → ℝ)
    (hFG : ∀x y, y-x≠0 ∧ IsSquare (y-x) → F x y=G x y) :
    tupleComponent S (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      tupleComponent S (fun z => G (z (cycleVertex k)) (z (cycleVertex (k+1)))) := by
  unfold tupleComponent
  apply expect_congr rfl; intro Y _
  apply expect_congr rfl; intro j _
  by_cases hY : tupleValidity S Y=0
  · rw [hY]; ring
  · dsimp only
    rw [hFG _ _ (tuple_cycle_support S hS Y hY j k)]

lemma tupleComponent_pair_square {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hS : S.card≤tupleT) (k : ℕ)
    (F : ZMod p → ZMod p → ℝ) :
    tupleComponent S (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      tupleComponent (p := p) S (fun _ => 1)*squarePairAverage F := by
  have havg : tupleComponent S (fun z => 𝔼 q : (ZMod p)ˣ, 𝔼 a : ZMod p,
      F ((q : ZMod p)^2*z (cycleVertex k)+a) ((q : ZMod p)^2*z (cycleVertex (k+1))+a))=
      tupleComponent S (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1)))) := by
    change tupleComponentMap S (fun z => 𝔼 q : (ZMod p)ˣ, 𝔼 a : ZMod p,
      F ((q : ZMod p)^2*z (cycleVertex k)+a) ((q : ZMod p)^2*z (cycleVertex (k+1))+a))=_
    rw [linearMap_expect]
    simp_rw [linearMap_expect]
    have hi (q : (ZMod p)ˣ) (a : ZMod p) : tupleComponentMap S
        (fun z => F ((q : ZMod p)^2*z (cycleVertex k)+a) ((q : ZMod p)^2*z (cycleVertex (k+1))+a))=
        tupleComponent S (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1)))) :=
      tupleComponent_affine S (q : ZMod p) a q.ne_zero
        (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))
    simp only [hi, Fintype.expect_const]
  rw [← havg]
  have he := tupleComponent_pair_congr S hS k
    (fun x y => 𝔼 q : (ZMod p)ˣ, 𝔼 a : ZMod p, F ((q : ZMod p)^2*x+a) ((q : ZMod p)^2*y+a))
    (fun _ _ => squarePairAverage F) (fun x y h => square_affine_pair_average F x y h)
  exact he.trans (by
    change tupleComponentMap S (fun _ => squarePairAverage F)=_
    have hc : (fun _ : TupleVertex → ZMod p => squarePairAverage F)=squarePairAverage F • (fun _ => (1:ℝ)) := by
      ext; simp
    rw [hc, map_smul, smul_eq_mul]
    exact mul_comm _ _)

lemma expect_eval {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Nonempty X]
    (i : I) (f : X → ℝ) : (𝔼 Y : I → X, f (Y i))=𝔼 x, f x := by
  have h := Fintype.expect_equiv (Equiv.funSplitAt i X) (fun Y => f (Y i))
    (fun z => f z.1) (fun _ => rfl)
  rw [h, ← univ_product_univ, expect_product]
  simp only [Fintype.expect_const]

end SquareDifference
end

end OAI
