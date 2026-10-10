import OAI.Combinatorics.Sidorenko.Configurations

namespace OAI

namespace SidorenkoCounterexample
open Module
section CommonOrbitGeometry
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)

 theorem reduceSubspace_finrank_containing (S A : Submodule K E)
    (hSA : S ≤ A) (hAP : A ≤ ω.orthogonal S) :
    finrank K (reduceSubspace ω S A) + finrank K S = finrank K A := by
  let f : A →ₗ[K] ReducedSpace ω S := (reductionKernel ω S).mkQ.comp (Submodule.inclusion hAP)
  have hk : LinearMap.ker f = S.comap A.subtype := by
    ext x
    exact Submodule.Quotient.mk_eq_zero (reductionKernel ω S)
  have hr : LinearMap.range f = reduceSubspace ω S A := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hAP x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  have hh := f.finrank_range_add_finrank_ker
  rw [hk,hr,(Submodule.comapSubtypeEquivOfLe hSA).finrank_eq] at hh
  exact hh

noncomputable def commonReductionLagrangian (S : Submodule K E) (ha : ω.IsAlt)
    (hS : S ≤ ω.orthogonal S) (L : SymplecticLagrangian ω) (hSL : S ≤ L.val) :
    SymplecticLagrangian (symplecticReductionForm ω S ha) :=
  ⟨reduceSubspace ω S L.val,reduce_lagrangian ω S ha hS L.val L.property hSL⟩

 theorem commonOrbit_injection [Finite E] (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : SymplecticLagrangian ω) :
    let S := (L.val ⊓ M.val) ⊓ N.val
    ∃ f : IsotropicDimspace ω (finrank K S) ×
      OrderedTripleOrbit (symplecticReductionForm ω S ha)
        (reduceSubspace ω S L.val) (reduceSubspace ω S M.val) (reduceSubspace ω S N.val) →
      OrderedTripleOrbit ω L.val M.val N.val, Function.Injective f := by
  dsimp only
  classical
  let S := (L.val ⊓ M.val) ⊓ N.val
  have hSL : S ≤ L.val := inf_le_left.trans inf_le_left
  have hSM : S ≤ M.val := inf_le_left.trans inf_le_right
  have hSN : S ≤ N.val := inf_le_right
  have hS : S ≤ ω.orthogonal S := by
    intro x hx y hy
    exact L.property.ge (hSL hx) y (hSL hy)
  let η := symplecticReductionForm ω S ha
  let L' := commonReductionLagrangian ω S ha hS L hSL
  let M' := commonReductionLagrangian ω S ha hS M hSM
  let N' := commonReductionLagrangian ω S ha hS N hSN
  have hzero : (L'.val ⊓ M'.val) ⊓ N'.val = ⊥ := by
    change (reduceSubspace ω S L.val ⊓ reduceSubspace ω S M.val) ⊓ reduceSubspace ω S N.val = ⊥
    rw [←reduceSubspace_inf ω S L.val M.val hSL,
      ←reduceSubspace_inf ω S (L.val ⊓ M.val) N.val inf_le_left]
    exact reduceSubspace_self ω S
  have ht (T : IsotropicDimspace ω (finrank K S)) := isotropic_transitivity ω h2 ha hω
    S T.val hS T.property.1 T.property.2.symm
  let e (T : IsotropicDimspace ω (finrank K S)) := (ht T).choose
  have he (T : IsotropicDimspace ω (finrank K S)) := (ht T).choose_spec
  let Orb := OrderedTripleOrbit η L'.val M'.val N'.val
  have hpLag (p : Orb) := orderedTripleOrbit_lagrangians η L' M' N' p
  have hpzero (p : Orb) : (p.val.1 ⊓ p.val.2.1) ⊓ p.val.2.2 = ⊥ := by
    obtain ⟨g,_,hgL,hgM,hgN⟩ := p.property
    rw [←hgL,←hgM,←hgN,←Submodule.map_inf g.toLinearMap g.injective,
      ←Submodule.map_inf g.toLinearMap g.injective,hzero,Submodule.map_bot]
  have hgood (p : Orb) : TripleIsometry ω ω L.val M.val N.val
      (liftReduction ω S p.val.1) (liftReduction ω S p.val.2.1) (liftReduction ω S p.val.2.2) := by
    apply triple_containing_isometry_lift ω S ha hω hS L.val M.val N.val
      (liftReduction ω S p.val.1) (liftReduction ω S p.val.2.1) (liftReduction ω S p.val.2.2)
      L.property M.property N.property
      (liftReduction_lagrangian ω S ha hS _ (hpLag p).1)
      (liftReduction_lagrangian ω S ha hS _ (hpLag p).2.1)
      (liftReduction_lagrangian ω S ha hS _ (hpLag p).2.2)
      hSL hSM hSN (le_liftReduction ω S hS _) (le_liftReduction ω S hS _) (le_liftReduction ω S hS _)
    rw [reduce_lift,reduce_lift,reduce_lift]
    exact p.property
  have hgood' (T : IsotropicDimspace ω (finrank K S)) (p : Orb) : TripleIsometry ω ω L.val M.val N.val
      ((liftReduction ω S p.val.1).map (e T).toLinearMap)
      ((liftReduction ω S p.val.2.1).map (e T).toLinearMap)
      ((liftReduction ω S p.val.2.2).map (e T).toLinearMap) := by
    obtain ⟨g,hg,hgL,hgM,hgN⟩ := hgood p
    refine ⟨g.trans (e T),?_,?_,?_,?_⟩
    · intro x y
      exact ((he T).1 (g x) (g y)).trans (hg x y)
    · rw [submodule_map_trans,hgL]
    · rw [submodule_map_trans,hgM]
    · rw [submodule_map_trans,hgN]
  let f : IsotropicDimspace ω (finrank K S) × Orb → OrderedTripleOrbit ω L.val M.val N.val := fun p =>
    ⟨((liftReduction ω S p.2.val.1).map (e p.1).toLinearMap,
      (liftReduction ω S p.2.val.2.1).map (e p.1).toLinearMap,
      (liftReduction ω S p.2.val.2.2).map (e p.1).toLinearMap),hgood' p.1 p.2⟩
  have hrec (p) : ((f p).val.1 ⊓ (f p).val.2.1) ⊓ (f p).val.2.2 = p.1.val := by
    change (((liftReduction ω S p.2.val.1).map (e p.1).toLinearMap) ⊓
      ((liftReduction ω S p.2.val.2.1).map (e p.1).toLinearMap)) ⊓
      ((liftReduction ω S p.2.val.2.2).map (e p.1).toLinearMap) = _
    rw [←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←liftReduction_inf,←liftReduction_inf,hpzero, liftReduction_bot ω S hS]
    exact (he p.1).2
  refine ⟨f,?_⟩
  rintro ⟨T,p⟩ ⟨T',p'⟩ h
  have hT : T = T' := by
    apply Subtype.ext
    exact (hrec (T,p)).symm.trans ((congrArg (fun x : OrderedTripleOrbit ω L.val M.val N.val =>
      (x.val.1 ⊓ x.val.2.1) ⊓ x.val.2.2) h).trans (hrec (T',p')))
  subst T'
  have hv := congrArg Subtype.val h
  have hinj := (Submodule.map_injective_of_injective (e T).injective).comp (liftReduction_injective ω S)
  have hp : p = p' := Subtype.ext (Prod.ext (hinj (congrArg Prod.fst hv))
    (Prod.ext (hinj (congrArg (fun x => x.2.1) hv)) (hinj (congrArg (fun x => x.2.2) hv))))
  subst p'
  rfl

variable [Finite E]
 theorem commonOrbit_card_lower (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : SymplecticLagrangian ω) :
    let S := (L.val ⊓ M.val) ⊓ N.val
    Nat.card (IsotropicDimspace ω (finrank K S)) *
      Nat.card (OrderedTripleOrbit (symplecticReductionForm ω S ha)
        (reduceSubspace ω S L.val) (reduceSubspace ω S M.val) (reduceSubspace ω S N.val)) ≤
      Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  obtain ⟨f,hf⟩ := commonOrbit_injection ω h2 ha hω L M N
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf
end CommonOrbitGeometry
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section AllOrbitMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)

noncomputable def tripleDefect (D : ℕ) (L M N : Submodule K E) : ℕ :=
  let c := finrank K ↥((L ⊓ M) ⊓ N)
  (D+1)*c + ((finrank K ↥(L ⊓ M)-c+1).choose 2 +
    (finrank K ↥(L ⊓ N)-c+1).choose 2 + (finrank K ↥(M ⊓ N)-c+1).choose 2)

 theorem pairOrbitConstant_mono : Monotone pairOrbitConstant := by
  intro m n h
  unfold pairOrbitConstant
  have hm := lagrangianConstant_pos m
  have hn := lagrangianConstant_pos n
  have hc := lagrangianConstant_mono h
  gcongr <;> norm_num

noncomputable def orbitMassConstant (D : ℕ) : ℝ := lagrangianConstant D*pairOrbitConstant D

 theorem orbitMassConstant_pos (D : ℕ) : 0 < orbitMassConstant D :=
  mul_pos (lagrangianConstant_pos D) (pairOrbitConstant_pos D)

 theorem tripleOrbit_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (L M N : SymplecticLagrangian ω) :
    (Fintype.card K : ℝ)^(3*(D+1).choose 2) ≤
      orbitMassConstant D * (Fintype.card K : ℝ)^(tripleDefect D L.val M.val N.val) *
        Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  let S := (L.val ⊓ M.val) ⊓ N.val
  have hSL : S ≤ L.val := inf_le_left.trans inf_le_left
  have hSM : S ≤ M.val := inf_le_left.trans inf_le_right
  have hSN : S ≤ N.val := inf_le_right
  have hS : S ≤ ω.orthogonal S := by
    intro x hx y hy
    exact L.property.ge (hSL hx) y (hSL hy)
  let c := finrank K S
  have hc : c ≤ D := isotropic_finrank_le_half ω hω D hD S hS
  let η := symplecticReductionForm ω S ha
  let L' := commonReductionLagrangian ω S ha hS L hSL
  let M' := commonReductionLagrangian ω S ha hS M hSM
  let N' := commonReductionLagrangian ω S ha hS N hSN
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  have hzero : (L'.val ⊓ M'.val) ⊓ N'.val = ⊥ := by
    change (reduceSubspace ω S L.val ⊓ reduceSubspace ω S M.val) ⊓ reduceSubspace ω S N.val = ⊥
    rw [←reduceSubspace_inf ω S L.val M.val hSL,
      ←reduceSubspace_inf ω S (L.val ⊓ M.val) N.val inf_le_left]
    exact reduceSubspace_self ω S
  have hdim : 2*(D-c) = finrank K (ReducedSpace ω S) := by
    have hh := reducedSpace_finrank ω S hω hS
    change _ + 2*c = _ at hh
    omega
  have hq' : 4*lagrangianConstant (D-c) ≤ (Fintype.card K : ℝ) :=
    (mul_le_mul_of_nonneg_left (lagrangianConstant_mono (Nat.sub_le D c)) (by norm_num)).trans hq
  have hp := commonZeroOrbit_card_lower η (symplecticReductionForm_alt ω S ha)
    (symplecticReductionForm_nondegenerate ω S ha hω) (D-c) hdim hq' L' M' N' hzero
  have hpair (P Q : SymplecticLagrangian ω) (hSP : S ≤ P.val) (hSQ : S ≤ Q.val) :
      finrank K ↥(reduceSubspace ω S P.val ⊓ reduceSubspace ω S Q.val) =
        finrank K ↥(P.val ⊓ Q.val)-c := by
    rw [←reduceSubspace_inf ω S P.val Q.val hSP]
    have hh := reduceSubspace_finrank_containing ω S (P.val ⊓ Q.val) (le_inf hSP hSQ)
      (inf_le_left.trans (lagrangian_le_orthogonal ω S P.val P.property hSP))
    change _ + c = _ at hh
    omega
  change (Fintype.card K : ℝ)^(3*(D-c+1).choose 2) ≤ pairOrbitConstant (D-c) *
    (Fintype.card K : ℝ)^((finrank K ↥(reduceSubspace ω S L.val ⊓ reduceSubspace ω S M.val)+1).choose 2 +
      (finrank K ↥(reduceSubspace ω S L.val ⊓ reduceSubspace ω S N.val)+1).choose 2 +
      (finrank K ↥(reduceSubspace ω S M.val ⊓ reduceSubspace ω S N.val)+1).choose 2) * _ at hp
  rw [hpair L M hSL hSM,hpair L N hSL hSN,hpair M N hSM hSN] at hp
  have h2 := (isUnit_of_invertible (2:K)).ne_zero
  have hi := (isotropic_card_bounds ω h2 ha hω D hD c hc).1
  have hm : (Nat.card (IsotropicDimspace ω c) : ℝ) *
    Nat.card (OrderedTripleOrbit η L'.val M'.val N'.val) ≤
      Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    exact_mod_cast commonOrbit_card_lower ω h2 ha hω L M N
  let δ := (finrank K ↥(L.val ⊓ M.val)-c+1).choose 2 +
    (finrank K ↥(L.val ⊓ N.val)-c+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)-c+1).choose 2
  have hconst : lagrangianConstant (D-c)*pairOrbitConstant (D-c) ≤ orbitMassConstant D :=
    mul_le_mul (lagrangianConstant_mono (Nat.sub_le D c)) (pairOrbitConstant_mono (Nat.sub_le D c))
      (le_of_lt (pairOrbitConstant_pos _)) (le_of_lt (lagrangianConstant_pos _))
  have hm' := mul_le_mul hconst hm (by positivity) (le_of_lt (orbitMassConstant_pos D))
  have hbase : (Fintype.card K : ℝ)^(isotropicExponent D c+3*(D-c+1).choose 2) ≤
      orbitMassConstant D * (Fintype.card K : ℝ)^δ * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    calc
      _ ≤ (lagrangianConstant (D-c)*Nat.card (IsotropicDimspace ω c)) *
        (pairOrbitConstant (D-c)*(Fintype.card K : ℝ)^δ * Nat.card (OrderedTripleOrbit η L'.val M'.val N'.val)) := by
          rw [pow_add]
          exact mul_le_mul hi hp (by positivity) (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (Nat.cast_nonneg _))
      _ = ((lagrangianConstant (D-c)*pairOrbitConstant (D-c))*
        ((Nat.card (IsotropicDimspace ω c) : ℝ)*Nat.card (OrderedTripleOrbit η L'.val M'.val N'.val)))*
          (Fintype.card K : ℝ)^δ := by ring
      _ ≤ (orbitMassConstant D*Nat.card (OrderedTripleOrbit ω L.val M.val N.val))*
          (Fintype.card K : ℝ)^δ := mul_le_mul_of_nonneg_right hm' (by positivity)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_right hbase (show 0 ≤ (Fintype.card K : ℝ)^((D+1)*c) by positivity)
  rw [←pow_add,common_cost_cancellation D c hc] at hh
  change _ ≤ orbitMassConstant D * (Fintype.card K : ℝ)^((D+1)*c+δ) * _
  rw [pow_add]
  calc
    _ ≤ (orbitMassConstant D*(Fintype.card K : ℝ)^δ*Nat.card (OrderedTripleOrbit ω L.val M.val N.val))*
      (Fintype.card K : ℝ)^((D+1)*c) := hh
    _ = _ := by ring
end AllOrbitMass
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section ConfigurationUpper
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem triple_subspace_orbit_surjection (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (_hsum : U ⊔ V ⊔ W = S) :
    ∃ f : IsotropicDimspace ω (finrank K S) ×
      TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        OrderedTripleOrbit ω U V W, Function.Surjective f := by
  classical
  have ht (T : IsotropicDimspace ω (finrank K S)) := isotropic_transitivity ω h2 ha hω
    S T.val hS T.property.1 T.property.2.symm
  let e (T : IsotropicDimspace ω (finrank K S)) := (ht T).choose
  have he (T) := (ht T).choose_spec
  have hgood (T : IsotropicDimspace ω (finrank K S))
      (p : TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) :
      ∃ f : E ≃ₗ[K] E, (∀ x y, ω (f x) (f y) = ω x y) ∧
        U.map f.toLinearMap = (p.val.1.map S.subtype).map (e T).toLinearMap ∧
        V.map f.toLinearMap = (p.val.2.1.map S.subtype).map (e T).toLinearMap ∧
        W.map f.toLinearMap = (p.val.2.2.map S.subtype).map (e T).toLinearMap := by
    obtain ⟨g,hgU,hgV,hgW⟩ := p.property
    obtain ⟨r,hr,hrg⟩ := exists_isotropic_isometry_extension ω h2 ha hω S S hS hS g
    refine ⟨r.trans (e T),?_,?_,?_,?_⟩
    · intro x y
      exact ((he T).1 (r x) (r y)).trans (hr x y)
    · rw [submodule_map_trans,subspace_map_extension S S U hU r g hrg,hgU]
    · rw [submodule_map_trans,subspace_map_extension S S V hV r g hrg,hgV]
    · rw [submodule_map_trans,subspace_map_extension S S W hW r g hrg,hgW]
  let f : IsotropicDimspace ω (finrank K S) ×
      TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        OrderedTripleOrbit ω U V W := fun p =>
    ⟨((p.2.val.1.map S.subtype).map (e p.1).toLinearMap,
      (p.2.val.2.1.map S.subtype).map (e p.1).toLinearMap,
      (p.2.val.2.2.map S.subtype).map (e p.1).toLinearMap),hgood p.1 p.2⟩
  refine ⟨f,?_⟩
  intro p
  obtain ⟨g,hg,hgU,hgV,hgW⟩ := p.property
  have hT : S.map g.toLinearMap ≤ ω.orthogonal (S.map g.toLinearMap) := by
    rw [orthogonal_map_of_isometry ω g hg]
    exact Submodule.map_mono hS
  let T : IsotropicDimspace ω (finrank K S) :=
    ⟨S.map g.toLinearMap,hT,g.finrank_map_eq S⟩
  let r := g.trans (e T).symm
  have hrS : S.map r.toLinearMap = S := by
    rw [submodule_map_trans]
    change T.val.map (e T).symm.toLinearMap = S
    rw [←(he T).2,submodule_map_symm_cancel]
  let rS : S ≃ₗ[K] S := r.ofSubmodules S S hrS
  let q := tripleLinearOrbitMap (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) rS
  have heq : r.trans (e T) = g := by
    ext x
    simp only [r,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  have hmap (A : Submodule K E) (hA : A ≤ S) :
      ((((A.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap) = A.map g.toLinearMap := by
    rw [←subspace_map_extension S S A hA r rS (fun _ => rfl),←submodule_map_trans,heq]
  refine ⟨(T,q),Subtype.ext ?_⟩
  change (((((U.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap),
    ((((V.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap),
    ((((W.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap)) = p.val
  rw [hmap U hU,hmap V hV,hmap W hW,hgU,hgV,hgW]

 theorem triple_subspace_orbit_card_identity (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S) :
    Nat.card (OrderedTripleOrbit ω U V W) = Nat.card (IsotropicDimspace ω (finrank K S)) *
      Nat.card (TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) := by
  apply le_antisymm
  · obtain ⟨f,hf⟩ := triple_subspace_orbit_surjection ω h2 ha hω S U V W hS hU hV hW hsum
    simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hf
  · obtain ⟨f,hf⟩ := triple_subspace_orbit_injection ω h2 ha hω S U V W hS hU hV hW hsum
    simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf
end ConfigurationUpper
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DecompositionTransitivity
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

 theorem subspace_map_eq_of_restriction_equiv (U : Submodule K E) (V : Submodule K F)
    (e : E ≃ₗ[K] F) (g : U ≃ₗ[K] V) (h : ∀ x : U, e x.val = (g x).val) :
    U.map e.toLinearMap = V := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change e (⟨x,hx⟩ : U).val ∈ V
    rw [h ⟨x,hx⟩]
    exact (g ⟨x,hx⟩).property
  · intro hy
    obtain ⟨x,hx⟩ := g.surjective ⟨y,hy⟩
    exact ⟨x.val,x.property,(h x).trans (congrArg Subtype.val hx)⟩

variable [FiniteDimensional K E] [FiniteDimensional K F]
 theorem triple_decomposition_equiv (U V W : Submodule K E) (U' V' W' : Submodule K F)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W)
    (hU' : IsCompl U' (V' ⊔ W')) (hVW' : Disjoint V' W')
    (hu : finrank K U = finrank K U') (hv : finrank K V = finrank K V') (hw : finrank K W = finrank K W') :
    ∃ e : E ≃ₗ[K] F, U.map e.toLinearMap = U' ∧ V.map e.toLinearMap = V' ∧ W.map e.toLinearMap = W' := by
  let gu := LinearEquiv.ofFinrankEq U U' hu
  let gv := LinearEquiv.ofFinrankEq V V' hv
  let gw := LinearEquiv.ofFinrankEq W W' hw
  let a := tripleSumEquiv U V W hU hVW
  let b := tripleSumEquiv U' V' W' hU' hVW'
  let e := a.symm.trans ((gu.prodCongr (gv.prodCongr gw)).trans b)
  have heU (x : U) : e x.val = (gu x).val := by
    have hax : a (x,(0,0)) = x.val := by simp [a]
    rw [←hax]
    simp [e,b]
  have heV (x : V) : e x.val = (gv x).val := by
    have hax : a (0,(x,0)) = x.val := by simp [a]
    rw [←hax]
    simp [e,b]
  have heW (x : W) : e x.val = (gw x).val := by
    have hax : a (0,(0,x)) = x.val := by simp [a]
    rw [←hax]
    simp [e,b]
  exact ⟨e,subspace_map_eq_of_restriction_equiv U U' e gu heU,
    subspace_map_eq_of_restriction_equiv V V' e gv heV,subspace_map_eq_of_restriction_equiv W W' e gw heW⟩
end DecompositionTransitivity

section ConfigTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)

 omit [Finite E] in
 theorem triple_comap_isCompl (S U V W : Submodule K E)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S)
    (hsum : U ⊔ V ⊔ W = S) (hdis : Disjoint U (V ⊔ W)) :
    IsCompl (U.comap S.subtype) (V.comap S.subtype ⊔ W.comap S.subtype) := by
  constructor
  · apply disjoint_iff.mpr
    rw [←subspace_comap_sup_of_le S V W hV hW,←Submodule.comap_inf,disjoint_iff.mp hdis]
    simp
  · apply codisjoint_iff.mpr
    rw [←sup_assoc,←subspace_comap_sup_of_le S U V hU hV,
      ←subspace_comap_sup_of_le S (U ⊔ V) W (sup_le hU hV) hW,hsum]
    simp

 theorem triple_isotropic_config_transitivity (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (U V W U' V' W' : Submodule K E)
    (hS : U ⊔ V ⊔ W ≤ ω.orthogonal (U ⊔ V ⊔ W))
    (hS' : U' ⊔ V' ⊔ W' ≤ ω.orthogonal (U' ⊔ V' ⊔ W'))
    (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W)
    (hdis' : Disjoint U' (V' ⊔ W')) (hVW' : Disjoint V' W')
    (hu : finrank K U = finrank K U') (hv : finrank K V = finrank K V') (hw : finrank K W = finrank K W') :
    TripleIsometry ω ω U V W U' V' W' := by
  let S := U ⊔ V ⊔ W
  let T := U' ⊔ V' ⊔ W'
  have hU : U ≤ S := le_sup_of_le_left le_sup_left
  have hV : V ≤ S := le_sup_of_le_left le_sup_right
  have hW : W ≤ S := le_sup_right
  have hU' : U' ≤ T := le_sup_of_le_left le_sup_left
  have hV' : V' ≤ T := le_sup_of_le_left le_sup_right
  have hW' : W' ≤ T := le_sup_right
  have hd : Disjoint (V.comap S.subtype) (W.comap S.subtype) := by
    apply disjoint_iff.mpr
    rw [←Submodule.comap_inf,hVW.eq_bot]
    simp
  have hd' : Disjoint (V'.comap T.subtype) (W'.comap T.subtype) := by
    apply disjoint_iff.mpr
    rw [←Submodule.comap_inf,hVW'.eq_bot]
    simp
  obtain ⟨g,hgU,hgV,hgW⟩ := triple_decomposition_equiv
    (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)
    (U'.comap T.subtype) (V'.comap T.subtype) (W'.comap T.subtype)
    (triple_comap_isCompl S U V W hU hV hW rfl hdis) hd
    (triple_comap_isCompl T U' V' W' hU' hV' hW' rfl hdis') hd'
    (by rw [(Submodule.comapSubtypeEquivOfLe hU).finrank_eq,(Submodule.comapSubtypeEquivOfLe hU').finrank_eq]; exact hu)
    (by rw [(Submodule.comapSubtypeEquivOfLe hV).finrank_eq,(Submodule.comapSubtypeEquivOfLe hV').finrank_eq]; exact hv)
    (by rw [(Submodule.comapSubtypeEquivOfLe hW).finrank_eq,(Submodule.comapSubtypeEquivOfLe hW').finrank_eq]; exact hw)
  obtain ⟨e,he,heg⟩ := exists_isotropic_isometry_extension ω h2 ha hω S T hS hS' g
  refine ⟨e,he,?_,?_,?_⟩
  · rw [subspace_map_extension S T U hU e g heg,hgU,subtype_map_comap_of_le T U' hU']
  · rw [subspace_map_extension S T V hV e g heg,hgV,subtype_map_comap_of_le T V' hV']
  · rw [subspace_map_extension S T W hW e g heg,hgW,subtype_map_comap_of_le T W' hW']
end ConfigTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem triple_isotropic_orbit_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S)
    (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W) :
    (Nat.card (OrderedTripleOrbit ω U V W) : ℝ) ≤
      (lagrangianConstant D * 4^D) * (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
        2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by
  have hconst := lagrangianConstant_pos D
  let U' := U.comap S.subtype
  let V' := V.comap S.subtype
  let W' := W.comap S.subtype
  have hc : IsCompl U' (V' ⊔ W') := triple_comap_isCompl S U V W hU hV hW hsum hdis
  have hvw : Disjoint V' W' := by
    apply disjoint_iff.mpr
    change V.comap S.subtype ⊓ W.comap S.subtype = ⊥
    rw [←Submodule.comap_inf,disjoint_iff.mp hVW]
    simp
  have hu' : finrank K U' = finrank K U := (Submodule.comapSubtypeEquivOfLe hU).finrank_eq
  have hv' : finrank K V' = finrank K V := (Submodule.comapSubtypeEquivOfLe hV).finrank_eq
  have hw' : finrank K W' = finrank K W := (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have hb := (tripleLinearOrbit_card_bounds U' V' W' hc hvw).2
  rw [hu',hv',hw'] at hb
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  have hi := (isotropic_card_bounds ω h2 ha hω D hD (finrank K S) hs).2
  have hk : (2:ℝ)^(finrank K S) * 2^(finrank K S) ≤ 4^D := by
    calc
      _ = (4:ℝ)^(finrank K S) := by rw [←mul_pow]; norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hs
  rw [triple_subspace_orbit_card_identity ω h2 ha hω S U V W hS hU hV hW hsum,Nat.cast_mul]
  calc
    _ ≤ ((lagrangianConstant D*2^(finrank K S))*(Fintype.card K : ℝ)^isotropicExponent D (finrank K S)) *
      (2^(finrank K S)*(Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W))) :=
        mul_le_mul hi hb (Nat.cast_nonneg _) (by positivity)
    _ = (lagrangianConstant D*(2^(finrank K S)*2^(finrank K S))) * (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
        2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by rw [pow_add]; ring
    _ ≤ _ := by gcongr
end ConfigurationBound

section CommonZeroProfiles
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev CommonZeroDimProfile (L M N : SymplecticLagrangian ω) :=
  {p : SymplecticLagrangian ω × SymplecticLagrangian ω × SymplecticLagrangian ω //
    (p.1.val ⊓ p.2.1.val) ⊓ p.2.2.val = ⊥ ∧
    finrank K ↥(p.1.val ⊓ p.2.1.val) = finrank K ↥(L.val ⊓ M.val) ∧
    finrank K ↥(p.1.val ⊓ p.2.2.val) = finrank K ↥(L.val ⊓ N.val) ∧
    finrank K ↥(p.2.1.val ⊓ p.2.2.val) = finrank K ↥(M.val ⊓ N.val)}
variable [Finite E]
 omit [FiniteDimensional K E] in
 theorem commonZeroProfile_injection (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    ∃ f : CommonZeroDimProfile ω L M N →
      OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
      {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ P.val} ×
      {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ P.val} ×
      {P : SymplecticLagrangian ω // (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ P.val},
      Function.Injective f := by
  classical
  let O := OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)
  have ht (p : CommonZeroDimProfile ω L M N) :
      TripleIsometry ω ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)
        (p.val.1.val ⊓ p.val.2.1.val) (p.val.1.val ⊓ p.val.2.2.val) (p.val.2.1.val ⊓ p.val.2.2.val) := by
    have hd := triple_pairs_disjoint L.val M.val N.val h0
    have hd' := triple_pairs_disjoint p.val.1.val p.val.2.1.val p.val.2.2.val p.property.1
    exact triple_isotropic_config_transitivity ω h2 ha hω _ _ _ _ _ _
      (triplePairSum_isotropic ω _ _ _ L.property M.property N.property)
      (triplePairSum_isotropic ω _ _ _ p.val.1.property p.val.2.1.property p.val.2.2.property)
      hd.1 hd.2 hd'.1 hd'.2 p.property.2.1.symm p.property.2.2.1.symm p.property.2.2.2.symm
  let orb (p : CommonZeroDimProfile ω L M N) : O :=
    ⟨(p.val.1.val ⊓ p.val.2.1.val,p.val.1.val ⊓ p.val.2.2.val,p.val.2.1.val ⊓ p.val.2.2.val),ht p⟩
  let e (o : O) := o.property.choose
  have he (o : O) := o.property.choose_spec
  have hes (o : O) (x y : E) : ω ((e o).symm x) ((e o).symm y) = ω x y := by
    simpa only [e,LinearEquiv.apply_symm_apply] using ((he o).1 ((e o).symm x) ((e o).symm y)).symm
  let g (o : O) := lagrangianIsometryEquiv ω (e o).symm (hes o)
  have hg (o : O) (P : SymplecticLagrangian ω) : (g o P).val = P.val.map (e o).symm.toLinearMap := rfl
  have hpL (p : CommonZeroDimProfile ω L M N) :
      (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ (g (orb p) p.val.1).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ M.val) ⊔ (L.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.1.val
    rw [Submodule.map_sup,(he (orb p)).2.1,(he (orb p)).2.2.1]
    exact sup_le inf_le_left inf_le_left
  have hpM (p : CommonZeroDimProfile ω L M N) :
      (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ (g (orb p) p.val.2.1).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ M.val) ⊔ (M.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.2.1.val
    rw [Submodule.map_sup,(he (orb p)).2.1,(he (orb p)).2.2.2]
    exact sup_le inf_le_right inf_le_left
  have hpN (p : CommonZeroDimProfile ω L M N) :
      (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ (g (orb p) p.val.2.2).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ N.val) ⊔ (M.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.2.2.val
    rw [Submodule.map_sup,(he (orb p)).2.2.1,(he (orb p)).2.2.2]
    exact sup_le inf_le_right inf_le_right
  let f (p : CommonZeroDimProfile ω L M N) :=
    (orb p,(⟨g (orb p) p.val.1,hpL p⟩ : {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ P.val}),
      (⟨g (orb p) p.val.2.1,hpM p⟩ : {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ P.val}),
      (⟨g (orb p) p.val.2.2,hpN p⟩ : {P : SymplecticLagrangian ω // (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ P.val}))
  refine ⟨f,?_⟩
  intro p q hpq
  have ho : orb p = orb q := congrArg Prod.fst hpq
  have hL : g (orb p) p.val.1 = g (orb p) q.val.1 := by
    simpa only [f,ho] using congrArg (fun r => r.2.1.val) hpq
  have hM : g (orb p) p.val.2.1 = g (orb p) q.val.2.1 := by
    simpa only [f,ho] using congrArg (fun r => r.2.2.1.val) hpq
  have hN : g (orb p) p.val.2.2 = g (orb p) q.val.2.2 := by
    simpa only [f,ho] using congrArg (fun r => r.2.2.2.val) hpq
  exact Subtype.ext (Prod.ext ((g (orb p)).injective hL)
    (Prod.ext ((g (orb p)).injective hM) ((g (orb p)).injective hN)))
end CommonZeroProfiles
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
noncomputable def profileMassConstant (D : ℕ) : ℝ := lagrangianConstant D^4 * 4^D
 theorem profileMassConstant_pos (D : ℕ) : 0 < profileMassConstant D := by
  unfold profileMassConstant
  have := lagrangianConstant_pos D
  positivity
 theorem profileMassConstant_mono : Monotone profileMassConstant := by
  intro a b hab
  unfold profileMassConstant
  exact mul_le_mul (pow_le_pow_left₀ (le_of_lt (lagrangianConstant_pos a)) (lagrangianConstant_mono hab) 4)
    (pow_le_pow_right₀ (by norm_num) hab) (by positivity) (by positivity)
section CommonZeroMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem commonZeroProfile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2 +
      (finrank K ↥(L.val ⊓ N.val)+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)+1).choose 2) *
      Nat.card (CommonZeroDimProfile ω L M N) ≤ profileMassConstant D * (Fintype.card K : ℝ)^(3*(D+1).choose 2) := by
  have hconst := lagrangianConstant_pos D
  let u := finrank K ↥(L.val ⊓ M.val)
  let v := finrank K ↥(L.val ⊓ N.val)
  let w := finrank K ↥(M.val ⊓ N.val)
  let S := triplePairSum L.val M.val N.val
  let A := (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val)
  let B := (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val)
  let C := (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val)
  have hA : A ≤ L.val := sup_le inf_le_left inf_le_left
  have hB : B ≤ M.val := sup_le inf_le_right inf_le_left
  have hC : C ≤ N.val := sup_le inf_le_right inf_le_right
  have his (P : SymplecticLagrangian ω) (T : Submodule K E) (hT : T ≤ P.val) : T ≤ ω.orthogonal T := by
    intro x hx y hy
    exact P.property.ge (hT hx) y (hT hy)
  have hd := triple_pairs_disjoint L.val M.val N.val h0
  have hdimA : finrank K A = u+v := finrank_sup_of_disjoint _ _ (hd.1.mono_right le_sup_left)
  have hdimB : finrank K B = u+w := finrank_sup_of_disjoint _ _ (hd.1.mono_right le_sup_right)
  have hdimC : finrank K C = v+w := finrank_sup_of_disjoint _ _ hd.2
  have hdim : finrank K S = u+v+w := triplePairSum_finrank L.val M.val N.val h0
  have hs : S ≤ ω.orthogonal S := triplePairSum_isotropic ω _ _ _ L.property M.property N.property
  have haD : u+v+w ≤ D := hdim ▸ isotropic_finrank_le_half ω hω D hD S hs
  have hc := triple_isotropic_orbit_card_upper ω h2 ha hω D hD S
    (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) hs
    (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right) le_sup_right rfl hd.1 hd.2
  rw [hdim] at hc
  have hcont (P : SymplecticLagrangian ω) (T : Submodule K E) (hT : T ≤ P.val) :
      (Nat.card {Q : SymplecticLagrangian ω // T ≤ Q.val} : ℝ) ≤
        lagrangianConstant D * (Fintype.card K : ℝ)^((D-finrank K T+1).choose 2) :=
    ((containingLagrangian_card_bounds ω h2 ha hω D hD T (his P T hT)).2).trans
      (mul_le_mul_of_nonneg_right (lagrangianConstant_mono (Nat.sub_le _ _)) (by positivity))
  have h₁ := hcont L A hA
  have h₂ := hcont M B hB
  have h₃ := hcont N C hC
  rw [hdimA] at h₁
  rw [hdimB] at h₂
  rw [hdimC] at h₃
  obtain ⟨f,hf⟩ := commonZeroProfile_injection ω h2 ha hω L M N h0
  have hcard : (Nat.card (CommonZeroDimProfile ω L M N) : ℝ) ≤
      Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
        ((Nat.card {Q : SymplecticLagrangian ω // A ≤ Q.val} : ℝ) *
          (Nat.card {Q : SymplecticLagrangian ω // B ≤ Q.val} * Nat.card {Q : SymplecticLagrangian ω // C ≤ Q.val})) := by
    have hh := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod,Nat.card_prod,Nat.card_prod] at hh
    exact_mod_cast hh
  have hb : (Nat.card (CommonZeroDimProfile ω L M N) : ℝ) ≤
      profileMassConstant D * (Fintype.card K : ℝ)^(isotropicExponent D (u+v+w)+2*(u*v+u*w+v*w)+
        ((D-(u+v)+1).choose 2+(D-(u+w)+1).choose 2+(D-(v+w)+1).choose 2)) := by
    calc
      _ ≤ _ := hcard
      _ ≤ ((lagrangianConstant D*4^D)*(Fintype.card K : ℝ)^(isotropicExponent D (u+v+w)+2*(u*v+u*w+v*w))) *
        ((lagrangianConstant D*(Fintype.card K : ℝ)^((D-(u+v)+1).choose 2))*
          ((lagrangianConstant D*(Fintype.card K : ℝ)^((D-(u+w)+1).choose 2))*
            (lagrangianConstant D*(Fintype.card K : ℝ)^((D-(v+w)+1).choose 2)))) := by
          gcongr
      _ = _ := by unfold profileMassConstant; simp only [pow_add]; ring
  have hh := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (Fintype.card K : ℝ)^((u+1).choose 2+(v+1).choose 2+(w+1).choose 2) by positivity)
  rw [mul_assoc,←pow_add,pair_cost_cancellation D u v w haD] at hh
  simpa only [mul_comm] using hh
end CommonZeroMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ProfileQuotient
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev TripleDimProfile (c u v w : ℕ) :=
  {p : SymplecticLagrangian ω × SymplecticLagrangian ω × SymplecticLagrangian ω //
    finrank K ↥((p.1.val ⊓ p.2.1.val) ⊓ p.2.2.val) = c ∧
    finrank K ↥(p.1.val ⊓ p.2.1.val) = u ∧
    finrank K ↥(p.1.val ⊓ p.2.2.val) = v ∧
    finrank K ↥(p.2.1.val ⊓ p.2.2.val) = w}
noncomputable def tripleProfileCommon {c u v w : ℕ} (p : TripleDimProfile ω c u v w) : IsotropicDimspace ω c :=
  ⟨(p.val.1.val ⊓ p.val.2.1.val) ⊓ p.val.2.2.val,
    (by intro x hx y hy; exact p.val.1.property.ge hx.1.1 y hy.1.1),p.property.1⟩

 theorem reducePair_finrank (S : Submodule K E) (P Q : SymplecticLagrangian ω)
    (hSP : S ≤ P.val) (hSQ : S ≤ Q.val) :
    finrank K ↥(reduceSubspace ω S P.val ⊓ reduceSubspace ω S Q.val) =
      finrank K ↥(P.val ⊓ Q.val)-finrank K S := by
  rw [←reduceSubspace_inf ω S P.val Q.val hSP]
  have hh := reduceSubspace_finrank_containing ω S (P.val ⊓ Q.val) (le_inf hSP hSQ)
    (inf_le_left.trans (lagrangian_le_orthogonal ω S P.val P.property hSP))
  omega

 omit [FiniteDimensional K E] in
 theorem reduceLagrangian_injective (S : Submodule K E) :
    Function.Injective (fun P : {P : SymplecticLagrangian ω // S ≤ P.val} => reduceSubspace ω S P.val.val) := by
  intro P Q h
  apply Subtype.ext
  apply Subtype.ext
  have hh := congrArg (liftReduction ω S) h
  simpa only [lift_reduce ω S P.val.val P.property (lagrangian_le_orthogonal ω S P.val.val P.val.property P.property),
    lift_reduce ω S Q.val.val Q.property (lagrangian_le_orthogonal ω S Q.val.val Q.val.property Q.property)] using hh

 theorem fixedCommonProfile_injection (ha : ω.IsAlt) {c u v w : ℕ}
    (S : IsotropicDimspace ω c)
    (p₀ : {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S}) :
    ∃ L M N : SymplecticLagrangian (symplecticReductionForm ω S.val ha),
      (L.val ⊓ M.val) ⊓ N.val = ⊥ ∧
      finrank K ↥(L.val ⊓ M.val) = u-c ∧
      finrank K ↥(L.val ⊓ N.val) = v-c ∧
      finrank K ↥(M.val ⊓ N.val) = w-c ∧
      ∃ f : {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} →
        CommonZeroDimProfile (symplecticReductionForm ω S.val ha) L M N, Function.Injective f := by
  let F := {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S}
  have heq (p : F) : (p.val.val.1.val ⊓ p.val.val.2.1.val) ⊓ p.val.val.2.2.val = S.val :=
    congrArg Subtype.val p.property
  have hL (p : F) : S.val ≤ p.val.val.1.val := (heq p).symm ▸ inf_le_left.trans inf_le_left
  have hM (p : F) : S.val ≤ p.val.val.2.1.val := (heq p).symm ▸ inf_le_left.trans inf_le_right
  have hN (p : F) : S.val ≤ p.val.val.2.2.val := (heq p).symm ▸ inf_le_right
  let L (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.1 (hL p)
  let M (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.1 (hM p)
  let N (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.2 (hN p)
  have hzero (p : F) : ((L p).val ⊓ (M p).val) ⊓ (N p).val = ⊥ := by
    change (reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) ⊓
      reduceSubspace ω S.val p.val.val.2.2.val = ⊥
    rw [←reduceSubspace_inf ω S.val _ _ (hL p),←reduceSubspace_inf ω S.val _ _ (le_inf (hL p) (hM p)),heq p]
    exact reduceSubspace_self ω S.val
  have hu (p : F) : finrank K ↥((L p).val ⊓ (M p).val) = u-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hM p),p.val.property.2.1,S.property.2]
  have hv (p : F) : finrank K ↥((L p).val ⊓ (N p).val) = v-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hN p),p.val.property.2.2.1,S.property.2]
  have hw (p : F) : finrank K ↥((M p).val ⊓ (N p).val) = w-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.2.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hM p) (hN p),p.val.property.2.2.2,S.property.2]
  let f (p : F) : CommonZeroDimProfile (symplecticReductionForm ω S.val ha) (L p₀) (M p₀) (N p₀) :=
    ⟨(L p,M p,N p),hzero p,(hu p).trans (hu p₀).symm,(hv p).trans (hv p₀).symm,(hw p).trans (hw p₀).symm⟩
  refine ⟨L p₀,M p₀,N p₀,hzero p₀,hu p₀,hv p₀,hw p₀,f,?_⟩
  intro p q hpq
  have heL : (L p).val = (L q).val := congrArg (fun r => r.val.1.val) hpq
  have heM : (M p).val = (M q).val := congrArg (fun r => r.val.2.1.val) hpq
  have heN : (N p).val = (N q).val := congrArg (fun r => r.val.2.2.val) hpq
  have hpL : p.val.val.1 = q.val.val.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.1,hL p⟩) (a₂ := ⟨q.val.val.1,hL q⟩) heL)
  have hpM : p.val.val.2.1 = q.val.val.2.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.1,hM p⟩) (a₂ := ⟨q.val.val.2.1,hM q⟩) heM)
  have hpN : p.val.val.2.2 = q.val.val.2.2 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.2,hN p⟩) (a₂ := ⟨q.val.val.2.2,hN q⟩) heN)
  exact Subtype.ext (Subtype.ext (Prod.ext hpL (Prod.ext hpM hpN)))
end ProfileQuotient
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section AllProfileMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem fixedCommonProfile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c u v w : ℕ} (S : IsotropicDimspace ω c) :
    (Fintype.card K : ℝ)^((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2) *
      Nat.card {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} ≤
        profileMassConstant (D-c) * (Fintype.card K : ℝ)^(3*(D-c+1).choose 2) := by
  classical
  let F := {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S}
  by_cases hF : Nonempty F
  · obtain ⟨p₀⟩ := hF
    obtain ⟨L,M,N,hzero,hu,hv,hw,f,hf⟩ := fixedCommonProfile_injection ω ha S p₀
    let : Finite (ReducedSpace ω S.val) := Module.finite_of_finite K
    have hc : c ≤ D := S.property.2 ▸ isotropic_finrank_le_half ω hω D hD S.val S.property.1
    have hdim : 2*(D-c) = finrank K (ReducedSpace ω S.val) := by
      have hh := reducedSpace_finrank ω S.val hω S.property.1
      rw [S.property.2,←hD] at hh
      omega
    have hp := commonZeroProfile_card_upper (symplecticReductionForm ω S.val ha) h2
      (symplecticReductionForm_alt ω S.val ha) (symplecticReductionForm_nondegenerate ω S.val ha hω)
      (D-c) hdim L M N hzero
    rw [hu,hv,hw] at hp
    have hc : (Nat.card F : ℝ) ≤ Nat.card (CommonZeroDimProfile (symplecticReductionForm ω S.val ha) L M N) := by
      exact_mod_cast Nat.card_le_card_of_injective f hf
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans hp
  · have h_empty : IsEmpty F := not_nonempty_iff.mp hF
    have hc : Nat.card F = 0 := Nat.card_eq_zero.mpr (Or.inl h_empty)
    change _ * (Nat.card F : ℝ) ≤ _
    rw [hc,Nat.cast_zero,mul_zero]
    exact mul_nonneg (le_of_lt (profileMassConstant_pos _)) (by positivity)

noncomputable def fullProfileConstant (D : ℕ) : ℝ := lagrangianConstant D * 2^D * profileMassConstant D
 theorem fullProfileConstant_pos (D : ℕ) : 0 < fullProfileConstant D :=
  mul_pos (mul_pos (lagrangianConstant_pos _) (by positivity)) (profileMassConstant_pos _)

 theorem tripleProfile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c u v w : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^((D+1)*c + ((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)) *
      Nat.card (TripleDimProfile ω c u v w) ≤ fullProfileConstant D * (Fintype.card K : ℝ)^(3*(D+1).choose 2) := by
  classical
  let := Fintype.ofFinite (IsotropicDimspace ω c)
  let δ := (u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2
  let q : ℝ := Fintype.card K
  have hi := (isotropic_card_bounds ω h2 ha hω D hD c hc).2
  have hsum : (Nat.card (TripleDimProfile ω c u v w) : ℝ) =
      ∑ S : IsotropicDimspace ω c, (Nat.card {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} : ℝ) := by
    have hh := (Nat.card_congr (Equiv.sigmaFiberEquiv (tripleProfileCommon ω (c := c) (u := u) (v := v) (w := w)))).symm
    rw [Nat.card_sigma] at hh
    exact_mod_cast hh
  have hbase : q^δ * Nat.card (TripleDimProfile ω c u v w) ≤
      (Nat.card (IsotropicDimspace ω c) : ℝ) * (profileMassConstant (D-c)*q^(3*(D-c+1).choose 2)) := by
    rw [hsum,Finset.mul_sum]
    calc
      _ ≤ ∑ _S : IsotropicDimspace ω c, profileMassConstant (D-c)*q^(3*(D-c+1).choose 2) :=
        Finset.sum_le_sum (fun S _ => fixedCommonProfile_card_upper ω h2 ha hω D hD S)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hk : (lagrangianConstant D*2^c)*profileMassConstant (D-c) ≤ fullProfileConstant D := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hc) (le_of_lt (lagrangianConstant_pos _)))
      (profileMassConstant_mono (Nat.sub_le D c)) (le_of_lt (profileMassConstant_pos _))
      (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (by positivity))
  have hconst := fullProfileConstant_pos D
  calc
    _ = q^((D+1)*c) * (q^δ * Nat.card (TripleDimProfile ω c u v w)) := by rw [pow_add,mul_assoc]
    _ ≤ q^((D+1)*c) * ((Nat.card (IsotropicDimspace ω c) : ℝ)*(profileMassConstant (D-c)*q^(3*(D-c+1).choose 2))) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ q^((D+1)*c) * (((lagrangianConstant D*2^c)*q^isotropicExponent D c)*(profileMassConstant (D-c)*q^(3*(D-c+1).choose 2))) := by
      gcongr
      exact mul_nonneg (le_of_lt (profileMassConstant_pos _)) (by positivity)
    _ = ((lagrangianConstant D*2^c)*profileMassConstant (D-c))*q^(isotropicExponent D c+3*(D-c+1).choose 2+(D+1)*c) := by
      simp only [pow_add]; ring
    _ = ((lagrangianConstant D*2^c)*profileMassConstant (D-c))*q^(3*(D+1).choose 2) := by
      rw [common_cost_cancellation D c hc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hk (by positivity)
end AllProfileMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GeneralPairCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem symplectic_pair_count (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (A : SymplecticLagrangian ω) (h : ℕ) (hh : h ≤ finrank K A.val) :
    Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} =
      Nat.card (DimSubspace K A.val (finrank K A.val-h)) * (Fintype.card K)^((finrank K A.val-h+1).choose 2) := by
  classical
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω A.val h2 ha hω A.property
  let f := symplecticLagrangianEquiv canonicalSymplectic ω e he
  let A₀ := f.symm A
  have hm : A₀.val.map e.toLinearMap = A.val := congrArg Subtype.val (f.apply_symm_apply A)
  have hd (L : Lagrangian (K := K) (V := A.val)) :
      finrank K ↥((f L).val ⊓ A.val) = finrank K ↥(L.val ⊓ A₀.val) := by
    change finrank K ↥(L.val.map e.toLinearMap ⊓ A.val) = _
    calc
      _ = finrank K ↥(L.val.map e.toLinearMap ⊓ A₀.val.map e.toLinearMap) :=
        congrArg (fun S : Submodule K E => finrank K ↥(L.val.map e.toLinearMap ⊓ S)) hm.symm
      _ = _ := by rw [←Submodule.map_inf e.toLinearMap e.injective]; exact e.finrank_map_eq _
  have hc : Nat.card {L : Lagrangian (K := K) (V := A.val) // finrank K ↥(L.val ⊓ A₀.val) = h} =
      Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} :=
    Nat.card_congr (f.subtypeEquiv (fun L => by rw [hd]))
  rw [←hc]
  exact lagrangian_pair_count h2 A₀ h hh

 theorem symplectic_pair_card_bounds (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (A : SymplecticLagrangian ω) (h : ℕ) (hh : h ≤ D) :
    (Fintype.card K : ℝ)^((D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) *
      Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} ∧
    (Fintype.card K : ℝ)^((h+1).choose 2) *
      Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} ≤
        2^D*(Fintype.card K : ℝ)^((D+1).choose 2) := by
  have hd : finrank K A.val = D := by
    have h := self_orthogonal_twice_finrank ω A.val hω A.property
    omega
  have hhA : h ≤ finrank K A.val := by omega
  have hcount := symplectic_pair_count ω h2 ha hω A h hhA
  rw [hd] at hcount
  rw [hcount,Nat.cast_mul,Nat.cast_pow]
  have hl := subspace_count_lower (K := K) (V := A.val) (D-h) (by omega)
  have hu := subspace_count_upper (K := K) (V := A.val) (D-h) (by omega)
  rw [hd,Nat.sub_sub_self hh] at hl hu
  have he : (Fintype.card K : ℝ)^((h+1).choose 2) *
      ((Fintype.card K : ℝ)^((D-h)*h)*(Fintype.card K : ℝ)^((D-h+1).choose 2)) =
      (Fintype.card K : ℝ)^((D+1).choose 2) := by
    rw [←pow_add,←pow_add]
    congr 1
    have hexp := symmetric_nullity_exponent D h hh
    rw [Nat.mul_comm h (D-h)] at hexp
    omega
  constructor
  · rw [←he]
    gcongr
  · calc
      _ ≤ (Fintype.card K : ℝ)^((h+1).choose 2) *
        ((2^(D-h)*(Fintype.card K : ℝ)^((D-h)*h))*(Fintype.card K : ℝ)^((D-h+1).choose 2)) := by gcongr
      _ = 2^(D-h)*(Fintype.card K : ℝ)^((D+1).choose 2) := by rw [←he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le D h)) (by positivity)

abbrev OrderedPairDim (h : ℕ) := {p : SymplecticLagrangian ω × SymplecticLagrangian ω //
  finrank K ↥(p.1.val ⊓ p.2.val) = h}
noncomputable def orderedPairDimEquiv (h : ℕ) : OrderedPairDim ω h ≃
    Σ A : SymplecticLagrangian ω, {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} where
  toFun p := ⟨p.val.1,⟨p.val.2,by rw [inf_comm]; exact p.property⟩⟩
  invFun p := ⟨(p.1,p.2.val),by rw [inf_comm]; exact p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

 theorem orderedPairDim_card_lower (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (h : ℕ) (hh : h ≤ D) :
    (Fintype.card K : ℝ)^(2*(D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) * Nat.card (OrderedPairDim ω h) := by
  classical
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  have hc : (Nat.card (OrderedPairDim ω h) : ℝ) =
      ∑ A : SymplecticLagrangian ω, (Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} : ℝ) := by
    rw [Nat.card_congr (orderedPairDimEquiv ω h),Nat.card_sigma,Nat.cast_sum]
  rw [hc,Finset.mul_sum]
  have he : 2*(D+1).choose 2 = (D+1).choose 2+(D+1).choose 2 := by omega
  rw [he,pow_add]
  calc
    _ ≤ (Nat.card (SymplecticLagrangian ω) : ℝ)*(Fintype.card K : ℝ)^((D+1).choose 2) :=
      mul_le_mul_of_nonneg_right (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1 (by positivity)
    _ = ∑ _A : SymplecticLagrangian ω, (Fintype.card K : ℝ)^((D+1).choose 2) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ _ := Finset.sum_le_sum (fun A _ => (symplectic_pair_card_bounds ω h2 ha hω D hD A h hh).1)
end GeneralPairCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConditionalProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev PairCompletion (L M : SymplecticLagrangian ω) (c v w : ℕ) :=
  {N : SymplecticLagrangian ω // finrank K ↥((L.val ⊓ M.val) ⊓ N.val) = c ∧
    finrank K ↥(L.val ⊓ N.val) = v ∧ finrank K ↥(M.val ⊓ N.val) = w}

 omit [FiniteDimensional K E] in
 theorem pairCompletion_card_congr (L M L' M' : SymplecticLagrangian ω)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y)
    (hL : L.val.map e.toLinearMap = L'.val) (hM : M.val.map e.toLinearMap = M'.val) (c v w : ℕ) :
    Nat.card (PairCompletion ω L M c v w) = Nat.card (PairCompletion ω L' M' c v w) := by
  let f := lagrangianIsometryEquiv ω e he
  have hp (A B : Submodule K E) : finrank K ↥(A.map e.toLinearMap ⊓ B.map e.toLinearMap) = finrank K ↥(A ⊓ B) := by
    rw [←Submodule.map_inf e.toLinearMap e.injective]
    exact e.finrank_map_eq _
  have hc (P : SymplecticLagrangian ω) : finrank K ↥((L'.val ⊓ M'.val) ⊓ (f P).val) =
      finrank K ↥((L.val ⊓ M.val) ⊓ P.val) := by
    change finrank K ↥((L'.val ⊓ M'.val) ⊓ P.val.map e.toLinearMap) = _
    rw [←hL,←hM,←Submodule.map_inf e.toLinearMap e.injective,hp]
  have hv (P : SymplecticLagrangian ω) : finrank K ↥(L'.val ⊓ (f P).val) = finrank K ↥(L.val ⊓ P.val) := by
    change finrank K ↥(L'.val ⊓ P.val.map e.toLinearMap) = _
    rw [←hL,hp]
  have hw (P : SymplecticLagrangian ω) : finrank K ↥(M'.val ⊓ (f P).val) = finrank K ↥(M.val ⊓ P.val) := by
    change finrank K ↥(M'.val ⊓ P.val.map e.toLinearMap) = _
    rw [←hM,hp]
  exact Nat.card_congr (f.subtypeEquiv (fun P => by rw [hc,hv,hw]))

noncomputable def profilePairCompletionEquiv (c u v w : ℕ) : TripleDimProfile ω c u v w ≃
    Σ p : OrderedPairDim ω u, PairCompletion ω p.val.1 p.val.2 c v w where
  toFun p := ⟨⟨(p.val.1,p.val.2.1),p.property.2.1⟩,⟨p.val.2.2,p.property.1,p.property.2.2⟩⟩
  invFun p := ⟨(p.1.val.1,p.1.val.2,p.2.val),p.2.property.1,p.1.property,p.2.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Finite E]
 theorem tripleProfile_completion_card (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M : SymplecticLagrangian ω) (c v w : ℕ) :
    Nat.card (TripleDimProfile ω c (finrank K ↥(L.val ⊓ M.val)) v w) =
      Nat.card (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (PairCompletion ω L M c v w) := by
  classical
  let := Fintype.ofFinite (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val)))
  rw [Nat.card_congr (profilePairCompletionEquiv ω c (finrank K ↥(L.val ⊓ M.val)) v w),Nat.card_sigma]
  have hc (p : OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) :
      Nat.card (PairCompletion ω p.val.1 p.val.2 c v w) = Nat.card (PairCompletion ω L M c v w) := by
    obtain ⟨e,he,hL,hM⟩ := ordered_pair_transitivity ω h2 ha hω
      p.val.1.val p.val.2.val L.val M.val p.val.1.property p.val.2.property L.property M.property p.property
    exact pairCompletion_card_congr ω p.val.1 p.val.2 L M e he hL hM c v w
  simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  simp only [Nat.cast_id]

variable [Fintype K]
 theorem conditionalProfile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (L M : SymplecticLagrangian ω) (c v w : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^((D+1)*c + ((finrank K ↥(L.val ⊓ M.val)-c+1).choose 2+
      (v-c+1).choose 2+(w-c+1).choose 2)) * Nat.card (PairCompletion ω L M c v w) ≤
        fullProfileConstant D * (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2+(D+1).choose 2) := by
  let u := finrank K ↥(L.val ⊓ M.val)
  let δ := (D+1)*c + ((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hu : u ≤ D := by
    have h := self_orthogonal_twice_finrank ω L.val hω L.property
    have hle := Submodule.finrank_mono (show L.val ⊓ M.val ≤ L.val from inf_le_left)
    dsimp [u]
    omega
  have hp := orderedPairDim_card_lower ω h2 ha hω D hD u hu
  have ht := tripleProfile_card_upper ω h2 ha hω D hD c u v w hc
  have hi : (Nat.card (TripleDimProfile ω c u v w) : ℝ) =
      (Nat.card (OrderedPairDim ω u) : ℝ)*Nat.card (PairCompletion ω L M c v w) := by
    exact_mod_cast tripleProfile_completion_card ω h2 ha hω L M c v w
  apply (mul_le_mul_iff_right₀ (pow_pos hq (2*(D+1).choose 2))).mp
  calc
    _ = q^δ*(q^(2*(D+1).choose 2)*Nat.card (PairCompletion ω L M c v w)) := by ring
    _ ≤ q^δ*((q^((u+1).choose 2)*Nat.card (OrderedPairDim ω u))*Nat.card (PairCompletion ω L M c v w)) := by gcongr
    _ = q^((u+1).choose 2)*(q^δ*Nat.card (TripleDimProfile ω c u v w)) := by rw [hi]; ring
    _ ≤ q^((u+1).choose 2)*(fullProfileConstant D*q^(3*(D+1).choose 2)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = q^(2*(D+1).choose 2)*(fullProfileConstant D*q^((u+1).choose 2+(D+1).choose 2)) := by
      have he : 3*(D+1).choose 2 = 2*(D+1).choose 2+(D+1).choose 2 := by omega
      rw [he,pow_add,pow_add]
      ring
end ConditionalProfile
end SidorenkoCounterexample

end OAI
