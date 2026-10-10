import OAI.Combinatorics.Sidorenko.SubspaceCounts

namespace OAI

namespace SidorenkoCounterexample
open Module
section PairSpaceFacts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

 theorem triple_pairs_disjoint (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    Disjoint (L ⊓ M) ((L ⊓ N) ⊔ (M ⊓ N)) ∧ Disjoint (L ⊓ N) (M ⊓ N) := by
  constructor
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    exact h0.le ⟨hx.1,(show (L ⊓ N) ⊔ (M ⊓ N) ≤ N from sup_le inf_le_right inf_le_right) hx.2⟩
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    exact h0.le ⟨⟨hx.1.1,hx.2.1⟩,hx.1.2⟩

 theorem triple_own_avoidance (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    L ⊓ triplePairSum L M N = (L ⊓ M) ⊔ (L ⊓ N) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u,hu,v,hv,hxuv⟩ := Submodule.mem_sup.mp hx.2
    have huL : u ∈ L := (show (L ⊓ M) ⊔ (L ⊓ N) ≤ L from sup_le inf_le_left inf_le_left) hu
    have hvL : v ∈ L := by
      have hh := L.sub_mem hx.1 huL
      rw [←hxuv,add_sub_cancel_left] at hh
      exact hh
    have hz : v = 0 := by simpa only [Submodule.mem_bot] using h0.le ⟨⟨hvL,hv.1⟩,hv.2⟩
    have hxu : u = x := by simpa only [hz,add_zero] using hxuv
    exact hxu ▸ hu
  · exact le_inf (sup_le inf_le_left inf_le_left) le_sup_left

 theorem reduction_intersection_of_split_kernel (ω : LinearMap.BilinForm K E)
    (S L M : Submodule K E) (hS : S ≤ ω.orthogonal S) (hsplit : (L ⊓ S) ⊔ (M ⊓ S) = S) :
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = reduceSubspace ω S (L ⊓ M) := by
  apply le_antisymm
  · rintro x ⟨⟨l,hl,hlx⟩,⟨m,hm,hmx⟩⟩
    have heq : (reductionKernel ω S).mkQ (l-m) = 0 := by rw [map_sub,hlx,hmx,sub_self]
    have hdiff : l.val-m.val ∈ (L ⊓ S) ⊔ (M ⊓ S) := by
      rw [hsplit]
      exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp heq
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hdiff
    have hla : l.val-a = m.val+b := by
      calc
        _ = (l.val-m.val)-a+m.val := by abel
        _ = (a+b)-a+m.val := by rw [hab]
        _ = _ := by abel
    have haP : a ∈ ω.orthogonal S := hS ha.2
    exact ⟨⟨l.val-a,(ω.orthogonal S).sub_mem l.property haP⟩,
      ⟨L.sub_mem hl ha.1,by change l.val-a ∈ M; rw [hla]; exact M.add_mem hm hb.1⟩,by
        change (reductionKernel ω S).mkQ (l-⟨a,haP⟩) = x
        have hz : (reductionKernel ω S).mkQ ⟨a,haP⟩ = 0 :=
          (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr ha.2
        rw [map_sub,hz,sub_zero,hlx]⟩
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy.1,rfl⟩,⟨y,hy.2,rfl⟩⟩
end PairSpaceFacts
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section GenericTransverseMass
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

noncomputable def orderedTransversePairEquiv
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ x y, η (e x) (e y) = ω x y) :
    OrderedTransversePair ω ≃ OrderedTransversePair η := by
  let c := symplecticLagrangianEquiv ω η e he
  refine (c.prodCongr c).subtypeEquiv ?_
  intro p
  change p.1.val ⊓ p.2.val = ⊥ ↔
    p.1.val.map e.toLinearMap ⊓ p.2.val.map e.toLinearMap = ⊥
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_bot e.toLinearMap]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff.symm

variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)

 theorem symplectic_orderedTransversePair_card (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E) :
    Nat.card (OrderedTransversePair ω) = Nat.card (SymplecticLagrangian ω) *
      Fintype.card K^((D+1).choose 2) := by
  obtain ⟨L,_,hL⟩ := exists_containing_lagrangian ω ha ⊥ bot_le
  have hd : finrank K L = D := by
    have h := self_orthogonal_twice_finrank ω L hω hL
    omega
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  have hc := Nat.card_congr (symplecticLagrangianEquiv canonicalSymplectic ω e he)
  have hp := Nat.card_congr (orderedTransversePairEquiv canonicalSymplectic ω e he)
  rw [←hp,orderedTransversePair_card h2,hc,hd]

 theorem symplectic_transverseTriple_card_lower [Invertible (2 : K)]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω)
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    Nat.card (SymplecticLagrangian ω) * (Fintype.card K^((D+1).choose 2))^2 ≤
      4^D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  have hd : finrank K L.val = D := by
    have h := self_orthogonal_twice_finrank ω L.val hω L.property
    omega
  have hcard := fixedPairOrbit_card_lower ω L.val M.val N.val ha hω
    L.property M.property N.property hLM hLN hMN
  rw [hd] at hcard
  obtain ⟨f,hf⟩ := orderedTripleOrbit_pair_injection ω ha hω L.val M.val N.val
    L.property M.property hLM
  have hi := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,symplectic_orderedTransversePair_card ω
    (isUnit_of_invertible (2 : K)).ne_zero ha hω D hD] at hi
  calc
    _ = (Nat.card (SymplecticLagrangian ω) * Fintype.card K^((D+1).choose 2)) *
        Fintype.card K^((D+1).choose 2) := by rw [pow_two]; ac_rfl
    _ ≤ (Nat.card (SymplecticLagrangian ω) * Fintype.card K^((D+1).choose 2)) *
        (4^D * Nat.card (FixedPairOrbit ω L.val M.val N.val)) := Nat.mul_le_mul_left _ hcard
    _ = 4^D * (Nat.card (SymplecticLagrangian ω) * Fintype.card K^((D+1).choose 2) *
        Nat.card (FixedPairOrbit ω L.val M.val N.val)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hi

 theorem symplectic_transverseTriple_probability_lower [Invertible (2 : K)]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω)
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    (Nat.card (SymplecticLagrangian ω) : ℝ)^3 ≤
      (4^D * lagrangianConstant D^2) * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  have hb := (symplecticLagrangian_card_bounds ω (isUnit_of_invertible (2 : K)).ne_zero ha hω D hD).2
  have ho : (Nat.card (SymplecticLagrangian ω) : ℝ) *
      ((Fintype.card K : ℝ)^((D+1).choose 2))^2 ≤
      4^D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    exact_mod_cast symplectic_transverseTriple_card_lower ω ha hω D hD L M N hLM hLN hMN
  calc
    _ = (Nat.card (SymplecticLagrangian ω) : ℝ) * (Nat.card (SymplecticLagrangian ω) : ℝ)^2 := by ring
    _ ≤ (Nat.card (SymplecticLagrangian ω) : ℝ) *
      (lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2))^2 := by gcongr
    _ = lagrangianConstant D^2 * ((Nat.card (SymplecticLagrangian ω) : ℝ) *
      ((Fintype.card K : ℝ)^((D+1).choose 2))^2) := by ring
    _ ≤ lagrangianConstant D^2 * (4^D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val)) :=
      mul_le_mul_of_nonneg_left ho (sq_nonneg _)
    _ = _ := by ring
end GenericTransverseMass
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section ResidualTransversality
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)

 theorem reduceSubspace_eq_bot_of_le (S L : Submodule K E) (hLS : L ≤ S) :
    reduceSubspace ω S L = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  rintro x ⟨y,hy,rfl⟩
  exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr (hLS hy)

 theorem triplePairSum_split (L M N : Submodule K E) :
    (L ⊓ triplePairSum L M N) ⊔ (M ⊓ triplePairSum L M N) = triplePairSum L M N := by
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  unfold triplePairSum
  apply sup_le (sup_le _ _) _
  · exact (le_inf inf_le_left (le_sup_left.trans le_sup_left)).trans le_sup_left
  · exact (le_inf inf_le_left (le_sup_right.trans le_sup_left)).trans le_sup_left
  · exact (le_inf inf_le_left le_sup_right).trans le_sup_right

 theorem triplePairSum_reduce_pair (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N) :
    reduceSubspace ω (triplePairSum L M N) L ⊓
      reduceSubspace ω (triplePairSum L M N) M = ⊥ := by
  rw [reduction_intersection_of_split_kernel ω _ L M
    (triplePairSum_isotropic ω L M N hL hM hN) (triplePairSum_split L M N)]
  exact reduceSubspace_eq_bot_of_le ω _ _ (le_sup_left.trans le_sup_left)

 theorem triplePairSum_reductions_transverse (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N) :
    let S := triplePairSum L M N
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥ ∧
    reduceSubspace ω S L ⊓ reduceSubspace ω S N = ⊥ ∧
    reduceSubspace ω S M ⊓ reduceSubspace ω S N = ⊥ := by
  dsimp only
  refine ⟨triplePairSum_reduce_pair ω L M N hL hM hN,?_,?_⟩
  · have hs : triplePairSum L N M = triplePairSum L M N := by
      unfold triplePairSum
      rw [inf_comm N M,sup_comm (L ⊓ N) (L ⊓ M)]
    have h := triplePairSum_reduce_pair ω L N M hL hN hM
    rw [hs] at h
    exact h
  · have hs : triplePairSum M N L = triplePairSum L M N := by
      unfold triplePairSum
      rw [inf_comm M L,inf_comm N L]
      ac_rfl
    have h := triplePairSum_reduce_pair ω M N L hM hN hL
    rw [hs] at h
    exact h
end ResidualTransversality

section LagrangianTripleOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)

abbrev LagTripleOrbit := {p : SymplecticLagrangian ω × SymplecticLagrangian ω × SymplecticLagrangian ω //
  TripleIsometry ω ω L.val M.val N.val p.1.val p.2.1.val p.2.2.val}

 theorem orderedTripleOrbit_lagrangians (p : OrderedTripleOrbit ω L.val M.val N.val) :
    ω.orthogonal p.val.1 = p.val.1 ∧ ω.orthogonal p.val.2.1 = p.val.2.1 ∧
      ω.orthogonal p.val.2.2 = p.val.2.2 := by
  obtain ⟨e,he,hL,hM,hN⟩ := p.property
  rw [←hL,←hM,←hN,orthogonal_map_of_isometry ω e he,orthogonal_map_of_isometry ω e he,
    orthogonal_map_of_isometry ω e he,L.property,M.property,N.property]
  exact ⟨rfl,rfl,rfl⟩

noncomputable def lagTripleOrbitEquiv : LagTripleOrbit ω L M N ≃ OrderedTripleOrbit ω L.val M.val N.val where
  toFun p := ⟨(p.val.1.val,p.val.2.1.val,p.val.2.2.val),p.property⟩
  invFun p := ⟨(⟨p.val.1,(orderedTripleOrbit_lagrangians ω L M N p).1⟩,
    ⟨p.val.2.1,(orderedTripleOrbit_lagrangians ω L M N p).2.1⟩,
    ⟨p.val.2.2,(orderedTripleOrbit_lagrangians ω L M N p).2.2⟩),p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
end LagrangianTripleOrbit

section AvoidanceTripleCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)

noncomputable def avoidanceTripleReduction (A B C : Submodule K E) :
    (AvoidanceSpace ω S A × AvoidanceSpace ω S B × AvoidanceSpace ω S C) →
      SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha) := fun p =>
  (avoidanceReduction ω S ha hω hS A p.1,
    avoidanceReduction ω S ha hω hS B p.2.1,avoidanceReduction ω S ha hω hS C p.2.2)

 theorem avoidanceTripleReduction_uniform (h2 : (2 : K) ≠ 0)
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (p : SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha)) :
    Nat.card {x // avoidanceTripleReduction ω S ha hω hS A B C x = p} *
      Nat.card (SymplecticLagrangian (symplecticReductionForm ω S ha) ×
        SymplecticLagrangian (symplecticReductionForm ω S ha) ×
        SymplecticLagrangian (symplecticReductionForm ω S ha)) =
      Nat.card (AvoidanceSpace ω S A × AvoidanceSpace ω S B × AvoidanceSpace ω S C) := by
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  exact uniform_prod_card _ _ (avoidanceReduction_uniform ω S h2 ha hω hS A hA)
    (uniform_prod_card _ _ (avoidanceReduction_uniform ω S h2 ha hω hS B hB)
      (avoidanceReduction_uniform ω S h2 ha hω hS C hC)) p

abbrev AvoidanceOrbitFiber (A B C : Submodule K E)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha)) :=
  {p : AvoidanceSpace ω S A × AvoidanceSpace ω S B × AvoidanceSpace ω S C //
    TripleIsometry (symplecticReductionForm ω S ha) (symplecticReductionForm ω S ha)
      L.val M.val N.val (reduceSubspace ω S p.1.val)
        (reduceSubspace ω S p.2.1.val) (reduceSubspace ω S p.2.2.val)}

include hω hS in
 theorem avoidanceOrbitFiber_card_identity (h2 : (2 : K) ≠ 0)
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha)) :
    Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) *
      Nat.card (SymplecticLagrangian (symplecticReductionForm ω S ha))^3 =
      Nat.card (OrderedTripleOrbit (symplecticReductionForm ω S ha) L.val M.val N.val) *
        (Nat.card (AvoidanceSpace ω S A) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) := by
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  have h := uniform_preimage_card (avoidanceTripleReduction ω S ha hω hS A B C)
    (avoidanceTripleReduction_uniform ω S ha hω hS h2 A B C hA hB hC)
    (fun p => TripleIsometry (symplecticReductionForm ω S ha) (symplecticReductionForm ω S ha)
      L.val M.val N.val p.1.val p.2.1.val p.2.2.val)
  change Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) * _ =
    Nat.card (LagTripleOrbit _ L M N) * _ at h
  rw [Nat.card_congr (lagTripleOrbitEquiv _ L M N)] at h
  simp only [Nat.card_prod] at h
  convert h using 1; ring
end AvoidanceTripleCount
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section AvoidanceTripleBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2 : K)]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)

 theorem avoidanceOrbitFiber_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (z : ℕ) (hz : 2*z = finrank K (ReducedSpace ω S))
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha))
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    (Nat.card (AvoidanceSpace ω S A) : ℝ) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C)) ≤
      (4^z * lagrangianConstant z^2) * Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) := by
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  let Ω := symplecticReductionForm ω S ha
  have hΩ := symplecticReductionForm_alt ω S ha
  have hp := symplecticLagrangian_card_pos Ω hΩ
  have hb := symplectic_transverseTriple_probability_lower Ω hΩ
    (symplecticReductionForm_nondegenerate ω S ha hω) z hz L M N hLM hLN hMN
  have hi : (Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) : ℝ) *
      (Nat.card (SymplecticLagrangian Ω) : ℝ)^3 =
      (Nat.card (OrderedTripleOrbit Ω L.val M.val N.val) : ℝ) *
        (Nat.card (AvoidanceSpace ω S A) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) := by
    exact_mod_cast avoidanceOrbitFiber_card_identity ω S ha hω hS
      (isUnit_of_invertible (2 : K)).ne_zero A B C hA hB hC L M N
  have hpos : 0 < (Nat.card (SymplecticLagrangian Ω) : ℝ)^3 := by exact pow_pos (by exact_mod_cast hp) _
  apply (mul_le_mul_iff_left₀ hpos).mp
  calc
    _ ≤ ((Nat.card (AvoidanceSpace ω S A) : ℝ) *
      (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) *
      ((4^z * lagrangianConstant z^2) * Nat.card (OrderedTripleOrbit Ω L.val M.val N.val)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (4^z * lagrangianConstant z^2) *
      ((Nat.card (OrderedTripleOrbit Ω L.val M.val N.val) : ℝ) *
        (Nat.card (AvoidanceSpace ω S A) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C)))) := by ring
    _ = _ := by rw [←hi]; ring

 theorem containmentOrbitFiber_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4 * lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha))
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) *
      (Nat.card {L : SymplecticLagrangian ω // B ≤ L.val} *
        Nat.card {L : SymplecticLagrangian ω // C ≤ L.val}) ≤
      (8 * (4^D * lagrangianConstant D^2)) * Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) := by
  have h2 := (isUnit_of_invertible (2 : K)).ne_zero
  have h₁ : (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S A) := by
    exact_mod_cast avoidance_card_lower ω h2 ha hω D hD A S hA hS hq
  have h₂ : (Nat.card {L : SymplecticLagrangian ω // B ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S B) := by
    exact_mod_cast avoidance_card_lower ω h2 ha hω D hD B S hB hS hq
  have h₃ : (Nat.card {L : SymplecticLagrangian ω // C ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S C) := by
    exact_mod_cast avoidance_card_lower ω h2 ha hω D hD C S hC hS hq
  have hr := reducedSpace_finrank ω S hω hS
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  have hb := avoidanceOrbitFiber_card_lower ω S ha hω hS (D-finrank K S) (by omega)
    A B C hA hB hC L M N hLM hLN hMN
  have hk : (4:ℝ)^(D-finrank K S) * lagrangianConstant (D-finrank K S)^2 ≤
      4^D * lagrangianConstant D^2 := by
    gcongr
    · norm_num
    · exact Nat.sub_le D _
    · exact le_of_lt (lagrangianConstant_pos _)
    · exact lagrangianConstant_mono (Nat.sub_le D _)
  calc
    _ ≤ ((2:ℝ)*Nat.card (AvoidanceSpace ω S A)) *
      ((2*Nat.card (AvoidanceSpace ω S B)) * (2*Nat.card (AvoidanceSpace ω S C))) := by gcongr
    _ = 8 * ((Nat.card (AvoidanceSpace ω S A) : ℝ) *
      (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) := by ring
    _ ≤ 8 * (((4:ℝ)^(D-finrank K S) * lagrangianConstant (D-finrank K S)^2) *
      Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 8 * ((4^D * lagrangianConstant D^2) *
      Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk (by positivity)) (by norm_num)
    _ = _ := by ring
end AvoidanceTripleBound
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section IsotropicExtension
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)

/-- A prescribed linear isomorphism of isotropic spaces extends to an actual
symplectic automorphism, not only to a dimension-preserving correspondence. -/
 theorem exists_isotropic_isometry_extension (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (S T : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (hT : T ≤ ω.orthogonal T) (g : S ≃ₗ[K] T) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      ∀ x : S, e x.val = (g x).val := by
  obtain ⟨L,hSL,hL⟩ := exists_containing_lagrangian ω ha S hS
  obtain ⟨M,hTM,hM⟩ := exists_containing_lagrangian ω ha T hT
  obtain ⟨eL,hEL,hωL⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  obtain ⟨eM,hEM,hωM⟩ := exists_lagrangian_coordinates ω M h2 ha hω hM
  have hdim : finrank K L = finrank K M := by
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω M hω hM
    omega
  let U := S.comap L.subtype
  let W := T.comap M.subtype
  let g₀ : U ≃ₗ[K] W := (Submodule.comapSubtypeEquivOfLe hSL).trans
    (g.trans (Submodule.comapSubtypeEquivOfLe hTM).symm)
  obtain ⟨f,hf⟩ := exists_linearEquiv_extension U W hdim g₀
  let c : (L × Module.Dual K L) ≃ₗ[K] (M × Module.Dual K M) := f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      canonicalSymplectic (c x) (c y) = canonicalSymplectic x y := by
    simp [c,canonicalSymplectic_apply]
  let e := eL.symm.trans (c.trans eM)
  have he (l : L) : e l.val = (f l).val := by
    change eM (c (eL.symm l.val)) = (f l).val
    rw [←hEL l,eL.symm_apply_apply]
    simpa [c] using hEM (f l)
  refine ⟨e,?_,?_⟩
  · intro x y
    change ω (eM (c (eL.symm x))) (eM (c (eL.symm y))) = ω x y
    rw [hωM,hc,←hωL,eL.apply_symm_apply,eL.apply_symm_apply]
  · intro x
    let u : U := ⟨⟨x.val,hSL x.property⟩,x.property⟩
    change e u.val.val = (g x).val
    rw [he,hf u]
    rfl
end IsotropicExtension
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section FixedPairs
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)

abbrev FixedPairTripleOrbit := {p : LagTripleOrbit ω L M N //
  p.val.1.val ⊓ p.val.2.1.val = L.val ⊓ M.val ∧
  p.val.1.val ⊓ p.val.2.2.val = L.val ⊓ N.val ∧
  p.val.2.1.val ⊓ p.val.2.2.val = M.val ⊓ N.val}

 theorem triplePair_inter_own (P Q R : Submodule K E) :
    (P ⊓ triplePairSum P Q R) ⊓ (Q ⊓ triplePairSum P Q R) = P ⊓ Q := by
  apply le_antisymm (inf_le_inf inf_le_left inf_le_left)
  intro x hx
  have hs : x ∈ triplePairSum P Q R :=
    (show P ⊓ Q ≤ triplePairSum P Q R from le_sup_left.trans le_sup_left) hx
  exact ⟨⟨hx.1,hs⟩,⟨hx.2,hs⟩⟩

 theorem triplePairSum_split_all (P Q R : Submodule K E) :
    let S := triplePairSum P Q R
    ((P ⊓ S) ⊔ (Q ⊓ S) = S) ∧ ((P ⊓ S) ⊔ (R ⊓ S) = S) ∧
      ((Q ⊓ S) ⊔ (R ⊓ S) = S) := by
  dsimp only
  have h₁ : triplePairSum P R Q = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  have h₂ : triplePairSum Q R P = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  exact ⟨triplePairSum_split P Q R,by simpa only [h₁] using triplePairSum_split P R Q,
    by simpa only [h₂] using triplePairSum_split Q R P⟩

 theorem triplePair_inter_all (P Q R : Submodule K E) :
    let S := triplePairSum P Q R
    ((P ⊓ S) ⊓ (Q ⊓ S) = P ⊓ Q) ∧ ((P ⊓ S) ⊓ (R ⊓ S) = P ⊓ R) ∧
      ((Q ⊓ S) ⊓ (R ⊓ S) = Q ⊓ R) := by
  dsimp only
  have h₁ : triplePairSum P R Q = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  have h₂ : triplePairSum Q R P = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  exact ⟨triplePair_inter_own P Q R,by simpa only [h₁] using triplePair_inter_own P R Q,
    by simpa only [h₂] using triplePair_inter_own Q R P⟩

variable [FiniteDimensional K E]
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate)

noncomputable def tripleResidualLagrangian (P : SymplecticLagrangian ω) :
    SymplecticLagrangian (symplecticReductionForm ω (triplePairSum L.val M.val N.val) ha) :=
  ⟨reduceSubspace ω (triplePairSum L.val M.val N.val) P.val,
    general_lagrangian_reduction ω _ ha hω
      (triplePairSum_isotropic ω _ _ _ L.property M.property N.property) P.val P.property⟩

abbrev OwnAvoidanceOrbitFiber :=
  AvoidanceOrbitFiber ω (triplePairSum L.val M.val N.val) ha
    (L.val ⊓ triplePairSum L.val M.val N.val)
    (M.val ⊓ triplePairSum L.val M.val N.val)
    (N.val ⊓ triplePairSum L.val M.val N.val)
    (tripleResidualLagrangian ω L M N ha hω L)
    (tripleResidualLagrangian ω L M N ha hω M)
    (tripleResidualLagrangian ω L M N ha hω N)

 theorem ownAvoidanceOrbitFiber_pairs (p : OwnAvoidanceOrbitFiber ω L M N ha hω) :
    p.val.1.val ⊓ p.val.2.1.val = L.val ⊓ M.val ∧
    p.val.1.val ⊓ p.val.2.2.val = L.val ⊓ N.val ∧
    p.val.2.1.val ⊓ p.val.2.2.val = M.val ⊓ N.val := by
  let S := triplePairSum L.val M.val N.val
  have hs := triplePairSum_split_all L.val M.val N.val
  have hi := triplePair_inter_all L.val M.val N.val
  have ht := triplePairSum_reductions_transverse ω L.val M.val N.val L.property M.property N.property
  obtain ⟨e,he,h₁,h₂,h₃⟩ := p.property
  dsimp only [tripleResidualLagrangian] at h₁ h₂ h₃
  have hp₁ : reduceSubspace ω S p.val.1.val ⊓ reduceSubspace ω S p.val.2.1.val = ⊥ := by
    rw [←h₁,←h₂,←Submodule.map_inf e.toLinearMap e.injective,ht.1,Submodule.map_bot]
  have hp₂ : reduceSubspace ω S p.val.1.val ⊓ reduceSubspace ω S p.val.2.2.val = ⊥ := by
    rw [←h₁,←h₃,←Submodule.map_inf e.toLinearMap e.injective,ht.2.1,Submodule.map_bot]
  have hp₃ : reduceSubspace ω S p.val.2.1.val ⊓ reduceSubspace ω S p.val.2.2.val = ⊥ := by
    rw [←h₂,←h₃,←Submodule.map_inf e.toLinearMap e.injective,ht.2.2,Submodule.map_bot]
  refine ⟨?_,?_,?_⟩
  · exact (avoidance_exact_intersection ω S _ _ _ _ p.val.1.property.1 p.val.2.1.property.1
      p.val.1.property.2 p.val.2.1.property.2 hs.1 hp₁).trans hi.1
  · exact (avoidance_exact_intersection ω S _ _ _ _ p.val.1.property.1 p.val.2.2.property.1
      p.val.1.property.2 p.val.2.2.property.2 hs.2.1 hp₂).trans hi.2.1
  · exact (avoidance_exact_intersection ω S _ _ _ _ p.val.2.1.property.1 p.val.2.2.property.1
      p.val.2.1.property.2 p.val.2.2.property.2 hs.2.2 hp₃).trans hi.2.2

noncomputable def ownAvoidanceOrbitFiberEmbedding (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    OwnAvoidanceOrbitFiber ω L M N ha hω ↪ FixedPairTripleOrbit ω L M N where
  toFun p := by
    have hp := ownAvoidanceOrbitFiber_pairs ω L M N ha hω p
    have hs : triplePairSum p.val.1.val p.val.2.1.val p.val.2.2.val =
        triplePairSum L.val M.val N.val := by unfold triplePairSum; rw [hp.1,hp.2.1,hp.2.2]
    have hp0 : (p.val.1.val ⊓ p.val.2.1.val) ⊓ p.val.2.2.val = ⊥ := by
      calc
        _ = (p.val.1.val ⊓ p.val.2.1.val) ⊓ (p.val.1.val ⊓ p.val.2.2.val) := by ac_rfl
        _ = (L.val ⊓ M.val) ⊓ (L.val ⊓ N.val) := by rw [hp.1,hp.2.1]
        _ = (L.val ⊓ M.val) ⊓ N.val := by ac_rfl
        _ = ⊥ := h0
    have hr : TripleResidualIsometry ω ω ha ha L.val M.val N.val p.val.1.val p.val.2.1.val p.val.2.2.val := by
      unfold TripleResidualIsometry
      rw [hs]
      exact p.property
    have ho := triple_common_zero_classification ω ω ha ha hω hω _ _ _ _ _ _
      L.property M.property N.property p.val.1.property.1 p.val.2.1.property.1 p.val.2.2.property.1
      h0 hp0 (by rw [hp.1]) (by rw [hp.2.1]) (by rw [hp.2.2]) hr
    exact ⟨⟨(⟨p.val.1.val,p.val.1.property.1⟩,⟨p.val.2.1.val,p.val.2.1.property.1⟩,
      ⟨p.val.2.2.val,p.val.2.2.property.1⟩),ho⟩,hp⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    have hval := congrArg (fun x : FixedPairTripleOrbit ω L M N =>
      (x.val.val.1.val,x.val.val.2.1.val,x.val.val.2.2.val)) h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hval))
      (Prod.ext (Subtype.ext (congrArg (fun x => x.2.1) hval))
        (Subtype.ext (congrArg (fun x => x.2.2) hval)))
end FixedPairs
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section ConfigurationOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)

 theorem subspace_map_extension (S T U : Submodule K E) (hU : U ≤ S)
    (e : E ≃ₗ[K] E) (g : S ≃ₗ[K] T) (he : ∀ x : S, e x.val = (g x).val) :
    U.map e.toLinearMap = ((U.comap S.subtype).map g.toLinearMap).map T.subtype := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨g ⟨y,hU hy⟩,⟨⟨y,hU hy⟩,hy,rfl⟩,(he ⟨y,hU hy⟩).symm⟩
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨z.val,hz,he z⟩

 theorem subtype_map_comap_of_le (S U : Submodule K E) (hU : U ≤ S) :
    (U.comap S.subtype).map S.subtype = U := by
  ext x
  exact ⟨fun ⟨y,hy,hyx⟩ => hyx ▸ hy,fun hx => ⟨⟨x,hU hx⟩,hx,rfl⟩⟩

 theorem subspace_comap_sup_of_le (S U V : Submodule K E) (hU : U ≤ S) (hV : V ≤ S) :
    (U ⊔ V).comap S.subtype = U.comap S.subtype ⊔ V.comap S.subtype := by
  apply Submodule.map_injective_of_injective S.subtype_injective
  rw [Submodule.map_sup,subtype_map_comap_of_le S U hU,subtype_map_comap_of_le S V hV,
    subtype_map_comap_of_le S (U ⊔ V) (sup_le hU hV)]

variable [FiniteDimensional K E] [Finite E]

 theorem triple_subspace_orbit_injection (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S) :
    ∃ f : IsotropicDimspace ω (finrank K S) ×
      TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        OrderedTripleOrbit ω U V W, Function.Injective f := by
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
  have hsum' (p : TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) :
      p.val.1 ⊔ p.val.2.1 ⊔ p.val.2.2 = ⊤ := by
    obtain ⟨g,hgU,hgV,hgW⟩ := p.property
    rw [←hgU,←hgV,←hgW,←Submodule.map_sup,←Submodule.map_sup,
      ←subspace_comap_sup_of_le S U V hU hV,
      ←subspace_comap_sup_of_le S (U ⊔ V) W (sup_le hU hV) hW,hsum]
    simp
  have hrecover (p) : (f p).val.1 ⊔ (f p).val.2.1 ⊔ (f p).val.2.2 = p.1.val := by
    change ((p.2.val.1.map S.subtype).map (e p.1).toLinearMap) ⊔
      ((p.2.val.2.1.map S.subtype).map (e p.1).toLinearMap) ⊔
      ((p.2.val.2.2.map S.subtype).map (e p.1).toLinearMap) = _
    rw [←Submodule.map_sup,←Submodule.map_sup,←Submodule.map_sup,←Submodule.map_sup,hsum']
    simpa only [Submodule.map_top,Submodule.range_subtype] using (he p.1).2
  refine ⟨f,?_⟩
  rintro ⟨T,p⟩ ⟨T',p'⟩ h
  have hT : T = T' := by
    apply Subtype.ext
    exact (hrecover (T,p)).symm.trans ((congrArg (fun x : OrderedTripleOrbit ω U V W =>
      x.val.1 ⊔ x.val.2.1 ⊔ x.val.2.2) h).trans (hrecover (T',p')))
  subst T'
  have hv := congrArg Subtype.val h
  have hinj := (Submodule.map_injective_of_injective (e T).injective).comp
    (Submodule.map_injective_of_injective S.subtype_injective)
  have hp : p = p' := Subtype.ext (Prod.ext (hinj (congrArg Prod.fst hv))
    (Prod.ext (hinj (congrArg (fun x => x.2.1) hv)) (hinj (congrArg (fun x => x.2.2) hv))))
  subst p'
  rfl
end ConfigurationOrbit
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section PairOrbitAssembly
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)

 theorem fullTripleOrbit_fixedPair_injection :
    ∃ f : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
      FixedPairTripleOrbit ω L M N → OrderedTripleOrbit ω L.val M.val N.val,
      Function.Injective f := by
  classical
  let e (p : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) :=
    p.property.choose
  have he (p : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) := p.property.choose_spec
  have hgood (p : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val))
      (q : FixedPairTripleOrbit ω L M N) :
      TripleIsometry ω ω L.val M.val N.val (q.val.val.1.val.map (e p).toLinearMap)
        (q.val.val.2.1.val.map (e p).toLinearMap) (q.val.val.2.2.val.map (e p).toLinearMap) := by
    obtain ⟨g,hg,hgL,hgM,hgN⟩ := q.val.property
    refine ⟨g.trans (e p),?_,?_,?_,?_⟩
    · intro x y
      exact ((he p).1 (g x) (g y)).trans (hg x y)
    · rw [submodule_map_trans,hgL]
    · rw [submodule_map_trans,hgM]
    · rw [submodule_map_trans,hgN]
  let f : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
      FixedPairTripleOrbit ω L M N → OrderedTripleOrbit ω L.val M.val N.val := fun p =>
    ⟨(p.2.val.val.1.val.map (e p.1).toLinearMap,
      p.2.val.val.2.1.val.map (e p.1).toLinearMap,
      p.2.val.val.2.2.val.map (e p.1).toLinearMap),hgood p.1 p.2⟩
  have hrec (p) : ((f p).val.1 ⊓ (f p).val.2.1,
      (f p).val.1 ⊓ (f p).val.2.2,(f p).val.2.1 ⊓ (f p).val.2.2) = p.1.val := by
    change ((p.2.val.val.1.val.map (e p.1).toLinearMap) ⊓ (p.2.val.val.2.1.val.map (e p.1).toLinearMap),
      (p.2.val.val.1.val.map (e p.1).toLinearMap) ⊓ (p.2.val.val.2.2.val.map (e p.1).toLinearMap),
      (p.2.val.val.2.1.val.map (e p.1).toLinearMap) ⊓ (p.2.val.val.2.2.val.map (e p.1).toLinearMap)) = _
    rw [←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      p.2.property.1,p.2.property.2.1,p.2.property.2.2,
      (he p.1).2.1,(he p.1).2.2.1,(he p.1).2.2.2]
  refine ⟨f,?_⟩
  rintro ⟨p,q⟩ ⟨p',q'⟩ h
  have hp : p = p' := by
    apply Subtype.ext
    exact (hrec (p,q)).symm.trans ((congrArg (fun x : OrderedTripleOrbit ω L.val M.val N.val =>
      (x.val.1 ⊓ x.val.2.1,x.val.1 ⊓ x.val.2.2,x.val.2.1 ⊓ x.val.2.2)) h).trans (hrec (p',q')))
  subst p'
  have hv := congrArg Subtype.val h
  have hinj := Submodule.map_injective_of_injective (e p).injective
  have hq : q = q' := Subtype.ext (Subtype.ext
    (Prod.ext (Subtype.ext (hinj (congrArg Prod.fst hv)))
      (Prod.ext (Subtype.ext (hinj (congrArg (fun x => x.2.1) hv)))
        (Subtype.ext (hinj (congrArg (fun x => x.2.2) hv))))))
  subst q'
  rfl

variable [Finite E]
 theorem fullTripleOrbit_fixedPair_card_lower :
    Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
        Nat.card (FixedPairTripleOrbit ω L M N) ≤ Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  obtain ⟨f,hf⟩ := fullTripleOrbit_fixedPair_injection ω L M N
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf
end PairOrbitAssembly
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section ConfigurationCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)

 theorem triple_isotropic_orbit_card_lower (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S)
    (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W) :
    (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
      2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) ≤
      (lagrangianConstant D * 2^D) * Nat.card (OrderedTripleOrbit ω U V W) := by
  let U' := U.comap S.subtype
  let V' := V.comap S.subtype
  let W' := W.comap S.subtype
  have hc : IsCompl U' (V' ⊔ W') := by
    constructor
    · apply disjoint_iff.mpr
      change U.comap S.subtype ⊓ (V.comap S.subtype ⊔ W.comap S.subtype) = ⊥
      rw [←subspace_comap_sup_of_le S V W hV hW,←Submodule.comap_inf,disjoint_iff.mp hdis]
      simp
    · apply codisjoint_iff.mpr
      change U.comap S.subtype ⊔ (V.comap S.subtype ⊔ W.comap S.subtype) = ⊤
      rw [←sup_assoc,←subspace_comap_sup_of_le S U V hU hV,
        ←subspace_comap_sup_of_le S (U ⊔ V) W (sup_le hU hV) hW,hsum]
      simp
  have hvw : Disjoint V' W' := by
    apply disjoint_iff.mpr
    change V.comap S.subtype ⊓ W.comap S.subtype = ⊥
    rw [←Submodule.comap_inf,disjoint_iff.mp hVW]
    simp
  have hu' : finrank K U' = finrank K U := (Submodule.comapSubtypeEquivOfLe hU).finrank_eq
  have hv' : finrank K V' = finrank K V := (Submodule.comapSubtypeEquivOfLe hV).finrank_eq
  have hw' : finrank K W' = finrank K W := (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have hb := (tripleLinearOrbit_card_bounds U' V' W' hc hvw).1
  rw [hu',hv',hw'] at hb
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  have hi := (isotropic_card_bounds ω h2 ha hω D hD (finrank K S) hs).1
  obtain ⟨f,hf⟩ := triple_subspace_orbit_injection ω h2 ha hω S U V W hS hU hV hW hsum
  have hcard : (Nat.card (IsotropicDimspace ω (finrank K S)) : ℝ)*
      Nat.card (TripleLinearOrbit U' V' W') ≤ Nat.card (OrderedTripleOrbit ω U V W) := by
    have hh := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at hh
    exact_mod_cast hh
  have hk : lagrangianConstant (D-finrank K S) * (2:ℝ)^(finrank K S) ≤ lagrangianConstant D * 2^D := by
    exact mul_le_mul (lagrangianConstant_mono (Nat.sub_le D _))
      (pow_le_pow_right₀ (by norm_num) hs) (by positivity)
      (le_of_lt (lagrangianConstant_pos D))
  calc
    _ = (Fintype.card K : ℝ)^isotropicExponent D (finrank K S) *
      (Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by rw [pow_add]
    _ ≤ (lagrangianConstant (D-finrank K S)*Nat.card (IsotropicDimspace ω (finrank K S))) *
      (2^(finrank K S)*Nat.card (TripleLinearOrbit U' V' W')) :=
        mul_le_mul hi hb (by positivity)
          (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (Nat.cast_nonneg _))
    _ = (lagrangianConstant (D-finrank K S)*2^(finrank K S))*
      ((Nat.card (IsotropicDimspace ω (finrank K S)) : ℝ)*Nat.card (TripleLinearOrbit U' V' W')) := by ring
    _ ≤ (lagrangianConstant D*2^D)*Nat.card (OrderedTripleOrbit ω U V W) :=
      mul_le_mul hk hcard (by positivity)
        (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (by positivity))
end ConfigurationCount

section FixedPairCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)
 theorem fixedPairTripleOrbit_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    let S := triplePairSum L.val M.val N.val
    (Fintype.card K : ℝ)^((D-finrank K ↥(L.val ⊓ S)+1).choose 2 +
      (D-finrank K ↥(M.val ⊓ S)+1).choose 2 + (D-finrank K ↥(N.val ⊓ S)+1).choose 2) ≤
      (8 * (4^D * lagrangianConstant D^2)) * Nat.card (FixedPairTripleOrbit ω L M N) := by
  dsimp only
  let S := triplePairSum L.val M.val N.val
  have hs : S ≤ ω.orthogonal S := triplePairSum_isotropic ω _ _ _ L.property M.property N.property
  have his (P : SymplecticLagrangian ω) : P.val ⊓ S ≤ ω.orthogonal (P.val ⊓ S) := by
    intro x hx y hy
    exact P.property.ge hx.1 y hy.1
  have h2 := (isUnit_of_invertible (2:K)).ne_zero
  have h₁ := (containingLagrangian_card_bounds ω h2 ha hω D hD (L.val ⊓ S) (his L)).1
  have h₂ := (containingLagrangian_card_bounds ω h2 ha hω D hD (M.val ⊓ S) (his M)).1
  have h₃ := (containingLagrangian_card_bounds ω h2 ha hω D hD (N.val ⊓ S) (his N)).1
  have ht := triplePairSum_reductions_transverse ω L.val M.val N.val L.property M.property N.property
  have hb := containmentOrbitFiber_card_lower ω S ha hω hs D hD hq
    (L.val ⊓ S) (M.val ⊓ S) (N.val ⊓ S) inf_le_right inf_le_right inf_le_right
    (tripleResidualLagrangian ω L M N ha hω L)
    (tripleResidualLagrangian ω L M N ha hω M) (tripleResidualLagrangian ω L M N ha hω N)
    ht.1 ht.2.1 ht.2.2
  have he := ownAvoidanceOrbitFiberEmbedding ω L M N ha hω h0
  have hc : (Nat.card (OwnAvoidanceOrbitFiber ω L M N ha hω) : ℝ) ≤
      Nat.card (FixedPairTripleOrbit ω L M N) := by exact_mod_cast Nat.card_le_card_of_injective he he.injective
  calc
    _ = (Fintype.card K : ℝ)^((D-finrank K ↥(L.val ⊓ S)+1).choose 2) *
      ((Fintype.card K : ℝ)^((D-finrank K ↥(M.val ⊓ S)+1).choose 2) *
        (Fintype.card K : ℝ)^((D-finrank K ↥(N.val ⊓ S)+1).choose 2)) := by simp only [pow_add]; ring
    _ ≤ (Nat.card {P : SymplecticLagrangian ω // L.val ⊓ S ≤ P.val} : ℝ)*
      (Nat.card {P : SymplecticLagrangian ω // M.val ⊓ S ≤ P.val} *
        Nat.card {P : SymplecticLagrangian ω // N.val ⊓ S ≤ P.val}) := by gcongr
    _ ≤ _ := hb
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
end FixedPairCount
end SidorenkoCounterexample

namespace SidorenkoCounterexample
theorem pair_cost_cancellation (D u v w : ℕ) (h : u+v+w ≤ D) :
    isotropicExponent D (u+v+w) + 2*(u*v+u*w+v*w) +
      ((D-(u+v)+1).choose 2 + (D-(u+w)+1).choose 2 + (D-(v+w)+1).choose 2) +
      ((u+1).choose 2 + (v+1).choose 2 + (w+1).choose 2) = 3*(D+1).choose 2 := by
  have hu : u+v ≤ D := by omega
  have hv : u+w ≤ D := by omega
  have hw : v+w ≤ D := by omega
  have hi := isotropicExponent_add D (u+v+w) h
  have hi' : (isotropicExponent D (u+v+w) : ℚ) =
      ((D+1).choose 2 : ℚ) + (u+v+w)*(D-(u+v+w)) - ((D-(u+v+w)+1).choose 2 : ℚ) := by
    have hiq := congrArg (fun x : ℕ => (x:ℚ)) hi
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub h] at hiq
    linarith
  apply @Nat.cast_injective ℚ
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hi',Nat.cast_choose_two,Nat.cast_one,
    Nat.cast_sub hu,Nat.cast_sub hv,Nat.cast_sub hw,Nat.cast_sub h]
  ring

theorem common_cost_cancellation (D c : ℕ) (hc : c ≤ D) :
    isotropicExponent D c + 3*(D-c+1).choose 2 + (D+1)*c = 3*(D+1).choose 2 := by
  have hi := isotropicExponent_add D c hc
  have h : 2*((D-c+1).choose 2) + (D+1)*c + c*(D-c) = 2*((D+1).choose 2) := by
    apply @Nat.cast_injective ℚ
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_choose_two,Nat.cast_one,Nat.cast_sub hc]
    ring
  omega

open Module
section PairMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)

 theorem finrank_sup_of_disjoint (U V : Submodule K E) (h : Disjoint U V) :
    finrank K ↥(U ⊔ V) = finrank K U + finrank K V := by
  have hh := U.finrank_sup_add_finrank_inf_eq V
  rw [disjoint_iff.mp h,finrank_bot,add_zero] at hh
  exact hh

 theorem triplePairSum_finrank (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    finrank K ↥(triplePairSum L M N) = finrank K ↥(L ⊓ M) + finrank K ↥(L ⊓ N) + finrank K ↥(M ⊓ N) := by
  have hd := triple_pairs_disjoint L M N h0
  change finrank K ↥(((L ⊓ M) ⊔ (L ⊓ N)) ⊔ (M ⊓ N)) = _
  rw [sup_assoc,finrank_sup_of_disjoint _ _ hd.1,finrank_sup_of_disjoint _ _ hd.2,add_assoc]

 theorem triplePairSum_inter_finrank (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    finrank K ↥(L ⊓ triplePairSum L M N) = finrank K ↥(L ⊓ M) + finrank K ↥(L ⊓ N) := by
  rw [triple_own_avoidance L M N h0]
  exact finrank_sup_of_disjoint _ _ ((triple_pairs_disjoint L M N h0).1.mono_right le_sup_left)

noncomputable def pairOrbitConstant (D : ℕ) : ℝ :=
  (lagrangianConstant D*2^D)*(8*(4^D*lagrangianConstant D^2))

 theorem pairOrbitConstant_pos (D : ℕ) : 0 < pairOrbitConstant D := by
  unfold pairOrbitConstant
  have h := lagrangianConstant_pos D
  positivity

variable [Fintype K] [Finite E] [Invertible (2:K)]

 theorem commonZeroOrbit_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    (Fintype.card K : ℝ)^(3*(D+1).choose 2) ≤
      pairOrbitConstant D * (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2 +
        (finrank K ↥(L.val ⊓ N.val)+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)+1).choose 2) *
      Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  let S := triplePairSum L.val M.val N.val
  let u := finrank K ↥(L.val ⊓ M.val)
  let v := finrank K ↥(L.val ⊓ N.val)
  let w := finrank K ↥(M.val ⊓ N.val)
  have hs : S ≤ ω.orthogonal S := triplePairSum_isotropic ω _ _ _ L.property M.property N.property
  have hdim : finrank K S = u+v+w := triplePairSum_finrank _ _ _ h0
  have hdimL : finrank K ↥(L.val ⊓ S) = u+v := triplePairSum_inter_finrank _ _ _ h0
  have h0M : (M.val ⊓ L.val) ⊓ N.val = ⊥ := by simpa only [inf_comm] using h0
  have h0N : (N.val ⊓ L.val) ⊓ M.val = ⊥ := by simpa only [inf_assoc,inf_left_comm,inf_comm] using h0
  have hSM : triplePairSum M.val L.val N.val = S := by dsimp [S,triplePairSum]; ac_rfl
  have hSN : triplePairSum N.val L.val M.val = S := by dsimp [S,triplePairSum]; ac_rfl
  have hdimM : finrank K ↥(M.val ⊓ S) = u+w := by
    have hh := triplePairSum_inter_finrank M.val L.val N.val h0M
    rw [hSM,inf_comm M.val L.val] at hh
    exact hh
  have hdimN : finrank K ↥(N.val ⊓ S) = v+w := by
    have hh := triplePairSum_inter_finrank N.val L.val M.val h0N
    rw [hSN,inf_comm N.val L.val,inf_comm N.val M.val] at hh
    exact hh
  have haD : u+v+w ≤ D := hdim ▸ isotropic_finrank_le_half ω hω D hD S hs
  have hd := triple_pairs_disjoint L.val M.val N.val h0
  have hc := triple_isotropic_orbit_card_lower ω (isUnit_of_invertible (2:K)).ne_zero ha hω D hD S
    (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) hs
    (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right) le_sup_right rfl hd.1 hd.2
  rw [hdim] at hc
  have hf := fixedPairTripleOrbit_card_lower ω ha hω D hD hq L M N h0
  change (Fintype.card K : ℝ)^((D-finrank K ↥(L.val ⊓ S)+1).choose 2 +
      (D-finrank K ↥(M.val ⊓ S)+1).choose 2 + (D-finrank K ↥(N.val ⊓ S)+1).choose 2) ≤ _ at hf
  rw [hdimL,hdimM,hdimN] at hf
  have hm : (Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) : ℝ) *
      Nat.card (FixedPairTripleOrbit ω L M N) ≤ Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    exact_mod_cast fullTripleOrbit_fixedPair_card_lower ω L M N
  have hn : 0 ≤ lagrangianConstant D*2^D := mul_nonneg (le_of_lt (lagrangianConstant_pos D)) (by positivity)
  have hp := mul_le_mul hc hf (by positivity)
    (mul_nonneg hn (Nat.cast_nonneg _))
  have hh : (Fintype.card K : ℝ)^(isotropicExponent D (u+v+w)+2*(u*v+u*w+v*w)+
      ((D-(u+v)+1).choose 2+(D-(u+w)+1).choose 2+(D-(v+w)+1).choose 2)) ≤
      pairOrbitConstant D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    calc
      _ ≤ (lagrangianConstant D*2^D)*Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
          ((8*(4^D*lagrangianConstant D^2))*Nat.card (FixedPairTripleOrbit ω L M N)) := by
        simpa only [pow_add] using hp
      _ = pairOrbitConstant D * ((Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) : ℝ)*
          Nat.card (FixedPairTripleOrbit ω L M N)) := by unfold pairOrbitConstant; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (le_of_lt (pairOrbitConstant_pos D))
  have hh' := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ (Fintype.card K : ℝ)^((u+1).choose 2+(v+1).choose 2+(w+1).choose 2) by positivity)
  rw [←pow_add,pair_cost_cancellation D u v w haD] at hh'
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh'
end PairMass
end SidorenkoCounterexample

end OAI
