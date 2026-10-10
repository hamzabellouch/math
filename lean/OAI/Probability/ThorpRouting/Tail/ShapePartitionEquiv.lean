import Mathlib
import OAI.Probability.ThorpRouting.Tail.ModifiedReverseEquiv

namespace OAI

namespace ThorpNine.Tail

namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def shapePartitionEquiv (N : ℕ) : Shapes N ≃ Nat.Partition N where
  toFun μ := { parts := μ.1.rowLens
               parts_pos := fun {i} hi => μ.1.pos_of_mem_rowLens i (by simpa using hi)
               parts_sum := by simpa using (sum_rowLens μ.1).trans μ.2 }
  invFun p := ⟨partitionDiagram p,partitionDiagram_card p⟩
  left_inv μ := by
    apply Subtype.ext
    obtain ⟨μ,rfl⟩ := μ
    exact partitionDiagram_diagramPartition μ
  right_inv p := by
    apply Nat.Partition.ext
    change ((partitionDiagram p).rowLens : Multiset ℕ) = p.parts
    rw [partitionDiagram_rowLens,Multiset.sort_eq]

noncomputable instance (N : ℕ) : Fintype (Shapes N) := Fintype.ofEquiv _ (shapePartitionEquiv N).symm

noncomputable def conjugacyPartition {α : Type*} [Fintype α] [DecidableEq α] :
    ConjClasses (Equiv.Perm α) → Nat.Partition (Fintype.card α) :=
  Quotient.lift Equiv.Perm.partition (fun _ _ hpq => (Equiv.Perm.partition_eq_of_isConj).mp hpq)

lemma conjugacyPartition_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (conjugacyPartition (α := α)) := by
  intro p q
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      intro h
      exact Quotient.sound ((Equiv.Perm.partition_eq_of_isConj).mpr h)

lemma card_conjugacy_le_shapes (N : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Fin N))) ≤ Fintype.card (Shapes N) := by
  have h := Nat.card_le_card_of_injective _ (conjugacyPartition_injective (α := Fin N))
  simpa only [Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_congr (shapePartitionEquiv N)] using h

noncomputable def labels {N : ℕ} (μ : Shapes N) : Cell μ.1 ≃ Fin N :=
  (Fintype.equivFin (Cell μ.1)).trans (finCongr ((card_cell μ.1).trans μ.2))

noncomputable def labelledRepresentation {N : ℕ} (μ : Shapes N) :
    Representation ℂ (Equiv.Perm (Fin N)) (space μ.1) :=
  (representation μ.1).comp (labels μ).symm.permCongrHom.toMonoidHom

lemma labelledRepresentation_irreducible {N : ℕ} (μ : Shapes N) :
    Representation.IsIrreducible (labelledRepresentation μ) := by
  let e := (labels μ).symm.permCongrHom
  let ρ := representation μ.1
  have hn : (⊥ : Subrepresentation (labelledRepresentation μ)) ≠ ⊤ := by
    intro h
    have he : (⟨polytabloid μ.1,polytabloid_mem_space μ.1⟩ : space μ.1) ∈
        (⊥ : Subrepresentation (labelledRepresentation μ)) := by rw [h]; trivial
    exact polytabloid_ne_zero μ.1 (congrArg Subtype.val he)
  refine { exists_pair_ne := ⟨⊥,⊤,hn⟩,eq_bot_or_eq_top := ?_ }
  intro U
  let U' : Subrepresentation ρ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := fun p v hv => by
        have hh := U.apply_mem_toSubmodule (e.symm p) hv
        change ρ (e (e.symm p)) v ∈ U.toSubmodule at hh
        simpa using hh }
  have := representation_irreducible μ.1
  obtain h | h := IsSimpleOrder.eq_bot_or_eq_top U'
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun R : Subrepresentation ρ => R.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun R : Subrepresentation ρ => R.toSubmodule) h

lemma labelledRepresentation_equiv_shapes {N : ℕ} (μ ν : Shapes N)
    (T : Representation.Equiv (labelledRepresentation μ) (labelledRepresentation ν)) : μ = ν := by
  apply Subtype.ext
  apply shapes_eq_of_equivariant_equiv μ.1 ν.1 ((labels μ).trans (labels ν).symm) T.toLinearEquiv
  intro p v
  have hh := Representation.IntertwiningMap.isIntertwining _ _ T.toIntertwiningMap ((labels μ).permCongr p) v
  change T.toLinearEquiv
    (representation μ.1 ((labels μ).symm.permCongr ((labels μ).permCongr p)) v) =
      representation ν.1 ((labels ν).symm.permCongr ((labels μ).permCongr p)) (T.toLinearEquiv v) at hh
  have hp : (labels μ).symm.permCongr ((labels μ).permCongr p) = p := by
    apply Equiv.ext
    intro x
    simp [Equiv.permCongr_apply]
  rw [hp] at hh
  convert hh using 2
  congr 1

end Thorp.Specht

namespace Thorp.FiniteCharacters
open scoped BigOperators Classical

section Group
variable {G : Type*} [Group G] [Fintype G]

noncomputable def classRep (c : ConjClasses G) : G := (ConjClasses.exists_rep c).choose
omit [Fintype G] in
lemma classRep_spec (c : ConjClasses G) : ConjClasses.mk (classRep c) = c :=
  (ConjClasses.exists_rep c).choose_spec

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

noncomputable def characterClass (ρ : Representation ℂ G V) : ConjClasses G → ℂ :=
  fun c => ρ.character (classRep c)

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma characterClass_mk (ρ : Representation ℂ G V) (g : G) :
    characterClass ρ (ConjClasses.mk g) = ρ.character g := by
  have h := ConjClasses.mk_eq_mk_iff_isConj.mp (classRep_spec (ConjClasses.mk g))
  obtain ⟨p,hp⟩ := isConj_iff.mp h
  change ρ.character (classRep (ConjClasses.mk g)) = ρ.character g
  exact (Representation.char_conj ρ _ p).symm.trans (congrArg ρ.character hp)

noncomputable def characterDual (ρ : Representation ℂ G V) :
    (ConjClasses G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Nat.card G : ℂ)⁻¹ * ∑ g, f (ConjClasses.mk g) * ρ.character g⁻¹
  map_add' f h := by simp [Finset.sum_add_distrib,add_mul,mul_add]
  map_smul' a f := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_assoc]
    rw [←Finset.mul_sum]
    ring

lemma characterDual_characterClass (ρ : Representation ℂ G V)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ] :
    characterDual ρ (characterClass σ) = if Nonempty (Representation.Equiv ρ σ) then 1 else 0 := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  change (Nat.card G : ℂ)⁻¹ * ∑ g, characterClass σ (ConjClasses.mk g) * ρ.character g⁻¹ = _
  simp only [characterClass_mk]
  exact Representation.char_orthonormal σ ρ

end Group

theorem complete_of_card_conjugacy_le
    {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
    (hneq : ∀ i j, i ≠ j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
    (hcard : Nat.card (ConjClasses G) ≤ Fintype.card ι)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [Representation.IsIrreducible σ] :
    ∃ i, Nonempty (Representation.Equiv (ρ i) σ) := by
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  have horth (i j : ι) : characterDual (ρ i) (characterClass (ρ j)) = if i=j then 1 else 0 := by
    rw [characterDual_characterClass]
    by_cases hij : i=j
    · subst j
      simp only [ite_true]
      exact ite_eq_left ⟨Representation.Equiv.refl _⟩
    · rw [ite_eq_right hij,ite_eq_right (hneq i j hij)]
  have hLI : LinearIndependent ℂ (fun i => characterClass (ρ i)) := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun i => characterDual (ρ i))
    · intro i j hij
      exact (horth i j).trans (ite_eq_right hij)
    · intro i
      simpa using horth i i
  have heq : Fintype.card ι = Module.finrank ℂ (ConjClasses G → ℂ) := by
    apply Nat.le_antisymm hLI.fintype_card_le_finrank
    simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
      smul_eq_mul,mul_one,Nat.card_eq_fintype_card] using hcard
  have hspan := hLI.span_eq_top_of_card_eq_finrank' heq
  by_contra h
  push Not at h
  have hker : Submodule.span ℂ (Set.range (fun i => characterClass (ρ i))) ≤
      (characterDual σ).ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨i,rfl⟩
    change characterDual σ (characterClass (ρ i)) = 0
    rw [characterDual_characterClass,ite_eq_right]
    rintro ⟨T⟩
    exact (h i).false T.symm
  rw [hspan] at hker
  have hz : characterDual σ (characterClass σ) = 0 := hker (show characterClass σ ∈ ⊤ from trivial)
  rw [characterDual_characterClass,ite_eq_left ⟨Representation.Equiv.refl σ⟩] at hz
  exact one_ne_zero hz

end Thorp.FiniteCharacters

namespace Thorp.Specht
open scoped Classical

theorem labelled_complete {N : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) V) [Representation.IsIrreducible ρ] :
    ∃ μ : Shapes N, Nonempty (Representation.Equiv (labelledRepresentation μ) ρ) := by
  let (μ : Shapes N) : Representation.IsIrreducible (labelledRepresentation μ) :=
    labelledRepresentation_irreducible μ
  apply FiniteCharacters.complete_of_card_conjugacy_le
    (fun μ : Shapes N => space μ.1) labelledRepresentation _ (card_conjugacy_le_shapes N) ρ
  intro μ ν h ⟨T⟩
  exact h (labelledRepresentation_equiv_shapes μ ν T)

end Thorp.Specht

namespace Thorp.PermutationHilbert

section
open scoped BigOperators ComplexConjugate Classical
open Complex

variable {X : Type*} [Fintype X]

noncomputable def act (p : Equiv.Perm X) : H X ≃ₗᵢ[ℂ] H X :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ p

@[simp] lemma act_apply (p : Equiv.Perm X) (v : H X) (x : X) :
    act p v x = v (p⁻¹ x) := rfl

lemma act_single [DecidableEq X] (p : Equiv.Perm X) (x : X) :
    act p (EuclideanSpace.single x (1:ℂ)) = EuclideanSpace.single (p x) 1 := by
  exact EuclideanSpace.piLpCongrLeft_single p x 1

lemma trace_projection (W : Submodule ℂ (H X)) :
    ∑ x, (W.starProjection (EuclideanSpace.single x (1:ℂ))) x = Module.finrank ℂ W := by
  classical
  have hp : LinearMap.IsProj W W.starProjection.toLinearMap := by
    constructor
    · intro x; exact (W.orthogonalProjectionOnto x).2
    · intro x hx; exact W.starProjection_eq_self_iff.mpr hx
  have ht := hp.trace
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun X ℂ).toBasis] at ht
  simpa only [Matrix.trace,Matrix.diag_apply,LinearMap.toMatrix_apply,EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply,ContinuousLinearMap.coe_coe] using ht

lemma projection_diagonal (W : Submodule ℂ (H X)) (x : X) :
    (W.starProjection (EuclideanSpace.single x (1:ℂ))) x =
      (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 : ℝ) := by
  classical
  have hh := W.inner_starProjection_left_eq_right
    (EuclideanSpace.single x (1:ℂ)) (W.starProjection (EuclideanSpace.single x (1:ℂ)))
  have hf : W.starProjection (W.starProjection (EuclideanSpace.single x (1:ℂ))) =
      W.starProjection (EuclideanSpace.single x (1:ℂ)) :=
    W.starProjection_eq_self_iff.mpr (W.orthogonalProjectionOnto _).2
  rw [hf] at hh
  rw [inner_self_eq_norm_sq_to_K,EuclideanSpace.inner_single_left] at hh
  simpa using hh.symm

lemma projection_comm (W : Submodule ℂ (H X)) (p : Equiv.Perm X)
    (hW : W.map (act p).toLinearEquiv.toLinearMap = W) (v : H X) :
    act p (W.starProjection v) = W.starProjection (act p v) := by
  have hh := (act p).toLinearIsometry.map_starProjection W v
  change act p (W.starProjection v) =
    (W.map (act p).toLinearEquiv.toLinearMap).starProjection (act p v) at hh
  simpa only [hW] using hh

lemma uniform_diagonal (W : Submodule ℂ (H X))
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W) (x : X) :
    (Fintype.card X:ℝ) * ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 =
      Module.finrank ℂ W := by
  classical
  have hh (y : X) : (W.starProjection (EuclideanSpace.single y (1:ℂ))) y =
      (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 : ℝ) := by
    obtain ⟨p,hp,hW⟩ := htrans x y
    subst y
    rw [projection_diagonal,←act_single p x,←projection_comm W p hW,(act p).norm_map]
  have ht := trace_projection W
  simp_rw [hh] at ht
  have hhreal : (∑ _y : X, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2) =
      (Module.finrank ℂ W:ℝ) := by exact_mod_cast ht
  simpa using hhreal

theorem uncertainty (W : Submodule ℂ (H X))
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W)
    (v : H X) (hv : v ∈ W) (x : X) :
    (Fintype.card X:ℝ) * ‖v x‖^2 ≤ (Module.finrank ℂ W:ℝ) * ‖v‖^2 := by
  classical
  have hh : inner ℂ (W.starProjection (EuclideanSpace.single x (1:ℂ))) v = v x := by
    rw [W.inner_starProjection_left_eq_right,W.starProjection_eq_self_iff.mpr hv,
      EuclideanSpace.inner_single_left]
    simp
  have hc := norm_inner_le_norm (𝕜 := ℂ) (W.starProjection (EuclideanSpace.single x (1:ℂ))) v
  rw [hh] at hc
  have hs : ‖v x‖^2 ≤ ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 * ‖v‖^2 := by
    nlinarith [norm_nonneg (v x),norm_nonneg v,
      norm_nonneg (W.starProjection (EuclideanSpace.single x (1:ℂ)))]
  calc
    (Fintype.card X:ℝ) * ‖v x‖^2 ≤
      (Fintype.card X:ℝ) * (‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 * ‖v‖^2) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = _ := by rw [←mul_assoc,uniform_diagonal W htrans x]

end
open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

lemma trace_projection_real (W : Submodule ℂ (H X)) :
    ∑ x, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 = (Module.finrank ℂ W:ℝ) := by
  have hh := trace_projection W
  simp_rw [projection_diagonal] at hh
  exact_mod_cast hh

theorem footprint_dimension (W K : Submodule ℂ (H X)) (hKW : K ≤ W)
    (htrans : ∀ x y : X, ∃ p : Equiv.Perm X, p x = y ∧
      W.map (act p).toLinearEquiv.toLinearMap = W)
    (S : Finset X) (hS : ∀ x ∈ S, W.starProjection (EuclideanSpace.single x (1:ℂ)) ∈ K) :
    (S.card:ℝ) * (Module.finrank ℂ W:ℝ) ≤
      (Fintype.card X:ℝ) * (Module.finrank ℂ K:ℝ) := by
  have he (x : X) (hx : x ∈ S) :
      K.starProjection (EuclideanSpace.single x (1:ℂ)) =
        W.starProjection (EuclideanSpace.single x (1:ℂ)) := by
    apply K.eq_starProjection_of_mem_of_inner_eq_zero (hS x hx)
    intro v hv
    exact W.starProjection_inner_eq_zero _ v (hKW hv)
  have hs : ∑ x ∈ S, ‖W.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 ≤
      (Module.finrank ℂ K:ℝ) := by
    rw [←trace_projection_real K]
    calc
      _ = ∑ x ∈ S, ‖K.starProjection (EuclideanSpace.single x (1:ℂ))‖^2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [he x hx]
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun x => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (Fintype.card X): (0:ℝ) ≤ _)
  rw [Finset.mul_sum] at hmul
  simp_rw [uniform_diagonal W htrans] at hmul
  simpa using hmul

end Thorp.PermutationHilbert
namespace Thorp.Specht
open scoped BigOperators Classical

lemma finrank_hilbertSpace (μ : YoungDiagram) :
    Module.finrank ℂ (hilbertSpace μ) = Module.finrank ℂ (space μ) :=
  (hilbertEquiv μ).finrank_map_eq (space μ)

lemma hilbert_action (μ : YoungDiagram) (p : Equiv.Perm (Cell μ)) (v : Tabloid μ → ℂ) :
    hilbertEquiv μ (tabloidRep μ p v) =
      PermutationHilbert.act (tabloidAct p) (hilbertEquiv μ v) := by
  ext f
  simp [hilbertEquiv,PermutationHilbert.act_apply]

lemma hilbertSpace_invariant (μ : YoungDiagram) (p : Equiv.Perm (Cell μ)) :
    (hilbertSpace μ).map (PermutationHilbert.act (tabloidAct p)).toLinearEquiv.toLinearMap =
      hilbertSpace μ := by
  apply le_antisymm
  · rintro _ ⟨v,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨tabloidRep μ p w,action_mem_space μ p w hw,hilbert_action μ p w⟩
  · rintro _ ⟨w,hw,rfl⟩
    refine ⟨hilbertEquiv μ (tabloidRep μ p⁻¹ w),
      ⟨tabloidRep μ p⁻¹ w,action_mem_space μ p⁻¹ w hw,rfl⟩, ?_⟩
    change PermutationHilbert.act (tabloidAct p) (hilbertEquiv μ (tabloidRep μ p⁻¹ w)) = hilbertEquiv μ w
    rw [←hilbert_action]
    change hilbertEquiv μ ((tabloidRep μ p * tabloidRep μ p⁻¹) w) = _
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl

lemma tabloidAct_transitive (μ : YoungDiagram) (f g : Tabloid μ) :
    ∃ p : Equiv.Perm (Cell μ), tabloidAct p f = g := by
  obtain ⟨q,hq⟩ := f.2
  obtain ⟨r,hr⟩ := g.2
  refine ⟨r⁻¹*q, ?_⟩
  apply Subtype.ext
  funext x
  simp only [tabloidAct_apply,mul_inv_rev,Equiv.Perm.mul_apply,hq,hr,
    Function.comp_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply,Equiv.symm_symm]

lemma polytabloid_pairing (μ : YoungDiagram) :
    pairing (polytabloid μ) (polytabloid μ) = Fintype.card (colGroup μ) := by
  have h := alternator_pairing μ (polytabloid μ)
  have he (c : colGroup μ) : tabloidRep μ c (polytabloid μ) =
      permSign (c:Equiv.Perm (Cell μ)) • polytabloid μ :=
    action_alternator_apply (colGroup μ) (tabloidRep μ) c _
  have hb := congrArg (fun v : Tabloid μ → ℂ => v (baseTabloid μ)) h
  simp only [alternator,LinearMap.sum_apply,LinearMap.smul_apply,he,
    Pi.smul_apply,smul_eq_mul,Finset.sum_apply,polytabloid_base,mul_one] at hb
  simp only [permSign_sq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hb
  exact hb.symm

lemma polytabloid_norm_sq (μ : YoungDiagram) :
    ‖hilbertEquiv μ (polytabloid μ)‖^2 = (Fintype.card (colGroup μ):ℝ) := by
  have hp := polytabloid_pairing μ
  change inner ℂ (hilbertEquiv μ (polytabloid μ)) (hilbertEquiv μ (polytabloid μ)) = _ at hp
  rw [inner_self_eq_norm_sq_to_K] at hp
  have hre := congrArg Complex.re hp
  simpa [pow_two] using hre

theorem dimension_times_column_ge_tabloids (μ : YoungDiagram) :
    Fintype.card (Tabloid μ) ≤ Module.finrank ℂ (space μ) * Fintype.card (colGroup μ) := by
  have ht (f g : Tabloid μ) : ∃ p : Equiv.Perm (Tabloid μ), p f = g ∧
      (hilbertSpace μ).map (PermutationHilbert.act p).toLinearEquiv.toLinearMap = hilbertSpace μ := by
    obtain ⟨p,hp⟩ := tabloidAct_transitive μ f g
    exact ⟨tabloidAct p,hp,hilbertSpace_invariant μ p⟩
  have hu := PermutationHilbert.uncertainty (hilbertSpace μ) ht
    (hilbertEquiv μ (polytabloid μ)) ⟨polytabloid μ,polytabloid_mem_space μ,rfl⟩ (baseTabloid μ)
  have he : hilbertEquiv μ (polytabloid μ) (baseTabloid μ) = 1 := polytabloid_base μ
  rw [he,norm_one,one_pow,mul_one,finrank_hilbertSpace,polytabloid_norm_sq] at hu
  exact_mod_cast hu


section FiberGroup
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def fiberGroupEquiv (f : α → β) :
    fiberGroup f ≃ (∀ b, Equiv.Perm {x // f x = b}) where
  toFun p b :=
    { toFun x := ⟨p.1 x.1,(p.2 x.1).trans x.2⟩
      invFun x := ⟨p.1⁻¹ x.1, by
        have hh := p.2 (p.1⁻¹ x.1)
        simp only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] at hh
        exact hh.symm.trans x.2⟩
      left_inv x := by apply Subtype.ext; simp
      right_inv x := by apply Subtype.ext; simp }
  invFun q :=
    ⟨(Equiv.sigmaFiberEquiv f).permCongr (Equiv.Perm.sigmaCongrRight q),
      fun x => (q (f x) ⟨x,rfl⟩).2⟩
  left_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rfl
  right_inv q := by
    funext b
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (q (f x.1) ⟨x.1,rfl⟩).1 = (q b x).1
    cases x with
    | mk x hx => dsimp only at *; subst b; rfl

lemma nat_card_fiberGroup (f : α → β) :
    Nat.card (fiberGroup f) = ∏ b, (Nat.card {x // f x=b}).factorial := by
  rw [Nat.card_congr (fiberGroupEquiv f),Nat.card_pi]
  simp only [Nat.card_eq_fintype_card,Fintype.card_perm]

omit [Fintype β] [Fintype γ] in

lemma card_fiberGroups_mul_le (f : α → β) (g : α → γ)
    (hinj : ∀ x y, f x = f y → g x = g y → x=y) :
    Fintype.card (fiberGroup f) * Fintype.card (fiberGroup g) ≤ (Fintype.card α).factorial := by
  have hi : Function.Injective (fun p : fiberGroup f × fiberGroup g => p.1.1*p.2.1) := by
    intro p q hpq
    dsimp only at hpq
    have he : p.1.1⁻¹*q.1.1 = p.2.1*q.2.1⁻¹ := by
      apply inv_mul_eq_iff_eq_mul.mpr
      rw [←mul_assoc,hpq,mul_assoc,mul_inv_cancel,mul_one]
    have hf : p.1.1⁻¹*q.1.1 ∈ fiberGroup f := (fiberGroup f).mul_mem ((fiberGroup f).inv_mem p.1.2) q.1.2
    have hg : p.1.1⁻¹*q.1.1 ∈ fiberGroup g := he ▸ (fiberGroup g).mul_mem p.2.2 ((fiberGroup g).inv_mem q.2.2)
    have h1 : p.1.1⁻¹*q.1.1 = 1 := by
      apply Equiv.ext
      intro x
      exact hinj _ x (hf x) (hg x)
    have hpf : p.1=q.1 := Subtype.ext (inv_mul_eq_one.mp h1)
    have hpg : p.2=q.2 := by
      apply Subtype.ext
      have hh := hpq
      rw [show p.1.1=q.1.1 from congrArg Subtype.val hpf] at hh
      exact mul_left_cancel hh
    exact Prod.ext hpf hpg
  have hc := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_prod,Fintype.card_perm] using hc

end FiberGroup

noncomputable def rowGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) :=
  fiberGroup (rowIndex (μ := μ))

noncomputable def colIndex {μ : YoungDiagram} (x : Cell μ) : Fin (μ.rowLen 0) :=
  ⟨col x, (YoungDiagram.mem_iff_lt_rowLen.mp x.2).trans_le (μ.rowLen_anti 0 (row x) (Nat.zero_le _))⟩

lemma colGroup_eq (μ : YoungDiagram) : colGroup μ = fiberGroup (colIndex (μ := μ)) := by
  ext p
  constructor
  · intro hp x; exact Fin.ext (hp x)
  · intro hp x; exact congrArg Fin.val (hp x)

noncomputable instance tabloidMulAction (μ : YoungDiagram) : MulAction (Equiv.Perm (Cell μ)) (Tabloid μ) where
  smul p f := tabloidAct p f
  one_smul f := by change tabloidAct 1 f = f; rw [tabloidAct_one]; rfl
  mul_smul p q f := by change tabloidAct (p*q) f = tabloidAct p (tabloidAct q f); rw [tabloidAct_mul]; rfl

lemma tabloid_orbit_all (μ : YoungDiagram) :
    MulAction.orbit (Equiv.Perm (Cell μ)) (baseTabloid μ) = Set.univ := by
  ext f
  simp only [Set.mem_univ,iff_true]
  obtain ⟨p,hp⟩ := tabloidAct_transitive μ (baseTabloid μ) f
  exact ⟨p,hp⟩

lemma tabloid_stabilizer (μ : YoungDiagram) :
    MulAction.stabilizer (Equiv.Perm (Cell μ)) (baseTabloid μ) = rowGroup μ := by
  ext p
  change tabloidAct p (baseTabloid μ) = baseTabloid μ ↔ ∀ x, rowIndex (p x) = rowIndex x
  constructor
  · intro h x
    have hh := congrArg (fun f : Tabloid μ => f.1 (p x)) h
    simpa only [tabloidAct_apply,baseTabloid,Equiv.Perm.inv_def,Equiv.symm_apply_apply] using hh.symm
  · intro h
    apply Subtype.ext
    funext x
    exact (h (p⁻¹ x)).symm.trans (by simp [baseTabloid])

lemma card_tabloid_mul_row (μ : YoungDiagram) :
    Fintype.card (Tabloid μ)*Fintype.card (rowGroup μ) = μ.card.factorial := by
  have hh := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (Equiv.Perm (Cell μ)) (baseTabloid μ)
  have hc : Fintype.card (MulAction.orbit (Equiv.Perm (Cell μ)) (baseTabloid μ)) =
      Fintype.card (Tabloid μ) := by
    rw [tabloid_orbit_all,Fintype.card_setUniv]
  simpa only [hc,tabloid_stabilizer,Fintype.card_perm,card_cell] using hh

theorem factorial_le_dimension_row_column (μ : YoungDiagram) :
    μ.card.factorial ≤ Module.finrank ℂ (space μ)*Fintype.card (rowGroup μ)*Fintype.card (colGroup μ) := by
  rw [←card_tabloid_mul_row]
  nlinarith [dimension_times_column_ge_tabloids μ]


lemma card_row_fiber (μ : YoungDiagram) (i : Fin (μ.colLen 0)) :
    Fintype.card {x : Cell μ // rowIndex x = i} = μ.rowLen i := by
  let e : {x : Cell μ // rowIndex x = i} ≃ {x : Cell μ // row x = i} :=
    Equiv.subtypeEquivRight (fun x => Fin.ext_iff)
  rw [Fintype.card_congr e,Fintype.card_congr (rowEquiv μ i),Fintype.card_fin]

lemma card_col_fiber (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) :
    Fintype.card {x : Cell μ // colIndex x = j} = μ.colLen j := by
  let e : {x : Cell μ // colIndex x = j} ≃ {x : Cell μ // col x = j} :=
    Equiv.subtypeEquivRight (fun x => Fin.ext_iff)
  rw [Fintype.card_congr e,Fintype.card_congr (columnEquiv μ j),Fintype.card_fin]

lemma card_rowGroup (μ : YoungDiagram) :
    Fintype.card (rowGroup μ) = ∏ i : Fin (μ.colLen 0), (μ.rowLen i).factorial := by
  rw [←Nat.card_eq_fintype_card,rowGroup,nat_card_fiberGroup]
  simp only [Nat.card_eq_fintype_card]
  simp only [card_row_fiber]

lemma card_colGroup (μ : YoungDiagram) :
    Fintype.card (colGroup μ) = ∏ j : Fin (μ.rowLen 0), (μ.colLen j).factorial := by
  rw [←Nat.card_eq_fintype_card,colGroup_eq,nat_card_fiberGroup]
  simp only [Nat.card_eq_fintype_card,card_col_fiber]

abbrev TailCell (μ : YoungDiagram) := {x : Cell μ // row x ≠ 0}

lemma tail_card (μ : YoungDiagram) : Fintype.card (TailCell μ) = μ.card - μ.rowLen 0 := by
  have hh := Fintype.card_subtype_compl (p := fun x : Cell μ => row x=0)
  rw [Fintype.card_congr (rowEquiv μ 0),Fintype.card_fin,card_cell] at hh
  exact hh

lemma rowLen_zero_le_card (μ : YoungDiagram) : μ.rowLen 0 ≤ μ.card := by
  have h := Fintype.card_subtype_le (fun x : Cell μ => row x=0)
  rwa [Fintype.card_congr (rowEquiv μ 0),Fintype.card_fin,card_cell] at h

noncomputable def tailColumnEquiv (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) :
    {x : TailCell μ // colIndex x.1 = j} ≃ Fin (μ.colLen j-1) where
  toFun x := ⟨row x.1.1-1, by
    have hx := row_lt_colLen x.1.1
    have hc : col x.1.1 = j := congrArg Fin.val x.2
    rw [hc] at hx
    have hz := x.1.2
    omega⟩
  invFun i := ⟨⟨⟨(i+1,j),YoungDiagram.mem_iff_lt_colLen.mpr (by omega)⟩,by simp [row]⟩,rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change row x.1.1 - 1 + 1 = row x.1.1
      have := x.1.2
      omega
    · exact (congrArg Fin.val x.2).symm
  right_inv i := by apply Fin.ext; simp [row]

lemma card_tail_col (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) :
    Fintype.card {x : TailCell μ // colIndex x.1 = j} = μ.colLen j-1 := by
  rw [Fintype.card_congr (tailColumnEquiv μ j),Fintype.card_fin]

lemma card_tail_row (μ : YoungDiagram) (i : Fin (μ.colLen 0)) :
    Fintype.card {x : TailCell μ // rowIndex x.1 = i} = if i.val=0 then 0 else μ.rowLen i := by
  by_cases hi : i.val=0
  · rw [ite_eq_left hi]
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun x => x.1.2 ?_⟩
    exact (congrArg Fin.val x.2).trans hi
  · rw [ite_eq_right hi]
    let e : {x : TailCell μ // rowIndex x.1 = i} ≃ {x : Cell μ // rowIndex x=i} :=
      { toFun := fun x => ⟨x.1.1,x.2⟩
        invFun := fun x => ⟨⟨x.1,fun hz => hi ((congrArg Fin.val x.2).symm.trans hz)⟩,x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rw [Fintype.card_congr e,card_row_fiber]

lemma tail_row_group (μ : YoungDiagram) :
    (μ.rowLen 0).factorial * Fintype.card (fiberGroup (fun x : TailCell μ => rowIndex x.1)) =
      Fintype.card (rowGroup μ) := by
  rw [←Nat.card_eq_fintype_card (α := fiberGroup (fun x : TailCell μ => rowIndex x.1)),nat_card_fiberGroup,card_rowGroup]
  simp only [Nat.card_eq_fintype_card]
  simp only [card_tail_row]
  by_cases hn : μ.colLen 0=0
  · have hr : μ.rowLen 0=0 := by
      by_contra h
      have hmem : (0,0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)
      have hh := YoungDiagram.mem_iff_lt_colLen.mp hmem
      omega
    let : IsEmpty (Fin (μ.colLen 0)) := ⟨fun i => by have := i.isLt; omega⟩
    simp [hr]
  · let z : Fin (μ.colLen 0) := ⟨0,Nat.pos_of_ne_zero hn⟩
    have hz : ∀ i : Fin (μ.colLen 0), i.val=0 ↔ i=z := fun i => by simp [z,Fin.ext_iff]
    simp only [hz]
    have hprod : (∏ x : Fin (μ.colLen 0), (if x=z then 0 else μ.rowLen x).factorial) =
        ∏ x ∈ Finset.univ.erase z, (μ.rowLen x).factorial := by
      rw [←Finset.prod_erase_mul Finset.univ (fun x : Fin (μ.colLen 0) => (if x=z then 0 else μ.rowLen x).factorial) (Finset.mem_univ z)]
      simp only [ite_true,Nat.factorial_zero,mul_one]
      apply Finset.prod_congr rfl
      intro x hx
      rw [ite_eq_right (Finset.mem_erase.mp hx).1]
    rw [hprod]
    exact Finset.mul_prod_erase Finset.univ (fun i : Fin (μ.colLen 0) => (μ.rowLen i).factorial) (Finset.mem_univ z)

lemma sum_tail_columns (μ : YoungDiagram) :
    ∑ j : Fin (μ.rowLen 0), (μ.colLen j-1) = μ.card-μ.rowLen 0 := by
  simp_rw [←card_tail_col]
  rw [←Fintype.card_sigma,Fintype.card_congr (Equiv.sigmaFiberEquiv (fun x : TailCell μ => colIndex x.1)),tail_card]

lemma column_pos (μ : YoungDiagram) (j : Fin (μ.rowLen 0)) : 0 < μ.colLen j :=
  YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt)

lemma nat_le_two_pow_pred (n : ℕ) (hn : 0<n) : n ≤ 2^(n-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [Nat.add_one_sub_one]
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

lemma column_group_le_tail (μ : YoungDiagram) :
    Fintype.card (colGroup μ) ≤ 2^(μ.card-μ.rowLen 0) *
      Fintype.card (fiberGroup (fun x : TailCell μ => colIndex x.1)) := by
  rw [card_colGroup,←Nat.card_eq_fintype_card (α := fiberGroup (fun x : TailCell μ => colIndex x.1)),nat_card_fiberGroup]
  simp only [Nat.card_eq_fintype_card]
  simp only [card_tail_col]
  calc
    _ = ∏ j : Fin (μ.rowLen 0), μ.colLen j * (μ.colLen j-1).factorial := by
      apply Finset.prod_congr rfl
      intro j hj
      exact (Nat.mul_factorial_pred (column_pos μ j).ne').symm
    _ ≤ ∏ j : Fin (μ.rowLen 0), 2^(μ.colLen j-1) * (μ.colLen j-1).factorial := by
      apply Finset.prod_le_prod
      intro j hj
      exact Nat.mul_le_mul_right _ (nat_le_two_pow_pred _ (column_pos μ j))
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,sum_tail_columns]

theorem choose_tail_le_dimension (μ : YoungDiagram) :
    μ.card.choose (μ.card-μ.rowLen 0) ≤ Module.finrank ℂ (space μ) * 2^(μ.card-μ.rowLen 0) := by
  let j := μ.card-μ.rowLen 0
  have htail := card_fiberGroups_mul_le
    (fun x : TailCell μ => rowIndex x.1) (fun x : TailCell μ => colIndex x.1)
    (fun x y hr hc => Subtype.ext (Subtype.ext (Prod.ext (congrArg Fin.val hr) (congrArg Fin.val hc))))
  rw [tail_card] at htail
  have hc := column_group_le_tail μ
  have hr := tail_row_group μ
  have hd := factorial_le_dimension_row_column μ
  simp only [←Nat.card_eq_fintype_card] at htail hc hr hd
  have hh : μ.card.factorial ≤ Module.finrank ℂ (space μ) * 2^j *
      ((μ.rowLen 0).factorial * j.factorial) := by
    calc
      _ ≤ _ := hd
      _ ≤ Module.finrank ℂ (space μ) * Nat.card (rowGroup μ) *
          (2^j * Nat.card (fiberGroup (fun x : TailCell μ => colIndex x.1))) := Nat.mul_le_mul_left _ hc
      _ = Module.finrank ℂ (space μ) * 2^j * (μ.rowLen 0).factorial *
          (Nat.card (fiberGroup (fun x : TailCell μ => rowIndex x.1)) *
           Nat.card (fiberGroup (fun x : TailCell μ => colIndex x.1))) := by rw [←hr]; ring
      _ ≤ _ := by
        calc
          _ ≤ Module.finrank ℂ (space μ) * 2^j * (μ.rowLen 0).factorial * j.factorial :=
            Nat.mul_le_mul_left _ htail
          _ = _ := by ring
  have hj : j ≤ μ.card := Nat.sub_le _ _
  have hs : μ.card-j = μ.rowLen 0 := by dsimp [j]; have := rowLen_zero_le_card μ; omega
  have hf := Nat.choose_mul_factorial_mul_factorial hj
  rw [hs] at hf
  rw [←hf] at hh
  have hpos : 0 < (μ.rowLen 0).factorial * j.factorial := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  nlinarith


lemma exists_perm_mem_iff {α : Type*} [Fintype α] (s t : Finset α) (hc : s.card=t.card) :
    ∃ p : Equiv.Perm α, ∀ x, p x ∈ t ↔ x ∈ s := by
  let e : s ≃ t := Finset.equivOfCardEq hc
  let ec : {x : α // x ∉ s} ≃ {x : α // x ∉ t} := Fintype.equivOfCardEq (by
    simp only [Fintype.card_subtype_compl,Fintype.card_coe,hc])
  let p := (Equiv.sumCompl (· ∈ s)).symm.trans ((Equiv.sumCongr e ec).trans (Equiv.sumCompl (· ∈ t)))
  refine ⟨p,fun x => ?_⟩
  by_cases hx : x ∈ s
  · have hp : p x ∈ t := by
      change ((Equiv.sumCompl (· ∈ t)) ((Equiv.sumCongr e ec) ((Equiv.sumCompl (· ∈ s)).symm x))) ∈ t
      rw [Equiv.sumCompl_symm_apply_of_pos hx]
      exact (e ⟨x,hx⟩).2
    exact iff_of_true hp hx
  · have hp : p x ∉ t := by
      change ((Equiv.sumCompl (· ∈ t)) ((Equiv.sumCongr e ec) ((Equiv.sumCompl (· ∈ s)).symm x))) ∉ t
      rw [Equiv.sumCompl_symm_apply_of_neg hx]
      exact (ec ⟨x,hx⟩).2
    exact iff_of_false hp hx

noncomputable def tailSet {μ : YoungDiagram} (f : Tabloid μ) : Finset (Cell μ) :=
  Finset.univ.filter (fun x => (f.1 x).val ≠ 0)

@[simp] lemma mem_tailSet {μ : YoungDiagram} (f : Tabloid μ) (x : Cell μ) :
    x ∈ tailSet f ↔ (f.1 x).val ≠ 0 := by simp [tailSet]

lemma tailSet_act {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) (f : Tabloid μ) :
    tailSet (tabloidAct p f) = (tailSet f).image p := by
  ext x
  simp only [mem_tailSet,tabloidAct_apply,Finset.mem_image]
  constructor
  · intro h; exact ⟨p⁻¹ x,h,by simp⟩
  · rintro ⟨y,hy,rfl⟩; simpa using hy

lemma card_tailSet {μ : YoungDiagram} (f : Tabloid μ) :
    (tailSet f).card = μ.card-μ.rowLen 0 := by
  obtain ⟨p,rfl⟩ := tabloidAct_transitive μ (baseTabloid μ) f
  rw [tailSet_act,Finset.card_image_of_injective _ p.injective]
  change (Finset.univ.filter (fun x : Cell μ => row x ≠ 0)).card = _
  rw [←Fintype.card_subtype]
  exact tail_card μ

noncomputable def footprint (μ : YoungDiagram) (A : Finset (Cell μ)) : Finset (Tabloid μ) :=
  Finset.univ.filter (fun f => tailSet f ⊆ A)

lemma tail_fiber_card_eq (μ : YoungDiagram) (s t : Finset (Cell μ)) (hst : s.card=t.card) :
    (Finset.univ.filter (fun f : Tabloid μ => tailSet f=s)).card =
      (Finset.univ.filter (fun f : Tabloid μ => tailSet f=t)).card := by
  obtain ⟨p,hp⟩ := exists_perm_mem_iff s t hst
  have he : s.image p=t := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (hp y).mpr hy
    · intro hx
      exact Finset.mem_image.mpr ⟨p⁻¹ x,(hp (p⁻¹ x)).mp (by simpa using hx),by simp⟩
  apply Finset.card_equiv (tabloidAct p)
  intro f
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,tailSet_act,←he]
  exact (Finset.image_inj p.injective).symm

lemma footprint_card_product (μ : YoungDiagram) (A : Finset (Cell μ)) :
    (footprint μ A).card * μ.card.choose (μ.card-μ.rowLen 0) =
      Fintype.card (Tabloid μ) * A.card.choose (μ.card-μ.rowLen 0) := by
  let j := μ.card-μ.rowLen 0
  let s := tailSet (baseTabloid μ)
  let c := (Finset.univ.filter (fun f : Tabloid μ => tailSet f=s)).card
  have hconstant (t : Finset (Cell μ)) (ht : t.card=j) :
      (Finset.univ.filter (fun f : Tabloid μ => tailSet f=t)).card = c :=
    tail_fiber_card_eq μ t s (ht.trans (card_tailSet _).symm)
  have hcount (A : Finset (Cell μ)) : (footprint μ A).card = A.card.choose j*c := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Tabloid μ)) (A.powersetCard j) tailSet
    have he : (Finset.univ.filter (fun f : Tabloid μ => tailSet f ∈ A.powersetCard j)) = footprint μ A := by
      ext f
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powersetCard,
        card_tailSet,footprint]
      simp [j]
    rw [he] at h
    rw [←h]
    calc
      _ = ∑ _t ∈ A.powersetCard j, c := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hconstant t (Finset.mem_powersetCard.mp ht).2
      _ = _ := by simp [Finset.card_powersetCard]
  have hfull : (footprint μ Finset.univ).card = Fintype.card (Tabloid μ) := by
    simp only [footprint,Finset.subset_univ,Finset.filter_true,Finset.card_univ]
  have hN := hcount Finset.univ
  rw [hfull,Finset.card_univ,card_cell] at hN
  rw [hcount,hN]
  ring

lemma footprint_fixed {μ : YoungDiagram} (A : Finset (Cell μ))
    (f : Tabloid μ) (hf : f ∈ footprint μ A) (p : Equiv.Perm (Cell μ))
    (hp : ∀ x ∈ A, p x=x) : tabloidAct p f=f := by
  have htail : tailSet f ⊆ A := (Finset.mem_filter.mp hf).2
  apply Subtype.ext
  funext x
  change f.1 (p⁻¹ x) = f.1 x
  by_cases hx : x ∈ A
  · rw [show p⁻¹ x=x from p.injective (by simpa using (hp x hx).symm)]
  · have hy : p⁻¹ x ∉ A := by
      intro h
      have hh := hp (p⁻¹ x) h
      have he : x=p⁻¹ x := by simpa using hh
      exact hx (he ▸ h)
    apply Fin.ext
    have hx0 : (f.1 x).val=0 := by by_contra h; exact hx (htail (mem_tailSet f x |>.mpr h))
    have hy0 : (f.1 (p⁻¹ x)).val=0 := by by_contra h; exact hy (htail (mem_tailSet f _ |>.mpr h))
    exact hy0.trans hx0.symm

noncomputable def fixedHilbert (μ : YoungDiagram) (A : Finset (Cell μ)) :
    Submodule ℂ (PermutationHilbert.H (Tabloid μ)) where
  carrier := {v | v ∈ hilbertSpace μ ∧ ∀ p : Equiv.Perm (Cell μ),
    (∀ x ∈ A, p x=x) → PermutationHilbert.act (tabloidAct p) v=v}
  zero_mem' := ⟨Submodule.zero_mem _,fun p hp => map_zero _⟩
  add_mem' := fun hv hw => ⟨Submodule.add_mem _ hv.1 hw.1,fun p hp => by
    rw [map_add,hv.2 p hp,hw.2 p hp]⟩
  smul_mem' := fun c v hv => ⟨Submodule.smul_mem _ c hv.1,fun p hp => by
    rw [map_smul,hv.2 p hp]⟩

lemma fixedHilbert_le (μ : YoungDiagram) (A : Finset (Cell μ)) : fixedHilbert μ A ≤ hilbertSpace μ :=
  fun _ hv => hv.1

theorem fixedHilbert_dimension (μ : YoungDiagram) (A : Finset (Cell μ)) :
    Module.finrank ℂ (space μ) * A.card.choose (μ.card-μ.rowLen 0) ≤
      Module.finrank ℂ (fixedHilbert μ A) * μ.card.choose (μ.card-μ.rowLen 0) := by
  let : DecidableEq (Tabloid μ) := Classical.decEq _
  have ht (f g : Tabloid μ) : ∃ p : Equiv.Perm (Tabloid μ), p f=g ∧
      (hilbertSpace μ).map (PermutationHilbert.act p).toLinearEquiv.toLinearMap = hilbertSpace μ := by
    obtain ⟨p,hp⟩ := tabloidAct_transitive μ f g
    exact ⟨tabloidAct p,hp,hilbertSpace_invariant μ p⟩
  have hproj (f : Tabloid μ) (hf : f ∈ footprint μ A) :
      (hilbertSpace μ).starProjection (EuclideanSpace.single f (1:ℂ)) ∈ fixedHilbert μ A := by
    refine ⟨((hilbertSpace μ).orthogonalProjectionOnto _).2,fun p hp => ?_⟩
    rw [PermutationHilbert.projection_comm _ _ (hilbertSpace_invariant μ p),
      PermutationHilbert.act_single,footprint_fixed A f hf p hp]
  have h := PermutationHilbert.footprint_dimension (hilbertSpace μ) (fixedHilbert μ A)
    (fixedHilbert_le μ A) ht (footprint μ A) hproj
  rw [finrank_hilbertSpace] at h
  have hn : (footprint μ A).card * Module.finrank ℂ (space μ) ≤
      Fintype.card (Tabloid μ)*Module.finrank ℂ (fixedHilbert μ A) := by exact_mod_cast h
  have hc := footprint_card_product μ A
  have hpos : 0 < Fintype.card (Tabloid μ) := Fintype.card_pos_iff.mpr ⟨baseTabloid μ⟩
  have hh := Nat.mul_le_mul_right (μ.card.choose (μ.card-μ.rowLen 0)) hn
  nlinarith

end Thorp.Specht

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

def IsUnitary (ρ : Representation ℂ G V) : Prop :=
  ∀ g v w, inner ℂ (ρ g v) (ρ g w) = inner ℂ v w

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_inner_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) (v w : V) :
    inner ℂ v (ρ g⁻¹ w) = inner ℂ (ρ g v) w := by
  have h := hρ g v (ρ g⁻¹ w)
  have he : ρ g (ρ g⁻¹ w) = w := by
    change (ρ g * ρ g⁻¹) w = w
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl
  rw [he] at h
  exact h.symm

noncomputable def averageMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A : V →ₗ[ℂ] W) : Representation.IntertwiningMap ρ σ where
  toLinearMap := ∑ g, (σ g).comp (A.comp (ρ g⁻¹))
  isIntertwining' h := by
    ext v
    simp only [LinearMap.comp_apply,LinearMap.sum_apply,map_sum]
    apply Fintype.sum_equiv (Equiv.mulLeft h⁻¹)
    intro g
    simp only [Equiv.coe_mulLeft,mul_inv_rev,inv_inv,map_mul,Module.End.mul_apply]
    have hh (w : W) : σ h (σ h⁻¹ w)=w := by
      change (σ h*σ h⁻¹) w=w
      rw [←map_mul,mul_inv_cancel,map_one]
      rfl
    rw [hh]

end Thorp.UnitaryFinite

end ThorpNine.Tail

end OAI
