import OAI.Probability.CubeShuffle.ShapeSpectral
import OAI.RepresentationTheory.FiniteUnitary.Fourier

namespace OAI

namespace CubeShuffle.Specht
open scoped BigOperators Classical
open UnitaryFinite

noncomputable def cardLabels (d : ℕ) (μ : Shapes (2^d)) : Card d ≃ Cell μ.1 :=
  ((Fintype.equivFin (Card d)).trans (finCongr (card_positions d))).trans (labels μ).symm

noncomputable def cardRepresentation (d : ℕ) (μ : Shapes (2^d)) :
    Representation ℂ (Equiv.Perm (Card d)) (hilbertSpace μ.1) :=
  relabelledUnitary μ.1 (cardLabels d μ)

lemma cardRepresentation_unitary (d : ℕ) (μ : Shapes (2^d)) :
    IsUnitary (V := hilbertSpace μ.1) (cardRepresentation d μ) :=
  relabelledUnitary_unitary _ _

noncomputable instance cardRepresentation_irreducible (d : ℕ) (μ : Shapes (2^d)) :
    Representation.IsIrreducible (cardRepresentation d μ) :=
  relabelledUnitary_irreducible _ _

lemma relabelledUnitary_neq {α : Type*} (μ ν : YoungDiagram)
    (e : α ≃ Cell μ) (f : α ≃ Cell ν)
    (T : Representation.Equiv (relabelledUnitary μ e) (relabelledUnitary ν f)) : μ=ν := by
  let S := (spaceHilbertEquiv μ).trans (T.toLinearEquiv.trans (spaceHilbertEquiv ν).symm)
  apply shapes_eq_of_equivariant_equiv μ ν (e.symm.trans f) S
  intro p v
  have hT := Representation.IntertwiningMap.isIntertwining _ _ T.toIntertwiningMap
    (e.symm.permCongr p) (spaceHilbertEquiv μ v)
  change T.toLinearEquiv (spaceHilbertEquiv μ
    (representation μ (e.permCongr (e.symm.permCongr p))
      ((spaceHilbertEquiv μ).symm (spaceHilbertEquiv μ v))))=
    spaceHilbertEquiv ν (representation ν (f.permCongr (e.symm.permCongr p))
      ((spaceHilbertEquiv ν).symm (T.toLinearEquiv (spaceHilbertEquiv μ v)))) at hT
  have he : e.permCongr (e.symm.permCongr p)=p := by
    apply Equiv.ext
    intro x
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,e.apply_symm_apply]
  have hf : f.permCongr (e.symm.permCongr p)=(e.symm.trans f).permCongr p := by
    apply Equiv.ext
    intro x
    rfl
  rw [he,hf,LinearEquiv.symm_apply_apply] at hT
  have ht := congrArg (spaceHilbertEquiv ν).symm hT
  simpa only [LinearEquiv.symm_apply_apply,S,LinearEquiv.trans_apply] using ht

lemma cardRepresentation_distinct (d : ℕ) (μ ν : Shapes (2^d)) (hne : μ≠ν) :
    ¬Nonempty (Representation.Equiv (cardRepresentation d μ) (cardRepresentation d ν)) := by
  rintro ⟨T⟩
  exact hne (Subtype.ext (relabelledUnitary_neq μ.1 ν.1 (cardLabels d μ) (cardLabels d ν) T))

lemma card_conjugacy_shapes (d : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Card d)))≤Fintype.card (Shapes (2^d)) := by
  have h := Nat.card_le_card_of_injective _ (conjugacyPartition_injective (α := Card d))
  simpa only [card_positions,Nat.card_eq_fintype_card,Fintype.card_congr (shapePartitionEquiv (2^d))] using h

lemma row_zero_of_full_row (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card) (x : Cell μ) : row x=0 := by
  have hr : μ.row 0=μ.cells := Finset.eq_of_subset_of_card_le
    (Finset.filter_subset _ _) (by rw [←μ.rowLen_eq_card]; exact hμ.ge)
  have hx : x.1∈μ.row 0 := by rw [hr]; exact x.2
  exact (YoungDiagram.mem_row_iff.mp hx).2

lemma tabloid_subsingleton_of_full_row (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card) :
    Subsingleton (Tabloid μ) := by
  refine ⟨fun f g => ?_⟩
  apply Subtype.ext
  funext x
  obtain ⟨p,hp⟩ := f.2
  obtain ⟨q,hq⟩ := g.2
  simp only [hp,hq,Function.comp_apply]
  apply Fin.ext
  exact (row_zero_of_full_row μ hμ (p x)).trans (row_zero_of_full_row μ hμ (q x)).symm

lemma representation_full_row (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card)
    (p : Equiv.Perm (Cell μ)) : representation μ p=1 := by
  let := tabloid_subsingleton_of_full_row μ hμ
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext f
  change v.1 (tabloidAct p⁻¹ f)=v.1 f
  rw [show tabloidAct p⁻¹ f=f from Subsingleton.elim _ _]

lemma relabelled_full_row {α : Type*} (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card)
    (e : α ≃ Cell μ) (p : Equiv.Perm α) : relabelledUnitary μ e p=1 := by
  change ((spaceHilbertEquiv μ).conjAlgEquiv ℂ) (representation μ (e.permCongr p))=1
  rw [representation_full_row μ hμ,map_one]

end CubeShuffle.Specht
namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical
variable {G Ω V : Type*} [Group G] [Fintype G] [Fintype Ω] [Nonempty Ω]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma sample_uniform_left (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ P*uniformOperator ρ=uniformOperator ρ := by
  rw [sampleOperator_weighted,weighted_uniform_left,sampleLaw_sum,one_smul]

lemma uniform_zero_of_sample_norm_lt_one (ρ : Representation ℂ G V) (P : Ω → G)
    (h : ‖sampleOperator ρ P‖<1) : uniformOperator ρ=0 := by
  have hn := norm_mul_le (sampleOperator ρ P) (uniformOperator ρ)
  rw [sample_uniform_left] at hn
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (uniformOperator ρ)]

omit [Fintype G] in
lemma sampleOperator_trivial (ρ : Representation ℂ G V) (hρ : ∀ g,ρ g=1) (P : Ω → G) :
    sampleOperator ρ P=1 := by
  convert sampleOperator_one (Ω := Ω) ρ using 1
  unfold sampleOperator
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  apply ContinuousLinearMap.ext
  intro v
  change ρ (P ω) v=ρ 1 v
  rw [hρ,hρ]

lemma uniformOperator_trivial (ρ : Representation ℂ G V) (hρ : ∀ g,ρ g=1) :
    uniformOperator ρ=1 := by
  rw [←sampleOperator_uniform]
  exact sampleOperator_trivial ρ hρ id

lemma weighted_sub (ρ : Representation ℂ G V) (p q : G → ℝ) :
    weightedOperator ρ (fun g => p g-q g)=weightedOperator ρ p-weightedOperator ρ q := by
  simp only [weightedOperator,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]

end CubeShuffle.UnitaryFinite

namespace CubeShuffle
open scoped BigOperators Classical
open UnitaryFinite
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma physical_palindrome_norm (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) :
    ‖sampleOperator ρ (run d d)‖^2=‖sampleOperator ρ (palindromePerm d)‖ := by
  rw [physical_sweep_adjoint d ρ hρ,sampleOperator_palindrome d ρ hρ]
  have h := ContinuousLinearMap.norm_adjoint_comp_self
    ((sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint)
  rw [ContinuousLinearMap.adjoint_adjoint] at h
  simpa only [ContinuousLinearMap.mul_def,←sq] using h.symm

lemma physical_power_bound (d C : ℕ) (hC : 0 < C) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) :
    ‖sampleOperator ρ (run d (C*d))‖^2≤‖sampleOperator ρ (palindromePerm d)‖^C := by
  have he : sampleOperator ρ (run d (C*d))=(sampleOperator ρ (run d d))^C := by
    simp only [sampleOperator_run,←pow_mul,Nat.mul_comm C d]
  rw [he,←physical_palindrome_norm d ρ hρ]
  calc
    _ ≤ (‖sampleOperator ρ (run d d)‖^C)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_pow_le' _ hC) _
    _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm C 2]

end CubeShuffle

end OAI
