import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.FlatAtlas
import OAI.Combinatorics.RamseyFive.Entropy.MetadataBudget
import OAI.Combinatorics.RamseyFive.Geometry.FlatPoints
import OAI.Combinatorics.RamseyFive.Decoding.PublicTraining

namespace OAI

namespace SharpRamseyFive.Metadata

section
open Module GreedyTraining MeasurePublicTable ProjectiveTraining
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)]

omit [FiniteDimensional K V] [Finite K] in
lemma projective_card_le_vectors [Finite V] (S : Finset (ℙ K V)) : S.card≤Nat.card V := by
  have hi : Function.Injective (fun x : ℙ K V=>x.rep) := by
    intro x y h
    rw [←x.mk_rep,←y.mk_rep]
    congr 1
  have hS : S.card≤Nat.card (ℙ K V) := by
    simpa only [Nat.card_eq_fintype_card] using Finset.card_le_univ S
  exact hS.trans (Nat.card_le_card_of_injective _ hi)

noncomputable def encodeLists {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) : TwoListCode V h p B :=
  (fun i=>FlatAtlas.flatCode 5 hd (H i), fun i=>FlatAtlas.flatCode 5 hd (P i),
    ⟨S.card,Nat.lt_succ_of_le hB⟩,
    fun i=>⟨(S∩publicRegion (fun j=>flatPoints (H j)) i).card,
      Nat.lt_succ_of_le ((Finset.card_le_card Finset.inter_subset_left).trans hB)⟩,
    fun i=>⟨(S∩publicRegion (fun j=>flatPoints (P j)) i).card,
      Nat.lt_succ_of_le ((Finset.card_le_card Finset.inter_subset_left).trans hB)⟩,
    fun i=>⟨((S∩publicRegion (fun j=>flatPoints (H j)) i.1)∩
      (S∩publicRegion (fun j=>flatPoints (P j)) i.2)).card,
      Nat.lt_succ_of_le ((Finset.card_le_card (Finset.inter_subset_left.trans Finset.inter_subset_left)).trans hB)⟩)

noncomputable def decodeH {h p B : ℕ} (c : TwoListCode V h p B) : Fin h→Finset (ℙ K V) :=
  fun i=>flatPoints (Submodule.span K (Set.range (c.1 i)))
noncomputable def decodeP {h p B : ℕ} (c : TwoListCode V h p B) : Fin p→Finset (ℙ K V) :=
  fun i=>flatPoints (Submodule.span K (Set.range (c.2.1 i)))
noncomputable def decodeOwn {h p B : ℕ} (c : TwoListCode V h p B) (x : ℙ K V) : Finset (ℙ K V) :=
  twoPublicOwn (decodeH c) (decodeP c) x

noncomputable def decodeOwnCount {h p B : ℕ} (c : TwoListCode V h p B) (x : ℙ K V) : ℕ :=
  let ih := firstIndex {F | x∈F} (decodeH c)
  let ip := firstIndex {F | x∈F} (decodeP c)
  (ih.elim 0 (fun i=>(c.2.2.2.1 i).val))+
    (ip.elim 0 (fun i=>(c.2.2.2.2.1 i).val))-
      (ih.elim 0 (fun i=>ip.elim 0 (fun j=>(c.2.2.2.2.2 (i,j)).val)))

omit [Fintype (ℙ K V)]

lemma decodeH_encode {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) :
    decodeH (encodeLists hd H P S hB)=fun i=>flatPoints (H i) := by
  funext i
  exact congrArg flatPoints (FlatAtlas.decode_flatCode 5 hd (H i))
lemma decodeP_encode {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) :
    decodeP (encodeLists hd H P S hB)=fun i=>flatPoints (P i) := by
  funext i
  exact congrArg flatPoints (FlatAtlas.decode_flatCode 5 hd (P i))

lemma decodeOwn_encode {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) (x : ℙ K V) :
    decodeOwn (encodeLists hd H P S hB) x=
      twoPublicOwn (fun i=>flatPoints (H i)) (fun i=>flatPoints (P i)) x := by
  simp only [decodeOwn,decodeH_encode,decodeP_encode]

theorem decodeOwnCount_encode {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) (x : ℙ K V) :
    decodeOwnCount (encodeLists hd H P S hB) x=
      (S∩twoPublicOwn (fun i=>flatPoints (H i)) (fun i=>flatPoints (P i)) x).card := by
  simp only [decodeOwnCount,decodeH_encode,decodeP_encode,twoPublicOwn,publicOwn,
    Finset.inter_union_distrib_left]
  cases hh : firstIndex {F | x∈F} (fun i=>flatPoints (H i)) <;>
    cases hp : firstIndex {F | x∈F} (fun i=>flatPoints (P i)) <;>
    simp [encodeLists,Finset.card_union]

noncomputable def decodeBaseScore {h p B : ℕ} (c : TwoListCode V h p B) (L : ℝ) (x : ℙ K V) : ℝ :=
  Real.exp (-L*(1-(decodeOwnCount c x:ℝ)/c.2.2.1.val))

lemma decodeBaseScore_encode {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) (L : ℝ) (x : ℙ K V) :
    decodeBaseScore (encodeLists hd H P S hB) L x=
      Real.exp (-L*(1-((S∩twoPublicOwn (fun i=>flatPoints (H i))
        (fun i=>flatPoints (P i)) x).card:ℝ)/S.card)) := by
  simp only [decodeBaseScore,decodeOwnCount_encode]
  rfl

end

open Module GreedyTraining ProjectiveTraining
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype V] [Fintype (ℙ K V)]

omit [Fintype V] [Fintype (ℙ K V)] in
lemma vector_card_le_exp (σ : ℝ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5) :
    (Nat.card V:ℝ)≤Real.exp (5*σ) := by
  have hq1 : 1≤Nat.card K := Nat.card_pos
  have hh : Nat.card V≤Nat.card K^5 := by
    rw [Module.natCard_eq_pow_finrank (K:=K)]
    exact Nat.pow_le_pow_right hq1 hd
  have he : (Nat.card K:ℝ)^5=Real.exp (5*σ) := by
    rw [←hq,←Real.exp_nat_mul];norm_num
  exact (by exact_mod_cast hh : (Nat.card V:ℝ)≤(Nat.card K:ℝ)^5).trans_eq he

noncomputable def encodeTraining {h p : ℕ} (σ : ℝ) (hd : finrank K V≤5)
    (hh : h≤listCap σ) (hp : p≤listCap σ) (hj : h*p≤productCap σ)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V) (S : Finset (ℙ K V)) :
    TrainingCode V (listCap σ) (productCap σ) (Nat.card V) :=
  ⟨⟨(⟨h,Nat.lt_succ_of_le hh⟩,⟨p,Nat.lt_succ_of_le hp⟩),hj⟩,
    encodeLists hd H P S (projective_card_le_vectors S)⟩

noncomputable def messageOwn {H J B : ℕ} (c : TrainingCode V H J B) (x : ℙ K V) : Finset (ℙ K V) :=
  decodeOwn c.2 x
noncomputable def messageBase {H J B : ℕ} (c : TrainingCode V H J B) (L : ℝ) (x : ℙ K V) : ℝ :=
  decodeBaseScore c.2 L x

theorem training_message {h p : ℕ} (σ g : ℝ) (hd : finrank K V≤5)
    (hσ : 100000≤σ) (hq : Real.exp σ=Nat.card K)
    (hg : 0≤g) (hghi : g≤σ+Real.log 4)
    (hlen : (h:ℝ)*Real.exp (2*σ)≤Real.exp (3*σ/2+g))
    (plen : (p:ℝ)*Real.exp (σ+17*g/15)≤Real.exp (3*σ/2+g))
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V) (S : Finset (ℙ K V)) :
    Real.log (Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V)))≤Nat.card K ∧
    ∃c : TrainingCode V (listCap σ) (productCap σ) (Nat.card V),
      (∀x,messageOwn c x=twoPublicOwn (fun i=>flatPoints (H i)) (fun i=>flatPoints (P i)) x) ∧
      (∀L x,messageBase c L x=Real.exp (-L*(1-((S∩twoPublicOwn (fun i=>flatPoints (H i))
        (fun i=>flatPoints (P i)) x).card:ℝ)/S.card))) := by
  obtain ⟨hh,hp,hj⟩ := profile_of_lengths σ g h p hg hghi hlen plen
  refine ⟨?_,encodeTraining σ hd hh hp hj H P S,?_,?_⟩
  · rw [←hq]
    exact log_card_training_le σ hσ (vector_card_le_exp σ hq hd)
  · intro x
    exact decodeOwn_encode hd H P S (projective_card_le_vectors S) x
  · intro L x
    exact decodeBaseScore_encode hd H P S (projective_card_le_vectors S) L x

end SharpRamseyFive.Metadata

end OAI
