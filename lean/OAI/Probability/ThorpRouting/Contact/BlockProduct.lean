import Mathlib
import OAI.Probability.ThorpRouting.Contact.Representative

namespace OAI

namespace ThorpNine.Contact

namespace Thorp.CommutingBlocks
open scoped BigOperators Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
variable (P : ι → V →L[ℂ] V) (hcomm : ∀ i j, Commute (P i) (P j))
include hcomm
omit [CompleteSpace V] [Fintype ι] in
lemma sector_sum (s : Finset ι) : ∑ E∈s.powerset, sector P hcomm s E=1 := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.powerset_empty,Finset.sum_singleton]
    exact Finset.noncommProd_empty _ _
  | @insert a s ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have h₁ (E : Finset ι) (hE : E∈s.powerset) :
        sector P hcomm (insert a s) E=P a*sector P hcomm s E := by
      rw [sector_insert P hcomm s E a ha]
      congr 1
      exact ite_eq_right (fun h => ha ((Finset.mem_powerset.mp hE) h))
    have h₂ (E : Finset ι) (_hE : E∈s.powerset) :
        sector P hcomm (insert a s) (insert a E)=(1-P a)*sector P hcomm s E := by
      rw [sector_insert P hcomm s (insert a E) a ha]
      simp only [choice,Finset.mem_insert_self,↓reduceIte]
      congr 1
      apply sector_congr
      intro i hi
      simp [ne_of_mem_of_not_mem hi ha]
    rw [Finset.sum_congr rfl h₁,Finset.sum_congr rfl h₂,
      ←Finset.mul_sum,←Finset.mul_sum,ih]
    simp

omit [Fintype ι] in
lemma sector_absorb_factor (s E : Finset ι) (i : ι) (hi : i∈s)
    (hP : ∀ i, IsStarProjection (P i)) :
    choice P E i*sector P hcomm s E=sector P hcomm s E := by
  have hc : IsIdempotentElem (choice P E i) := by
    unfold choice
    split_ifs
    · exact (hP i).one_sub.isIdempotentElem
    · exact (hP i).isIdempotentElem
  have hsplit := Finset.mul_noncommProd_erase s hi (choice P E)
    (fun i _ j _ _ => choice_commute P hcomm E E i j)
  change choice P E i*sector P hcomm s E=sector P hcomm s E
  change _=sector P hcomm s E at hsplit
  nth_rw 1 [←hsplit]
  rw [←mul_assoc,hc.eq,hsplit]

omit [Fintype ι] in
lemma sector_orthogonal (s E F : Finset ι) (hE : E⊆s) (hF : F⊆s) (hEF : E≠F)
    (hP : ∀ i, IsStarProjection (P i)) :
    sector P hcomm s E*sector P hcomm s F=0 := by
  have hdiff : ∃ i∈s, ¬(i∈E ↔ i∈F) := by
    by_contra h
    push Not at h
    exact hEF (Finset.ext fun i => by
      by_cases hi : i∈s
      · exact h i hi
      · exact iff_of_false (fun h => hi (hE h)) (fun h => hi (hF h)))
  obtain ⟨i,hi,hdiff⟩ := hdiff
  have hz : choice P E i*choice P F i=0 := by
    by_cases he : i∈E <;> by_cases hf : i∈F
    · exact (hdiff (iff_of_true he hf)).elim
    · simpa only [choice,ite_eq_left he,ite_eq_right hf] using (hP i).one_sub_mul_self
    · simpa only [choice,ite_eq_right he,ite_eq_left hf] using (hP i).mul_one_sub_self
    · exact (hdiff (iff_of_false he hf)).elim
  have hEi := sector_absorb_factor P hcomm s E i hi hP
  have hFi := sector_absorb_factor P hcomm s F i hi hP
  calc
    _ = sector P hcomm s E*(choice P E i*choice P F i)*sector P hcomm s F := by
      simp only [mul_assoc]
      rw [hFi]
      rw [←mul_assoc,(sector_factor_commute P hcomm s E E i).eq.symm,hEi]
    _ = 0 := by rw [hz,mul_zero,zero_mul]

noncomputable def blockProduct (A : ι → V →L[ℂ] V)
    (hA : ∀ i j, Commute (A i) (A j)) (s : Finset ι) : V →L[ℂ] V :=
  s.noncommProd A (fun i _ j _ _ => hA i j)

omit hcomm [Fintype ι] in
lemma norm_noncommProd_le (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (s : Finset ι) : ‖blockProduct A hA s‖≤∏ i∈s,‖A i‖ := by
  induction s using Finset.induction_on with
  | empty => exact ContinuousLinearMap.norm_id_le
  | @insert a s ha ih =>
    have he : blockProduct A hA (insert a s)=A a*blockProduct A hA s :=
      Finset.noncommProd_insert_of_notMem _ _ _ _ ha
    rw [he,Finset.prod_insert ha]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

noncomputable def blocks (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j)) : V →L[ℂ] V :=
  blockProduct A hA Finset.univ

omit hcomm in
lemma blocks_norm_le_one (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hn : ∀ i,‖A i‖≤1) : ‖blocks A hA‖≤1 :=
  (norm_noncommProd_le A hA Finset.univ).trans (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hn i))

omit [CompleteSpace V] in
lemma blocks_sector_commute (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hAP : ∀ i j, Commute (A i) (P j)) (E : Finset ι) :
    Commute (blocks A hA) (sector P hcomm Finset.univ E) := by
  unfold blocks blockProduct
  apply (Finset.noncommProd_commute _ _ (fun i _ j _ _ => hA i j) _ _).symm
  intro i _
  unfold sector
  apply (Finset.noncommProd_commute _ _ (fun i _ j _ _ => choice_commute P hcomm E E i j) _ _).symm
  intro j _
  unfold choice
  split_ifs
  · exact (Commute.one_right _).sub_right (hAP i j)
  · exact hAP i j

lemma blocks_sector_norm (hP : ∀ i, IsStarProjection (P i))
    (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hAP : ∀ i j, Commute (A i) (P j)) (hn : ∀ i,‖A i‖≤1)
    (θ : ℝ) (_hθ : 0≤θ) (hgap : ∀ i,‖A i*(1-P i)‖≤θ) (E : Finset ι) :
    ‖blocks A hA*sector P hcomm Finset.univ E‖≤θ^E.card := by
  have hAC (i j : ι) : Commute (A i) (choice P E j) := by
    unfold choice
    split_ifs
    · exact (Commute.one_right _).sub_right (hAP i j)
    · exact hAP i j
  have hprod := Finset.noncommProd_mul_distrib (s := Finset.univ) A (choice P E)
    (fun i _ j _ _ => hA i j) (fun i _ j _ _ => choice_commute P hcomm E E i j)
    (fun i _ j _ _ => (hAC j i).symm)
  change _=blocks A hA*sector P hcomm Finset.univ E at hprod
  rw [←hprod]
  have hc (i j : ι) : Commute ((A*choice P E) i) ((A*choice P E) j) :=
    ((hA i j).mul_right (hAC i j)).mul_left ((hAC j i).symm.mul_right (choice_commute P hcomm E E i j))
  apply (norm_noncommProd_le _ hc Finset.univ).trans
  calc
    _ ≤ ∏ i : ι, if i∈E then θ else 1 := by
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      intro i _
      dsimp only [Pi.mul_apply]
      unfold choice
      split_ifs with hi
      · exact hgap i
      · exact (norm_mul_le _ _).trans (by nlinarith [hn i,(hP i).norm_le (P i),norm_nonneg (A i),norm_nonneg (P i)])
    _ = _ := by rw [Fintype.prod_ite_mem,Finset.prod_const]

noncomputable def coarse (E : Finset ι) : V →L[ℂ] V :=
  Eᶜ.noncommProd P (fun i _ j _ _ => hcomm i j)

lemma coarse_projection (hP : ∀ i, IsStarProjection (P i)) (E : Finset ι) :
    IsStarProjection (coarse P hcomm E) := by
  have he : coarse P hcomm E=sector P hcomm Eᶜ ∅ := by
    apply Finset.noncommProd_congr rfl
    intro i _
    simp [choice]
  rw [he]
  exact sector_projection P hcomm hP _ _

lemma sector_coarse (hP : ∀ i, IsStarProjection (P i)) (E : Finset ι) :
    sector P hcomm Finset.univ E*coarse P hcomm E=sector P hcomm Finset.univ E := by
  have hpi (i : ι) (hi : i∈Eᶜ) : sector P hcomm Finset.univ E*P i=sector P hcomm Finset.univ E := by
    have h := sector_absorb_factor P hcomm Finset.univ E i (Finset.mem_univ i) hP
    rw [(sector_factor_commute P hcomm Finset.univ E E i).eq] at h
    simpa only [choice,ite_eq_right (Finset.mem_compl.mp hi)] using h
  have hp (s : Finset ι) (hs : ∀ i∈s,
      sector P hcomm Finset.univ E*P i=sector P hcomm Finset.univ E) :
      sector P hcomm Finset.univ E*blockProduct P hcomm s=sector P hcomm Finset.univ E := by
    induction s using Finset.induction_on with
    | empty => exact mul_one _
    | @insert a s ha ih =>
      have he : blockProduct P hcomm (insert a s)=P a*blockProduct P hcomm s :=
        Finset.noncommProd_insert_of_notMem _ _ _ _ ha
      rw [he,←mul_assoc,hs a (Finset.mem_insert_self _ _)]
      exact ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
  exact hp Eᶜ hpi

theorem blocks_exception_bound (hP : ∀ i, IsStarProjection (P i))
    (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hAP : ∀ i j, Commute (A i) (P j)) (hn : ∀ i,‖A i‖≤1)
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (hgap : ∀ i,‖A i*(1-P i)‖≤θ)
    (B : V →L[ℂ] V) (hB : ‖B‖≤1) (n : ℕ) :
    ‖B.adjoint*blocks A hA*B‖≤θ^n+
      ∑ E : Finset ι, if E.card<n then ‖B.adjoint*coarse P hcomm E*B‖ else 0 := by
  let T : Finset ι → V →L[ℂ] V := sector P hcomm Finset.univ
  have hsum : ∑ E,T E=1 := by
    simpa only [Finset.powerset_univ] using sector_sum P hcomm Finset.univ
  have hbound := resolution_exception_bound T (coarse P hcomm)
    (fun E => sector_projection P hcomm hP _ E)
    (fun E F hEF => sector_orthogonal P hcomm _ E F (Finset.subset_univ _) (Finset.subset_univ _) hEF hP)
    hsum (coarse_projection P hcomm hP) (sector_coarse P hcomm hP)
    (blocks A hA) B (blocks_sector_commute P hcomm A hA hAP)
    (blocks_norm_le_one A hA hn) hB (Finset.univ.filter fun E : Finset ι => E.card<n)
    (θ^n) (pow_nonneg hθ _) (by
      intro E hE
      have hEn : n≤E.card := by simpa using hE
      exact (blocks_sector_norm P hcomm hP A hA hAP hn θ hθ hgap E).trans
        (pow_le_pow_of_le_one hθ hθ1 hEn))
  simpa only [Finset.sum_filter] using hbound


end Thorp.CommutingBlocks

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma sampleOperator_weighted (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ P=weightedOperator ρ (sampleLaw P) := by
  unfold sampleOperator weightedOperator sampleLaw finiteMean
  simp only [Complex.ofReal_sum,div_eq_mul_inv,Finset.sum_mul,Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ g, if P ω=g then (Fintype.card Ω:ℂ)⁻¹ • continuousRepresentation ρ g else 0 := by
      symm
      simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp_all

lemma sampleOperator_norm_le [Nonempty Ω] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (P : Ω → G) :
    ‖sampleOperator ρ P‖≤1 := by
  rw [sampleOperator_weighted]
  exact (weightedOperator_norm_le ρ hρ _ (sampleLaw_nonneg _)).trans_eq (sampleLaw_sum P)

omit [Fintype G] in
lemma sampleOperator_equiv (ρ : Representation ℂ G V) (P : Ω → G) (e : Ξ ≃ Ω) :
    sampleOperator ρ (P ∘ e)=sampleOperator ρ P := by
  simp only [sampleOperator,Fintype.card_congr e,Function.comp_apply]
  rw [Equiv.sum_comp e (fun ω => continuousRepresentation ρ (P ω))]

omit [Fintype G] in
lemma sampleOperator_prod (ρ : Representation ℂ G V) (P : Ω → G) (Q : Ξ → G) :
    sampleOperator ρ (fun ω : Ω × Ξ => P ω.1*Q ω.2)=sampleOperator ρ P*sampleOperator ρ Q := by
  simp only [sampleOperator,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,map_mul,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum,smul_mul_smul,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ξ _
  rw [mul_comm]

omit [Fintype G] in
lemma sampleOperator_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (P : Ω → G) :
    sampleOperator ρ (fun ω => (P ω)⁻¹)=(sampleOperator ρ P).adjoint := by
  simp only [sampleOperator,map_smulₛₗ,map_sum,map_inv₀,map_natCast,
    continuousRepresentation_adjoint ρ hρ]

lemma sampleOperator_palindrome (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) :
    sampleOperator ρ (palindromePerm d)=
      sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))*
      (sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint := by
  rw [←sampleOperator_inv ρ hρ,←sampleOperator_prod]
  rfl

omit [Fintype G] in
lemma sampleOperator_one [Nonempty Ω] (ρ : Representation ℂ G V) :
    sampleOperator ρ (fun _ : Ω => 1)=1 := by
  simp only [sampleOperator,map_one,Finset.sum_const,Finset.card_univ,←Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]

lemma sampleOperator_uniform (ρ : Representation ℂ G V) : sampleOperator ρ (id : G → G)=uniformOperator ρ := by
  simp only [sampleOperator,uniformOperator,weightedOperator,Complex.ofReal_inv,Complex.ofReal_natCast,
    Finset.smul_sum,id_eq]

lemma sampleOperator_uniform_mul [Nonempty Ω] (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ (fun ω : Ω × G => P ω.1*ω.2⁻¹)=uniformOperator ρ := by
  rw [sampleOperator_prod]
  have he : sampleOperator ρ (fun g : G => g⁻¹)=uniformOperator ρ := by
    rw [←sampleOperator_uniform]
    exact sampleOperator_equiv ρ id (Equiv.inv G)
  rw [he,sampleOperator_weighted,weighted_uniform_left,sampleLaw_sum,one_smul]

end Thorp.UnitaryFinite

namespace Thorp.FiniteAverage
open scoped BigOperators Classical
variable {I Ω A : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    [Ring A] [Algebra ℂ A]

noncomputable def orderedProduct : MultilinearMap ℂ (fun _ : I => A) A :=
  MultilinearMap.domDomCongr (Fintype.equivFin I).symm
    (MultilinearMap.mkPiAlgebraFin ℂ (Fintype.card I) A)

lemma orderedProduct_eq (f : I → A) (hc : Pairwise fun i j => Commute (f i) (f j)) :
    orderedProduct f=Finset.univ.noncommProd f (fun _ _ _ _ hij => hc hij) := by
  unfold orderedProduct
  rw [MultilinearMap.domDomCongr_apply,MultilinearMap.mkPiAlgebraFin_apply]
  let l := List.ofFn (Fintype.equivFin I).symm
  have hl : l.Nodup := List.nodup_ofFn.mpr (Fintype.equivFin I).symm.injective
  have hu : l.toFinset=Finset.univ := by
    ext i
    simp only [List.mem_toFinset,List.mem_ofFn,Finset.mem_univ,iff_true,l]
    exact (Fintype.equivFin I).symm.surjective i
  have he := Finset.noncommProd_toFinset l f (by intro i hi j hj hij; exact hc hij) hl
  rw [hu] at he
  rw [he]
  congr 1
  exact List.map_ofFn.symm

lemma multilinear_average (F : MultilinearMap ℂ (fun _ : I => A) A) (x : I → Ω → A) :
    F (fun i => (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x i ω)=
      (Fintype.card (I → Ω):ℂ)⁻¹ • ∑ ω : I → Ω,F (fun i => x i (ω i)) := by
  rw [F.map_smul_univ,F.map_sum]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,inv_pow]

lemma ordered_average (x : I → Ω → A)
    (hc : ∀ ω, Pairwise fun i j => Commute (x i (ω i)) (x j (ω j)))
    (havg : Pairwise fun i j => Commute ((Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x i ω)
      ((Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x j ω)) :
    (Finset.univ.noncommProd (fun i => (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x i ω)
      (fun _ _ _ _ hij => havg hij))=
    (Fintype.card (I → Ω):ℂ)⁻¹ • ∑ ω : I → Ω,
      Finset.univ.noncommProd (fun i => x i (ω i)) (fun _ _ _ _ hij => hc ω hij) := by
  rw [←orderedProduct_eq _ havg,multilinear_average]
  simp only [orderedProduct_eq _ (hc _)]

end Thorp.FiniteAverage
namespace Thorp.FiniteCharacters
open Module
open scoped BigOperators Classical

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
variable (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
variable (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
variable (hneq : ∀ i j, i≠j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
  (hcard : Nat.card (ConjClasses G)≤Fintype.card ι)
include hneq hcard

lemma character_expansion (f : ConjClasses G → ℂ) :
    f=∑ i, characterDual (ρ i) f • characterClass (ρ i) := by
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  have horth (i j : ι) : characterDual (ρ i) (characterClass (ρ j))=if i=j then 1 else 0 := by
    rw [characterDual_characterClass]
    by_cases h : i=j
    · subst j; rw [ite_eq_left ⟨Representation.Equiv.refl _⟩,ite_eq_left rfl]
    · rw [ite_eq_right h,ite_eq_right (hneq i j h)]
  have hLI : LinearIndependent ℂ (fun i => characterClass (ρ i)) := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun i => characterDual (ρ i))
    · intro i j hij; exact (horth i j).trans (ite_eq_right hij)
    · intro i; simpa using horth i i
  have heq : Fintype.card ι=Module.finrank ℂ (ConjClasses G → ℂ) := by
    apply Nat.le_antisymm hLI.fintype_card_le_finrank
    simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
      smul_eq_mul,mul_one,Nat.card_eq_fintype_card] using hcard
  let b := Basis.mk hLI (by rw [hLI.span_eq_top_of_card_eq_finrank' heq])
  have hb (i : ι) : b i=characterClass (ρ i) := Basis.mk_apply _ _ _
  have hd (i : ι) : b.coord i=characterDual (ρ i) := by
    apply b.ext
    intro j
    rw [hb,horth]
    simp only [←hb,Basis.coord_apply,Basis.repr_self,Finsupp.single_apply]
    split_ifs <;> simp_all
  have h := b.sum_repr f
  simpa only [hb,show ∀ i,b.repr f i=characterDual (ρ i) f from fun i => congrArg (fun l => l f) (hd i)] using h.symm

theorem sum_dimension_sq : ∑ i, (Module.finrank ℂ (V i))^2=Fintype.card G := by
  let f : ConjClasses G → ℂ := fun c => if c=ConjClasses.mk (1:G) then 1 else 0
  have hf (g : G) : f (ConjClasses.mk g)=if g=1 then 1 else 0 := by
    simp only [f,ConjClasses.mk_eq_mk_iff_isConj,isConj_one_left]
  have hd (i : ι) : characterDual (ρ i) f=(Fintype.card G:ℂ)⁻¹*(Module.finrank ℂ (V i):ℂ) := by
    change (Nat.card G:ℂ)⁻¹ * ∑ g, f (ConjClasses.mk g)*(ρ i).character g⁻¹=_
    simp only [hf,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,inv_one,
      Representation.char_one,Nat.card_eq_fintype_card]
  have he := congrFun (character_expansion V ρ hneq hcard f) (ConjClasses.mk (1:G))
  rw [hf,ite_eq_left rfl] at he
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hd,characterClass_mk,Representation.char_one] at he
  have hN : (Fintype.card G:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ i,(Module.finrank ℂ (V i):ℂ)^2)=(Fintype.card G:ℂ) := by
    calc
      _ = (Fintype.card G:ℂ) * ∑ i,(Fintype.card G:ℂ)⁻¹ *
          (Module.finrank ℂ (V i):ℂ)*(Module.finrank ℂ (V i):ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
      _ = _ := by rw [←he,mul_one]
  exact_mod_cast hs

end Thorp.FiniteCharacters

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ V] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma averageMap_zero (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hne : ¬Nonempty (Representation.Equiv ρ σ)) (A : V →ₗ[ℂ] W) :
    averageMap ρ σ A=0 := by
  rcases Representation.IsIrreducible.bijective_or_eq_zero (averageMap ρ σ A) with h|h
  · exact (hne ⟨Representation.IntertwiningMap.ofBijective _ h⟩).elim
  · exact h

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma coefficient_cross_orthogonality (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hρ : IsUnitary ρ) (hne : ¬Nonempty (Representation.Equiv ρ σ))
    (u z : W) (v w : V) :
    ∑ g, inner ℂ u (σ g z)*inner ℂ (ρ g w) v=0 := by
  have he := averageMap_zero ρ σ hne (InnerProductSpace.rankOne ℂ z w).toLinearMap
  have hv := congrArg (fun T : Representation.IntertwiningMap ρ σ => inner ℂ u (T v)) he
  change inner ℂ u ((∑ g, (σ g).comp ((InnerProductSpace.rankOne ℂ z w).toLinearMap.comp (ρ g⁻¹))) v)=_ at hv
  simpa only [LinearMap.sum_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply,map_smul,unitary_inner_inv ρ hρ,inner_sum,
    inner_smul_right,Representation.IntertwiningMap.coe_zero,Pi.zero_apply,inner_zero_right,mul_comm] using hv

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]

def regularAction : G →* Equiv.Perm G where
  toFun := Equiv.mulLeft
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

omit [Fintype G] in
lemma regular_transitive (x : G) : ∃ g,regularAction g (1:G)=x := ⟨x,mul_one x⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma regular_fixed (ρ : Representation ℂ G V) (w : V) : IsFixed regularAction (1:G) ρ w := by
  intro g hg
  have he : g=1 := by simpa only [regularAction,MonoidHom.coe_mk,OneHom.coe_mk,Equiv.coe_mulLeft,mul_one] using hg
  subst g
  simp

noncomputable def regularCoefficient (ρ : Representation ℂ G V) (w v : V) : EuclideanSpace ℂ G :=
  normalizedCoefficient regularAction 1 regular_transitive ρ w v

omit [FiniteDimensional ℂ V] in
lemma regularCoefficient_apply (ρ : Representation ℂ G V) (w v : V) (g : G) :
    regularCoefficient ρ w v g = (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card G:ℝ)):ℂ)*inner ℂ (ρ g w) v := by
  unfold regularCoefficient normalizedCoefficient
  simp only [PiLp.smul_apply,smul_eq_mul]
  congr 1
  have he := coefficient_at regularAction 1 regular_transitive ρ w (regular_fixed ρ w) v g
  simpa only [regularAction,MonoidHom.coe_mk,OneHom.coe_mk,Equiv.coe_mulLeft,mul_one] using he

lemma regularCoefficient_inner (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (w z v t : V) :
    inner ℂ (regularCoefficient ρ w v) (regularCoefficient ρ z t)=inner ℂ z w*inner ℂ v t :=
  normalizedCoefficient_inner regularAction 1 regular_transitive ρ hρ w z
    (regular_fixed ρ w) (regular_fixed ρ z) v t

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma regularCoefficient_cross (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hσ : IsUnitary σ) (hne : ¬Nonempty (Representation.Equiv σ ρ))
    (w v : V) (z t : W) : inner ℂ (regularCoefficient ρ w v) (regularCoefficient σ z t)=0 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,regularCoefficient_apply,map_mul,Complex.conj_ofReal,
    inner_conj_symm]
  have he := coefficient_cross_orthogonality σ ρ hσ hne v w t z
  calc
    _ = ((Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card G:ℝ)):ℂ)*
        (Real.sqrt ((Module.finrank ℂ W:ℝ)/(Fintype.card G:ℝ)):ℂ)) *
        ∑ g,inner ℂ v (ρ g w)*inner ℂ (σ g z) t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = 0 := by rw [he,mul_zero]

end Thorp.UnitaryFinite

namespace Thorp.FiniteFourier
open scoped BigOperators ComplexConjugate Classical
open UnitaryFinite
variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
variable (V : ι → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
variable (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
variable (hρ : ∀ i, IsUnitary (ρ i))
variable (hneq : ∀ i j, i≠j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
  (hcard : Nat.card (ConjClasses G)≤Fintype.card ι)


abbrev CoefficientIndex := Σ i,Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i))

noncomputable def coefficientFamily (a : CoefficientIndex V) : EuclideanSpace ℂ G :=
  regularCoefficient (ρ a.1) (stdOrthonormalBasis ℂ (V a.1) a.2.1) (stdOrthonormalBasis ℂ (V a.1) a.2.2)

omit [Fintype ι] in
include hρ hneq in
lemma coefficientFamily_orthonormal : Orthonormal ℂ (coefficientFamily V ρ) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i,a,b⟩ ⟨j,c,d⟩
  dsimp only [coefficientFamily]
  by_cases hij : i=j
  · subst j
    rw [regularCoefficient_inner _ (hρ i)]
    simp only [(stdOrthonormalBasis ℂ (V i)).inner_eq_ite]
    by_cases hac : a=c <;> by_cases hbd : b=d <;> simp [hac,hbd,eq_comm]
  · rw [regularCoefficient_cross _ _ (hρ j) (hneq j i (Ne.symm hij))]
    rw [ite_eq_right (by intro h; exact hij (congrArg Sigma.fst h))]

include ρ hneq hcard in
lemma coefficientIndex_card : Fintype.card (CoefficientIndex V)=Fintype.card G := by
  simp only [CoefficientIndex,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,←pow_two]
  exact FiniteCharacters.sum_dimension_sq V ρ hneq hcard

noncomputable def coefficientBasis : OrthonormalBasis (CoefficientIndex V) ℂ (EuclideanSpace ℂ G) :=
  OrthonormalBasis.mk (coefficientFamily_orthonormal V ρ hρ hneq)
    (by rw [(coefficientFamily_orthonormal V ρ hρ hneq).linearIndependent.span_eq_top_of_card_eq_finrank'
          (by rw [coefficientIndex_card V ρ hneq hcard,finrank_euclideanSpace])])

lemma coefficientBasis_apply (a : CoefficientIndex V) :
    coefficientBasis V ρ hρ hneq hcard a=coefficientFamily V ρ a := congrFun (OrthonormalBasis.coe_mk _ _) a

include hρ hneq hcard in

theorem parseval (f : EuclideanSpace ℂ G) :
    ∑ a : CoefficientIndex V, ‖inner ℂ (coefficientFamily V ρ a) f‖^2=‖f‖^2 := by
  simpa only [coefficientBasis_apply] using
    (coefficientBasis V ρ hρ hneq hcard).sum_sq_norm_inner_right f


noncomputable def realVector (p : G → ℝ) : EuclideanSpace ℂ G := WithLp.toLp 2 (fun g => (p g:ℂ))

omit [Fintype ι] [∀ i, Representation.IsIrreducible (ρ i)] in
lemma coefficient_realVector (p : G → ℝ) (a : CoefficientIndex V) :
    inner ℂ (coefficientFamily V ρ a) (realVector p)=
      (Real.sqrt ((Module.finrank ℂ (V a.1):ℝ)/(Fintype.card G:ℝ)):ℂ)*
      inner ℂ (stdOrthonormalBasis ℂ (V a.1) a.2.2)
        (weightedOperator (ρ a.1) p (stdOrthonormalBasis ℂ (V a.1) a.2.1)) := by
  simp only [PiLp.inner_apply,coefficientFamily,regularCoefficient_apply,realVector,
    RCLike.inner_apply,map_mul,Complex.conj_ofReal,inner_conj_symm,
    weightedOperator,sum_apply,smul_apply,
    continuousRepresentation_apply,inner_sum,inner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  ring

omit [Fintype ι] [∀ i, Representation.IsIrreducible (ρ i)] in
lemma coefficient_realVector_sq (p : G → ℝ) (a : CoefficientIndex V) :
    ‖inner ℂ (coefficientFamily V ρ a) (realVector p)‖^2=
      ((Module.finrank ℂ (V a.1):ℝ)/(Fintype.card G:ℝ))*
      ‖inner ℂ (stdOrthonormalBasis ℂ (V a.1) a.2.2)
        (weightedOperator (ρ a.1) p (stdOrthonormalBasis ℂ (V a.1) a.2.1))‖^2 := by
  rw [coefficient_realVector,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]

include hρ hneq hcard in
lemma parseval_operator (p : G → ℝ) :
    (Fintype.card G:ℝ)*‖realVector p‖^2=
      ∑ i,(Module.finrank ℂ (V i):ℝ)*∑ a : Fin (Module.finrank ℂ (V i)),
        ‖weightedOperator (ρ i) p (stdOrthonormalBasis ℂ (V i) a)‖^2 := by
  rw [←parseval V ρ hρ hneq hcard (realVector p)]
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,coefficient_realVector_sq]
  have hN : (Fintype.card G:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he (a : Fin (Module.finrank ℂ (V i))) :
      (∑ b : Fin (Module.finrank ℂ (V i)),
        (Module.finrank ℂ (V i):ℝ)/(Fintype.card G:ℝ)*
          ‖inner ℂ (stdOrthonormalBasis ℂ (V i) b)
            (weightedOperator (ρ i) p (stdOrthonormalBasis ℂ (V i) a))‖^2)=
        (Module.finrank ℂ (V i):ℝ)/(Fintype.card G:ℝ)*
          ‖weightedOperator (ρ i) p (stdOrthonormalBasis ℂ (V i) a)‖^2 := by
    rw [←Finset.mul_sum,(stdOrthonormalBasis ℂ (V i)).sum_sq_norm_inner_right]
  simp_rw [he]
  rw [←Finset.mul_sum]
  field_simp

include hρ hneq hcard in
lemma realVector_bound (p : G → ℝ) :
    (Fintype.card G:ℝ)*‖realVector p‖^2≤
      ∑ i,(Module.finrank ℂ (V i):ℝ)^2*‖weightedOperator (ρ i) p‖^2 := by
  rw [parseval_operator V ρ hρ hneq hcard]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ (Module.finrank ℂ (V i):ℝ)*∑ _a : Fin (Module.finrank ℂ (V i)),‖weightedOperator (ρ i) p‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro a _
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [(stdOrthonormalBasis ℂ (V i)).norm_eq_one,mul_one] using
        (weightedOperator (ρ i) p).le_opNorm (stdOrthonormalBasis ℂ (V i) a)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

include hρ hneq hcard in

theorem l1_fourier_bound (p : G → ℝ) :
    (∑ g,|p g|)^2≤∑ i,(Module.finrank ℂ (V i):ℝ)^2*‖weightedOperator (ρ i) p‖^2 := by
  apply le_trans _ (realVector_bound V ρ hρ hneq hcard p)
  have he : ‖realVector p‖^2=∑ g,|p g|^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [realVector,PiLp.toLp_apply,Complex.norm_real,Real.norm_eq_abs]
  rw [he]
  simpa only [Finset.card_univ] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun g => |p g|)

end Thorp.FiniteFourier

namespace Thorp.ParallelBlocks
open scoped BigOperators Classical
variable {B X : Type*}

def lift : (B → Equiv.Perm X) →* Equiv.Perm (B × X) where
  toFun p :=
    { toFun := fun x => (x.1,p x.1 x.2)
      invFun := fun x => (x.1,(p x.1).symm x.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma lift_apply (p : B → Equiv.Perm X) (x : B × X) : lift p x=(x.1,p x.1 x.2) := rfl

noncomputable def injection (b : B) : Equiv.Perm X →* Equiv.Perm (B × X) :=
  lift.comp
    { toFun := fun p c => if c=b then p else 1
      map_one' := by funext c; simp
      map_mul' := by intro p q; funext c; by_cases h : c=b <;> simp [h] }

@[simp] lemma injection_apply (b : B) (p : Equiv.Perm X) (x : B × X) :
    injection b p x=(x.1,if x.1=b then p x.2 else x.2) := by
  simp only [injection,MonoidHom.comp_apply,lift_apply]
  by_cases h : x.1=b <;> simp [h]

lemma injection_commute {b c : B} (h : b≠c) (p q : Equiv.Perm X) :
    Commute (injection b p) (injection c q) := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply,injection_apply]
  by_cases hb : x.1=b <;> by_cases hc : x.1=c <;> simp_all

variable [Fintype B]

lemma lift_product (p : B → Equiv.Perm X) :
    lift p=Finset.univ.noncommProd (fun b => injection b (p b))
      (fun _ _ _ _ h => injection_commute h _ _) := by
  have he (s : Finset B) (x : B × X) :
      s.noncommProd (fun b => injection b (p b))
        (fun _ _ _ _ h => injection_commute h _ _) x=
          (x.1,if x.1∈s then p x.1 x.2 else x.2) := by
    induction s using Finset.induction_on with
    | empty =>
      have hz : Finset.noncommProd (∅ : Finset B) (fun b => injection b (p b))
          (fun _ _ _ _ h => injection_commute h _ _)=1 := Finset.noncommProd_empty _ _
      rw [hz]; simp
    | @insert a s ha ih =>
      have hz : (insert a s).noncommProd (fun b => injection b (p b))
          (fun _ _ _ _ h => injection_commute h _ _)=injection a (p a)*
          s.noncommProd (fun b => injection b (p b))
            (fun _ _ _ _ h => injection_commute h _ _) :=
        Finset.noncommProd_insert_of_notMem _ _ _ _ ha
      rw [hz,Equiv.Perm.mul_apply,ih,injection_apply]
      by_cases h : x.1=a
      · subst a; simp [ha]
      · simp [h]
  apply Equiv.ext
  intro x
  rw [he]
  simp

end Thorp.ParallelBlocks
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G H : Type*} [Group G] [Group H]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma continuousRepresentation_comp (ρ : Representation ℂ G V) (φ : H →* G) (h : H) :
    continuousRepresentation (ρ.comp φ) h=continuousRepresentation ρ (φ h) := rfl

lemma sampleOperator_comp (ρ : Representation ℂ G V) (φ : H →* G) (P : Ω → H) :
    sampleOperator (ρ.comp φ) P=sampleOperator ρ (φ ∘ P) := rfl

omit [FiniteDimensional ℂ V] in
lemma unitary_comp (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (φ : H →* G) :
    IsUnitary (ρ.comp φ) := fun h v w => hρ (φ h) v w

lemma sampleOperator_commute (ρ : Representation ℂ G V) (P : Ω → G) (Q : Ξ → G)
    (h : ∀ ω ξ, Commute (P ω) (Q ξ)) :
    Commute (sampleOperator ρ P) (sampleOperator ρ Q) := by
  unfold sampleOperator
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sum_left
  intro ω _
  apply Commute.sum_right
  intro ξ _
  exact (h ω ξ).map (continuousRepresentation ρ)

lemma sampleOperator_uniform_absorb [Fintype G] [Nonempty Ω]
    (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ P*uniformOperator ρ=uniformOperator ρ := by
  rw [sampleOperator_weighted,weighted_uniform_left,sampleLaw_sum,one_smul]

end Thorp.UnitaryFinite
namespace Thorp.ParallelBlocks
open scoped BigOperators Classical
open UnitaryFinite
variable {B X Ω : Type*} [Fintype B] [DecidableEq B] [Fintype Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype B] [DecidableEq B] in
lemma local_average_commute (ρ : Representation ℂ (Equiv.Perm (B × X)) V)
    (P : B → Ω → Equiv.Perm X) (b c : B) :
    Commute (sampleOperator (ρ.comp (injection b)) (P b))
      (sampleOperator (ρ.comp (injection c)) (P c)) := by
  by_cases h : b=c
  · subst c; exact Commute.refl _
  · rw [sampleOperator_comp,sampleOperator_comp]
    exact sampleOperator_commute ρ _ _ (fun _ _ => injection_commute h _ _)

lemma sampleOperator_parallel (ρ : Representation ℂ (Equiv.Perm (B × X)) V)
    (P : B → Ω → Equiv.Perm X) :
    sampleOperator ρ (fun ω : B → Ω => lift (fun b => P b (ω b)))=
      CommutingBlocks.blocks (fun b => sampleOperator (ρ.comp (injection b)) (P b))
        (local_average_commute ρ P) := by
  let A (b : B) (w : Ω) := continuousRepresentation ρ (injection b (P b w))
  have hc : ∀ ω : B → Ω, Pairwise fun b c => Commute (A b (ω b)) (A c (ω c)) := by
    intro ω b c h
    exact (injection_commute h _ _).map (continuousRepresentation ρ)
  have havg : Pairwise fun b c => Commute ((Fintype.card Ω:ℂ)⁻¹ • ∑ w,A b w)
      ((Fintype.card Ω:ℂ)⁻¹ • ∑ w,A c w) := by
    intro b c _
    exact local_average_commute ρ P b c
  have he (ω : B → Ω) : continuousRepresentation ρ (lift (fun b => P b (ω b)))=
      Finset.univ.noncommProd (fun b => A b (ω b)) (fun _ _ _ _ h => hc ω h) := by
    rw [lift_product]
    exact Finset.map_noncommProd _ _ _ (continuousRepresentation ρ)
  unfold sampleOperator
  simp_rw [he]
  exact (FiniteAverage.ordered_average A hc havg).symm

end Thorp.ParallelBlocks
namespace Thorp
open scoped BigOperators Classical

noncomputable def splitPerm (r L : ℕ) : Equiv.Perm (Card (L+r)) ≃* Equiv.Perm (Card r × Card L) :=
  (cardSplit r L).permCongrHom

noncomputable def outerPerm (r L : ℕ) (hi : Card L × SwitchIndex r → Bool) :
    Equiv.Perm (Card r × Card L) :=
  (Equiv.prodComm (Card L) (Card r)).permCongrHom
    (ParallelBlocks.lift (fun x => butterflyPerm r (decodeButterfly r (fun i => hi (x,i)))))

lemma outerPerm_apply (r L : ℕ) (hi : Card L × SwitchIndex r → Bool) (x : Card r × Card L) :
    outerPerm r L hi x=(butterflyPerm r (decodeButterfly r (fun i => hi (x.2,i))) x.1,x.2) := rfl

lemma splitPerm_butterfly (r L : ℕ) (lo : Card r × SwitchIndex L → Bool)
    (hi : Card L × SwitchIndex r → Bool) :
    splitPerm r L (butterflyPerm (L+r) (decodeButterfly (L+r) (assembleBits r L lo hi)))=
      outerPerm r L hi*ParallelBlocks.lift
        (fun b => butterflyPerm L (decodeButterfly L (fun i => lo (b,i)))) := by
  apply Equiv.ext
  intro x
  change cardSplit r L (butterflyPerm (L+r) (decodeButterfly (L+r) (assembleBits r L lo hi))
    ((cardSplit r L).symm x))=_
  rw [butterfly_split,Equiv.apply_symm_apply]
  rfl

lemma boundaryTree_node_raw (L r : ℕ) (U : Card (r+1) → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r+1) → Bool) :
    boundaryTree L (r+1) U X=InputTree.node (fun y => X (Sum.inl y))
      (fun b => boundaryTree L r (fun u => U (Fin.cons b u)) (fun i => X (Sum.inr (b,i)))) := by
  conv_lhs => unfold boundaryTree
  congr 1
  funext b
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> rfl

lemma boundaryOutput_node_raw (L r : ℕ) (Y : SwitchIndex (L+r+1) → Bool) (b : Card (r+1)) :
    boundaryOutput L (r+1) Y b=
      boundaryOutput L r (fun i => Y (Sum.inr (b 0,i))) (Fin.tail b) := by
  conv_lhs => unfold boundaryOutput
  cases b 0 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> rfl

lemma boundaryTree_split (L r : ℕ) (U : Card r → Equiv.Perm (Card L))
    (lo : Card r × SwitchIndex L → Bool) (hi : Card L × SwitchIndex r → Bool) (x : Card (L+r)) :
    cardSplit r L ((boundaryTree L r U (assembleBits r L lo hi)).perm x)=
      let y := cardSplit r L x
      let z := U y.1 y.2
      (butterflyPerm r (decodeButterfly r (fun i => hi (z,i))) y.1,z) := by
  induction r with
  | zero =>
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  | succ r ih =>
    let lo' : Card r × SwitchIndex L → Bool := fun j => lo (Fin.cons (x 0) j.1,j.2)
    let hi' : Card L × SwitchIndex r → Bool := fun j => hi (j.1,Sum.inr (x 0,j.2))
    let U' : Card r → Equiv.Perm (Card L) := fun b => U (Fin.cons (x 0) b)
    have hh := ih U' lo' hi' (Fin.tail x)
    let u := (boundaryTree L r U' (assembleBits r L lo' hi')).perm (Fin.tail x)
    let y := cardSplit r L (Fin.tail x)
    let z := U' y.1 y.2
    let w := butterflyPerm r (decodeButterfly r (fun i => hi' (z,i))) y.1
    change cardSplit r L u=(w,z) at hh
    rw [boundaryTree_node_raw]
    change ((Fin.cons (Bool.xor (x 0) (hi ((cardSplit r L u).2,Sum.inl (cardSplit r L u).1)))
      ((cardSplit r L u).1) : Card (r+1)),(cardSplit r L u).2)=
        ((Fin.cons (Bool.xor (x 0) (hi (z,Sum.inl w))) w : Card (r+1)),z)
    rw [hh]

lemma splitPerm_boundaryTree (L r : ℕ) (U : Card r → Equiv.Perm (Card L))
    (lo : Card r × SwitchIndex L → Bool) (hi : Card L × SwitchIndex r → Bool) :
    splitPerm r L (boundaryTree L r U (assembleBits r L lo hi)).perm=
      outerPerm r L hi*ParallelBlocks.lift U := by
  apply Equiv.ext
  intro x
  change cardSplit r L ((boundaryTree L r U (assembleBits r L lo hi)).perm
    ((cardSplit r L).symm x))=_
  rw [boundaryTree_split,Equiv.apply_symm_apply]
  rfl

lemma boundaryOutput_split (L r : ℕ) (lo : Card r × SwitchIndex L → Bool)
    (hi : Card L × SwitchIndex r → Bool) (b : Card r) :
    boundaryOutput L r (assembleBits r L lo hi) b=
      butterflyPerm L (decodeButterfly L (fun i => lo (b,i))) := by
  induction r with
  | zero =>
    rw [Subsingleton.elim b (fun j => Fin.elim0 j)]
    rfl
  | succ r ih =>
    rw [boundaryOutput_node_raw]
    change boundaryOutput L r (assembleBits r L (fun j => lo (Fin.cons (b 0) j.1,j.2))
      (fun j => hi (j.1,Sum.inr (b 0,j.2)))) (Fin.tail b)=_
    rw [ih]
    simp only [Fin.cons_self_tail]


abbrev OuterCoins (r L : ℕ) := Card L × SwitchIndex r → Bool
abbrev LocalCoins (L : ℕ) := SwitchIndex L → Bool

def parallelSplitCoinEquiv (r L : ℕ) :
    ((Card r → LocalCoins L) × OuterCoins r L) ≃ LocalCoins (L+r) :=
  (Equiv.prodCongr (Equiv.curry (Card r) (SwitchIndex L) Bool).symm (Equiv.refl _)).trans
    (splitCoinEquiv r L)

lemma parallelSplitCoinEquiv_apply (r L : ℕ) (c : Card r → LocalCoins L) (h : OuterCoins r L) :
    parallelSplitCoinEquiv r L (c,h)=assembleBits r L (fun x => c x.1 x.2) h := by
  exact splitCoinEquiv_apply _ _ _ _

def pairAssembleEquiv (B C H : Type*) :
    ((H × (B → C × C)) × H) ≃ (((B → C) × H) × ((B → C) × H)) where
  toFun w := (((fun b => (w.1.2 b).1),w.1.1),((fun b => (w.1.2 b).2),w.2))
  invFun w := ((w.1.2,fun b => (w.1.1 b,w.2.1 b)),w.2.2)
  left_inv _w := rfl
  right_inv _w := rfl

def palindromeStageEquiv (r L : ℕ) :
    ((OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) ≃ BenesCoins (L+r) :=
  (pairAssembleEquiv _ _ _).trans
    (Equiv.prodCongr (parallelSplitCoinEquiv r L) (parallelSplitCoinEquiv r L))

lemma palindromeStageEquiv_apply (r L : ℕ)
    (w : (OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) :
    palindromeStageEquiv r L w=
      (assembleBits r L (fun x => (w.1.2 x.1).1 x.2) w.1.1,
       assembleBits r L (fun x => (w.1.2 x.1).2 x.2) w.2) := by
  simp only [palindromeStageEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,pairAssembleEquiv,
    Equiv.coe_fn_mk,Prod.map_apply,parallelSplitCoinEquiv_apply]

def modifiedAssembleEquiv (B C H U : Type*) :
    ((H × (B → U × (C × C))) × H) ≃ (B → U) × (((B → C) × H) × ((B → C) × H)) where
  toFun w := ((fun b => (w.1.2 b).1),
    (((fun b => (w.1.2 b).2.1),w.1.1),((fun b => (w.1.2 b).2.2),w.2)))
  invFun w := ((w.2.1.2,fun b => (w.1 b,(w.2.1.1 b,w.2.2.1 b))),w.2.2.2)
  left_inv _w := rfl
  right_inv _w := rfl

end Thorp

end ThorpNine.Contact

end OAI
