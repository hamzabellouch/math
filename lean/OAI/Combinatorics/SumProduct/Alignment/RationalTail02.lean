import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MalcevCharacters01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace RationalTailCoordinates
open RationalLattice MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r n : ℕ} (c : RealCoordinates G (r+n)) (H : Subgroup G)
variable (hH : ∀ g : G, g ∈ H ↔ ∀ i : Fin (r+n), i.val < r → c.coord g i = 0)

 
def extendCoefficient {A : Type*} [Zero A] (k : Fin n → A) : Fin (r+n) → A :=
  Fin.addCases (fun _ => 0) k

omit [IsTopologicalGroup G] in
lemma sum_extend [IsTopologicalGroup G] (k : Fin n → ℝ) (g : G) :
    (∑ i, c.coord g i * extendCoefficient (r:=r) k i) =
      ∑ i, c.coord g (embed r i) * k i := by
  rw [Fin.sum_univ_add]
  simp only [extendCoefficient,Fin.addCases_left,Fin.addCases_right,mul_zero,Finset.sum_const_zero,zero_add]
  rfl

omit [IsTopologicalGroup G] in
lemma sum_extend_int [IsTopologicalGroup G] (k : Fin n → ℤ) (g : G) :
    (∑ i, c.coord g i * ((extendCoefficient (r:=r) k i : ℤ) : ℝ)) =
      ∑ i, c.coord g (embed r i) * (k i : ℝ) := by
  rw [Fin.sum_univ_add]
  simp only [extendCoefficient,Fin.addCases_left,Fin.addCases_right,Int.cast_zero,mul_zero,
    Finset.sum_const_zero,zero_add]
  rfl

include hH in
 

theorem exists_integer_extension (hsk : SecondKind c) (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
    (χ : H →* Multiplicative ℝ) (hcont : Continuous χ)
    (hz : ∀ g : H, g.val ∈ Γ → ∃ z : ℤ, Multiplicative.toAdd (χ g) = z)
    (hcomm : _root_.commutator G ≤ χ.ker.map H.subtype) :
    ∃ ψ : G →* Multiplicative ℝ, Continuous ψ ∧
      ψ.comp H.subtype = χ ∧
      (∀ g ∈ Γ, ∃ z : ℤ, Multiplicative.toAdd (ψ g) = z) ∧
      ∃ k : Fin n → ℤ, ∀ g : G,
        Multiplicative.toAdd (ψ g) = ∑ i, c.coord g (embed r i) * (k i : ℝ) := by
  obtain ⟨k,hk⟩ := integer_character_coordinates (tailCoordinates c H hH)
    (tail_secondKind c H hH hsk) χ (Γ.comap H.subtype)
    (fun g => tailCoordinates_lattice c H hH Γ hΓ g) hcont hz
  let a : Fin (r+n) → ℝ := fun i => ((extendCoefficient (r:=r) k i : ℤ) : ℝ)
  let N := χ.ker.map H.subtype
  let : N.Normal := Subgroup.Normal.of_commutator_le G hcomm
  have hzero : ∀ g ∈ N, ∑ i, c.coord g i * a i = 0 := by
    rintro g ⟨u,hu,rfl⟩
    change (∑ i, c.coord u.val i * ((extendCoefficient (r:=r) k i : ℤ) : ℝ)) = 0
    rw [sum_extend_int]
    change (∑ i, (tailCoordinates c H hH).coord u i * (k i : ℝ)) = 0
    rw [← hk]
    exact congrArg Multiplicative.toAdd hu
  let ψ := abelianCoordinateCharacter c hsk N hcomm a hzero
  have hψ (g : G) : Multiplicative.toAdd (ψ g) =
      ∑ i, c.coord g (embed r i) * (k i : ℝ) := by
    rw [abelianCoordinateCharacter_apply]
    exact sum_extend_int c k g
  refine ⟨ψ,abelianCoordinateCharacter_continuous c hsk N hcomm a hzero,?_,?_,k,hψ⟩
  · ext u
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (ψ u.val) = Multiplicative.toAdd (χ u)
    rw [hψ,hk]
    rfl
  · intro g hg
    choose z hz using (hΓ g).mp hg
    refine ⟨∑ i, z (embed r i) * k i,?_⟩
    rw [hψ]
    simp only [hz,Int.cast_sum,Int.cast_mul]

end RationalTailCoordinates
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace RationalCharacterFirst
open RationalLattice IntegerHyperplane
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}
variable (c : RealCoordinates G (n+1)) (χ : G →* Multiplicative ℝ)

 

theorem exists_refined_integer_cover (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
    (hcont : Continuous χ) (hz : ∀ g ∈ Γ, ∃ z : ℤ, Multiplicative.toAdd (χ g) = z)
    (hne : χ ≠ 1) :
    ∃ Λ : Subgroup G, ∃ e : RealCoordinates G (n+1),
      (∀ g : G, g ∈ Λ ↔ ∀ i, ∃ z : ℤ, e.coord g i = z) ∧
      Λ ≤ Γ ∧ (Λ.subgroupOf Γ).FiniteIndex ∧
      ∀ H : Subgroup G, ∀ r : ℕ,
        (∀ g : G, g ∈ H ↔ ∀ i : Fin (n+1), i.val < r → c.coord g i = 0) →
        ∃ t : ℕ, ∀ g : G, g ∈ H ⊓ χ.ker ↔ ∀ i : Fin (n+1), i.val < t → e.coord g i = 0 := by
  obtain ⟨k,hk⟩ := integer_character_expCoordinates c Γ hΓ χ hcont hz
  have hk0 : k ≠ 0 := by
    intro he
    apply hne
    ext g
    apply Multiplicative.toAdd.injective
    rw [hk,he]
    simp
  obtain ⟨p,hp,hlast⟩ := exists_last_nonzero k hk0
  have he : ∀ g : G, Multiplicative.toAdd (χ g) = form k ((secondCoordinates c).coord g) := by
    intro g
    rw [hk]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  let d := characterFirstCoordinates (secondCoordinates c) χ k p hp he hlast
  have hdpoly : ∀ i, RationalPolynomialMap.IsPolynomial (fun x : Fin (n+1) → ℝ => c.coord (d.coord.symm x) i) := by
    intro i
    change RationalPolynomialMap.IsPolynomial (fun x => c.coord (expProduct c (splitLift k p x)) i)
    exact polynomialMap_expProduct c (fun j => splitLift_polynomial k p j) i
  obtain ⟨Λ,e,hΛ,hle,hi,hzero⟩ := exists_integer_sublattice c d (MonoidHom.id G)
    hdpoly Γ hΓ continuous_id Function.injective_id
  refine ⟨Λ,e,hΛ,hle,hi,?_⟩
  intro H r hH
  refine ⟨deletedCutoff p r+1,fun g => ?_⟩
  rw [characterFirst_adapted (secondCoordinates c) χ k p hp he hlast H r
    (secondCoordinates_adapted c H r hH)]
  exact forall_congr' (fun i => imp_congr_right (fun _ => (hzero g i).symm))

end RationalCharacterFirst

namespace RationalTailCoordinates
open RationalLattice MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r n : ℕ} (c : RealCoordinates G (r+(n+1))) (H : Subgroup G)
variable (hH : ∀ g : G, g ∈ H ↔ ∀ i : Fin (r+(n+1)), i.val < r → c.coord g i = 0)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma mapped_kernel_eq_inter [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : H →* Multiplicative ℝ) (ψ : G →* Multiplicative ℝ)
    (he : ψ.comp H.subtype = χ) : χ.ker.map H.subtype = H ⊓ ψ.ker := by
  ext g
  constructor
  · rintro ⟨u,hu,rfl⟩
    refine ⟨u.property,?_⟩
    change ψ u.val=1
    change χ u = 1 at hu
    have hh := DFunLike.congr_fun he u
    change ψ u.val = χ u at hh
    exact hh.trans hu
  · rintro ⟨hg,hψ⟩
    refine ⟨⟨g,hg⟩,?_,rfl⟩
    change χ ⟨g,hg⟩=1
    rw [← he]
    exact hψ

include hH in
 

theorem exists_lower_refinement_geometry (hsk : SecondKind c) (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
    (χ : H →* Multiplicative ℝ) (hcont : Continuous χ)
    (hz : ∀ g : H, g.val ∈ Γ → ∃ z : ℤ, Multiplicative.toAdd (χ g) = z)
    (hcomm : _root_.commutator G ≤ χ.ker.map H.subtype) (hne : χ ≠ 1) :
    ∃ Λ : Subgroup G, ∃ e : RealCoordinates G (r+(n+1)),
      (∀ g : G, g ∈ Λ ↔ ∀ i, ∃ z : ℤ, e.coord g i = z) ∧
      Λ ≤ Γ ∧ (Λ.subgroupOf Γ).FiniteIndex ∧
      ∀ K : Subgroup G, K ≤ H → ∀ s : ℕ,
        (∀ g : G, g ∈ K ↔ ∀ i : Fin (r+(n+1)), i.val < s → c.coord g i = 0) →
        ∃ t : ℕ, ∀ g : G,
          g ∈ K ⊓ χ.ker.map H.subtype ↔ ∀ i : Fin (r+(n+1)), i.val < t → e.coord g i = 0 := by
  obtain ⟨ψ,hψ,hagree,hint,_⟩ := exists_integer_extension c H hH hsk Γ hΓ χ hcont hz hcomm
  have hnψ : ψ ≠ 1 := by
    intro h
    apply hne
    rw [← hagree,h]
    rfl
  obtain ⟨Λ,e,hΛ,hle,hi,ha⟩ := RationalCharacterFirst.exists_refined_integer_cover c ψ Γ hΓ hψ hint hnψ
  refine ⟨Λ,e,hΛ,hle,hi,?_⟩
  intro K hK s hKs
  obtain ⟨t,ht⟩ := ha K s hKs
  refine ⟨t,fun g => ?_⟩
  rw [mapped_kernel_eq_inter H χ ψ hagree,← inf_assoc,inf_eq_left.mpr hK]
  exact ht g

end RationalTailCoordinates
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace MalcevCharacters
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (H : Subgroup G) (r : ℕ) (hcomm : _root_.commutator G ≤ H)
variable (hH : ∀ g ∈ H, ∀ i : Fin n, i.val < r → c.coord g i = 0)

include hsk hcomm hH in
 

lemma prefix_coord_mul (i : Fin n) (hi : i.val < r) (g h : G) :
    c.coord (g*h) i = c.coord g i+c.coord h i := by
  classical
  let : H.Normal := Subgroup.Normal.of_commutator_le G hcomm
  have hz : ∀ g ∈ H, ∑ j, c.coord g j * (Pi.single i 1 : Fin n → ℝ) j = 0 := by
    intro g hg
    simpa [Pi.single_apply] using hH g hg i hi
  simpa [Pi.single_apply] using coordinate_form_mul c hsk H hcomm (Pi.single i 1) hz g h

 

def horizontalCoordinates : RealCoordinates G n where
  coord := c.coord
  one_coord := c.one_coord
  correction i := if i.val < r then 0 else c.correction i
  mul_coord g h i := by
    split_ifs with hi
    · simp only [MvPolynomial.eval₂_zero,add_zero]
      exact prefix_coord_mul c hsk H r hcomm hH i hi g h
    · exact c.mul_coord g h i

lemma horizontalCoordinates_correction (i : Fin n) (hi : i.val < r) :
    (horizontalCoordinates c hsk H r hcomm hH).correction i = 0 := by
  simp [horizontalCoordinates,hi]

lemma horizontalCoordinates_secondKind : SecondKind (horizontalCoordinates c hsk H r hcomm hH) :=
  ⟨hsk.axis_add,hsk.ordered⟩

end MalcevCharacters
end
end
 

 
section
noncomputable section
namespace RationalLatticeCover
open MeasureTheory RationalQuotientFunctions RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Λ Γ : Subgroup G}

 
def coverMap (h : Λ ≤ Γ) : C(G⧸Λ,G⧸Γ) :=
  ⟨cosetLift Λ (fun g => (QuotientGroup.mk g : G⧸Γ)) (by
      intro g a ha
      exact QuotientGroup.mk_mul_of_mem _ (h ha)),
    continuous_cosetLift _ _ _ QuotientGroup.continuous_mk⟩

omit [IsTopologicalGroup G] in
@[simp] lemma coverMap_mk [IsTopologicalGroup G] (h : Λ ≤ Γ) (g : G) :
    coverMap h (QuotientGroup.mk g) = QuotientGroup.mk g := rfl

omit [IsTopologicalGroup G] in
lemma coverMap_smul [IsTopologicalGroup G] (h : Λ ≤ Γ) (g : G) (x : G⧸Λ) :
    coverMap h (g • x) = g • coverMap h x := by
  induction x using Quotient.inductionOn with | h a => rfl

omit [IsTopologicalGroup G] in
lemma coverMap_surjective [IsTopologicalGroup G] (h : Λ ≤ Γ) :
    Function.Surjective (coverMap h) := by
  intro x
  induction x using Quotient.inductionOn with | h a => exact ⟨QuotientGroup.mk a,rfl⟩

variable [MeasurableSpace (G⧸Λ)] [BorelSpace (G⧸Λ)]
  [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

 

theorem map_coordinateHaar {d : ℕ} (c : RealCoordinates G d)
    (hint : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
    (h : Λ ≤ Γ) (μ : ProbabilityMeasure (G⧸Γ)) (ν : ProbabilityMeasure (G⧸Λ))
    [SMulInvariantMeasure G (G⧸Γ) (μ : Measure (G⧸Γ))]
    [SMulInvariantMeasure G (G⧸Λ) (ν : Measure (G⧸Λ))] :
    Measure.map (coverMap h) (ν : Measure (G⧸Λ)) = (μ : Measure (G⧸Γ)) := by
  let q := coverMap h
  let : SMulInvariantMeasure G (G⧸Γ) (Measure.map q (ν : Measure (G⧸Λ))) :=
    smulInvariantMeasure_map (ν : Measure (G⧸Λ)) q (coverMap_smul h) q.continuous.measurable
  let ρ : ProbabilityMeasure (G⧸Γ) := ν.map q
  have hρ : SMulInvariantMeasure G (G⧸Γ) (ρ : Measure (G⧸Γ)) := by
    change SMulInvariantMeasure G (G⧸Γ) (Measure.map q (ν : Measure (G⧸Λ)))
    infer_instance
  obtain ⟨hair,hh,hu⟩ := existsUnique_coordinateHaar c Γ hint
  have he : ρ=μ := (hu ρ hρ).trans (hu μ inferInstance).symm
  exact congrArg (fun p : ProbabilityMeasure (G⧸Γ) => (p : Measure (G⧸Γ))) he

end RationalLatticeCover

end
end
end
end
end

end OAI
