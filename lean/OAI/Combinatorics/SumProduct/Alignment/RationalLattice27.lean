import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice26
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
namespace RationalLattice.QuotientLogImage
open MalcevCharacters
variable {G H : Type*} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable {n m : ℕ} (c : RealCoordinates G n) (d : RealCoordinates H m)
variable (hsk : SecondKind c) (F : G →* H) (hF : Continuous F)
variable (p : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ))
variable (hp : RationalMatrix.real p=(logHomLinear d c F).toLinearMap)
variable (E : RationalEchelon.Chart (LinearMap.ker p))

lemma coordinates_mul (g h : F.range) :
    coordinates c d hsk F hF p hp E (g*h)=
      QuotientLaw.multiply c E (Sum.elim
        (coordinates c d hsk F hF p hp E g) (coordinates c d hsk F hF p hp E h)) := by
  let e:=coordinates c d hsk F hF p hp E
  have hg : g=F.rangeRestrict (canonicalExp c (RationalMatrix.real E.sectionMap (e g))) :=
    (e.symm_apply_apply g).symm
  have hh : h=F.rangeRestrict (canonicalExp c (RationalMatrix.real E.sectionMap (e h))) :=
    (e.symm_apply_apply h).symm
  rw [show g*h=F.rangeRestrict
    (canonicalExp c (RationalMatrix.real E.sectionMap (e g))*
      canonicalExp c (RationalMatrix.real E.sectionMap (e h))) by rw [map_mul,← hg,← hh]]
  rw [coordinates_map]
  rfl

end RationalLattice.QuotientLogImage
end
 
end

section
 

 

noncomputable section
namespace RationalLattice.QuotientLogImage
open MalcevCharacters MalcevWeightedCoordinates
variable {G H : Type*} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable {n m : ℕ} (c : RealCoordinates G n) (d : RealCoordinates H m)
variable (hsk : SecondKind c) (F : G →* H) (hF : Continuous F)
variable (p : (Fin n → ℚ) →ₗ[ℚ] (Fin m → ℚ))
variable (hp : RationalMatrix.real p=(logHomLinear d c F).toLinearMap)
variable (E : RationalEchelon.Chart (LinearMap.ker p))
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ) (hw : ∀ i,0<w i)
variable (hmono : Monotone w)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)

lemma law_eq (x : (Fin E.freeSet.card ⊕ Fin E.freeSet.card) → ℝ) :
    WeightedLawChart.law (coordinates c d hsk F hF p hp E) x=QuotientLaw.multiply c E x := by
  rw [WeightedLawChart.law,coordinates_mul]
  simp only [Homeomorph.apply_symm_apply]
  congr 1
  funext j
  cases j <;> rfl

 

def imageChart : RealCoordinates F.range E.freeSet.card:=
  WeightedLawChart.realCoordinates (coordinates c d hsk F hF p hp E)
    (coordinates_one c d hsk F hF p hp E) (fun i=>w (E.free i))
    (fun i=>hw (E.free i)) (hmono.comp E.free.monotone)
    (fun i=>by simpa only [law_eq c d hsk F hF p hp E] using QuotientLaw.multiply_polynomial c E i)
    (fun i=>by simpa only [law_eq c d hsk F hF p hp E] using
      QuotientLaw.multiply_weighted c E hsk A w hmono hA i)

include hmono hA in
lemma coordinates_adapted (k : ℕ) (g : F.range) :
    g∈(A.level k).map F.rangeRestrict ↔ ∀ i,w (E.free i)<k →
      coordinates c d hsk F hF p hp E g i=0 := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [coordinates_map]
    exact E.real_quotient_level w hmono k (canonicalLog c x)
      ((mem_level_iff_log c A w hmono hA k x).mp hx)
  · intro hg
    let x:=canonicalExp c (RationalMatrix.real E.sectionMap
      (coordinates c d hsk F hF p hp E g))
    refine ⟨x,?_,?_⟩
    · apply (canonicalExp_mem_level_iff c A w hmono hA k _).mpr
      exact E.real_section_level w k _ hg
    · exact (coordinates c d hsk F hF p hp E).symm_apply_apply g

lemma imageChart_adapted (k : ℕ) (g : F.range) :
    g∈(A.level k).map F.rangeRestrict ↔ ∀ i,w (E.free i)<k →
      (imageChart c d hsk F hF p hp E A w hw hmono hA).coord g i=0 :=
  coordinates_adapted c d hsk F hF p hp E A w hmono hA k g

def imageSecondChart : RealCoordinates F.range E.freeSet.card:=
  secondCoordinates (imageChart c d hsk F hF p hp E A w hw hmono hA)

lemma imageSecondChart_secondKind : SecondKind (imageSecondChart c d hsk F hF p hp E A w hw hmono hA) :=
  secondCoordinates_secondKind _

lemma imageSecondChart_adapted (k : ℕ) (g : F.range) :
    g∈(A.level k).map F.rangeRestrict ↔ ∀ i,w (E.free i)<k →
      (imageSecondChart c d hsk F hF p hp E A w hw hmono hA).coord g i=0 := by
  let b:=imageChart c d hsk F hF p hp E A w hw hmono hA
  obtain ⟨r,hr,he⟩:=exists_weight_cutoff (fun i=>w (E.free i)) (hmono.comp E.free.monotone) k
  have hb : ∀ g : F.range,g∈(A.level k).map F.rangeRestrict ↔
      ∀ i : Fin E.freeSet.card,i.val<r → b.coord g i=0 := by
    intro g
    simpa only [he] using imageChart_adapted c d hsk F hF p hp E A w hw hmono hA k g
  simpa only [← he,imageSecondChart,b] using secondCoordinates_adapted b ((A.level k).map F.rangeRestrict) r hb g

lemma imageEmbedding_polynomial (i : Fin m) :
    RationalPolynomialMap.IsPolynomial (fun x=>d.coord
      ((imageChart c d hsk F hF p hp E A w hw hmono hA).coord.symm x:H) i) := by
  have hh:=RationalPolynomialMap.comp (canonicalExp_polynomial d i)
    (RationalMatrix.real_polynomial (p.comp E.sectionMap))
  change RationalPolynomialMap.IsPolynomial (fun x=>d.coord (parametrization c F p E x:H) i)
  simpa only [parametrization_exp c d hsk F hF p hp E] using hh

lemma imageEmbedding_rational (g : F.range)
    (hg : IsRational (imageSecondChart c d hsk F hF p hp E A w hw hmono hA) g) :
    IsRational d (g:H) := by
  have hb:=expProduct_rational (imageChart c d hsk F hF p hp E A w hw hmono hA) hg
  change IsRational (imageChart c d hsk F hF p hp E A w hw hmono hA)
    (expProduct (imageChart c d hsk F hF p hp E A w hw hmono hA)
      (expCoordinates (imageChart c d hsk F hF p hp E A w hw hmono hA) g)) at hb
  rw [expProduct_expCoordinates] at hb
  intro i
  obtain ⟨P,hP⟩:=imageEmbedding_polynomial c d hsk F hF p hp E A w hw hmono hA i
  obtain ⟨q,hq⟩:=eval_rational P
    ((imageChart c d hsk F hF p hp E A w hw hmono hA).coord g) hb
  refine ⟨q,?_⟩
  rw [hq,← hP]
  simp only [Homeomorph.symm_apply_apply]

end RationalLattice.QuotientLogImage
end
 
end

section
 

 

noncomputable section
namespace RationalLattice
open MalcevCharacters MalcevWeightedCoordinates
variable {G K : Type} [Group G] [Group K]
variable [TopologicalSpace G] [TopologicalSpace K]
variable [IsTopologicalGroup G] [IsTopologicalGroup K]
variable {m n : ℕ} (c : RealCoordinates G m) (d : RealCoordinates K n)
variable (hsk : SecondKind d) (F : K →* G) (hF : Continuous F)
variable (hinj : Function.Injective F)
variable (hrat : ∀ x,IsRational d x → IsRational c (F x))
variable (Γ : Subgroup G) (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)

include hΓ hF hinj in
omit [IsTopologicalGroup K] in
lemma rationalInduced_discrete : DiscreteTopology (Γ.comap F) := by
  let : DiscreteTopology Γ:=integerCoordinates_discrete c Γ hΓ
  exact DiscreteTopology.preimage_of_continuous_injective (Γ:Set G) hF hinj

include hsk hF hinj hrat hΓ in
lemma rationalInduced_compact_reps (B : Subgroup K) (w : Fin n → ℕ)
    (hmono : Monotone w) (l : ℕ)
    (hB : ∀ g : K,g∈B ↔ ∀ i,w i<l → d.coord g i=0) :
    CompactGroupProducts.HasCompactReps B (Γ.comap F) := by
  obtain ⟨Λ,e,hΛ,hle,_,he,_⟩:=exists_integer_sublattice_rational c d F
    (rationalHom_polynomial c d hsk F hF hrat) Γ hΓ hF hinj
  obtain ⟨r,_,hr⟩:=exists_weight_cutoff w hmono l
  have hBe : B=coordinateTail e r := by
    ext g
    rw [hB]
    change (∀ i,w i<l → d.coord g i=0) ↔ (∀ i : Fin n,i.val<r → e.coord g i=0)
    simp only [← hr,he]
  obtain ⟨C,hC,hCB,hrep⟩:=coordinateTail_compact_reps e Λ hΛ r
  rw [← hBe] at hCB hrep
  exact ⟨C,hC,hCB,fun g hg=>by
    obtain ⟨a,ha,hag⟩:=hrep g hg
    exact ⟨a,ha,hle hag⟩⟩

include hsk hF hinj hrat hΓ in
lemma rationalInduced_compactSpace : CompactSpace (K⧸Γ.comap F) := by
  obtain ⟨Λ,e,hΛ,hle,_,_,_⟩:=exists_integer_sublattice_rational c d F
    (rationalHom_polynomial c d hsk F hF hrat) Γ hΓ hF hinj
  obtain ⟨C,hC,hrep⟩:=compact_reps_of_integerCoordinates e Λ hΛ
  apply CompactGroupProducts.HasCompactReps.quotient_compactSpace
  refine ⟨C,hC,fun _ _=>Subgroup.mem_top _,?_⟩
  intro g _
  obtain ⟨a,ha,hag⟩:=hrep g
  exact ⟨a,ha,hle hag⟩

include hsk hF hinj hrat hΓ in
lemma rationalConjugate_compact_reps (σ : G) (hσ : IsRational c σ)
    (B : Subgroup K) (w : Fin n → ℕ) (hmono : Monotone w) (l : ℕ)
    (hB : ∀ g : K,g∈B ↔ ∀ i,w i<l → d.coord g i=0) :
    CompactGroupProducts.HasCompactReps B
      ((CubeLocalHaar.conjugateLattice Γ σ).comap F) := by
  have hc : Continuous (conjugateEmbedding F σ) :=
    (continuous_const.mul hF).mul continuous_const
  have hi : Function.Injective (conjugateEmbedding F σ) :=
    (MulAut.conj σ⁻¹).injective.comp hinj
  have hr (x : K) (hx : IsRational d x) :
      IsRational c (conjugateEmbedding F σ x) := by
    rw [conjugateEmbedding_apply]
    exact rational_mul c (rational_mul c (rational_inv c hσ) (hrat x hx)) hσ
  exact rationalInduced_compact_reps c d hsk (conjugateEmbedding F σ) hc hi hr Γ hΓ B w hmono l hB

include hsk hF hinj hrat hΓ in
lemma rationalConjugate_compactSpace (σ : G) (hσ : IsRational c σ) :
    CompactSpace (K⧸(CubeLocalHaar.conjugateLattice Γ σ).comap F) := by
  have hc : Continuous (conjugateEmbedding F σ) :=
    (continuous_const.mul hF).mul continuous_const
  have hi : Function.Injective (conjugateEmbedding F σ) :=
    (MulAut.conj σ⁻¹).injective.comp hinj
  have hr (x : K) (hx : IsRational d x) :
      IsRational c (conjugateEmbedding F σ x) := by
    rw [conjugateEmbedding_apply]
    exact rational_mul c (rational_mul c (rational_inv c hσ) (hrat x hx)) hσ
  exact rationalInduced_compactSpace c d hsk (conjugateEmbedding F σ) hc hi hr Γ hΓ

include hΓ hF hinj in
omit [IsTopologicalGroup K] in
lemma rationalConjugate_discrete (σ : G) :
    DiscreteTopology ((CubeLocalHaar.conjugateLattice Γ σ).comap F) := by
  exact rationalInduced_discrete c (conjugateEmbedding F σ)
    ((continuous_const.mul hF).mul continuous_const)
    ((MulAut.conj σ⁻¹).injective.comp hinj) Γ hΓ

include hΓ in
lemma rationalConjugate_ambient_discrete (σ : G) :
    DiscreteTopology (CubeLocalHaar.conjugateLattice Γ σ) := by
  exact rationalInduced_discrete c (MulAut.conj σ⁻¹).toMonoidHom
    ((continuous_const.mul continuous_id).mul continuous_const)
    (MulAut.conj σ⁻¹).injective Γ hΓ

include hΓ in
lemma rationalConjugate_quotient_t2 (σ : G) :
    T2Space (G⧸CubeLocalHaar.conjugateLattice Γ σ) := by
  let : T2Space G:=c.coord.symm.t2Space
  let : DiscreteTopology (CubeLocalHaar.conjugateLattice Γ σ):=
    rationalConjugate_ambient_discrete c Γ hΓ σ
  let : IsClosed (CubeLocalHaar.conjugateLattice Γ σ : Set G):=
    (CubeLocalHaar.conjugateLattice Γ σ).isClosed_of_discreteTopology
  infer_instance

end RationalLattice
end
 

end
end

end OAI
