import Mathlib
import OAI.Analysis.Commutator.DiffuseProjection
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.MatrixDiagonal
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.RelativeMatrix

open Matrix

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype I] [DecidableEq I]

variable (M : VonNeumannAlgebra H) (φ : Matrix I I ℂ →⋆ₐ[ℂ] M)

abbrev concrete : Matrix I I ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype.comp φ

def relativeStar : StarSubalgebra ℂ (H →L[ℂ] H) :=
  M.toStarSubalgebra ⊓ StarSubalgebra.centralizer ℂ (Set.range (concrete M φ))

lemma mem_relativeStar (a : H →L[ℂ] H) : a∈relativeStar M φ ↔
    a∈M ∧ ∀ x : Matrix I I ℂ,concrete M φ x*a=a*concrete M φ x := by
  constructor
  · intro ha
    refine ⟨ha.1,fun x => ?_⟩
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp ha.2 _ ⟨x,rfl⟩).1
  · rintro ⟨ha,hc⟩
    refine ⟨ha,(StarSubalgebra.mem_centralizer_iff ℂ).mpr ?_⟩
    rintro b ⟨x,rfl⟩
    exact ⟨hc x,by simpa only [map_star] using hc (star x)⟩

def relative : VonNeumannAlgebra H where
  toStarSubalgebra := relativeStar M φ
  centralizer_centralizer' := by
    apply Set.Subset.antisymm
    · intro a ha
      apply (mem_relativeStar M φ a).mpr
      constructor
      · change a∈(M : Set (H →L[ℂ] H))
        rw [←M.centralizer_centralizer]
        intro c hc
        apply ha c
        intro b hb
        exact hc b ((mem_relativeStar M φ b).mp hb).1
      · intro x
        apply ha (concrete M φ x)
        intro b hb
        exact (((mem_relativeStar M φ b).mp hb).2 x).symm
    · exact Set.subset_centralizer_centralizer

lemma mem_relative (a : H →L[ℂ] H) : a∈relative M φ ↔
    a∈M ∧ ∀ x : Matrix I I ℂ,concrete M φ x*a=a*concrete M φ x :=
  mem_relativeStar M φ a

lemma le_original : relative M φ≤M := fun a ha => ((mem_relative M φ a).mp ha).1

lemma diagonal_mem (o : I) (a : M) :
    (MatrixDiagonal.diagonal φ o a:H →L[ℂ] H)∈relative M φ := by
  apply (mem_relative M φ _).mpr
  exact ⟨(MatrixDiagonal.diagonal φ o a).property,fun x =>
    congrArg Subtype.val (MatrixDiagonal.commutes φ o a x)⟩

lemma isFactor (hM : FactorCorner.IsFactor M) (o : I) :
    FactorCorner.IsFactor (relative M φ) := by
  intro c hc hcentral
  have hcM := (mem_relative M φ c).mp hc
  let cM : M := ⟨c,hcM.1⟩
  apply hM c hcM.1
  intro a ha
  have hcomm : Commute (⟨a,ha⟩:M) cM :=
    MatrixDiagonal.central_of_commutes_diagonal φ o cM
      (fun x => Subtype.ext (hcM.2 x))
      (fun b => Subtype.ext (hcentral _ (diagonal_mem M φ o b))) ⟨a,ha⟩
  exact congrArg Subtype.val hcomm.eq

lemma noMinimal (hdiffuse : DiffuseProjection.HasNoMinimalProjections M) (o : I) :
    DiffuseProjection.HasNoMinimalProjections (relative M φ) := by
  intro p hpN hp hpn
  have hpMem := (mem_relative M φ p).mp hpN
  let a : M := ⟨p,hpMem.1⟩
  have ha : IsStarProjection a :=
    ⟨Subtype.ext hp.isIdempotentElem.eq,Subtype.ext hp.isSelfAdjoint.star_eq⟩
  let e : M := φ (single o o 1)
  have he : IsStarProjection e := by
    apply IsStarProjection.map _ φ
    constructor
    · simp only [IsIdempotentElem,single_mul_single_same,one_mul]
    · change star (single o o (1:ℂ))=single o o 1
      simp only [Matrix.star_eq_conjTranspose,conjTranspose_single,star_one]
  have hcomm : Commute e a := Subtype.ext (hpMem.2 (single o o 1))
  have hep : IsStarProjection (e*a) := he.mul ha hcomm
  have hcut : e*a*e=e*a := by
    rw [hcomm.eq,mul_assoc,he.isIdempotentElem.eq,←hcomm.eq]
  have hd : MatrixDiagonal.diagonal φ o (e*a)=a := by
    rw [←hcut]
    exact MatrixDiagonal.fixed φ o a (fun x => Subtype.ext (hpMem.2 x))
  have hen : (↑(e*a):H →L[ℂ] H)≠0 := by
    intro hz
    have hzero : e*a=0 := Subtype.ext hz
    rw [hzero,map_zero] at hd
    exact hpn (congrArg Subtype.val hd.symm)
  obtain ⟨q,hqM,hq,hqn,hqp,hqle⟩ := hdiffuse (e*a) (e*a).property
    (hep.map M.toStarSubalgebra.subtype) hen
  let b : M := ⟨q,hqM⟩
  have hb : IsStarProjection b :=
    ⟨Subtype.ext hq.isIdempotentElem.eq,Subtype.ext hq.isSelfAdjoint.star_eq⟩
  have hbe : b≤e*a := hqle
  have hepe : e*a≤e := (hep.le_iff_mul_eq_left he).mpr hcut
  have hbr : b*e=b := (hb.le_iff_mul_eq_left he).mp (hbe.trans hepe)
  have hbl : e*b=b := (hb.le_iff_mul_eq_right he).mp (hbe.trans hepe)
  let r : M := MatrixDiagonal.diagonal φ o b
  have hr : IsStarProjection r := MatrixDiagonal.projection φ o hb hbr
  have hcutr : e*r*e=b := by rw [MatrixDiagonal.cut,hbl,hbr]
  have hrne : (r:H →L[ℂ] H)≠0 := by
    intro hz
    have hzero : r=0 := Subtype.ext hz
    rw [hzero,mul_zero,zero_mul] at hcutr
    exact hqn (congrArg Subtype.val hcutr.symm)
  have hrp : (r:H →L[ℂ] H)≠p := by
    intro hz
    have hzero : r=a := Subtype.ext hz
    rw [hzero,hcut] at hcutr
    exact hqp (congrArg Subtype.val hcutr.symm)
  have hrle : r≤a := by
    apply (hr.le_iff_mul_eq_left ha).mpr
    rw [←hd,MatrixDiagonal.mul_diagonal φ o b (e*a) hbr,
      (hb.le_iff_mul_eq_left hep).mp hbe]
  exact ⟨r,diagonal_mem M φ o b,hr.map M.toStarSubalgebra.subtype,hrne,hrp,hrle⟩

end Kadison.RelativeMatrix

end

end
end

end OAI
