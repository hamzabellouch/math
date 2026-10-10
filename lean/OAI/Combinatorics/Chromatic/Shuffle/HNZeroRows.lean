import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNSlope
import OAI.Combinatorics.Chromatic.Walls.StringStrip

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

omit [DecidableEq I] in
include hc in
lemma slopeValue_eq_zero_iff (θ : ℝ) (d : I → ℕ) (hd : d≠0) :
    slopeValue c η θ d=0 ↔ slope c η d=θ := by
  rw [slopeValue,sub_eq_zero,SlopeArithmetic.slope,div_eq_iff (ne_of_gt (mass_pos c hc d hd))]

lemma decorated_zero_each (θ : ℝ) (l : List (RowBlock a c η hc))
    (h : ∀b∈l,slopeValue c η θ b.1≤0)
    (hz : slopeValue c η θ (decoratedDimension a c η hc l)=0) :
    ∀b∈l,slopeValue c η θ b.1=0 := by
  induction l with
  | nil=>simp
  | cons b l ih=>
    have hb:=h b (by simp)
    have ht : ∀e∈l,slopeValue c η θ e.1≤0 := fun e he=>h e (by simp [he])
    have hl:=decorated_value_nonpos a c η hc θ l ht
    change slopeValue c η θ (b.1+decoratedDimension a c η hc l)=0 at hz
    rw [slopeValue_add] at hz
    have hb0 : slopeValue c η θ b.1=0 := by linarith
    have hl0 : slopeValue c η θ (decoratedDimension a c η hc l)=0 := by linarith
    intro e he
    rcases List.mem_cons.mp he with rfl|he
    · exact hb0
    · exact ih ht hl0 e he

lemma lowIndex_singleton (θ : ℝ) (d : I → ℕ) (hd : d≠0)
    (hz : slopeValue c η θ d=0) (x : LowHNIndex a c η hc θ d) :
    ∃r : BlockRows a c η hc d,x.val.val.val=[⟨d,r⟩] := by
  have hval : ∀b∈x.val.val.val,slopeValue c η θ b.1≤0 := fun b hb=>
    (slopeValue_nonpos_iff c η hc θ b.1 (x.val.val.property.1 b hb)).mpr (x.val.property b hb)
  have heach:=decorated_zero_each a c η hc θ x.val.val.val hval (by rw [x.property,hz])
  have hs : ∀b∈x.val.val.val,slope c η b.1=θ := fun b hb=>
    (slopeValue_eq_zero_iff c η hc θ b.1 (x.val.val.property.1 b hb)).mp (heach b hb)
  have hn : x.val.val.val≠[] := by
    intro H
    have hh:=x.property
    rw [H] at hh
    exact hd hh.symm
  obtain ⟨b,l,hl⟩:=List.exists_cons_of_ne_nil hn
  have hnil : l=[] := by
    cases l with
    | nil=>rfl
    | cons e l=>
      have H:=x.val.val.property.2
      rw [hl] at H
      have Hbe := (List.pairwise_cons.mp H).1 e (by simp)
      change slope c η e.1 < slope c η b.1 at Hbe
      rw [hs b (by rw [hl]; simp),hs e (by rw [hl]; simp)] at Hbe
      exact (lt_irrefl θ Hbe).elim
  subst l
  have hb : b.1=d := by
    have H:=x.property
    simpa only [hl,decoratedDimension,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using H
  rcases b with ⟨b,r⟩
  dsimp only at hb
  subst b
  exact ⟨r,hl⟩

def lowFromRow (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (r : BlockRows a c η hc d) : LowHNIndex a c η hc θ d :=
  ⟨⟨⟨[⟨d,r⟩],by simp [hd]⟩,by simp [hs]⟩,by simp [decoratedDimension]⟩

lemma lowFromRow_injective (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) :
    Function.Injective (lowFromRow a c η hc θ d hd hs) := by
  intro r s H
  have H':=congrArg (fun x : LowHNIndex a c η hc θ d=>x.val.val.val) H
  simpa only [lowFromRow,List.cons.injEq,and_true,Sigma.mk.inj_iff,heq_eq_eq,true_and] using H'

def lowRowsEquiv (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) :
    BlockRows a c η hc d ≃ LowHNIndex a c η hc θ d :=
  Equiv.ofBijective (lowFromRow a c η hc θ d hd hs)
    ⟨lowFromRow_injective a c η hc θ d hd hs,fun x=>by
      obtain ⟨r,hr⟩:=lowIndex_singleton a c η hc θ d hd
        ((slopeValue_eq_zero_iff c η hc θ d hd).mpr hs) x
      exact ⟨r,Subtype.ext (Subtype.ext (Subtype.ext hr.symm))⟩⟩

lemma lowFromRow_energy (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (r : BlockRows a c η hc d) :
    lowEnergy a κ c η hc θ d (lowFromRow a c η hc θ d hd hs r)=blockRowsEnergy a κ c η hc d r := by
  simp [lowEnergy,lowFromRow,decoratedEnergy,decoratedDimension,eulerForm]

lemma blockRowsEnergy_admissible (d : I → ℕ) (hd : d≠0) :
    Admissible (blockRowsEnergy a κ c η hc d) :=
  admissible_injective (lowEnergy_admissible a κ c η hc (slope c η d) d)
    (lowFromRow a c η hc (slope c η d) d hd rfl)
    (lowFromRow_injective a c η hc (slope c η d) d hd rfl)
    (lowFromRow_energy a κ c η hc (slope c η d) d hd rfl)

lemma lowSeries_on_slope (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ) :
    lowSeries a κ c η hc θ d=series (blockRowsEnergy a κ c η hc d)
      (blockRowsEnergy_admissible a κ c η hc d hd) := by
  symm
  exact series_equiv _ _ (lowRowsEquiv a c η hc θ d hd hs)
    (lowFromRow_energy a κ c η hc θ d hd hs)

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]
local instance (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

abbrev PrimitiveCounts (θ : ℝ) (d : I → ℕ) :=
  DimensionCounts (fun x : SlopeStringStart a c η hc θ × ℕ=>slopeStartRowType a c η hc θ x.1≠0)
    (fun x=>x.1.1.val.1.val) d

def primitiveCountsEnergy (θ : ℝ) (d : I → ℕ) (x : PrimitiveCounts a c η hc θ d) : ℤ :=
  countEnergy _ (fun x=>slopeStartParameter a κ c η hc θ x.1-2*(x.2:ℤ)) x.val

lemma primitiveCounts_onSlope (θ : ℝ) (d : I → ℕ) (x : PrimitiveCounts a c η hc θ d) :
    OnSlopeOrZero c η θ d := by
  rw [←x.property]
  exact countDimension_mem _ _ (slopeDimensions c η hc θ) (fun x=>x.1.1.val.1.property) x.val

def primitiveCountsRows (d : I → ℕ) :
    PrimitiveCounts a c η hc (slope c η d) d ≃ BlockRows a c η hc d :=
  (allUnitRowsEquiv (slopeStartRowType a c η hc (slope c η d))).subtypeEquiv
    (fun x=>by rw [rowsDimension_equiv]; rfl)

lemma primitiveCountsRows_energy (d : I → ℕ) (x : PrimitiveCounts a c η hc (slope c η d) d) :
    blockRowsEnergy a κ c η hc d (primitiveCountsRows a c η hc d x)=
      primitiveCountsEnergy a κ c η hc (slope c η d) d x := by
  change rowsEnergy _ _ (allUnitRowsEquiv _ x.val)=_
  rw [rowsEnergy_equiv]
  rfl

lemma primitiveCountsEnergy_admissible (θ : ℝ) (d : I → ℕ) :
    Admissible (primitiveCountsEnergy a κ c η hc θ d) := by
  classical
  by_cases hd : d=0
  · subst d
    let := dimensionCounts_zero_subsingleton
      (fun x : SlopeStringStart a c η hc θ × ℕ=>slopeStartRowType a c η hc θ x.1≠0)
      (fun x=>x.1.1.val.1.val) (fun x=>x.1.1.property)
    refine ⟨⟨0,fun x=>?_⟩,fun E=>inferInstance⟩
    change countEnergy _ _ x.val≤0
    rw [dimensionCounts_zero_energy _ _ (fun x=>x.1.1.property)]
  · by_cases h : Nonempty (PrimitiveCounts a c η hc θ d)
    · have hs : slope c η d=θ := (primitiveCounts_onSlope a c η hc θ d h.some).resolve_left hd
      subst θ
      exact admissible_injective (blockRowsEnergy_admissible a κ c η hc d hd)
        (primitiveCountsRows a c η hc d) (primitiveCountsRows a c η hc d).injective
        (primitiveCountsRows_energy a κ c η hc d)
    · let : IsEmpty (PrimitiveCounts a c η hc θ d) := not_nonempty_iff.mp h
      exact ⟨⟨0,fun x=>isEmptyElim x⟩,fun _=>inferInstance⟩

def primitiveCountsSeries (θ : ℝ) (d : I → ℕ) : LaurentSeries ℚ :=
  series _ (primitiveCountsEnergy_admissible a κ c η hc θ d)

lemma primitiveCountsSeries_zero (θ : ℝ) : primitiveCountsSeries a κ c η hc θ 0=1 := by
  have he : ∀x : PrimitiveCounts a c η hc θ 0,primitiveCountsEnergy a κ c η hc θ 0 x=0 :=
    fun x=>dimensionCounts_zero_energy _ _ (fun x=>x.1.1.property) _ x
  let := dimensionCounts_zero_subsingleton
    (fun x : SlopeStringStart a c η hc θ × ℕ=>slopeStartRowType a c η hc θ x.1≠0)
    (fun x=>x.1.1.val.1.val) (fun x=>x.1.1.property)
  let : Nonempty (PrimitiveCounts a c η hc θ 0) := ⟨⟨zeroCount _,countDimension_zero _ _⟩⟩
  ext j
  rw [primitiveCountsSeries,series_coeff,HahnSeries.coeff_one]
  by_cases hj : j=0
  · subst j
    have H : ∀x : PrimitiveCounts a c η hc θ 0,primitiveCountsEnergy a κ c η hc θ 0 x= -0 := by simpa using he
    simp only [H,neg_zero]
    simp
  · have H : IsEmpty {x : PrimitiveCounts a c η hc θ 0 // primitiveCountsEnergy a κ c η hc θ 0 x= -j} :=
      ⟨fun x=>hj (by have HH:=x.property; rw [he] at HH; omega)⟩
    let := H
    simp [hj]

end
end ElementaryPositivity.RawShuffle

end

end OAI
