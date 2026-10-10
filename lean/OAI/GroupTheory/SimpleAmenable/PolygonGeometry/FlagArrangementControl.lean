import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagSites
import OAI.GroupTheory.SimpleAmenable.RandomFields.UniformThresholdCDF

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagArrangementControl
open Classical MeasureTheory

theorem flagValue_arrangement {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (S : Finset PlaneCut)
    (hS : ∀p q,(∀l∈S,squareSign l p=squareSign l q) → f p=f q)
    (z w : SquareFlag a v)
    (hs : ∀l∈S,¬ FlagSeparates l.1 l.2 z w) :
    flagValue f ⟨S,hS⟩ z=flagValue f ⟨S,hS⟩ w := by
  obtain ⟨N,hN,hz,hf⟩ := flagValue_spec f ⟨S,hS⟩ z
  obtain ⟨M,hM,hw,hg⟩ := flagValue_spec f ⟨S,hS⟩ w
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z (hN.inter (arrangementNeighborhood_open a S z.val))
    ⟨hz,self_mem_arrangementNeighborhood a S z.val⟩
  obtain ⟨q,hq,hqv⟩ := squareSector_generic w (hM.inter (arrangementNeighborhood_open a S w.val))
    ⟨hw,self_mem_arrangementNeighborhood a S w.val⟩
  rw [← hf p hp.1 hpv,← hg q hq.1 hqv]
  apply hS p q
  intro l hl
  have h₁ := planeSign_neighborhood (p:=⟨p.val,p.property.2.2⟩) hp.2 hpv hl
  have h₂ := planeSign_neighborhood (p:=⟨q.val,q.property.2.2⟩) hq.2 hqv hl
  change squareSign l p=_ at h₁
  change squareSign l q=_ at h₂
  rw [h₁,h₂]
  apply decide_eq_decide.mpr
  have h := not_not.mp (hs l hl)
  simpa only [flagMem_halfPlane] using h

theorem flagMem_arrangement {a : ℕ} {v : ℝ×ℝ} (U : polygonAlgebra a) :
    ∃S : Finset PlaneCut,∀z w : SquareFlag a v,
      (∀l∈S,¬ FlagSeparates l.1 l.2 z w) → (flagMem U z ↔ flagMem U w) := by
  obtain ⟨S,hS⟩ := polygon_hasSquareArrangement U.property
  refine ⟨S,fun z w h => ?_⟩
  unfold flagMem
  rw [flagValue_arrangement (fun p => decide (p∈U.val)) S hS z w h]

theorem separatorMatrix_zero_of_cut {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) (z w : SquareFlag a v)
    (j : Fin 4) (c : CutRing) (hc : FlagSeparates j c z w)
    (hcut : |conjugate c| ≤ κ/s) :
    separatorMatrix (thresholdLaw s κ) z w=0 := by
  obtain ⟨d,hd,hdmin⟩ := flagSeparates_exists_min j z w ⟨c,hc⟩
  have h : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have hd' : |conjugate d| ≤ κ/s := (hdmin c hc).trans hcut
  have hp : directionNoCutProbability s κ j z w=0 := by
    rw [directionNoCutProbability,directionNoCut_of_min j z w d hd hdmin,
      uniformInterval_Iio h,intervalCDF]
    rw [max_eq_right (by linarith [min_le_right (2*κ/s) |conjugate d|]),zero_div]
  rw [separatorMatrix_product hs hκ]
  exact Finset.prod_eq_zero (Finset.mem_univ j) hp

theorem separatorMatrix_ne_zero_signs {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) (S : Finset PlaneCut)
    (hS : ∀l∈S,|conjugate l.2| ≤ κ/s) (z w : SquareFlag a v)
    (hp : separatorMatrix (thresholdLaw s κ) z w ≠ 0) :
    ∀l∈S,¬ FlagSeparates l.1 l.2 z w := by
  intro l hl hsep
  exact hp (separatorMatrix_zero_of_cut hs hκ z w l.1 l.2 hsep (hS l hl))

theorem separatorMatrix_controls_step {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) :
    ∃R : ℝ, 0 ≤ R ∧ ∀(s κ : ℝ),0 < s → 0 < κ → R ≤ κ/s →
      ∀z w : SquareFlag a v,separatorMatrix (thresholdLaw s κ) z w ≠ 0 →
        flagValue f hf z=flagValue f hf w := by
  obtain ⟨S,hS⟩ := hf
  let R := ∑l∈S,|conjugate l.2|
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨R,hR,fun s κ hs hκ hRs z w hp => ?_⟩
  apply flagValue_arrangement f S hS z w
  apply separatorMatrix_ne_zero_signs hs hκ S _ z w hp
  intro l hl
  exact (Finset.single_le_sum (fun _ _ => abs_nonneg _) hl).trans hRs

end FlagArrangementControl

section SquareAffineCharts
open Classical

theorem floor_add_unit {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) (y : ℝ) :
    ⌊x+y⌋ = ⌊y⌋ + if x < 1-Int.fract y then 0 else 1 := by
  have hy₀ := Int.floor_le y
  have hy₁ := Int.lt_floor_add_one y
  by_cases h : x < 1-Int.fract y
  · rw [ite_eq_left h,add_zero]
    simp only [Int.fract] at h
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  · rw [ite_eq_right h]
    simp only [Int.fract] at h
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith

noncomputable def squareTranslationPeriod {a : ℕ} (u : CutRing×CutRing)
    (p : GenericSquare a) : ℤ×ℤ :=
  (⌊p.val.1+ordinary u.1⌋,⌊p.val.2+ordinary u.2⌋)

theorem squareTranslationPeriod_arrangement {a : ℕ} (u : CutRing×CutRing) :
    HasSquareArrangement (squareTranslationPeriod (a:=a) u) := by
  let c₁ : CutRing := (⌊ordinary u.1⌋:CutRing)+1-u.1
  let c₂ : CutRing := (⌊ordinary u.2⌋:CutRing)+1-u.2
  have hc₁ : ordinary c₁=1-Int.fract (ordinary u.1) := by simp only [c₁,map_sub,map_add,map_intCast,map_one,Int.fract]; ring
  have hc₂ : ordinary c₂=1-Int.fract (ordinary u.2) := by simp only [c₂,map_sub,map_add,map_intCast,map_one,Int.fract]; ring
  refine ⟨{(0,c₁),(1,c₂)},fun p q h => ?_⟩
  have h₁ := decide_eq_decide.mp (h (0,c₁) (by simp))
  have h₂ := decide_eq_decide.mp (h (1,c₂) (by simp))
  change (p.val.1<ordinary c₁ ↔ q.val.1<ordinary c₁) at h₁
  change (p.val.2<ordinary c₂ ↔ q.val.2<ordinary c₂) at h₂
  rw [hc₁] at h₁
  rw [hc₂] at h₂
  apply Prod.ext
  · change ⌊p.val.1+ordinary u.1⌋=⌊q.val.1+ordinary u.1⌋
    rw [floor_add_unit p.property.1.1 p.property.1.2,floor_add_unit q.property.1.1 q.property.1.2]
    simp only [h₁]
  · change ⌊p.val.2+ordinary u.2⌋=⌊q.val.2+ordinary u.2⌋
    rw [floor_add_unit p.property.2.1.1 p.property.2.1.2,floor_add_unit q.property.2.1.1 q.property.2.1.2]
    simp only [h₂]

theorem squareTranslationPeriod_germ {a : ℕ} {v : ℝ×ℝ}
    (u : CutRing×CutRing) (z : SquareFlag a v) :
    IsSquareGerm (squareTranslationPeriod u) z (flagShiftPeriod u z) := by
  let k := flagShiftPeriod u z
  let t := u-SquareStep.intPair k
  let b : ℝ×ℝ := (ordinary t.1,ordinary t.2)
  have hbase : (flagTranslate u z).val=z.val+b := by
    apply Prod.ext <;> simp only [flagTranslate_val,flagFract_eq,b,t,k,flagShiftPeriod,SquareStep.intPair,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,map_sub,map_intCast] <;> ring
  let M : Set (ℝ×ℝ) := (fun p => p+b) ⁻¹' arrangementNeighborhood a SquareStep.squareEdgeCuts (flagTranslate u z).val
  refine ⟨M,(arrangementNeighborhood_open _ _ _).preimage (continuous_id.add continuous_const),?_,fun p hp hpv => ?_⟩
  · change z.val+b ∈ arrangementNeighborhood a SquareStep.squareEdgeCuts (flagTranslate u z).val
    rw [← hbase]
    exact self_mem_arrangementNeighborhood _ _ _
  · let q : GenericPlane a := GenericPlane.shift t ⟨p.val,p.property.2.2⟩
    have hqv : q.val ∈ planeSector a (flagTranslate u z).val v := by
      rw [hbase]
      exact (planeSector_add_iff z.val v b p.val).mpr hpv
    have hpq : q.val ∈ arrangementNeighborhood a SquareStep.squareEdgeCuts (flagTranslate u z).val := hp
    have hqs := sector_enters_square (flagTranslate u z).property.2 hpq hqv
    have hx : 0 ≤ p.val.1+ordinary u.1-(k.1:ℝ) ∧ p.val.1+ordinary u.1-(k.1:ℝ) < 1 := by
      simpa only [q,GenericPlane.shift,t,SquareStep.intPair,Prod.fst_add,Prod.fst_sub,map_sub,map_intCast,← add_sub_assoc,Set.mem_Ico] using hqs.1
    have hy : 0 ≤ p.val.2+ordinary u.2-(k.2:ℝ) ∧ p.val.2+ordinary u.2-(k.2:ℝ) < 1 := by
      simpa only [q,GenericPlane.shift,t,SquareStep.intPair,Prod.snd_add,Prod.snd_sub,map_sub,map_intCast,← add_sub_assoc,Set.mem_Ico] using hqs.2
    apply Prod.ext
    · exact Int.floor_eq_iff.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
    · exact Int.floor_eq_iff.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩

theorem squareTranslationPeriod_flagValue {a : ℕ} {v : ℝ×ℝ}
    (u : CutRing×CutRing) (z : SquareFlag a v) :
    flagValue (squareTranslationPeriod u) (squareTranslationPeriod_arrangement u) z=flagShiftPeriod u z :=
  flagValue_eq _ _ _ (squareTranslationPeriod_germ u z)

theorem squareArrangement_pair {a : ℕ} {K J : Type*} {f : GenericSquare a → K} {g : GenericSquare a → J}
    (hf : HasSquareArrangement f) (hg : HasSquareArrangement g) :
    HasSquareArrangement (fun p => (f p,g p)) := by
  obtain ⟨S,hS⟩ := hf
  obtain ⟨T,hT⟩ := hg
  refine ⟨S∪T,fun p q h => Prod.ext (hS p q (fun l hl => h l (Finset.mem_union_left _ hl)))
    (hT p q (fun l hl => h l (Finset.mem_union_right _ hl)))⟩

theorem squareArrangement_finite_family {a : ℕ} {ι K : Type*} [Finite ι]
    (f : ι → GenericSquare a → K) (hf : ∀i,HasSquareArrangement (f i)) :
    HasSquareArrangement (fun p i => f i p) := by
  let := Fintype.ofFinite ι
  choose S hS using hf
  refine ⟨Finset.univ.biUnion S,fun p q h => funext (fun i => hS i p q (fun l hl => ?_))⟩
  exact h l (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hl⟩)

end SquareAffineCharts

end SimpleAmenable
end
end

end OAI
