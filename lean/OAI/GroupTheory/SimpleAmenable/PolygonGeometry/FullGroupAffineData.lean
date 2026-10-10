import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagArrangementControl

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FullGroupAffineData
open Classical

theorem fullGroupSquareShift_exists {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) (p : GenericSquare a) :
    ∃u : CutRing×CutRing,(g.val (i,p)).2.val=p.val+(ordinary u.1,ordinary u.2) := by
  obtain ⟨S,hS,hcover⟩ := g.property
  obtain ⟨c,hc,hi,hp⟩ := hcover (i,p)
  change i=c.source at hi
  refine ⟨c.shift-SquareStep.intPair (squareTranslationPeriod c.shift p),?_⟩
  rw [hi,hS c hc p hp]
  apply Prod.ext <;>
    simp only [translate,Int.fract,squareTranslationPeriod,SquareStep.intPair,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,map_sub,map_intCast] <;> ring

noncomputable def fullGroupSquareShift {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) (p : GenericSquare a) : CutRing×CutRing :=
  (fullGroupSquareShift_exists g i p).choose

theorem fullGroupSquareShift_spec {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) (p : GenericSquare a) :
    (g.val (i,p)).2.val=p.val+(ordinary (fullGroupSquareShift g i p).1,
      ordinary (fullGroupSquareShift g i p).2) := (fullGroupSquareShift_exists g i p).choose_spec

noncomputable def fullGroupAffineData {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) (p : GenericSquare a) : Fin m × (CutRing×CutRing) :=
  ((g.val (i,p)).1,fullGroupSquareShift g i p)

theorem fullGroupAffineData_chart {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) (p : GenericSquare a) (c : TableChart a m) (hc : c.Holds g.val)
    (hi : i=c.source) (hp : p∈c.domain.val) :
    fullGroupAffineData g i p=(c.target,c.shift-SquareStep.intPair (squareTranslationPeriod c.shift p)) := by
  have he : g.val (i,p)=(c.target,translate a c.shift p) := by rw [hi,hc p hp]
  unfold fullGroupAffineData
  apply Prod.ext
  · change (g.val (i,p)).1=c.target
    exact congrArg Prod.fst he
  · have hv := fullGroupSquareShift_spec g i p
    rw [he] at hv
    apply Prod.ext
    · apply ordinary_injective
      have hx := congrArg Prod.fst hv
      simpa only [translate,Int.fract,squareTranslationPeriod,SquareStep.intPair,
        Prod.fst_sub,Prod.fst_add,map_sub,map_intCast,add_sub_assoc,add_right_inj] using hx.symm
    · apply ordinary_injective
      have hx := congrArg Prod.snd hv
      simpa only [translate,Int.fract,squareTranslationPeriod,SquareStep.intPair,
        Prod.snd_sub,Prod.snd_add,map_sub,map_intCast,add_sub_assoc,add_right_inj] using hx.symm

theorem fullGroupAffineData_arrangement {a m : ℕ} (g : polygonFullGroup a m)
    (i : Fin m) : HasSquareArrangement (fullGroupAffineData g i) := by
  obtain ⟨S,hS,hcover⟩ := g.property
  let f (c : S) (p : GenericSquare a) := (decide (p∈c.val.domain.val),squareTranslationPeriod c.val.shift p)
  have hf (c : S) : HasSquareArrangement (f c) :=
    squareArrangement_pair (polygon_hasSquareArrangement c.val.domain.property)
      (squareTranslationPeriod_arrangement c.val.shift)
  obtain ⟨T,hT⟩ := squareArrangement_finite_family f hf
  refine ⟨T,fun p q h => ?_⟩
  obtain ⟨c,hc,hi,hp⟩ := hcover (i,p)
  have he := congrFun (hT p q h) ⟨c,hc⟩
  have hq : q∈c.domain.val := (decide_eq_decide.mp (congrArg Prod.fst he)).mp hp
  rw [fullGroupAffineData_chart g i p c (hS c hc) hi hp,
    fullGroupAffineData_chart g i q c (hS c hc) hi hq]
  exact congrArg (fun k => (c.target,c.shift-SquareStep.intPair k)) (congrArg Prod.snd he)

noncomputable def flagAffineData {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (i : Fin m) (z : SquareFlag a v) : Fin m × (CutRing×CutRing) :=
  flagValue (fullGroupAffineData g i) (fullGroupAffineData_arrangement g i) z

theorem flagAffineData_chart {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (i : Fin m) (z : SquareFlag a v) (c : TableChart a m) (hc : c.Holds g.val)
    (hi : i=c.source) (hz : flagMem c.domain z) :
    flagAffineData g i z=(c.target,c.shift-SquareStep.intPair (flagShiftPeriod c.shift z)) := by
  obtain ⟨N,hN,hzN,hf⟩ := flagMem_iff c.domain z
  obtain ⟨M,hM,hzM,hp⟩ := squareTranslationPeriod_germ c.shift z
  apply flagValue_eq
  refine ⟨N∩M,hN.inter hM,⟨hzN,hzM⟩,fun p hpm hpv => ?_⟩
  rw [fullGroupAffineData_chart g i p c hc hi ((hf p hpm.1 hpv).mpr hz),hp p hpm.2 hpv]

theorem flagAffineData_selected {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) :
    flagAffineData g z.1 z.2=((flagChart g z).target,
      (flagChart g z).shift-SquareStep.intPair (flagShiftPeriod (flagChart g z).shift z.2)) :=
  flagAffineData_chart g z.1 z.2 (flagChart g z) (flagChart_spec g z).1
    (flagChart_spec g z).2.1 (flagChart_spec g z).2.2

theorem flagAffineData_action {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) :
    (flagAction g z).1=(flagAffineData g z.1 z.2).1 ∧
    (flagAction g z).2.val=z.2.val+
      (ordinary (flagAffineData g z.1 z.2).2.1,ordinary (flagAffineData g z.1 z.2).2.2) := by
  rw [flagAffineData_selected]
  refine ⟨rfl,?_⟩
  apply Prod.ext <;>
    simp only [flagAction,flagTranslate_val,flagFract_eq,flagShiftPeriod,SquareStep.intPair,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,map_sub,map_intCast] <;> ring

theorem flagAffineData_conjugate {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) :
    flagSiteConjugate (flagSiteAction hD g z)=flagSiteConjugate z+
      (conjugate (flagAffineData g z.val.1 z.val.2).2.1,
       conjugate (flagAffineData g z.val.1 z.val.2).2.2) := by
  rw [flagAffineData_selected,flagSiteConjugate_action hD]
  apply Prod.ext <;>
    simp only [SquareStep.intPair,Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,
      map_sub,map_intCast] <;> ring

end FullGroupAffineData

section FlagAffineControl
open Classical

theorem squareArrangement_finite_range {a : ℕ} {K : Type*} (f : GenericSquare a → K)
    (hf : HasSquareArrangement f) : (Set.range f).Finite := by
  obtain ⟨S,hS⟩ := hf
  let p (k : Set.range f) : GenericSquare a := k.property.choose
  have hp (k : Set.range f) : f (p k)=k.val := k.property.choose_spec
  let q (k : Set.range f) : S → Bool := fun l => squareSign l.val (p k)
  have hq : Function.Injective q := by
    intro k j h
    apply Subtype.ext
    rw [← hp k,← hp j]
    exact hS (p k) (p j) (fun l hl => congrFun h ⟨l,hl⟩)
  have : Finite (Set.range f) := Finite.of_injective q hq
  exact Set.toFinite _

theorem flagValue_mem_range {a : ℕ} {v : ℝ×ℝ} {K : Type*} (f : GenericSquare a → K)
    (hf : HasSquareArrangement f) (z : SquareFlag a v) : flagValue f hf z∈Set.range f := by
  obtain ⟨N,hN,hz,hf'⟩ := flagValue_spec f hf z
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z hN hz
  exact ⟨p,hf' p hp hpv⟩

theorem flagValue_finite_range {a : ℕ} {v : ℝ×ℝ} {K : Type*} (f : GenericSquare a → K)
    (hf : HasSquareArrangement f) : (Set.range (flagValue (v:=v) f hf)).Finite :=
  (squareArrangement_finite_range f hf).subset (by rintro _ ⟨z,rfl⟩; exact flagValue_mem_range f hf z)

theorem flagAffineData_finite_range {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m) :
    (Set.range (fun z : FlagTrackPoint a m v => flagAffineData g z.1 z.2)).Finite := by
  have h (i : Fin m) : (Set.range (flagAffineData (v:=v) g i)).Finite :=
    flagValue_finite_range (fullGroupAffineData g i) (fullGroupAffineData_arrangement g i)
  apply (Set.finite_iUnion h).subset
  rintro _ ⟨z,rfl⟩
  exact Set.mem_iUnion.mpr ⟨z.1,⟨z.2,rfl⟩⟩

theorem flagAffineData_bounded {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (f : (CutRing×CutRing) → ℝ) :
    ∃C : ℝ,0 ≤ C ∧ ∀z : FlagTrackPoint a m v,|f (flagAffineData g z.1 z.2).2| ≤ C := by
  let S := (flagAffineData_finite_range (v:=v) g).toFinset
  refine ⟨∑d∈S,|f d.2|,Finset.sum_nonneg (fun _ _ => abs_nonneg _),fun z => ?_⟩
  apply Finset.single_le_sum (f:=fun d : Fin m × (CutRing×CutRing) => |f d.2|) (fun _ _ => abs_nonneg _)
  change flagAffineData g z.1 z.2∈(flagAffineData_finite_range (v:=v) g).toFinset
  exact (Set.Finite.mem_toFinset _).mpr ⟨z,rfl⟩

theorem flagAffineData_separator_control {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m) :
    ∃R : ℝ,0 ≤ R ∧ ∀(s κ : ℝ),0 < s → 0 < κ → R ≤ κ/s →
      ∀(i : Fin m) (z w : SquareFlag a v),separatorMatrix (thresholdLaw s κ) z w ≠ 0 →
        flagAffineData g i z=flagAffineData g i w := by
  choose R hR hcontrol using fun i : Fin m => separatorMatrix_controls_step (v:=v)
    (fullGroupAffineData g i) (fullGroupAffineData_arrangement g i)
  refine ⟨∑i,R i,Finset.sum_nonneg (fun i _ => hR i),fun s κ hs hκ hbound i z w hp => ?_⟩
  exact hcontrol i s κ hs hκ ((Finset.single_le_sum
    (fun j _ => hR j) (Finset.mem_univ i)).trans hbound) z w hp

theorem flagAffineData_inverse {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) :
    flagAffineData g⁻¹ (flagAction g z).1 (flagAction g z).2=(z.1,-(flagAffineData g z.1 z.2).2) := by
  have he : flagAction g⁻¹ (flagAction g z)=z := by rw [← flagAction_mul,inv_mul_cancel,flagAction_one]
  have hf := flagAffineData_action g z
  have hb := flagAffineData_action g⁻¹ (flagAction g z)
  rw [he] at hb
  apply Prod.ext
  · exact hb.1.symm
  · rw [hf.2] at hb
    apply Prod.ext
    · apply ordinary_injective
      have hh := congrArg Prod.fst hb.2
      simp only [Prod.fst_add] at hh
      simp only [Prod.fst_neg,map_neg]
      linarith
    · apply ordinary_injective
      have hh := congrArg Prod.snd hb.2
      simp only [Prod.snd_add] at hh
      simp only [Prod.snd_neg,map_neg]
      linarith

end FlagAffineControl

end SimpleAmenable
end
end

end OAI
