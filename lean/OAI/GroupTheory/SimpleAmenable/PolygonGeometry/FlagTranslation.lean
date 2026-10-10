import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PeriodicSlotStars
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagGerms

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagTranslation
open Classical

noncomputable def flagFloor (x d : ℝ) : ℤ :=
  if d<0 then -1-⌊-x⌋ else ⌊x⌋

noncomputable def flagFract (x d : ℝ) : ℝ :=
  if d<0 then 1-Int.fract (-x) else Int.fract x

theorem flagFract_eq (x d : ℝ) : flagFract x d=x-(flagFloor x d:ℝ) := by
  unfold flagFract flagFloor
  split_ifs <;> simp only [Int.fract,Int.cast_sub,Int.cast_neg,Int.cast_one]
  ring

theorem flagFract_add_int (x d : ℝ) (n : ℤ) : flagFract (x+n) d=flagFract x d := by
  unfold flagFract
  split_ifs
  · rw [neg_add,← sub_eq_add_neg,Int.fract_sub_intCast]
  · rw [Int.fract_add_intCast]

theorem flagFract_sub_int (x d : ℝ) (n : ℤ) : flagFract (x-n) d=flagFract x d := by
  simpa [sub_eq_add_neg] using flagFract_add_int x d (-n)

theorem flagFract_flagFract_add (x y d : ℝ) :
    flagFract (flagFract x d+y) d=flagFract (x+y) d := by
  rw [flagFract_eq x d,sub_add_eq_add_sub,flagFract_sub_int]

theorem flagFract_boundary (x d : ℝ) (hd : d≠0) :
    flagFract x d∈Set.Icc (0:ℝ) 1 ∧
      (flagFract x d=0 → 0<d) ∧ (flagFract x d=1 → d<0) := by
  have h₀ := Int.fract_nonneg x
  have h₁ := Int.fract_lt_one x
  have h₀' := Int.fract_nonneg (-x)
  have h₁' := Int.fract_lt_one (-x)
  unfold flagFract
  split_ifs with ht
  · exact ⟨⟨by linarith,by linarith⟩,fun he => by linarith,fun _ => ht⟩
  · exact ⟨⟨h₀,le_of_lt h₁⟩,fun _ => lt_of_le_of_ne (le_of_not_gt ht) hd.symm,
      fun he => by linarith⟩

theorem flagFract_self {x d : ℝ} (hx : x∈Set.Icc (0:ℝ) 1)
    (h₀ : x=0 → 0<d) (h₁ : x=1 → d<0) : flagFract x d=x := by
  unfold flagFract
  split_ifs with ht
  · have hx₀ : 0<x := lt_of_le_of_ne hx.1 (by intro he; have := h₀ he.symm; linarith)
    have hf : Int.fract (-x)=1-x := Int.fract_eq_iff.mpr
      ⟨by linarith [hx.2],by linarith,⟨-1,by norm_num; ring⟩⟩
    rw [hf]; ring
  · exact Int.fract_eq_self.mpr ⟨hx.1,lt_of_le_of_ne hx.2 (fun he => ht (h₁ he))⟩

noncomputable def flagTranslate {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing)
    (z : SquareFlag a v) : SquareFlag a v := by
  have hv₁ : v.1≠0 := by simpa [cutForm] using z.property.1 0
  have hv₂ : v.2≠0 := by simpa [cutForm] using z.property.1 1
  have hx := flagFract_boundary (z.val.1+ordinary u.1) v.1 hv₁
  have hy := flagFract_boundary (z.val.2+ordinary u.2) v.2 hv₂
  exact ⟨(flagFract (z.val.1+ordinary u.1) v.1,flagFract (z.val.2+ordinary u.2) v.2),
    z.property.1,hx.1,hy.1,hx.2.1,hx.2.2,hy.2.1,hy.2.2⟩

@[simp] theorem flagTranslate_val {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing)
    (z : SquareFlag a v) : (flagTranslate u z).val=
      (flagFract (z.val.1+ordinary u.1) v.1,flagFract (z.val.2+ordinary u.2) v.2) := rfl

@[simp] theorem flagTranslate_zero {a : ℕ} {v : ℝ×ℝ} (z : SquareFlag a v) :
    flagTranslate 0 z=z := by
  apply Subtype.ext
  simp only [flagTranslate_val,Prod.fst_zero,Prod.snd_zero,map_zero,add_zero]
  exact Prod.ext (flagFract_self z.property.2.1 z.property.2.2.2.1 z.property.2.2.2.2.1)
    (flagFract_self z.property.2.2.1 z.property.2.2.2.2.2.1 z.property.2.2.2.2.2.2)

theorem flagTranslate_add {a : ℕ} {v : ℝ×ℝ} (u w : CutRing×CutRing)
    (z : SquareFlag a v) : flagTranslate (u+w) z=flagTranslate u (flagTranslate w z) := by
  apply Subtype.ext
  simp only [flagTranslate_val,Prod.fst_add,Prod.snd_add,map_add]
  rw [flagFract_flagFract_add,flagFract_flagFract_add]
  congr 1 <;> congr 1 <;> ring

theorem flagTranslate_period {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing) (k : ℤ×ℤ)
    (z : SquareFlag a v) : flagTranslate (u+SquareStep.intPair k) z=flagTranslate u z := by
  apply Subtype.ext
  simp only [flagTranslate_val,SquareStep.intPair,Prod.fst_add,Prod.snd_add,map_add,map_intCast]
  rw [← add_assoc,← add_assoc,flagFract_add_int,flagFract_add_int]

theorem flagTranslate_reduce {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing)
    (z : SquareFlag a v) : flagTranslate u z=flagTranslate (orbitRepresentative u) z := by
  have hu : u=orbitRepresentative u+SquareStep.intPair (u.1.re,u.2.re) := by
    apply Prod.ext <;> apply QuadraticAlgebra.ext <;> simp [orbitRepresentative,SquareStep.intPair,cutTau]
  calc
    _ = flagTranslate (orbitRepresentative u+SquareStep.intPair (u.1.re,u.2.re)) z := congrArg (fun t => flagTranslate t z) hu
    _ = _ := flagTranslate_period _ _ _

theorem planeSector_add_iff {a : ℕ} (z v t p : ℝ×ℝ) :
    p+t∈planeSector a (z+t) v ↔ p∈planeSector a z v := by
  unfold planeSector
  simp only [Set.mem_ofPred_eq,cutForm_add]
  apply forall_congr'
  intro j
  split_ifs <;> simp

theorem flagTranslate_neighborhood {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing)
    (z : SquareFlag a v) {N : Set (ℝ×ℝ)} (hN : IsOpen N)
    (hz : (flagTranslate u z).val∈N) :
    ∃ M : Set (ℝ×ℝ), IsOpen M ∧ z.val∈M ∧
      ∀ p : GenericSquare a, p.val∈M → p.val∈planeSector a z.val v →
        (translate a u p).val∈N ∧
          (translate a u p).val∈planeSector a (flagTranslate u z).val v := by
  let k : ℤ×ℤ := (flagFloor (z.val.1+ordinary u.1) v.1,
    flagFloor (z.val.2+ordinary u.2) v.2)
  let t : CutRing×CutRing := u-SquareStep.intPair k
  let b : ℝ×ℝ := (ordinary t.1,ordinary t.2)
  have hbase : (flagTranslate u z).val=z.val+b := by
    apply Prod.ext <;> simp only [flagTranslate_val,flagFract_eq,b,t,k,SquareStep.intPair,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,map_sub,map_intCast] <;> ring
  let L := N ∩ arrangementNeighborhood a SquareStep.squareEdgeCuts (flagTranslate u z).val
  let M : Set (ℝ×ℝ) := (fun p => p+b) ⁻¹' L
  have hL : IsOpen L := hN.inter (arrangementNeighborhood_open _ _ _)
  have hzL : (flagTranslate u z).val∈L := ⟨hz,self_mem_arrangementNeighborhood _ _ _⟩
  refine ⟨M,hL.preimage (continuous_id.add continuous_const),?_,fun p hp hpv => ?_⟩
  · change z.val+b∈L
    rw [← hbase]; exact hzL
  · let q : GenericPlane a := GenericPlane.shift t ⟨p.val,p.property.2.2⟩
    have hqv : q.val∈planeSector a (flagTranslate u z).val v := by
      rw [hbase]
      exact (planeSector_add_iff z.val v b p.val).mpr hpv
    have hqs : SquareStep.InSquare q := sector_enters_square (flagTranslate u z).property.2 hp.2 hqv
    have hqp : (translate a u p).val=q.val := by
      apply Prod.ext
      · change Int.fract (p.val.1+ordinary u.1)=p.val.1+ordinary t.1
        have he : p.val.1+ordinary t.1=p.val.1+ordinary u.1-(k.1:ℝ) := by
          simp only [t,SquareStep.intPair,Prod.fst_sub,map_sub,map_intCast]; ring
        rw [he]
        rw [← Int.fract_sub_intCast (p.val.1+ordinary u.1) k.1]
        exact Int.fract_eq_self.mpr (by simpa only [q,GenericPlane.shift,Prod.fst_add,he,Set.mem_Ico] using hqs.1)
      · change Int.fract (p.val.2+ordinary u.2)=p.val.2+ordinary t.2
        have he : p.val.2+ordinary t.2=p.val.2+ordinary u.2-(k.2:ℝ) := by
          simp only [t,SquareStep.intPair,Prod.snd_sub,map_sub,map_intCast]; ring
        rw [he]
        rw [← Int.fract_sub_intCast (p.val.2+ordinary u.2) k.2]
        exact Int.fract_eq_self.mpr (by simpa only [q,GenericPlane.shift,Prod.snd_add,he,Set.mem_Ico] using hqs.2)
    rw [hqp]
    exact ⟨hp.1,hqv⟩

theorem flagValue_translate {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) (u : CutRing×CutRing)
    (z : SquareFlag a v) :
    flagValue (fun p => f (translate a u p)) (squareArrangement_translate hf u) z =
      flagValue f hf (flagTranslate u z) := by
  obtain ⟨N,hN,hz,hf'⟩ := flagValue_spec f hf (flagTranslate u z)
  obtain ⟨M,hM,hzM,hg⟩ := flagTranslate_neighborhood u z hN hz
  exact flagValue_eq _ _ _ ⟨M,hM,hzM,fun p hp hpv =>
    hf' (translate a u p) (hg p hp hpv).1 (hg p hp hpv).2⟩

theorem flagMem_preimage_translate {a : ℕ} {v : ℝ×ℝ} (U : polygonAlgebra a)
    (u : CutRing×CutRing) (z : SquareFlag a v) :
    flagMem ⟨translate a u ⁻¹' U.val,polygon_preimage_translate u U.property⟩ z ↔
      flagMem U (flagTranslate u z) := by
  change flagValue (fun p => decide (translate a u p∈U.val))
    (squareArrangement_translate (polygon_hasSquareArrangement U.property) u) z=true ↔ _
  rw [flagValue_translate (fun p => decide (p∈U.val)) (polygon_hasSquareArrangement U.property)]
  rfl

end FlagTranslation

end SimpleAmenable
end
end

end OAI
