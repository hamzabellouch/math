import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonAlternatingExtension

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonSmallPartition

open Classical Set MeasureTheory
namespace PolygonGrid

noncomputable def strip (a : ℕ) (r : CutRing) (i : ℕ) : polygonAlgebra a :=
  ⟨halfPlane a 0 (r*(i+1)) ∩ (halfPlane a 0 (r*i))ᶜ,
    BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _))⟩

theorem mem_strip (a : ℕ) (r : CutRing) (i : ℕ) (x : GenericSquare a) :
    x∈(strip a r i).val ↔ x.val.1∈interval (ordinary r) i := by
  simp only [strip,halfPlane,interval,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_ofPred_eq,
    Set.mem_Ico,cutForm,Matrix.cons_val_zero,map_mul,map_add,map_natCast,map_one,not_lt]
  tauto

theorem strip_area_le (a : ℕ) (r : CutRing) (i : ℕ) :
    PolygonArea.area (strip a r i)≤ENNReal.ofReal (ordinary r) := by
  have hs : Subtype.val '' (strip a r i).val⊆interval (ordinary r) i ×ˢ Ico (0:ℝ) 1 := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨(mem_strip a r i x).mp hx,x.property.2.1⟩
  calc
    _≤(volume : Measure (ℝ×ℝ)) (interval (ordinary r) i ×ˢ Ico (0:ℝ) 1) := measure_mono hs
    _=ENNReal.ofReal (ordinary r) := by
      rw [show (volume : Measure (ℝ×ℝ))=Measure.prod (volume : Measure ℝ) volume from rfl]
      simp only [Measure.prod_prod,interval,Real.volume_Ico,sub_zero,ENNReal.ofReal_one,mul_one]
      congr 1
      ring

theorem small_bank_cover {a m : ℕ} {ε : ℝ} (hε : 0<ε) :
    ∃N : ℕ,∃P : Fin m × Fin N → Fin m → polygonAlgebra a,
      (∀p : TrackPoint a m,∃j,p.2∈(P j p.1).val) ∧
      ∀j,(∑i,PolygonArea.area (P j i))<ENNReal.ofReal ε := by
  obtain ⟨b,hr,hrε⟩ := exists_grid_side hε
  let r := shrinkingLevel b
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ordinary r)
  let P (j : Fin m × Fin N) (i : Fin m) : polygonAlgebra a :=
    if i=j.1 then strip a r j.2.val else ⊥
  refine ⟨N,P,?_,?_⟩
  · intro p
    have hp : (p.1.val,p.2.val.1,p.2.val.2)∈region m :=
      ⟨p.1.isLt,p.2.property.1,p.2.property.2.1⟩
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (region_covered hr hN hp)
    refine ⟨(p.1,j.2.1),?_⟩
    simp only [P,ite_true]
    exact (mem_strip a r _ p.2).mpr hj.2.1
  · intro j
    have he : (∑i,PolygonArea.area (P j i))=PolygonArea.area (strip a r j.2.val) := by
      simp [P,apply_ite,PolygonArea.area_bot]
    rw [he]
    exact (strip_area_le a r j.2.val).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr hrε)

end PolygonGrid
namespace PolygonObject.BankEmbedding
variable {a m : ℕ}

noncomputable def full_restrict (f : polygonFullGroup a m) (U : Fin m → polygonAlgebra a) :
    BankEmbedding (PolygonObject.mk m U) m where
  emb := ⟨fun p => f.val p.val,fun _ _ he => Subtype.ext (f.val.injective he)⟩
  table := by
    obtain ⟨S,hS,hcover⟩ := f.property
    let conv (c : TableChart a m) : PolygonObject.Chart (a:=a) m m :=
      ⟨c.source,c.target,c.shift,U c.source ⊓ c.domain⟩
    refine ⟨S.image conv,?_,?_⟩
    · intro c hc
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      exact ⟨hx.1,hS d hd x hx.2⟩
    · intro p
      obtain ⟨c,hc,hr,hx⟩ := hcover p.val
      refine ⟨conv c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,hr,?_,hx⟩
      simpa only [←hr] using p.property

@[simp] theorem full_restrict_apply (f : polygonFullGroup a m) (U : Fin m → polygonAlgebra a)
    (p : (PolygonObject.mk m U).Point) : full_restrict f U p=f.val p.val := rfl

end PolygonObject.BankEmbedding
end PolygonSmallPartition

section PolygonSmallSupport

open Classical Set
namespace PolygonObject.BankEmbedding
variable {a m : ℕ}

theorem small_support_coset (f : polygonFullGroup a m) {δ : ℝ} (hδ : 0<δ) :
    ∃a₀ : polygonAlternatingGroup a m,∃S : Fin m → polygonAlgebra a,
      (∑i,PolygonArea.area (S i))<ENNReal.ofReal δ ∧
      ∀y : TrackPoint a m,y.2∉(S y.1).val → (a₀.val*f).val y=y := by
  obtain ⟨N,P,hcover,hsmall⟩ := PolygonGrid.small_bank_cover (a:=a) (m:=m) (show 0<δ/20 by positivity)
  have hnum : (10:ENNReal)*ENNReal.ofReal (δ/20)<ENNReal.ofReal δ := by
    rw [←ENNReal.ofReal_ofNat 10,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10)]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr (by linarith)
  have step (s : Finset (Fin m × Fin N)) :
      ∃a₀ : polygonAlternatingGroup a m,∃B : Fin m → polygonAlgebra a,
        (∀y : TrackPoint a m,y.2∈(B y.1).val → (a₀.val*f).val y=y) ∧
        ((∑i,PolygonArea.area (B i)ᶜ)<ENNReal.ofReal δ ∨ B=fun i => s.sup (fun j => P j i)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,fun _ => ⊥,fun _ hp => False.elim hp,Or.inr (by simp)⟩
    | @insert j s hj ih =>
      obtain ⟨a₀,B,hfix,hB⟩ := ih
      by_cases hsmallB : (∑i,PolygonArea.area (B i)ᶜ)<ENNReal.ofReal δ
      · exact ⟨a₀,B,hfix,Or.inl hsmallB⟩
      · have hBeq := hB.resolve_left hsmallB
        let U (i : Fin m) : polygonAlgebra a := P j i ⊓ (B i)ᶜ
        let g : polygonFullGroup a m := a₀.val*f
        have hU : ∀p : (PolygonObject.mk m U).Point,p.val.2∉(B p.val.1).val :=
          fun p => p.property.2
        have hg : ∀p : (PolygonObject.mk m U).Point,
            (g.val p.val).2∉(B (g.val p.val).1).val := by
          intro p hp
          have he : g.val (g.val p.val)=g.val p.val := hfix (g.val p.val) hp
          have hh : g.val p.val=p.val := g.val.injective he
          exact hU p (by simpa only [hh] using hp)
        have harea : 10*(∑i,PolygonArea.area (U i))<∑i,PolygonArea.area (B i)ᶜ := by
          have hle : (∑i,PolygonArea.area (U i))≤ENNReal.ofReal (δ/20) :=
            (Finset.sum_le_sum (fun i _ => PolygonArea.area_mono inf_le_left)).trans (hsmall j).le
          exact ((mul_le_mul le_rfl hle (by positivity) (by positivity)).trans_lt hnum).trans_le
            (le_of_not_gt hsmallB)
        obtain ⟨c,hc,hcB⟩ := alternating_extension U B (full_restrict g U) hU hg harea
        let B' (i : Fin m) : polygonAlgebra a := P j i ⊔ B i
        refine ⟨c⁻¹*a₀,B',?_,Or.inr ?_⟩
        · intro y hy
          change c.val.val.symm (g.val y)=y
          apply (c.val.val.symm_apply_eq).mpr
          by_cases hyB : y.2∈(B y.1).val
          · rw [show g.val y=y from hfix y hyB,hcB y hyB]
          · have hyP : y.2∈(P j y.1).val := hy.resolve_right hyB
            let p : (PolygonObject.mk m U).Point := ⟨y,hyP,hyB⟩
            exact (hc p).symm
        · funext i
          simp only [B',hBeq,Finset.sup_insert]
  obtain ⟨a₀,B,hfix,hB⟩ := step Finset.univ
  refine ⟨a₀,fun i => (B i)ᶜ,?_,?_⟩
  · rcases hB with hB|rfl
    · exact hB
    · have hall (i : Fin m) : Finset.univ.sup (fun j => P j i)=⊤ := by
        apply top_unique
        intro x _
        obtain ⟨j,hj⟩ := hcover (i,x)
        exact (Finset.le_sup (f:=fun j => P j i) (Finset.mem_univ j)) hj
      simp only [hall,compl_top,PolygonArea.area_bot,Finset.sum_const_zero]
      exact ENNReal.ofReal_pos.mpr hδ
  · intro y hy
    exact hfix y (not_not.mp hy)

end PolygonObject.BankEmbedding
end PolygonSmallSupport

end SimpleAmenable
end
end

end OAI
