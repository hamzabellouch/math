import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonSmallPartition

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonCommutingRepresentatives

open Classical Set
namespace PolygonObject.BankEmbedding
variable {a m : ℕ}

theorem commuting_representatives (hm : 0 < m) (f g : polygonFullGroup a m) :
    ∃u v : polygonFullGroup a m,
      (∃a₀ : polygonAlternatingGroup a m,u=a₀.val*f) ∧
      (∃b₀ c : polygonAlternatingGroup a m,v=c.val*(b₀.val*g)*c.val⁻¹) ∧ Commute u v := by
  let δ : ℝ := (m:ℝ)/100
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨a₀,S,hS,hf⟩ := small_support_coset f hδ
  obtain ⟨b₀,T,hT,hg⟩ := small_support_coset g hδ
  have htotal : (∑i,PolygonArea.area (S i))+(∑i,PolygonArea.area (S i)ᶜ)=(m:ENNReal) := by
    rw [←Finset.sum_add_distrib]
    simp only [PolygonArea.area_compl,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have htwo : ENNReal.ofReal δ+ENNReal.ofReal δ<(m:ENNReal) := by
    rw [←ENNReal.ofReal_add hδ.le hδ.le,←ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
    dsimp [δ]
    have : (0:ℝ) < m := Nat.cast_pos.mpr hm
    linarith
  have hTS : (∑i,PolygonArea.area (T i))<∑i,PolygonArea.area (S i)ᶜ := by
    by_contra hn
    have hle := add_le_add hS.le ((le_of_not_gt hn).trans hT.le)
    rw [htotal] at hle
    exact (not_le_of_gt htwo) hle
  obtain ⟨e,he⟩ := exists_into hTS
  have hten : 10*(∑i,PolygonArea.area (T i))<∑_i : Fin m,PolygonArea.area (⊥ : polygonAlgebra a)ᶜ := by
    calc
      _≤10*ENNReal.ofReal δ := mul_le_mul le_rfl hT.le (by positivity) (by positivity)
      _<(m:ENNReal) := by
        rw [←ENNReal.ofReal_ofNat 10,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),←ENNReal.ofReal_natCast]
        apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
        dsimp [δ]
        have : (0:ℝ) < m := Nat.cast_pos.mpr hm
        linarith
      _=_ := by simp [PolygonArea.area_top]
  obtain ⟨c,hc,_⟩ := alternating_extension T (fun _ => ⊥) e
    (fun _ => id) (fun _ => id) hten
  let u : polygonFullGroup a m := a₀.val*f
  let v : polygonFullGroup a m := c.val*(b₀.val*g)*c.val⁻¹
  have hvfix : ∀y : TrackPoint a m,y.2∈(S y.1).val → v.val y=y := by
    intro y hy
    have hpre : (c.val.val.symm y).2∉(T (c.val.val.symm y).1).val := by
      intro hp
      let p : (PolygonObject.mk m T).Point := ⟨c.val.val.symm y,hp⟩
      have hcp : e p=y := by rw [←hc p]; exact c.val.val.apply_symm_apply y
      have hi := he p
      rw [hcp] at hi
      exact hi hy
    change c.val.val ((b₀.val*g).val (c.val.val.symm y))=y
    rw [hg _ hpre]
    exact c.val.val.apply_symm_apply y
  refine ⟨u,v,⟨a₀,rfl⟩,⟨b₀,c,rfl⟩,?_⟩
  have hh : Commute v.val u.val := supported_fixer_commute hvfix hf
  exact Subtype.ext hh.symm.eq

end PolygonObject.BankEmbedding

local instance polygonFullNormal (a m : ℕ) : (polygonAlternatingGroup a m).Normal :=
  polygonAlternatingGroup_normal a m

theorem polygonFullGroup_quotient_commutative (a m : ℕ) (hm : 0 < m) :
    IsMulCommutative (polygonFullGroup a m ⧸ polygonAlternatingGroup a m) := by
  let q := QuotientGroup.mk' (polygonAlternatingGroup a m)
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨f,rfl⟩ := QuotientGroup.mk'_surjective (polygonAlternatingGroup a m) x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (polygonAlternatingGroup a m) y
  obtain ⟨u,v,⟨a₀,rfl⟩,⟨b₀,c,rfl⟩,hc⟩ := PolygonObject.BankEmbedding.commuting_representatives hm f g
  have ha : q a₀.val=1 := (QuotientGroup.eq_one_iff a₀.val).mpr a₀.property
  have hb : q b₀.val=1 := (QuotientGroup.eq_one_iff b₀.val).mpr b₀.property
  have hcc : q c.val=1 := (QuotientGroup.eq_one_iff c.val).mpr c.property
  have hh := hc.map q
  simpa only [map_mul,map_inv,ha,hb,hcc,one_mul,mul_one,inv_one] using hh.eq

theorem polygonFullGroup_commutator_eq (a m : ℕ) (hm : 5 ≤ m) :
    _root_.commutator (polygonFullGroup a m)=polygonAlternatingGroup a m := by
  apply le_antisymm
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (polygonFullGroup_quotient_commutative a m (by omega))
  · have hp := Subgroup.isPerfect_iff.mp (polygonAlternatingGroup_perfect a m hm)
    rw [←hp]
    exact Subgroup.commutator_mono le_top le_top

end PolygonCommutingRepresentatives

end SimpleAmenable
end
end

end OAI
