import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonBankEmbedding

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonAlternatingExtension

open Classical Set
namespace PolygonObject
namespace BankEmbedding
variable {a m : ℕ}

theorem alternating_extension (U B : Fin m → polygonAlgebra a)
    (f : BankEmbedding (PolygonObject.mk m U) m)
    (hU : ∀p : (PolygonObject.mk m U).Point,p.val.2∉(B p.val.1).val)
    (hf : ∀p,(f p).2∉(B (f p).1).val)
    (harea : 10*(∑i,PolygonArea.area (U i))<∑i,PolygonArea.area (B i)ᶜ) :
    ∃c : polygonAlternatingGroup a m,
      (∀p,c.val.val p.val=f p) ∧
      (∀y : TrackPoint a m,y.2∈(B y.1).val → c.val.val y=y) := by
  let u := inclusion U
  have hB : (∑i,PolygonArea.area (B i))≤(m:ENNReal) := by
    calc
      _≤∑_i : Fin m,(1:ENNReal) := Finset.sum_le_sum (fun i _ => PolygonArea.area_le_one (B i))
      _=_ := by simp
  have hBn : (∑i,PolygonArea.area (B i))≠⊤ := ne_top_of_le_ne_top (by simp) hB
  have htotal : (∑i,PolygonArea.area (B i))+(∑i,PolygonArea.area (B i)ᶜ)=m := by
    rw [←Finset.sum_add_distrib]
    simp only [PolygonArea.area_compl,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have guard (r : ENNReal) (hr : r≤10) :
      (∑i,PolygonArea.area (B i))+r*(∑i,PolygonArea.area (U i)) < m := by
    rw [←htotal]
    exact ENNReal.add_lt_add_left hBn ((mul_le_mul hr le_rfl (by positivity) (by positivity)).trans_lt harea)
  obtain ⟨w₁,hw₁B,hw₁⟩ := exists_away U B ![u,f] (by apply guard; norm_num)
  obtain ⟨w₂,hw₂B,hw₂⟩ := exists_away U B ![u,f,w₁] (by apply guard; norm_num)
  obtain ⟨w₃,hw₃B,hw₃⟩ := exists_away U B ![u,f,w₁,w₂] (by apply guard; norm_num)
  obtain ⟨c₁,hc₁,hout₁⟩ := cycle_three u w₁ w₂
    (fun p q he => hw₁ 0 q p he.symm)
    (fun p q he => hw₂ 0 q p he.symm)
    (fun p q he => hw₂ 2 q p he.symm)
  obtain ⟨c₂,hc₂,hout₂⟩ := cycle_three w₁ f w₃
    (fun p q he => hw₁ 1 p q he)
    (fun p q he => hw₃ 2 q p he.symm)
    (fun p q he => hw₃ 1 q p he.symm)
  refine ⟨c₂*c₁,?_,?_⟩
  · intro p
    change c₂.val.val (c₁.val.val (u p))=f p
    rw [hc₁,hc₂]
  · intro y hy
    have avoid (e : BankEmbedding (PolygonObject.mk m U) m)
        (he : ∀p,(e p).2∉(B (e p).1).val) : ∀p,e p≠y := by
      intro p hp
      exact he p (by simpa only [hp] using hy)
    have hu : ∀p,u p≠y := avoid u hU
    have hf' : ∀p,f p≠y := avoid f hf
    have hw₁' := avoid w₁ hw₁B
    have hw₂' := avoid w₂ hw₂B
    have hw₃' := avoid w₃ hw₃B
    change c₂.val.val (c₁.val.val y)=y
    rw [hout₁ y hu hw₁' hw₂',hout₂ y hw₁' hf' hw₃']

end BankEmbedding
end PolygonObject
end PolygonAlternatingExtension

end SimpleAmenable
end
end

end OAI
