import Mathlib
import OAI.Analysis.HardSphere.Collisions.Insertion
import OAI.Analysis.HardSphere.Geometry.GridAlignment

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I E P : Type*} [Fintype I] [DecidableEq I] [Fintype E] [MeasurableSpace P]
  {V : I→Type*} [∀i,MeasurableSpace (V i)]
  (avoid : P→P→Prop) (hm : MeasurableSet {p : P×P | avoid p.1 p.2})
  (left right : E→I) (hdiff : ∀e,left e≠right e)
  (getL : (e:E)→V (left e)→P) (getR : (e:E)→V (right e)→P)
  (hL : ∀e,Measurable (getL e)) (hR : ∀e,Measurable (getR e))

def dependentCheck (e : E) : LocalCheck V where
  support := {left e,right e}
  nonempty := ⟨left e,by simp⟩
  arity := by simpa using Finset.card_insert_le (left e) ({right e}:Finset I)
  pass x := avoid (getL e (x (left e))) (getR e (x (right e)))
  measurable_pass := hm.preimage (f:=fun x : ∀i,V i ↦ (getL e (x (left e)),getR e (x (right e)))) (by fun_prop)
  depends x y h := by rw [h (left e) (by simp),h (right e) (by simp)]

include hdiff in
omit [Fintype I] [Fintype E] in
lemma dependentCheck_failure (μ : ∀i,Measure (V i)) (p : I→E→ℝ≥0∞)
    (hleft : ∀e,∀g : V (right e),μ (left e) {f | ¬avoid (getL e f) (getR e g)}≤p (left e) e)
    (hright : ∀e,∀f : V (left e),μ (right e) {g | ¬avoid (getL e f) (getR e g)}≤p (right e) e)
    (i : I) (e : E) (hi : i∈(dependentCheck avoid hm left right getL getR hL hR e).support)
    (x : ∀i,V i) :
    μ i {f | ¬(dependentCheck avoid hm left right getL getR hL hR e).pass (Function.update x i f)}≤p i e := by
  have hie : i=left e ∨ i=right e := by simpa [dependentCheck] using hi
  rcases hie with he|he
  · subst i
    simpa only [dependentCheck,Function.update_self,Function.update_of_ne (hdiff e).symm] using hleft e (x (right e))
  · subst i
    simpa only [dependentCheck,Function.update_self,Function.update_of_ne (hdiff e)] using hright e (x (left e))

include hdiff in
omit [Fintype I] in
lemma dependent_insertion (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]
    (p : I→E→ℝ≥0∞) (a : ℝ≥0∞) (U : Finset I)
    (hleft : ∀e,left e∈U→∀g : V (right e),μ (left e) {f | ¬avoid (getL e f) (getR e g)}≤p (left e) e)
    (hright : ∀e,right e∈U→∀f : V (left e),μ (right e) {g | ¬avoid (getL e f) (getR e g)}≤p (right e) e)
    (htotal : ∀i∈U,a+(∑e∈Finset.univ.filter
      (fun e ↦ i∈(dependentCheck avoid hm left right getL getR hL hR e).support),p i e)≤1) :
    UniformInsertionOn (dependentCheck avoid hm left right getL getR hL hR) μ a U := by
  apply uniformInsertionOn_of_check_failures _ μ p a U _ htotal
  intro i hi e he x
  have hie : i=left e ∨ i=right e := by simpa [dependentCheck] using he
  rcases hie with hh|hh
  · subst i
    simpa only [dependentCheck,Function.update_self,Function.update_of_ne (hdiff e).symm] using hleft e hi (x (right e))
  · subst i
    simpa only [dependentCheck,Function.update_self,Function.update_of_ne (hdiff e)] using hright e hi (x (left e))

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {I E B : Type*} [Fintype I] [DecidableEq I] [Fintype E]
  [Fintype B] [DecidableEq B]

omit [Fintype I] in
lemma card_incident_edge_le (left right : E → I) (color : E → B)
    (hinj : Function.Injective (fun e ↦ (color e,(left e,right e))))
    (i : I) (T : Finset I)
    (hnear : ∀e,left e=i → right e∈T)
    (hnear' : ∀e,right e=i → left e∈T) :
    (Finset.univ.filter (fun e ↦ left e=i ∨ right e=i)).card ≤ Fintype.card B*(2*T.card) := by
  classical
  let Q := (({i}:Finset I) ×ˢ T)∪(T ×ˢ {i})
  have hs : (Finset.univ.filter (fun e ↦ left e=i ∨ right e=i)).image
      (fun e ↦ (color e,(left e,right e)))⊆(Finset.univ : Finset B) ×ˢ Q := by
    intro p hp
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases (Finset.mem_filter.mp he).2 with hh|hh
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hh,hnear e hh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hnear' e hh,Finset.mem_singleton.mpr hh⟩)
  have hq : Q.card ≤ 2*T.card := by
    apply (Finset.card_union_le _ _).trans
    simp only [Finset.card_product,Finset.card_singleton,one_mul,mul_one]
    omega
  have hcard := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hinj,Finset.card_product,Finset.card_univ] at hcard
  exact hcard.trans (Nat.mul_le_mul_left _ hq)

omit [Fintype I] in
lemma bounded_check_insertion {V : I → Type*} [∀i,MeasurableSpace (V i)]
    (checks : E → LocalCheck V) (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]
    (D : ℕ) (p a : ℝ≥0∞) (U : Finset I)
    (hdegree : ∀i∈U,(Finset.univ.filter (fun e ↦ i∈(checks e).support)).card ≤ D)
    (hfail : ∀i∈U,∀e,i∈(checks e).support → ∀x : ∀j,V j,
      μ i {y | ¬(checks e).pass (Function.update x i y)} ≤ p)
    (hsmall : a+(D:ℝ≥0∞)*p ≤ 1) : UniformInsertionOn checks μ a U := by
  apply uniformInsertionOn_of_check_failures checks μ (fun _ _ ↦ p) a U hfail
  intro i hi
  have hb : ((Finset.univ.filter (fun e ↦ i∈(checks e).support)).card:ℝ≥0∞) ≤ D := by exact_mod_cast hdegree i hi
  calc
    a+(∑_e∈Finset.univ.filter (fun e ↦ i∈(checks e).support),p)=
        a+((Finset.univ.filter (fun e ↦ i∈(checks e).support)).card:ℝ≥0∞)*p := by simp
    _  ≤  a+(D:ℝ≥0∞)*p := add_le_add le_rfl (mul_le_mul' hb le_rfl)
    _  ≤  1 := hsmall

end HardSphere.Comparison
namespace HardSphere.Groups
open Comparison HardSphere.CellOrbital
attribute [local instance] Classical.propDecidable

lemma physical_incident_degree {I E B : Type*} [Fintype I] [DecidableEq I] [Fintype E]
    [Fintype B] [DecidableEq B] {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (anchor : I → Fin 3 → Fin K) (M : ℕ)
    (hm : ∀v,(Finset.univ.filter (fun i : I ↦ anchor i=v)).card ≤ M)
    (left right : E → I) (color : E → B)
    (hinj : Function.Injective (fun e ↦ (color e,(left e,right e))))
    (hnear : ∀e,torusDistance L (gridCenter L (anchor (left e))) (gridCenter L (anchor (right e))) ≤ 23)
    (i : I) :
    (Finset.univ.filter (fun e ↦ left e=i ∨ right e=i)).card ≤ Fintype.card B*(2*(49^3*M)) := by
  let T := Finset.univ.filter (fun j : I ↦ torusDistance L (gridCenter L (anchor j)) (gridCenter L (anchor i)) ≤ 23)
  have hcard := card_incident_edge_le left right color hinj i T (by
    intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simpa only [he,torusDistance_comm L (gridCenter L (anchor i))] using hnear e) (by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [he] using hnear e⟩)
  exact hcard.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (card_near_labels L hL anchor M hm _)))

end HardSphere.Groups

end
end

end

end OAI
