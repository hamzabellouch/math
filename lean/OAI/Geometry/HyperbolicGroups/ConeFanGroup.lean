import Mathlib
import OAI.Geometry.HyperbolicGroups.GraphLimit
import OAI.Geometry.HyperbolicGroups.ConeCellTarget

namespace OAI

noncomputable section

namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate
variable {H : Type*} [_root_.Group H]

lemma Path.eval_potential (U : Vertex → H) (l : Field → H)
    {a b : Vertex} (p : Path a b)
    (h : ∀ f ∈ p.fields, U (source f) * l f = U (target f)) :
    U a * p.eval l id = U b := by
  induction p with
  | nil => simp [Path.eval]
  | @cons a b c s p ih =>
    have hs := h s.field List.mem_cons_self
    have ht : U a * s.value l id = U b := by
      cases hh : s.forward
      · obtain ⟨ha,hb⟩ := s.endpoints_neg hh
        rw [ha,hb] at hs
        simpa only [Step.value,hh,Bool.false_eq_true,ite_false,id_eq] using
          (eq_mul_inv_iff_mul_eq.mpr hs).symm
      · obtain ⟨ha,hb⟩ := s.endpoints_pos hh
        rw [ha,hb] at hs
        simpa only [Step.value,hh,ite_true,id_eq] using hs
    rw [Path.eval,← mul_assoc,ht]
    exact ih (fun f hf => h f (List.mem_cons_of_mem _ hf))

lemma Path.eval_comp {n : ℕ} (l : Field → LetterPresentation.Alphabet n)
    (r : LetterPresentation.Alphabet n → H) {a b : Vertex} (p : Path a b) :
    p.eval (r ∘ l) id = p.eval l r := by
  induction p with
  | nil => rfl
  | cons s p ih => simp only [Path.eval,Step.value,Function.comp_apply,id_eq,ih]

end MasterGraph
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {H : Type*} [_root_.Group H] (c : Dart n w → H)
  (hc : ∀ e, c (rev n w e) = (c e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => c (side n w d a i))).prod = 1)

def radialValue (b : Fan n w) (v : FanVertex b.val.1) : H := c (.inr ⟨b,v⟩,true)

include hc hcell in
lemma fanTriangle_relation (f : FanTriangle n w) :
    radialValue n w c f.1 (fanLeft n w f) * c (letterDart n w (fanLetter n w f)) =
      radialValue n w c f.1 (fanRight n w f) := by
  have he := hcell (.inl f)
  change c (.inr ⟨f.1,fanLeft n w f⟩,true) *
    (c (letterDart n w (fanLetter n w f)) *
      (c (.inr ⟨f.1,fanRight n w f⟩,false) * 1)) = 1 at he
  have hr := hc (.inr ⟨f.1,fanRight n w f⟩,true)
  change c (.inr ⟨f.1,fanRight n w f⟩,false) = _ at hr
  rw [hr,mul_one,← mul_assoc] at he
  exact mul_inv_eq_one.mp he

def fanPotential (b : Fan n w) : MasterGraph.Vertex → H
  | .inl v => if hv : IsFanVertex b.val.1 v then radialValue n w c b ⟨v,hv⟩ else 1
  | .inr _ => 1

include hc hcell in
lemma fanPotential_edge (b : Fan n w) (e : IncidenceTemplate.Edge) (he : e ∈ fan b.val.1) :
    fanPotential n w c b (MasterGraph.source (.inl e)) *
      c (letterDart n w (b.val.2 ⟨.inl e,by simpa [rowSupport] using he⟩)) =
    fanPotential n w c b (MasterGraph.target (.inl e)) := by
  have hf := fanTriangle_relation n w d c hc hcell ⟨b,⟨e,he⟩⟩
  simpa only [fanPotential,MasterGraph.source,MasterGraph.target,
    dite_eq_left (edge_fan_vertices e b.val.1 he).1,
    dite_eq_left (edge_fan_vertices e b.val.1 he).2,
    fanLetter,fanLeft,fanRight] using hf

include hc hcell in
lemma fan_relator_value (l : Field → Alphabet n) (i : Fin 7)
    (present : w (TableModel.row rowSupport l (.inl i)) = true)
    (v : MasterGraph.Vertex) (p : MasterGraph.Path v v)
    (fields : p.fields.toFinset ⊆ rowSupport (.inl i)) :
    p.eval l (c ∘ letterDart n w) = 1 := by
  let b : Fan n w := ⟨⟨i,fun f => l f.val⟩,present⟩
  have hp : fanPotential n w c b v * p.eval ((c ∘ letterDart n w) ∘ l) id =
      fanPotential n w c b v := by
    apply p.eval_potential
    intro f hf
    have hh : f ∈ (fan i).map Function.Embedding.inl := fields (List.mem_toFinset.mpr hf)
    obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hh
    exact fanPotential_edge n w d c hc hcell b e he
  rw [MasterGraph.Path.eval_comp] at hp
  exact mul_left_cancel (hp.trans (mul_one _).symm)

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
