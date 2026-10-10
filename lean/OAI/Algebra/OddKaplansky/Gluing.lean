import OAI.Algebra.OddKaplansky.Amalgam

namespace OAI

universe portUniverse1 portUniverse2

section

namespace OddKaplansky.Gluing
noncomputable section
open scoped Classical
open Monoid
variable {V F A B : Type} [CommGroup A] [Group B]
variable (Inc : V → F → Prop) (ι : V → F → (A →* B))

def con : Con (CoprodI (fun _ : V => B)) := conGen fun x y =>
  ∃ (f : F) (v w : V) (a : A), Inc v f ∧ Inc w f ∧
    x = CoprodI.of (i := v) (ι v f a) ∧ y = CoprodI.of (i := w) (ι w f a)

def Q := (con Inc ι).Quotient
instance : Group (Q Inc ι) := by delta Q; infer_instance

def vertex (v : V) : B →* Q Inc ι := (con Inc ι).mk'.comp (CoprodI.of (M := fun _ : V => B) (i := v))

lemma edge_eq (f : F) (v w : V) (a : A) (hv : Inc v f) (hw : Inc w f) :
    vertex Inc ι v (ι v f a) = vertex Inc ι w (ι w f a) :=
  (Con.eq _).mpr <| ConGen.Rel.of _ _ ⟨f, v, w, a, hv, hw, rfl, rfl⟩

def lift {E : Type portUniverse1} [Group E] (d : V → B →* E)
    (hd : ∀ f v w a, Inc v f → Inc w f → d v (ι v f a) = d w (ι w f a)) : Q Inc ι →* E :=
  Con.lift _ (CoprodI.lift d) (Con.conGen_le.mpr (by
    rintro _ _ ⟨f, v, w, a, hv, hw, rfl, rfl⟩
    simpa using hd f v w a hv hw))

@[simp] lemma lift_vertex {E : Type portUniverse2} [Group E] (d : V → B →* E)
    (hd : ∀ f v w a, Inc v f → Inc w f → d v (ι v f a) = d w (ι w f a)) (v : V) (b : B) :
    lift Inc ι d hd (vertex Inc ι v b) = d v b := by
  change CoprodI.lift d (CoprodI.of (i := v) b) = d v b
  simp

theorem vertex_injective [Fintype V] (hInc : ∀ f, ∃ v, Inc v f)
    (hshort : Planar.ShortWords Inc ι) (hgirth : 8 ≤ (Planar.incidenceGraph Inc).egirth)
    (v : V) : Function.Injective (vertex Inc ι v) := by
  let S := fun v => GluedGroup.Local Inc ι v
  let f : ∀ v, S v →* GluedGroup.N Inc ι := GluedGroup.theta Inc ι
  let g : ∀ v, S v →* B := fun v => (GluedGroup.localEvaluation Inc ι v).range.subtype
  obtain ⟨E, hE, b, d, hb, hd, he⟩ := StarAmalgam.faithful_realization f g
    (GluedGroup.theta_injective Inc ι hInc hshort hgirth) (fun _ => Subtype.val_injective)
  have heq : ∀ e v w a, Inc v e → Inc w e → d v (ι v e a) = d w (ι w e a) := by
    intro e v w a hv hw
    have hv' := he v (GluedGroup.localEdge Inc ι v e hv a)
    have hw' := he w (GluedGroup.localEdge Inc ι w e hw a)
    change b (GluedGroup.theta Inc ι v (GluedGroup.localEdge Inc ι v e hv a)) =
      d v (GluedGroup.localEdge Inc ι v e hv a : B) at hv'
    change b (GluedGroup.theta Inc ι w (GluedGroup.localEdge Inc ι w e hw a)) =
      d w (GluedGroup.localEdge Inc ι w e hw a : B) at hw'
    rw [GluedGroup.theta_localEdge, GluedGroup.localEdge_val] at hv' hw'
    exact hv'.symm.trans hw'
  intro x y hxy
  apply hd v
  simpa using congrArg (lift Inc ι d heq) hxy

instance [Finite V] [Finite B] : Group.FG (Q Inc ι) := by
  let T : Set (Q Inc ι) := Set.range (fun x : V × B => vertex Inc ι x.1 x.2)
  apply Group.fg_iff.mpr
  refine ⟨T, ?_, Set.finite_range _⟩
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨w, rfl⟩ := (con Inc ι).mk'_surjective x
  induction w using CoprodI.induction_on with
  | one => rw [map_one]; exact (Subgroup.closure T).one_mem
  | of v b => exact Subgroup.subset_closure ⟨(v, b), rfl⟩
  | mul x y hx hy => rw [map_mul]; exact (Subgroup.closure T).mul_mem hx hy

end
end OddKaplansky.Gluing

end

end OAI
