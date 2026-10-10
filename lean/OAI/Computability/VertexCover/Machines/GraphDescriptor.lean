import Mathlib
import OAI.Computability.VertexCover.Machines.FiniteFunction
import OAI.Computability.VertexCover.Machines.GraphConstraint

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                    
section

namespace VertexCover.Machine.GraphMachine
open LabelCover
variable {a b d : ℕ}
attribute [local instance 0] Classical.propDecidable
noncomputable instance descriptorFintype (a b d : ℕ) : Fintype (Descriptor a b d) := by
  classical
  letI : Fintype (ProfileRep a b d → Bool) := inferInstance
  letI : Fintype (TracePos d × TracePos d → Bool) := inferInstance
  letI : Fintype (ProfileRep a b d × ProfileRep a b d → Bool) := inferInstance
  letI : Fintype (TraceWeights a b d) := inferInstance
  letI : Fintype ((ProfileRep a b d × ProfileRep a b d → Bool) × TraceWeights a b d) := inferInstance
  letI : Fintype ((TracePos d × TracePos d → Bool) ×
    ((ProfileRep a b d × ProfileRep a b d → Bool) × TraceWeights a b d)) := inferInstance
  exact inferInstanceAs (Fintype ((_ → Bool) × _))
noncomputable def validPoly (ha : 0<a) (hb : 0<b) (x : TracePos d) (A : Query.Profile a b d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide ((Q p x).ProfileValid A)) := by
  let c₁ := Poly.const (frameCode (a := a) (b := b) (d := d)) boolBits
    (decide (∀ k, ¬x.2 < k → A.1 k=⟨0,ha⟩))
  let c₂ := Poly.const (frameCode (a := a) (b := b) (d := d)) boolBits
    (decide (∀ k, ¬k < x.2 → A.2 k=⟨0,hb⟩))
  exact (Poly.decideAnd frameCode _ _ c₁ (Poly.decideAnd frameCode _ _ c₂ (pairPoly ha hb x x A A))).congr
    (fun _ => by apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_iff]; rfl)
noncomputable def queryEqualPoly (hb : 0<b) (x y : TracePos d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (Q p x=Q p y)) := by
  rcases x with ⟨s,j⟩
  rcases y with ⟨t,k⟩
  by_cases h : j=k
  · subst k
    let cu := Poly.decideForall (frameCode (a := a) (b := b) (d := d))
      (fun p (i : {k : Fin d // j<k}) => (Q p (s,j)).2.1 i=(Q p (t,j)).2.1 i)
      (fun i => (eqUPoly hb (s,j) (t,j) i i).congr (fun _ => by simp))
    let cv := Poly.decideForall (frameCode (a := a) (b := b) (d := d))
      (fun p (i : {k : Fin d // k<j}) => (Q p (s,j)).2.2 i=(Q p (t,j)).2.2 i)
      (fun i => (eqVPoly hb (s,j) (t,j) i i).congr (fun _ => by simp))
    exact (Poly.decideAnd frameCode _ _ cu cv).congr (fun p => by
      apply Bool.decide_congr
      simp only [Q,LabelCover.query,Sigma.mk.inj_iff,heq_eq_eq,
        Prod.mk.injEq,funext_iff,true_and])
  · exact (Poly.const frameCode boolBits false).congr (fun p => by
      symm
      apply decide_eq_false
      intro hh
      exact h (congrArg Sigma.fst hh))
noncomputable def boolFinite : Poly boolBits (finiteCode Bool) id :=
  Poly.finite boolBits (finiteCode Bool) (by intro a b h; simpa [boolBits] using h) id
noncomputable def descriptorPoly (ha : 0<a) (hb : 0<b) :
    Poly (frameCode (a := a) (b := b) (d := d)) (finiteCode (Descriptor a b d)) descriptor := by
  let cv := Poly.finiteFunction (frameCode (a := a) (b := b) (d := d))
    (fun p (r : ProfileRep a b d) => decide ((Q p r.1).ProfileValid r.2))
    (fun r => ((validPoly ha hb r.1 r.2).comp boolFinite).congr (fun _ => rfl))
  let ce := Poly.finiteFunction (frameCode (a := a) (b := b) (d := d))
    (fun p (xy : TracePos d × TracePos d) => decide (Q p xy.1=Q p xy.2))
    (fun xy => ((queryEqualPoly hb xy.1 xy.2).comp boolFinite).congr (fun _ => rfl))
  let cp := Poly.finiteFunction (frameCode (a := a) (b := b) (d := d))
    (fun p (rs : ProfileRep a b d × ProfileRep a b d) => decide (Query.ProfilePair (Q p rs.1.1) (Q p rs.2.1) rs.1.2 rs.2.2))
    (fun rs => ((pairPoly ha hb rs.1.1 rs.2.1 rs.1.2 rs.2.2).comp boolFinite).congr (fun _ => rfl))
  let cw := weightPoly (a := a) (b := b) (d := d)
  let ec : Descriptor a b d → List Bool := prodBits (finiteCode (ProfileRep a b d → Bool))
    (prodBits (finiteCode (TracePos d × TracePos d → Bool))
      (prodBits (finiteCode (ProfileRep a b d × ProfileRep a b d → Bool))
        (finiteCode (TraceWeights a b d))))
  let cc : Poly ec (finiteCode (Descriptor a b d)) id := Poly.finite _ _
    (prodBits_injective (finiteCode_injective _) (prodBits_injective (finiteCode_injective _)
      (prodBits_injective (finiteCode_injective _) (finiteCode_injective _)))) id
  exact ((cv.pair (ce.pair (cp.pair cw))).comp cc).congr (fun p => by
    apply Prod.ext
    · funext r; exact Bool.decide_congr Iff.rfl
    · apply Prod.ext
      · funext xy; exact Bool.decide_congr Iff.rfl
      · apply Prod.ext
        · funext rs; exact Bool.decide_congr Iff.rfl
        · rfl)
noncomputable def testFinitePoly (t : ℝ) :
    Poly (finiteCode (Descriptor a b d)) boolBits (Descriptor.test (a := a) (b := b) (d := d) t) :=
  Poly.finite (finiteCode (Descriptor a b d)) boolBits
    (finiteCode_injective (Descriptor a b d)) (Descriptor.test t)
noncomputable def normTestPoly (ha : 0<a) (hb : 0<b) (t : ℝ) :=
  @Poly.comp (Frame a b d) (Descriptor a b d) Bool
    (frameCode (a := a) (b := b) (d := d)) (finiteCode (Descriptor a b d)) boolBits
    (descriptor (a := a) (b := b) (d := d)) (Descriptor.test (a := a) (b := b) (d := d) t)
    (descriptorPoly (a := a) (b := b) (d := d) ha hb) (testFinitePoly (a := a) (b := b) (d := d) t)
 theorem diagramSum_frame (p : Frame a b d) :
    diagramSum (Q p) (W p)=p.1.toLC.sumVector (p.1.toLC.profileVertexEquiv d (rawVertex p.1 p.2.1)) +
      p.1.toLC.sumVector (p.1.toLC.profileVertexEquiv d (rawVertex p.1 p.2.2)) := by
  classical
  simp only [diagramSum,Fintype.sum_prod_type,Fintype.sum_bool]
  exact add_comm _ _
 theorem normTest_correct (p : Frame a b d) (t : ℝ) :
    (descriptor p).test t=true ↔ p.1.toLC.compatibilityNorm
      (p.1.toLC.sumVector (p.1.toLC.profileVertexEquiv d (rawVertex p.1 p.2.1))+
      p.1.toLC.sumVector (p.1.toLC.profileVertexEquiv d (rawVertex p.1 p.2.2))) ≤ 2*t := by
  have h := diagram_test (Φ := p.1.toLC) (Q p) (W (a := a) (b := b) p) t
  exact h.trans (Iff.of_eq (congrArg
    (fun f : p.1.toLC.Coordinate d → ℝ => p.1.toLC.compatibilityNorm f ≤ 2*t)
    (diagramSum_frame p)))
end VertexCover.Machine.GraphMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
