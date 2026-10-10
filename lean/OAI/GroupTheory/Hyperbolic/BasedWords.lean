import OAI.GroupTheory.Hyperbolic.FullChains

namespace OAI

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

def basePath : (a : d.Vertex) → (d.vertex .o ⟶ d.vertex a)
  | .o => 𝟙 _
  | .v => d.treePathV
  | .w => d.treePathW

private theorem based_comp_formula {C : Type*} [Groupoid C] {o a b c : C}
    (A : o ⟶ a) (B : o ⟶ b) (C' : o ⟶ c) (f : a ⟶ b) (g : b ⟶ c) :
    (MulOpposite.op (End.of (A ≫ f ≫ Groupoid.inv B)) : (End o)ᵐᵒᵖ) *
      MulOpposite.op (End.of (B ≫ g ≫ Groupoid.inv C')) =
      MulOpposite.op (End.of (A ≫ (f ≫ g) ≫ Groupoid.inv C')) := by
  apply MulOpposite.unop_injective
  change (A ≫ f ≫ Groupoid.inv B) ≫ (B ≫ g ≫ Groupoid.inv C') = _
  simp [Category.assoc,Groupoid.inv_eq_inv]

private theorem based_id_formula {C : Type*} [Groupoid C] {o a : C} (A : o ⟶ a) :
    (1 : (End o)ᵐᵒᵖ) = MulOpposite.op (End.of (A ≫ (𝟙 a) ≫ Groupoid.inv A)) := by
  apply MulOpposite.unop_injective
  change 𝟙 _ = A ≫ (𝟙 a) ≫ Groupoid.inv A
  simp

private theorem based_eq_id {C : Type*} [Groupoid C] {o a : C} (A : o ⟶ a)
    (f : a ⟶ a) (h : A ≫ f ≫ Groupoid.inv A = 𝟙 o) : f = 𝟙 a := by
  have hh := congrArg (fun f => Groupoid.inv A ≫ f ≫ A) h
  simpa [Groupoid.inv_eq_inv,Category.assoc] using hh

theorem based_oriented_arrow {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.toFundamentalGroup (d.edgeValue (d.orientedLabel f)) =
      MulOpposite.op (End.of (d.basePath a ≫ d.rawToFundamental.map f.toPath ≫
        Groupoid.inv (d.basePath c))) := by
  change d.Arrow a c ⊕ d.Arrow c a at f
  rcases f with f | f
  · change d.Arrow a c at f
    cases f with
    | x e => exact d.toFundamentalGroup_edge (.inl e)
    | l e =>
      have h := d.toFundamentalGroup_edge (.inr (.inl e))
      change d.toFundamentalGroup (d.edge (.inr (.inl e))) =
        MulOpposite.op (End.of ((𝟙 _) ≫ d.pathL e ≫ Groupoid.inv d.treePathV))
      simpa only [Category.id_comp,basedEdge] using h
    | rr e =>
      have h := d.toFundamentalGroup_edge (.inr (.inr e))
      change d.toFundamentalGroup (d.edge (.inr (.inr e))) =
        MulOpposite.op (End.of ((𝟙 _) ≫ d.pathR e ≫ Groupoid.inv d.treePathW))
      simpa only [Category.id_comp,basedEdge] using h
  · change d.Arrow c a at f
    cases f with
    | x e =>
      change d.toFundamentalGroup ((d.edge (.inl e))⁻¹) = _
      rw [map_inv,d.toFundamentalGroup_edge]
      apply MulOpposite.unop_injective
      change Groupoid.inv (d.treePathV ≫ d.pathX e ≫ Groupoid.inv d.treePathW) =
        d.treePathW ≫ Groupoid.inv (d.pathX e) ≫ Groupoid.inv d.treePathV
      simp [Groupoid.inv_eq_inv,Category.assoc]
    | l e =>
      change d.toFundamentalGroup ((d.edge (.inr (.inl e)))⁻¹) = _
      rw [map_inv,d.toFundamentalGroup_edge]
      apply MulOpposite.unop_injective
      change Groupoid.inv (d.pathL e ≫ Groupoid.inv d.treePathV) =
        d.treePathV ≫ Groupoid.inv (d.pathL e) ≫ Groupoid.inv (𝟙 _)
      simp [Groupoid.inv_eq_inv]
    | rr e =>
      change d.toFundamentalGroup ((d.edge (.inr (.inr e)))⁻¹) = _
      rw [map_inv,d.toFundamentalGroup_edge]
      apply MulOpposite.unop_injective
      change Groupoid.inv (d.pathR e ≫ Groupoid.inv d.treePathW) =
        d.treePathW ≫ Groupoid.inv (d.pathR e) ≫ Groupoid.inv (𝟙 _)
      simp [Groupoid.inv_eq_inv]

theorem based_rawWord {a c : Quiver.Symmetrify d.Vertex} (p : Quiver.Path a c) :
    d.toFundamentalGroup (d.wordValue (d.rawWord p)) =
      MulOpposite.op (End.of (d.basePath a ≫ d.rawToFundamental.map p ≫
        Groupoid.inv (d.basePath c))) := by
  induction p with
  | nil =>
    change 1 = MulOpposite.op (End.of (d.basePath a ≫
      d.rawToFundamental.map (𝟙 (d.rawVertex a)) ≫ Groupoid.inv (d.basePath a)))
    exact (based_id_formula (d.basePath a)).trans
      (congrArg (fun f : d.vertex a ⟶ d.vertex a =>
          MulOpposite.op (End.of (d.basePath a ≫ f ≫ Groupoid.inv (d.basePath a))))
        (CategoryTheory.Functor.map_id d.rawToFundamental (d.rawVertex a)).symm)
  | @cons c e p f ih =>
    change d.toFundamentalGroup (d.wordValue (d.rawWord p ++ [d.orientedLabel f])) = _
    rw [wordValue_append,wordValue_cons,wordValue_nil,mul_one,map_mul,ih,d.based_oriented_arrow]
    exact (based_comp_formula (d.basePath a) (d.basePath c) (d.basePath e) _ _).trans
      (congrArg (fun z : d.vertex a ⟶ d.vertex e =>
          MulOpposite.op (End.of (d.basePath a ≫ z ≫ Groupoid.inv (d.basePath e))))
        (CategoryTheory.Functor.map_comp d.rawToFundamental
          (show d.rawVertex a ⟶ d.rawVertex c from p)
          (show d.rawVertex c ⟶ d.rawVertex e from f.toPath)).symm)

theorem rawWord_nullhomotopic {a : Quiver.Symmetrify d.Vertex}
    (p : Quiver.Path a a) (h : d.wordValue (d.rawWord p) = 1) :
    d.RawHomotopic p (𝟙 (d.rawVertex a)) := by
  have hh := congrArg d.toFundamentalGroup h
  rw [d.based_rawWord,map_one] at hh
  have hu := congrArg MulOpposite.unop hh
  change d.basePath a ≫ d.rawToFundamental.map p ≫ Groupoid.inv (d.basePath a) = 𝟙 _ at hu
  apply (d.raw_equality_iff _ _).mp
  exact (based_eq_id (d.basePath a) _ hu).trans
    (CategoryTheory.Functor.map_id d.rawToFundamental (d.rawVertex a)).symm

end Release075.BlockPresentation

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

/-- The original oriented edges really are arrows in the symmetrified quiver. -/
def rawEdge (e : d.OrientedEdge) :
    (show Quiver.Symmetrify d.Vertex from d.edgeTarget (d.flipEdge e)) ⟶
      (show Quiver.Symmetrify d.Vertex from d.edgeTarget e) := by
  rcases e with ⟨e,s⟩
  rcases e with x | l | rr <;> cases s
  · exact Sum.inr (Arrow.x x)
  · exact Sum.inl (Arrow.x x)
  · exact Sum.inr (Arrow.l l)
  · exact Sum.inl (Arrow.l l)
  · exact Sum.inr (Arrow.rr rr)
  · exact Sum.inl (Arrow.rr rr)

@[simp] theorem orientedLabel_rawEdge (e : d.OrientedEdge) :
    d.orientedLabel (d.rawEdge e) = e := by
  rcases e with ⟨e,s⟩
  rcases e with x | l | rr <;> cases s <;> rfl

theorem WordPath.exists_raw {a c : d.Vertex} {w : List d.OrientedEdge}
    (h : Release075.WordPath d.flipEdge d.edgeTarget a c w) :
    ∃ p : (d.rawVertex a ⟶ d.rawVertex c), d.rawWord p = w := by
  induction h with
  | nil a => exact ⟨𝟙 _,rfl⟩
  | cons e h ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨(d.rawEdge e).toPath ≫ p,?_⟩
    exact (d.rawWord_path_comp (d.rawEdge e).toPath p).trans
      (congrArg₂ List.append
        ((d.rawWord_toPath (d.rawEdge e)).trans
          (congrArg (fun e => [e]) (d.orientedLabel_rawEdge e))) hp)

theorem typed_nullword_lifted_fillable {a : d.Vertex} {w : List d.OrientedEdge}
    (ht : Release075.WordPath d.flipEdge d.edgeTarget a a w)
    (hv : d.wordValue w = 1) (g : d.GroupType) :
    Fillable d.liftedFlip d.liftedTarget d.LiftedFace (d.liftWord g w) := by
  obtain ⟨p,rfl⟩ := WordPath.exists_raw d ht
  exact d.nullhomotopic_lifted_fillable (d.rawWord_nullhomotopic p hv) g

end Release075.BlockPresentation

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem wordValue_reverse (w : List d.OrientedEdge) :
    d.wordValue (reverseWord d.flipEdge w) = (d.wordValue w)⁻¹ := by
  induction w with
  | nil => simp
  | cons e w ih => simp [reverseWord_cons,ih,mul_inv_rev]

theorem exists_based_word (g : d.GroupType) :
    ∃ w, WordPath d.flipEdge d.edgeTarget .o .o w ∧ d.wordValue w = g := by
  let K : Subgroup d.GroupType := {
    carrier := {g | ∃ w, WordPath d.flipEdge d.edgeTarget .o .o w ∧ d.wordValue w = g}
    one_mem' := ⟨[],.nil _,rfl⟩
    mul_mem' := by
      rintro g h ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩
      exact ⟨u++v,hu.append hv,d.wordValue_append u v⟩
    inv_mem' := by
      rintro g ⟨w,hw,rfl⟩
      exact ⟨reverseWord d.flipEdge w,hw.reverse d.flipEdge_flipEdge,d.wordValue_reverse w⟩ }
  apply PresentedGroup.generated_by d.relators K _ g
  intro e
  change ∃ w, WordPath d.flipEdge d.edgeTarget .o .o w ∧ d.wordValue w = d.edge e
  rcases e with e | e | e
  · refine ⟨[(d.treeL,true),(.inl e,true),(d.treeR,false)],?_,?_⟩
    · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,true)
        (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (Sum.inl e,true)
          (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o)))
    · simp [wordValue,edgeValue,d.treeL_eq_one,d.treeR_eq_one]
  · refine ⟨[(.inr (.inl e),true),(d.treeL,false)],?_,?_⟩
    · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
        (.inr (.inl e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,false) (WordPath.nil Vertex.o))
    · simp [wordValue,edgeValue,d.treeL_eq_one]
  · refine ⟨[(.inr (.inr e),true),(d.treeR,false)],?_,?_⟩
    · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
        (.inr (.inr e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o))
    · simp [wordValue,edgeValue,d.treeR_eq_one]

theorem WordPath.shift {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) (g : d.GroupType) :
    WordPath d.liftedFlip d.liftedTarget (d.shiftVertex g x) (d.shiftVertex g y)
      (w.map (d.shiftEdge g)) := by
  induction hw with
  | nil x => exact .nil _
  | cons e hw ih =>
    have hh := WordPath.cons (flip:=d.liftedFlip) (color:=d.liftedTarget) (d.shiftEdge g e) ih
    simpa only [List.map_cons,←d.shiftEdge_flip,d.shiftEdge_target] using hh

theorem WordPath.forget {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    WordPath d.flipEdge d.edgeTarget x.1 y.1 (w.map Prod.fst) := by
  induction hw with
  | nil x => exact .nil _
  | cons e hw ih => exact .cons e.1 ih

theorem WordPath.displacement {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    x.2 * d.wordValue (w.map Prod.fst) = y.2 := by
  induction hw with
  | nil x => simp
  | cons e hw ih =>
    change (e.2*(d.edgeValue e.1)⁻¹) *
      (d.edgeValue e.1 * d.wordValue (_:List d.OrientedEdge)) = _
    simpa only [mul_assoc,inv_mul_cancel_left,liftedTarget] using ih

theorem WordPath.liftWord_eq {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    d.liftWord x.2 (w.map Prod.fst) = w := by
  induction hw with
  | nil x => rfl
  | cons e hw ih =>
    change d.liftWord (e.2 * (d.edgeValue e.1)⁻¹) (e.1::_) = e::_
    simpa only [liftWord_cons,inv_mul_cancel_right,Prod.mk.eta,liftedTarget] using congrArg (e::·) ih

theorem lifted_closed_fillable {x : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x x w) :
    Fillable d.liftedFlip d.liftedTarget d.LiftedFace w := by
  have hv : d.wordValue (w.map Prod.fst) = 1 :=
    mul_left_cancel ((WordPath.displacement d hw).trans (mul_one x.2).symm)
  have hf := d.typed_nullword_lifted_fillable (WordPath.forget d hw) hv x.2
  rwa [WordPath.liftWord_eq d hw] at hf

theorem exists_lifted_path (g : d.GroupType) :
    ∃ w, WordPath d.liftedFlip d.liftedTarget (.o,1) (.o,g) w := by
  obtain ⟨w,hw,hv⟩ := d.exists_based_word g
  exact ⟨d.liftWord 1 w,by simpa only [hv,one_mul] using d.liftWord_typed hw 1⟩

theorem boundary₁_wordChain {x y : d.LiftedVertex} {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget x y w) :
    d.boundary₁ (d.wordChain w) = Finsupp.single y 1 - Finsupp.single x 1 := by
  induction hw with
  | nil x => simp [wordChain]
  | cons e hw ih =>
    change d.boundary₁ (d.edgeChain e + d.wordChain _) = _
    rw [map_add,d.boundary₁_edgeChain,ih]
    abel

def powerWord (g : d.GroupType) (w : List d.LiftedEdge) : ℕ → List d.LiftedEdge
  | 0 => []
  | n+1 => powerWord g w n ++ w.map (d.shiftEdge (g^n))

@[simp] theorem powerWord_zero (g : d.GroupType) (w : List d.LiftedEdge) :
    d.powerWord g w 0 = [] := rfl

theorem powerWord_succ (g : d.GroupType) (w : List d.LiftedEdge) (n : ℕ) :
    d.powerWord g w (n+1) = d.powerWord g w n ++ w.map (d.shiftEdge (g^n)) := rfl

theorem powerWord_succ_left (g : d.GroupType) (w : List d.LiftedEdge) (n : ℕ) :
    d.powerWord g w (n+1) = w ++ (d.powerWord g w n).map (d.shiftEdge g) := by
  induction n with
  | zero => simpa only [powerWord,pow_zero,List.nil_append,List.map_nil,List.append_nil] using
      (List.map_id'' (d.shiftEdge_one) w)
  | succ n ih =>
    rw [powerWord_succ]
    conv_lhs => rw [ih]
    conv_rhs => rw [powerWord_succ]
    rw [List.map_append,List.map_map,List.append_assoc]
    congr 2
    apply List.map_congr_left
    intro e _
    simp only [Function.comp_def,←shiftEdge_mul,←pow_succ']

theorem powerWord_typed (g : d.GroupType) {w : List d.LiftedEdge}
    (hw : WordPath d.liftedFlip d.liftedTarget (.o,1) (.o,g) w) (n : ℕ) :
    WordPath d.liftedFlip d.liftedTarget (.o,1) (.o,g^n) (d.powerWord g w n) := by
  induction n with
  | zero => simpa only [powerWord_zero,pow_zero] using
      (WordPath.nil (flip:=d.liftedFlip) (color:=d.liftedTarget) (.o,1))
  | succ n ih =>
    rw [powerWord_succ]
    apply ih.append
    simpa only [shiftVertex,mul_one,pow_succ] using WordPath.shift d hw (g^n)

theorem powerWord_chain (g : d.GroupType) (w : List d.LiftedEdge) (n : ℕ) :
    d.wordChain (d.powerWord g w n) = ∑ i ∈ Finset.range n, chainShift (g^i) (d.wordChain w) := by
  induction n with
  | zero => simp [wordChain]
  | succ n ih => rw [powerWord_succ,wordChain_append,wordChain_shift,ih,Finset.sum_range_succ]

theorem powerWord_shift_rotate (g : d.GroupType) (w : List d.LiftedEdge) {n : ℕ}
    (hn : 0 < n) (hg : g^n = 1) :
    (d.powerWord g w n).map (d.shiftEdge g) = (d.powerWord g w n).rotate w.length := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  conv_rhs => rw [powerWord_succ_left,List.rotate_append_length_eq]
  rw [powerWord_succ,List.map_append,List.map_map]
  congr 1
  have he : (d.shiftEdge g) ∘ (d.shiftEdge (g^k)) = id := by
    funext e
    simp only [Function.comp_def,← shiftEdge_mul,← pow_succ',hg,shiftEdge_one,id_eq]
  rw [he,List.map_id]

theorem powerWord_chain_norm (g : d.GroupType) (hg : IsOfFinOrder g)
    [Fintype (Subgroup.zpowers g)] (w : List d.LiftedEdge) :
    d.wordChain (d.powerWord g w (orderOf g)) =
      FreeChain.subgroupNorm (Subgroup.zpowers g) (d.wordChain w) := by
  rw [powerWord_chain]
  simp only [FreeChain.subgroupNorm,LinearMap.sum_apply,LinearEquiv.coe_coe]
  rw [← Equiv.sum_comp (finEquivZPowers hg)]
  exact (Fin.sum_univ_eq_sum_range (fun i => chainShift (g^i) (d.wordChain w)) (orderOf g)).symm

end Release075.BlockPresentation

namespace Release075.FullFilling
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w w' : List d.LiftedEdge}
  (D : FullFilling d.liftedFlip d.liftedTarget d.LiftedFace w)

theorem allTriangles_reword (hD : D.AllTriangles) (h : w = w') :
    (D.reword h).AllTriangles := by subst w'; exact hD

@[simp] theorem faceChain_reword (h : w = w') : (D.reword h).faceChain = D.faceChain := by
  subst w'; rfl

end Release075.FullFilling

end OAI
