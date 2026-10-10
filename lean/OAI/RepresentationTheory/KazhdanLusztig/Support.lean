import OAI.RepresentationTheory.KazhdanLusztig.BalancedPairings

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/

section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n=⊥)
noncomputable section

 theorem unit_endomorphisms_commute (f g : Hom (unit.{uk,ua,um} hneg) (unit hneg))
    (v : unit hneg) : f.map (g.map v)=g.map (f.map v) := by
  let z : unit.{uk,ua,um} hneg := fun _ => (1 : A)
  have he (w : unit.{uk,ua,um} hneg) : w=w PUnit.unit • z := by
    funext j
    change w j=w PUnit.unit * 1
    simp only [mul_one]
  have hf (w : unit.{uk,ua,um} hneg) : f.map w=w PUnit.unit • f.map z := by
    conv_lhs => rw [he w]
    exact map_smul f.map _ z
  have hg (w : unit.{uk,ua,um} hneg) : g.map w=w PUnit.unit • g.map z := by
    conv_lhs => rw [he w]
    exact map_smul g.map _ z
  rw [hf (g.map v),hg (f.map v),hg v,hf v]
  funext j
  change (v PUnit.unit * (g.map z) PUnit.unit) * (f.map z) j =
    (v PUnit.unit * (f.map z) PUnit.unit) * (g.map z) j
  have hej : j=PUnit.unit := Subsingleton.elim _ _
  subst j
  ring

 theorem unit_split_reverse (f g : Hom (unit.{uk,ua,um} hneg) (unit hneg))
    (h : ∀ v, g.map (f.map v)=v) (v : unit hneg) : f.map (g.map v)=v :=
  (unit_endomorphisms_commute hneg f g v).trans (h v)


 theorem split_reverse_of_unit {B N : ModuleData.{uk,ua,um} 𝓐}
    (hB : B=unit hneg) (o : Hom N (unit hneg)) (o' : Hom (unit hneg) N)
    (ho : ∀ v, o'.map (o.map v)=v) (i : Hom B N) (p : Hom N B)
    (hpi : ∀ v, p.map (i.map v)=v) (v : N) : i.map (p.map v)=v := by
  subst B
  have hp : ∀ a, (p.comp o').map ((o.comp i).map a)=a := by
    intro a
    change p.map (o'.map (o.map (i.map a)))=a
    rw [ho]
    exact hpi a
  have hh := unit_split_reverse hneg (o.comp i) (p.comp o') hp (o.map v)
  change o.map (i.map (p.map (o'.map (o.map v))))=o.map v at hh
  rw [ho] at hh
  exact (ho _).symm.trans ((congrArg o'.map hh).trans (ho v))

end
end KLInvariance.Graded.ModuleData

end


section

/-! The projector of any actual normalized BMP splitting into the reduced
word, and its integral adjoint, are both the identity at the top. The splitting
is not asserted to exist; word BMP recognition and character remain separate. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (α : Edge cs 1 (cs.wordProd l) → SymmetricCoefficient (M := M))
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) α
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

include hl in
 theorem bottBoundarySplit_top_fixed (v : bottStalk cs l (cs.wordProd l)) :
    (s.projector.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map v=v := by
  exact ModuleData.split_reverse_of_unit (symmetricGrading_negative basis) B.top
    (bottTopHom cs basis l hl) (bottTopInvHom cs basis l hl)
    (bottTopInvHom_top cs basis l hl)
    (s.inclusion.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (s.projection.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (s.vertex_split ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) v

 theorem bottBoundarySplitAdjoint_top_fixed (v : bottStalk cs l (cs.wordProd l)) :
    ((bottAdjointSheaf cs basis l hl s.projector).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map v=v :=
  bottAdjointSheaf_fixed_stalk cs basis l hl s.projector
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩
    (bottBoundarySplit_top_fixed cs basis l hl α B s) v

end
end KLInvariance.TitsSpace

end


section


namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem symmetricGrading_zero (a : SymmetricCoefficient (M := M))
    (ha : a ∈ symmetricGrading basis 0) :
    ∃ c : ℝ, algebraMap ℝ (SymmetricCoefficient (M := M)) c=a := by
  obtain ⟨c,hc⟩ := polynomialGrading_zero ℝ σ
    (SymmetricAlgebra.equivMvPolynomial basis a) ((mem_symmetricGrading basis 0 a).mp ha)
  refine ⟨c,?_⟩
  apply (SymmetricAlgebra.equivMvPolynomial basis).injective
  exact ((SymmetricAlgebra.equivMvPolynomial basis).commutes c).trans hc

end
end KLInvariance.TitsSpace

end


section

/-! The actual BMP axioms inherited by a graded sheaf retract. These are
implications, not claims that the word sheaf already satisfies the axioms. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 theorem SplitIn.flabby (s : SplitIn B C) (hC : C.forget.Flabby) : B.forget.Flabby := by
  intro Ω hΩ f hf
  obtain ⟨g,hg,hgf⟩ := hC Ω hΩ (s.inclusion.assignmentMap f)
    (s.inclusion.assignmentMap_compatible Ω f hf)
  refine ⟨s.projection.assignmentMap g,
    s.projection.assignmentMap_compatible Set.univ g hg,?_⟩
  intro x hx
  change (s.projection.vertex x).map (g x)=f x
  rw [hgf x hx]
  exact s.vertex_split x (f x)

 theorem SplitIn.generated (s : SplitIn B C) (hC : C.forget.Generated) : B.forget.Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hC x ((s.inclusion.vertex x).map v)
  refine ⟨s.projection.assignmentMap f,
    s.projection.assignmentMap_compatible Set.univ f hf,?_⟩
  change (s.projection.vertex x).map (f x)=v
  rw [hfx]
  exact s.vertex_split x v

 theorem SplitIn.upperQuotient (s : SplitIn B C) {α : E → A}
    (hC : C.UpperQuotient α) : B.UpperQuotient α := by
  intro e
  constructor
  · intro v
    obtain ⟨c,hc⟩ := (hC e).1 ((s.inclusion.edge e).map v)
    refine ⟨(s.projection.vertex (G.target e)).map c,?_⟩
    rw [← s.projection.upper,hc]
    exact s.edge_split e v
  · intro v
    constructor
    · intro hv
      have hz : (C.upper e).map ((s.inclusion.vertex _).map v)=0 := by
        rw [← s.inclusion.upper,hv]
        exact map_zero _
      obtain ⟨c,hc⟩ := (hC e).2 _ |>.mp hz
      refine ⟨(s.projection.vertex _).map c,?_⟩
      have h := congrArg (s.projection.vertex _).map hc
      rw [s.vertex_split,map_smul] at h
      exact h
    · rintro ⟨w,rfl⟩
      have hz := ((hC e).2 (α e • (s.inclusion.vertex _).map w)).mpr
        ⟨(s.inclusion.vertex _).map w,rfl⟩
      have he : (s.inclusion.edge e).map ((B.upper e).map (α e • w))=0 := by
        rw [s.inclusion.upper,map_smul]
        exact hz
      have h := congrArg (s.projection.edge e).map he
      rw [s.edge_split,map_zero] at h
      exact h

 theorem SplitIn.vertex_projective (s : SplitIn B C) (x : V)
    [Module.Projective A (C.vertex x)] : Module.Projective A (B.vertex x) := by
  apply Module.Projective.of_split (s.inclusion.vertex x).map (s.projection.vertex x).map
  apply LinearMap.ext
  exact s.vertex_split x

 theorem SplitIn.vertex_free
    [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    [IsDomain A] [IsNoetherianRing A]
    (hneg : ∀ n < 0, 𝓐 n=⊥)
    (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c=a)
    (s : SplitIn B C) (x : V) [Module.Projective A (C.vertex x)] :
    Module.Free A (B.vertex x) := by
  let D := B.vertex x
  let : Module.Projective A D := s.vertex_projective x
  obtain ⟨ι,_,bs,_⟩ := exists_homogeneous_basis_connected 𝓐 D.piece hneg hzero 0 D.nonneg
  exact Module.Free.of_basis bs

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

 theorem equivOfEq_inverse {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) (m : M) :
    equivOfEq h.symm (equivOfEq h m)=m := by
  subst N
  rfl

 def homOfEq {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) : Hom M N :=
  ⟨(equivOfEq h).toLinearMap,equivOfEq_graded h⟩

end KLInvariance.Graded.ModuleData

end


section

/-! The actual minimal-boundary sheaf is a summand of the reduced word.
No splitting or word-recognition axiom is supplied as a premise. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def symmetricLabel (u b : W) (e : Edge cs u b) : SymmetricCoefficient (M := M) :=
  SymmetricAlgebra.ι ℝ (Extended M) (embed M (BruhatGraph.root cs u b e).val)

 theorem symmetricLabel_represents (u b : W) (e : Edge cs u b) :
    Represents M cs (label cs u b e) (BruhatGraph.root cs u b e).val :=
  positiveRoot_represents M cs ⟨label cs u b e,label_isReflection cs u b e⟩

 theorem bottGradedProjectionSheaf_upperQuotient (l : List I) (u b : W) :
    (bottGradedProjectionSheaf cs basis l u b).UpperQuotient (symmetricLabel cs u b) := by
  intro e
  exact ⟨bottProjectionSheaf_upper_surjective cs l u b e,
    bottProjectionSheaf_upper_kernel cs l u b e (symmetricLabel_represents cs u b e)⟩

 def bottBoundarySheafTopInclusion (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    ModuleData.Hom (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
      (bottStalkData cs basis l (cs.wordProd l)) :=
  (bottTopInvHom cs basis l hl).comp
    ⟨(ModuleData.equivOfEq B.top).toLinearMap,ModuleData.equivOfEq_graded B.top⟩

 def bottBoundarySheafTopProjection (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    ModuleData.Hom (bottStalkData cs basis l (cs.wordProd l))
      (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :=
  (⟨(ModuleData.equivOfEq B.top.symm).toLinearMap,ModuleData.equivOfEq_graded B.top.symm⟩ :
    ModuleData.Hom _ _).comp (bottTopHom cs basis l hl)

 theorem bottBoundarySheafTop_split (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (v : B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    (bottBoundarySheafTopProjection cs basis l hl B).map
      ((bottBoundarySheafTopInclusion cs basis l hl B).map v)=v := by
  change ModuleData.equivOfEq B.top.symm ((bottTopHom cs basis l hl).map
    ((bottTopInvHom cs basis l hl).map (ModuleData.equivOfEq B.top v)))=v
  rw [bottTopHom_inv]
  exact ModuleData.equivOfEq_inverse B.top v

 theorem bottBoundarySheaf_splitIn (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    Nonempty (GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  let := Fintype.ofFinite (Interval cs 1 (cs.wordProd l))
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  exact B.splitIn_of_top_split (symmetricGrading_zero basis) (fun x => x.property.2)
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf_upperQuotient cs basis l 1 (cs.wordProd l))
    (fun x => bottStalkFree cs l x.val) (bottProjectionSheaf_flabby cs l hl)
    (bottProjectionSheaf_generated cs l 1 (cs.wordProd l))
    (bottBoundarySheafTopInclusion cs basis l hl B) (bottBoundarySheafTopProjection cs basis l hl B)
    (bottBoundarySheafTop_split cs basis l hl B)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 def coefficientChange (S : GradedSheaf (𝓐 := 𝓐) G) : GradedSheaf (𝓐 := 𝓑) G where
  vertex x := ModuleData.change e he (S.vertex x)
  edge f := ModuleData.change e he (S.edge f)
  lower f := ModuleData.changeHom e he (S.lower f)
  upper f := ModuleData.changeHom e he (S.upper f)

 def Hom.coefficientChange {S T : GradedSheaf (𝓐 := 𝓐) G} (g : Hom S T) :
    Hom (coefficientChange e he S) (coefficientChange e he T) where
  vertex x := ModuleData.changeHom e he (g.vertex x)
  edge f := ModuleData.changeHom e he (g.edge f)
  lower f m := CoefficientChange.ext (g.lower f m.val)
  upper f m := CoefficientChange.ext (g.upper f m.val)

 theorem coefficientChange_free (S : GradedSheaf (𝓐 := 𝓐) G) (hS : S.FreeStalks) :
    (coefficientChange e he S).FreeStalks := by
  intro x
  let := hS x
  exact ModuleData.change_free e he (S.vertex x)

 theorem coefficientChange_upperQuotient (S : GradedSheaf (𝓐 := 𝓐) G)
    (α : E → A) (hS : S.UpperQuotient α) :
    (coefficientChange e he S).UpperQuotient (fun f => e (α f)) := by
  intro f
  constructor
  · exact CoefficientChange.map_surjective e _ (hS f).1
  · intro m
    constructor
    · intro hm
      have hz : (S.upper f).map m.val=0 := congrArg CoefficientChange.val hm
      obtain ⟨n,hn⟩ := (hS f).2 m.val |>.mp hz
      refine ⟨CoefficientChange.mk n,CoefficientChange.ext ?_⟩
      change m.val=e.symm (e (α f)) • n
      simpa only [e.symm_apply_apply] using hn
    · rintro ⟨n,rfl⟩
      apply CoefficientChange.ext
      change (S.upper f).map (e.symm (e (α f)) • n.val)=0
      rw [e.symm_apply_apply]
      exact ((hS f).2 _).mpr ⟨n.val,rfl⟩

 theorem coefficientChange_flabby (S : GradedSheaf (𝓐 := 𝓐) G) (hS : S.forget.Flabby) :
    (coefficientChange e he S).forget.Flabby := by
  intro U hU f hf
  have hf' : S.forget.CompatibleOn U (fun x => (f x).val) := fun q hs ht =>
    congrArg CoefficientChange.val (hf q hs ht)
  obtain ⟨g,hg,hgf⟩ := hS U hU (fun x => (f x).val) hf'
  refine ⟨fun x => CoefficientChange.mk (g x),?_,?_⟩
  · intro q hs ht
    exact CoefficientChange.ext (hg q hs ht)
  · intro x hx
    exact CoefficientChange.ext (hgf x hx)

 theorem coefficientChange_generated (S : GradedSheaf (𝓐 := 𝓐) G) (hS : S.forget.Generated) :
    (coefficientChange e he S).forget.Generated := by
  intro x m
  obtain ⟨g,hg,hgx⟩ := hS x m.val
  refine ⟨fun x => CoefficientChange.mk (g x),?_,CoefficientChange.ext hgx⟩
  intro q hs ht
  exact CoefficientChange.ext (hg q hs ht)

 def coefficientChangeSections (S : GradedSheaf (𝓐 := 𝓐) G) (U : Set V) :
    CoefficientChange e (S.forget.sections U) ≃ₗ[B] (coefficientChange e he S).forget.sections U where
  toFun m := ⟨fun x => CoefficientChange.mk (m.val.val x),fun q hs ht =>
    CoefficientChange.ext (m.val.property q hs ht)⟩
  invFun m := CoefficientChange.mk ⟨fun x => (m.val x).val,fun q hs ht =>
    congrArg CoefficientChange.val (m.property q hs ht)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Positive triangular decomposition of the honest word's character into
actual BMP stalk characters. The KL identification is not assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottPolynomialSheaf (l : List I) (u b : W) :
    GradedSheaf (𝓐 := polynomialGrading ℝ σ) (graph cs u b) :=
  GradedSheaf.coefficientChange (SymmetricAlgebra.equivMvPolynomial basis)
    (mem_symmetricGrading basis) (bottGradedProjectionSheaf cs basis l u b)

 theorem bottPolynomialSheaf_free (l : List I) (u b : W) :
    (bottPolynomialSheaf cs basis l u b).FreeStalks :=
  GradedSheaf.coefficientChange_free _ _ _ (fun x => bottStalkFree cs l x.val)

 theorem bottPolynomialSheaf_quotient (l : List I) (u b : W) :
    (bottPolynomialSheaf cs basis l u b).UpperQuotient (polynomialLabel cs u b basis) :=
  GradedSheaf.coefficientChange_upperQuotient _ _ _ _
    (bottGradedProjectionSheaf_upperQuotient cs basis l u b)

 theorem bottPolynomialSheaf_flabby (l : List I) (hl : cs.IsReduced l) :
    (bottPolynomialSheaf cs basis l 1 (cs.wordProd l)).forget.Flabby :=
  GradedSheaf.coefficientChange_flabby _ _ _ (bottProjectionSheaf_flabby cs l hl)

 theorem bottPolynomialSheaf_generated (l : List I) (u b : W) :
    (bottPolynomialSheaf cs basis l u b).forget.Generated :=
  GradedSheaf.coefficientChange_generated _ _ _ (bottProjectionSheaf_generated cs l u b)

 theorem bottPolynomialSheaf_character (l : List I) (u b : W) (x : Interval cs u b) :
    GradedSheaf.freeStalkChar (bottPolynomialSheaf cs basis l u b)
      (bottPolynomialSheaf_free cs basis l u b) x=bottStalkCharacter cs basis l x.val := rfl

 theorem bottStalkCharacter_decomposition (l : List I) (hl : cs.IsReduced l)
    [Fintype (Interval cs 1 (cs.wordProd l))] :
    ∃ m : Interval cs 1 (cs.wordProd l) → Polynomial ℤ,
      (∀ y n, 0≤(m y).coeff n) ∧ ∀ x,
      bottStalkCharacter cs basis l x.val=
        ∑ y, m y*lowerCharacter cs (cs.wordProd l) basis y x := by
  classical
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  obtain ⟨m,hm,he⟩ := GradedSheaf.exists_stalkCharacter_decomposition
    (boundaryModels cs (cs.wordProd l) basis)
    (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_free cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_quotient cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_flabby cs basis l hl)
    (bottPolynomialSheaf_generated cs basis l 1 (cs.wordProd l))
  refine ⟨m,hm,fun x => ?_⟩
  simpa only [bottPolynomialSheaf_character,boundaryModels_character] using he x

end
end KLInvariance.TitsSpace

end


section


namespace KLInvariance.IntegralSupport

universe ur uv um
variable {R : Type ur} [CommRing R]
  {V : Type uv} [DecidableEq V] {A : V → Type um} [∀ x, AddCommGroup (A x)] [∀ x, Module R (A x)]
  (M : Submodule R (∀ x, A x))

noncomputable def projection (x : V) : M →ₗ[R] A x := (LinearMap.proj x).comp M.subtype

def supported (x : V) : Submodule R M where
  carrier := {m | ∀ y, y ≠ x → m.val y = 0}
  zero_mem' := by intro y hy; rfl
  add_mem' := by intro m n hm hn y hy; exact congrArg₂ (· + ·) (hm y hy) (hn y hy) |>.trans (zero_add _)
  smul_mem' := by intro r m hm y hy; exact congrArg (r • ·) (hm y hy) |>.trans (smul_zero r)

variable (p : R)
  (hcut : ∀ x (m : M), (p • Pi.single x (m.val x)) ∈ M)

noncomputable def cut (x : V) : M →ₗ[R] M := by
  exact ((p • (LinearMap.single R A x).comp (LinearMap.proj x)).domRestrict M).codRestrict M (hcut x)

@[simp] theorem cut_apply (x : V) (m : M) : (cut M p hcut x m).val = p • Pi.single x (m.val x) := rfl

@[simp] theorem cut_self (x : V) (m : M) : (cut M p hcut x m).val x = p • m.val x := by
  simp [cut_apply]

 theorem cut_other (x y : V) (h : y ≠ x) (m : M) : (cut M p hcut x m).val y = 0 := by
  simp [cut_apply,h]

 theorem cut_of_supported (x : V) (m : M) (h : m ∈ supported M x) :
    cut M p hcut x m = p • m := by
  apply Subtype.ext
  funext y
  by_cases hy : y=x
  · subst y; exact cut_self M p hcut x m
  · rw [cut_other M p hcut x y hy]
    change 0 = p • m.val y
    rw [h y hy,smul_zero]

 theorem cut_eq_zero (x : V) (m : M) (h : projection M x m = 0) : cut M p hcut x m = 0 := by
  apply Subtype.ext
  change p • Pi.single x (m.val x) = 0
  change m.val x = 0 at h
  simp [h]

variable [IsDomain R] [∀ x, Module.IsTorsionFree R (A x)] (hp : p ≠ 0)
  (d : M ≃ₗ[R] Module.Dual R M)
  (hbalanced : ∀ x m n, d (cut M p hcut x m) n = d m (cut M p hcut x n))

include hp hbalanced in
/-- The exact integral annihilator, not merely its generic vector space. -/
 theorem supported_iff_annihilates (x : V) (m : M) :
    m ∈ supported M x ↔ ∀ n : M, projection M x n = 0 → d m n = 0 := by
  constructor
  · intro hm n hn
    have hh := hbalanced x m n
    rw [cut_of_supported M p hcut x m hm,cut_eq_zero M p hcut x n hn] at hh
    simpa only [map_smul,LinearMap.smul_apply,map_zero,smul_eq_zero_iff_right hp] using hh
  · intro hm y hy
    have hc : cut M p hcut y m = 0 := by
      apply d.injective
      apply LinearMap.ext
      intro n
      rw [hbalanced]
      simpa only [map_zero,LinearMap.zero_apply] using
        hm (cut M p hcut y n) (cut_other M p hcut y x (Ne.symm hy) n)
    have hv := congrArg (fun s : M => s.val y) hc
    simpa only [cut_self,Submodule.coe_zero,Pi.zero_apply,smul_eq_zero_iff_right hp] using hv

/-- Precomposition with a surjective stalk projection gives the integral
single-support module. No field extension was used anywhere in this map. -/
noncomputable def dualToSupport (x : V) : Module.Dual R (A x) →ₗ[R] supported M x :=
  (d.symm.toLinearMap.comp (projection M x).dualMap).codRestrict (supported M x) (by
    intro lam
    apply (supported_iff_annihilates M p hcut hp d hbalanced x _).mpr
    intro n hn
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
      LinearMap.dualMap_apply]
    change lam (projection M x n) = 0
    rw [hn,map_zero])

 theorem dualToSupport_bijective (x : V) (hπ : Function.Surjective (projection M x)) :
    Function.Bijective (dualToSupport M p hcut hp d hbalanced x) := by
  constructor
  · intro lam mu he
    apply LinearMap.dualMap_injective_of_surjective hπ
    apply d.symm.injective
    exact congrArg Subtype.val he
  · intro m
    have hm : d m.val ∈ (LinearMap.ker (projection M x)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro n hn
      exact (supported_iff_annihilates M p hcut hp d hbalanced x m.val).mp m.property n hn
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _ hπ] at hm
    obtain ⟨lam,hlam⟩ := hm
    refine ⟨lam,?_⟩
    apply Subtype.ext
    change d.symm ((projection M x).dualMap lam) = m.val
    rw [hlam,LinearEquiv.symm_apply_apply]

noncomputable def supportEquivDual (x : V) (hπ : Function.Surjective (projection M x)) :
    supported M x ≃ₗ[R] Module.Dual R (A x) :=
  (LinearEquiv.ofBijective (dualToSupport M p hcut hp d hbalanced x)
    (dualToSupport_bijective M p hcut hp d hbalanced x hπ)).symm

end KLInvariance.IntegralSupport

end


section


namespace BalancedCuts
universe ur um ua
variable {R : Type ur} [CommRing R] [IsDomain R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {A : Type ua} [AddCommGroup A] [Module R A]
  (d : M →ₗ[R] Module.Dual R M) (hsym : ∀ m n, d m n=d n m)
  (π : M →ₗ[R] A) (c : M →ₗ[R] M) (p : R) (hp : p ≠ 0)
  (hπ : ∀ m, π (c m)=p • π m)
  (horth : ∀ m n, π n=0 → d (c m) n=0)

include hsym hp hπ horth in
 theorem balanced (m n : M) : d (c m) n=d m (c n) := by
  have hn : π (p • n-c n)=0 := by rw [map_sub,map_smul,hπ,sub_self]
  have hm : π (p • m-c m)=0 := by rw [map_sub,map_smul,hπ,sub_self]
  have en := horth m _ hn
  have em := horth n _ hm
  simp only [map_sub,map_smul,smul_eq_mul,sub_eq_zero] at en em
  rw [hsym (c n) m,hsym (c n) (c m)] at em
  exact mul_left_cancel₀ hp (en.trans em.symm)

end BalancedCuts

end


section


namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
local instance (a : Type*) : DecidableEq a := Classical.decEq a

 theorem bottSection_supported_annihilates (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l))
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (hs : s ∈ IntegralSupport.supported
      ((bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) x)
    (hz : z.val x=0) : bottSectionDuality cs l hl s z=0 := by
  classical
  obtain ⟨m,rfl⟩ := bottSection_surjective cs l hl s
  obtain ⟨n,rfl⟩ := bottSection_surjective cs l hl z
  rw [bottSectionDuality_apply]
  apply bott_supported_annihilates cs l x.val
  · intro e he
    let y : Interval cs 1 (cs.wordProd l) :=
      ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩
    have hy : y ≠ x := fun h => he (congrArg Subtype.val h)
    have hh := hs y hy
    exact congrFun (congrArg Subtype.val hh) ⟨e,rfl⟩
  · exact congrArg Subtype.val hz

 theorem bottSection_projector_balanced (l : List I) (hl : cs.IsReduced l)
    (p : SymmetricCoefficient (M := M)) (hp : p ≠ 0)
    (x : Interval cs 1 (cs.wordProd l))
    (c : End (SymmetricCoefficient (M := M))
      ((bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ))
    (hself : ∀ m, (c m).val x=p • m.val x)
    (hother : ∀ m y, y ≠ x → (c m).val y=0)
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :
    bottSectionDuality cs l hl (c s) z = bottSectionDuality cs l hl s (c z) := by
  classical
  apply BalancedCuts.balanced (bottSectionDuality cs l hl).toLinearMap
    (bottSection_symmetric cs l hl)
    (IntegralSupport.projection (A := fun y : Interval cs 1 (cs.wordProd l) => bottStalk cs l y.val)
      ((bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) x)
    c p hp hself
  intro m n hn
  exact bottSection_supported_annihilates cs l hl x (c m) n (hother m) hn

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSupported_of_stalkSupport (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : ∀ y : Interval cs 1 (cs.wordProd l), y≠x → bottStalkProjection cs l y.val m=0) :
    m∈bottWeightSupported cs l x.val := by
  intro e he
  let y : Interval cs 1 (cs.wordProd l) :=
    ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩
  have hy : y≠x := fun h => he (congrArg Subtype.val h)
  exact congrFun (congrArg Subtype.val (hm y hy)) ⟨e,rfl⟩

 theorem bottStalk_supported_annihilates (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) (m n : BottSamelsonModule cs l)
    (hm : ∀ y : Interval cs 1 (cs.wordProd l), y≠x → bottStalkProjection cs l y.val m=0)
    (hn : bottStalkProjection cs l x.val n=0) : bottSamelsonDuality cs l m n=0 :=
  bott_supported_annihilates cs l x.val (bottSupported_of_stalkSupport cs l hl x m hm) n
    (congrArg Subtype.val hn)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.Graded
open Module
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul 𝓐 𝓜]
  {ι : Type ui} [Fintype ι] (b : Basis ι A M) (d : ι → ℤ)
  (hb : ∀ i, b i ∈ 𝓜 (d i))
noncomputable section

include hb in
 theorem homogeneous_basis_repr (n : ℤ) (v : M) (hv : v ∈ 𝓜 n) (i : ι) :
    b.repr v i ∈ 𝓐 (n-d i) := by
  let _ : DirectSum.Decomposition (shiftedPiece 𝓐 d) :=
    (shifted_isInternal 𝓐 d).chooseDecomposition
  have hg : ∀ n f, f ∈ shiftedPiece 𝓐 d n → b.equivFun.symm f ∈ 𝓜 (n+0) := by
    intro n f hf
    rw [add_zero,b.equivFun_symm_apply]
    apply Submodule.sum_mem
    intro j _
    simpa only [vadd_eq_add,sub_add_cancel] using SetLike.GradedSMul.smul_mem (hf j) (hb j)
  have h := equiv_inverse_homogeneous (shiftedPiece 𝓐 d) 𝓜 b.equivFun.symm 0 hg n v hv
  rw [sub_zero] at h
  exact h i

include hb in
 theorem dualBasis_homogeneous [DecidableEq ι] (i : ι) (n : ℤ) (v : M) (hv : v ∈ 𝓜 n) :
    b.dualBasis i v ∈ 𝓐 (n+(-d i)) := by
  simpa only [Basis.coe_dualBasis,Basis.coord_apply,← sub_eq_add_neg] using
    homogeneous_basis_repr 𝓐 𝓜 b d hb n v hv i

end
end KLInvariance.Graded

end


section

/-! Genuine polynomial reflection from a homogeneous perfect duality. The
nonnegative lattice supplies a weak degree bound, not the strict KL bound. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

omit [Finite σ] in
 theorem degree_le_of_dual_equiv
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l))
    (c : NonnegativeBasis (σ := σ) M.piece) (i : c.index) : c.degree i ≤ l := by
  classical
  have h := he (-(c.degree i : ℤ)) (c.basis.dualBasis i)
    (dualBasis_homogeneous (polynomialGrading k σ) M.piece c.basis
      (fun i => (c.degree i : ℤ)) c.homogeneous i)
  by_contra hn
  have hn' : -(c.degree i : ℤ)+(l:ℤ)<0 := by omega
  rw [N.nonneg _ hn',Submodule.mem_bot] at h
  have hz := e.injective (show e (c.basis.dualBasis i)=e 0 from
    h.trans (map_zero e).symm)
  exact c.basis.dualBasis.ne_zero i hz

 def reflectedBasis
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l))
    (c : NonnegativeBasis (σ := σ) M.piece) : NonnegativeBasis (σ := σ) N.piece := by
  classical
  exact {
    index := c.index
    finite := c.finite
    basis := c.basis.dualBasis.map e
    degree := fun i => l-c.degree i
    homogeneous := fun i => by
      have hi := M.degree_le_of_dual_equiv N e l he c i
      have h := he (-(c.degree i : ℤ)) (c.basis.dualBasis i)
        (dualBasis_homogeneous (polynomialGrading k σ) M.piece c.basis
          (fun i => (c.degree i : ℤ)) c.homogeneous i)
      change e (c.basis.dualBasis i) ∈ N.piece ((l-c.degree i : ℕ):ℤ)
      have hd : ((l-c.degree i : ℕ):ℤ)=-(c.degree i : ℤ)+(l:ℤ) := by omega
      rw [hd]
      exact h }

 theorem char_of_dual_equiv [Module.Free (MvPolynomial σ k) M]
    [Module.Free (MvPolynomial σ k) N]
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l)) :
    N.char=Polynomial.reflect l M.char := by
  classical
  let c := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [char,character_eq _ _ (M.reflectedBasis N e l he c),char,character_eq _ _ c]
  change (∑ i : c.index, (X : Polynomial ℤ)^(l-c.degree i))=
    Polynomial.reflect l (∑ i : c.index, X^c.degree i)
  have hs (s : Finset c.index) : Polynomial.reflect l (∑ i∈s, (X : Polynomial ℤ)^c.degree i)=
      ∑ i∈s, Polynomial.reflect l (X^c.degree i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha,ih]
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.reflect_monomial,Polynomial.revAt_le (M.degree_le_of_dual_equiv N e l he c i)]

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} (B : Sheaf.{ur,uv,ue,um} (R := R) G)

/-- A common edge annihilator makes all the scaled coordinate idempotents
integral endomorphisms of the section module. -/
 theorem scaled_single_section [DecidableEq V] {p : R}
    (hp : ∀ e (v : B.edge e), p • v = 0) (x : V) (m : B.sections Set.univ) :
    p • Pi.single x (m.val x) ∈ B.sections Set.univ := by
  intro e _ _
  simp only [Pi.smul_apply,map_smul,hp]

variable [Fintype E] (α : E → R)

def labelProduct : R := ∏ e, α e

 theorem labelProduct_ne_zero [IsDomain R] (hα : ∀ e, α e ≠ 0) : labelProduct α ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun e _ => hα e)

 theorem labelProduct_annihilates (hα : ∀ e (v : B.edge e), α e • v = 0)
    (e : E) (v : B.edge e) : labelProduct α • v = 0 := by
  obtain ⟨r,hr⟩ := Finset.dvd_prod_of_mem α (Finset.mem_univ e)
  change (∏ e, α e) • v = 0
  rw [hr,mul_comm, mul_smul,hα,smul_zero]

omit [Fintype E] in
 theorem projection_surjective (hg : B.Generated) (x : V) :
    Function.Surjective (IntegralSupport.projection (B.sections Set.univ) x) := by
  intro a
  obtain ⟨m,hm,hx⟩ := hg x a
  exact ⟨⟨m,hm⟩,hx⟩

variable [DecidableEq V] [IsDomain R] [∀ x, Module.IsTorsionFree R (B.vertex x)]
  (hα : ∀ e, α e ≠ 0) (ha : ∀ e (v : B.edge e), α e • v = 0)
  (d : B.sections Set.univ ≃ₗ[R] Module.Dual R (B.sections Set.univ))
  (hbalanced : ∀ x m n,
    d (IntegralSupport.cut (B.sections Set.univ) (labelProduct α)
      (B.scaled_single_section (B.labelProduct_annihilates α ha)) x m) n =
    d m (IntegralSupport.cut (B.sections Set.univ) (labelProduct α)
      (B.scaled_single_section (B.labelProduct_annihilates α ha)) x n))


noncomputable def singleSupportEquivDual (hg : B.Generated) (x : V) :
    IntegralSupport.supported (B.sections Set.univ) x ≃ₗ[R] Module.Dual R (B.vertex x) :=
  IntegralSupport.supportEquivDual (B.sections Set.univ) (labelProduct α)
    (B.scaled_single_section (B.labelProduct_annihilates α ha))
    (labelProduct_ne_zero α hα) d hbalanced x (B.projection_surjective hg x)

end KLInvariance.MomentGraph.Sheaf

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G) {α : E → A}

 theorem UpperQuotient.annihilates (h : B.UpperQuotient α) (e : E) (v : B.edge e) :
    α e • v = 0 := by
  obtain ⟨w,rfl⟩ := (h e).1 v
  rw [← map_smul]
  exact (h e).2 _ |>.mpr ⟨w,rfl⟩

end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um ui
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} (B : Sheaf.{ur,uv,ue,um} (R := R) G)

 theorem stalkMap_eq_zero_iff (x : V) (v : B.vertex x) :
    B.stalkMap x v = 0 ↔ ∀ e (h : G.source e = x), B.lower e (h.symm ▸ v) = 0 := by
  constructor
  · intro hv e he
    exact congrFun hv ⟨e,he⟩
  · intro hv
    funext e
    exact hv e.val e.property

 theorem single_section_iff [DecidableEq V] (x : V) (v : B.vertex x) :
    Pi.single x v ∈ B.sections Set.univ ↔
      B.stalkMap x v = 0 ∧ ∀ e (h : G.target e = x), B.upper e (h.symm ▸ v) = 0 := by
  constructor
  · intro hv
    constructor
    · apply (B.stalkMap_eq_zero_iff x v).mpr
      intro e he
      subst x
      have hc := hv e (Set.mem_univ _) (Set.mem_univ _)
      simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_gt (G.increasing e)),map_zero] using hc
    · intro e he
      subst x
      have hc := hv e (Set.mem_univ _) (Set.mem_univ _)
      simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_lt (G.increasing e)),map_zero] using hc.symm
  · rintro ⟨hu,hd⟩ e _ _
    by_cases hs : G.source e = x
    · subst x
      simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_gt (G.increasing e)),map_zero]
        using (B.stalkMap_eq_zero_iff _ _).mp hu e rfl
    · by_cases ht : G.target e = x
      · subst x
        simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_lt (G.increasing e)),map_zero]
          using (hd e rfl).symm
      · simp only [Pi.single_eq_of_ne hs,Pi.single_eq_of_ne ht,map_zero]

variable [Fintype E] [DecidableEq V]

def incoming (x : V) : Finset E := Finset.univ.filter (fun e => G.target e = x)

@[simp] theorem mem_incoming (x : V) (e : E) : e ∈ incoming (G := G) x ↔ G.target e = x := by
  simp [incoming]

def incomingProduct (α : E → R) (x : V) : R := ∏ e ∈ incoming (G := G) x, α e

variable [IsDomain R] (α : E → R)
  (hα : ∀ e, Prime (α e))
  (hq : ∀ e, Function.Surjective (B.upper e))
  (hk : ∀ e v, B.upper e v = 0 ↔ ∃ w, v = α e • w)
  {ι : V → Type ui} [∀ x, Fintype (ι x)] (bs : ∀ x, Module.Basis (ι x) R (B.vertex x))

include hα in
 theorem incomingProduct_ne_zero (x : V) : incomingProduct (G := G) α x ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun e _ => (hα e).ne_zero)

omit [IsDomain R] in
include hα hq hk bs in
 theorem outgoing_product_regular (x : V)
    (hsep : ∀ e f, G.source e = x → G.target f = x → ¬ α e ∣ α f)
    (e : E) (he : G.source e = x) :
    Function.Injective (fun v : B.edge e => incomingProduct (G := G) α x • v) := by
  apply FiniteFreeScalar.scalar_quotient_regular (bs (G.target e)) (B.upper e) (hq e)
    (α e) (incomingProduct (G := G) α x) (hα e) _ (hk e)
  intro hdiv
  obtain ⟨f,hf,hfdiv⟩ := ((hα e).dvd_finsetProd_iff α).mp hdiv
  exact hsep e f he ((mem_incoming (G := G) x f).mp hf) hfdiv

omit [IsDomain R] in
include hk bs in
/-- The actual integral single-support conditions. Downward labels impose
product divisibility, and they are regular at every upward edge. -/
 theorem single_section_iff_prod [DecompositionMonoid R] (x : V)
    (hrel : (incoming (G := G) x : Set E).Pairwise (Function.onFun IsRelPrime α))
    (hreg : ∀ e, G.source e = x → Function.Injective
      (fun v : B.edge e => incomingProduct (G := G) α x • v)) (v : B.vertex x) :
    Pi.single x v ∈ B.sections Set.univ ↔
      ∃ w : B.vertex x, v = incomingProduct (G := G) α x • w ∧ B.stalkMap x w = 0 := by
  constructor
  · intro hv
    obtain ⟨hu,hd⟩ := (B.single_section_iff x v).mp hv
    have hdiv : ∀ e ∈ incoming (G := G) x, ∃ w : B.vertex x, α e • w = v := by
      intro e he
      have ht := (mem_incoming (G := G) x e).mp he
      subst x
      obtain ⟨w,hw⟩ := (hk e v).mp (hd e rfl)
      exact ⟨w,hw.symm⟩
    obtain ⟨w,hw⟩ := FiniteFreeScalar.exists_prod_smul (bs x) (incoming (G := G) x) α hrel v hdiv
    refine ⟨w,hw.symm,?_⟩
    apply (B.stalkMap_eq_zero_iff x w).mpr
    intro e he
    apply hreg e he
    change incomingProduct (G := G) α x • _ = incomingProduct (G := G) α x • (0 : B.edge e)
    rw [smul_zero]
    have hz := (B.stalkMap_eq_zero_iff x v).mp hu e he
    subst x
    rw [← hw,map_smul] at hz
    exact hz
  · rintro ⟨w,rfl,hw⟩
    apply (B.single_section_iff x _).mpr
    constructor
    · rw [map_smul,hw,smul_zero]
    · intro e he
      subst x
      obtain ⟨r,hr⟩ := Finset.dvd_prod_of_mem α ((mem_incoming (G := G) _ e).mpr rfl)
      apply (hk e _).mpr
      exact ⟨r • w, by rw [incomingProduct,hr,mul_smul]⟩

/-- The single-support part as an actual submodule of its stalk. -/
def singleStalk (x : V) : Submodule R (B.vertex x) :=
  (B.sections Set.univ).comap (LinearMap.single R (fun y => B.vertex y) x)

noncomputable def singleStalkEquivSupport (x : V) :
    B.singleStalk x ≃ₗ[R] IntegralSupport.supported (B.sections Set.univ) x := by
  let f : B.singleStalk x →ₗ[R] IntegralSupport.supported (B.sections Set.univ) x :=
    { toFun := fun v => ⟨⟨Pi.single x v.val,v.property⟩,by
                        intro y hy; exact Pi.single_eq_of_ne hy _⟩
      map_add' := by intro v w; apply Subtype.ext; apply Subtype.ext; exact Pi.single_add _ _ _
      map_smul' := by intro r v; apply Subtype.ext; apply Subtype.ext; exact Pi.single_smul _ _ _ }
  apply LinearEquiv.ofBijective f
  constructor
  · intro v w hvw
    apply Subtype.ext
    have hv := congrArg (fun s : IntegralSupport.supported (B.sections Set.univ) x => s.val.val x) hvw
    change (Pi.single x v.val : B.Assignment) x = (Pi.single x w.val : B.Assignment) x at hv
    simpa only [Pi.single_eq_same] using hv
  · intro m
    have he : Pi.single x (m.val.val x) = m.val.val := by
      funext y
      by_cases hy : y=x
      · subst y; simp only [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hy, m.property y hy]
    refine ⟨⟨m.val.val x,?_⟩,?_⟩
    · change Pi.single x (m.val.val x) ∈ B.sections Set.univ
      rw [he]; exact m.val.property
    · apply Subtype.ext; apply Subtype.ext; exact he


noncomputable def kernelEquivSingleStalk [DecompositionMonoid R] (x : V)
    (hrel : (incoming (G := G) x : Set E).Pairwise (Function.onFun IsRelPrime α))
    (hreg : ∀ e, G.source e = x → Function.Injective
      (fun v : B.edge e => incomingProduct (G := G) α x • v)) :
    LinearMap.ker (B.stalkMap x) ≃ₗ[R] B.singleStalk x := by
  let p := incomingProduct (G := G) α x
  let f : LinearMap.ker (B.stalkMap x) →ₗ[R] B.singleStalk x :=
    (p • (LinearMap.ker (B.stalkMap x)).subtype).codRestrict (B.singleStalk x) (by
      intro v
      exact (B.single_section_iff_prod α hk bs x hrel hreg _).mpr ⟨v.val,rfl,v.property⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro v w hvw
    apply Subtype.ext
    let : Module.Free R (B.vertex x) := Module.Free.of_basis (bs x)
    exact smul_right_injective (B.vertex x) (incomingProduct_ne_zero α hα x)
      (congrArg Subtype.val hvw)
  · intro v
    obtain ⟨w,hw,hz⟩ := (B.single_section_iff_prod α hk bs x hrel hreg v.val).mp v.property
    exact ⟨⟨w,hz⟩,Subtype.ext hw.symm⟩

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem root_injective_on_labels {e f : Edge cs u b} (h : root cs u b e = root cs u b f) :
    label cs u b e = label cs u b f := by
  exact congrArg Subtype.val ((positiveRootEquiv M cs).injective h)

 theorem polynomialLabel_prime (e : Edge cs u b) : Prime (polynomialLabel cs u b basis e) := by
  apply (MulEquiv.prime_iff (SymmetricAlgebra.equivMvPolynomial basis)).mpr
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact (root cs u b e).property.1.ne_zero (congrArg Prod.fst h)

 theorem label_eq_of_polynomialLabel_dvd {e f : Edge cs u b}
    (h : polynomialLabel cs u b basis e ∣ polynomialLabel cs u b basis f) :
    label cs u b e = label cs u b f := by
  apply root_injective_on_labels cs u b
  by_contra hn
  have hd : SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b e).val) ∣
      SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b f).val) := by
    obtain ⟨z,hz⟩ := h
    exact ⟨(SymmetricAlgebra.equivMvPolynomial basis).symm z, by
      apply (SymmetricAlgebra.equivMvPolynomial basis).injective
      simpa only [map_mul,AlgEquiv.apply_symm_apply,polynomialLabel] using hz⟩
  have hm := (EdgeAlgebra.symmetric_ι_dvd_iff _ _).mp hd
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hm
  have he : r • (root cs u b e).val = (1 : ℝ) • (root cs u b f).val := by
    have hfst := congrArg Prod.fst hr
    change r • (root cs u b e).val = (root cs u b f).val at hfst
    simpa only [one_smul] using hfst
  exact one_ne_zero ((positiveRoots_independent _ _ hn).eq_zero_of_pair' he).2

 theorem incoming_pairwise_relPrime [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)] (x : Interval cs u b) :
    (Sheaf.incoming (G := graph cs u b) x : Set (Edge cs u b)).Pairwise
      (Function.onFun IsRelPrime (polynomialLabel cs u b basis)) := by
  intro e he f hf hne
  apply ((polynomialLabel_prime cs u b basis e).irreducible.isRelPrime_iff_not_dvd).mpr
  intro hdiv
  apply hne
  apply eq_of_label_target_eq cs u b (label_eq_of_polynomialLabel_dvd cs u b basis hdiv)
  exact ((Sheaf.mem_incoming x e).mp he).trans ((Sheaf.mem_incoming x f).mp hf).symm

 theorem outgoing_incoming_not_dvd (x : Interval cs u b) (e f : Edge cs u b)
    (he : (graph cs u b).source e = x) (hf : (graph cs u b).target f = x) :
    ¬ polynomialLabel cs u b basis e ∣ polynomialLabel cs u b basis f := by
  intro h
  apply source_ne_target_of_label_eq cs u b (label_eq_of_polynomialLabel_dvd cs u b basis h)
  exact he.trans hf.symm

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
  (a : A) (d : ℤ) (ha : a ∈ 𝓐 d)

 def scalarDegreeMap (n : ℤ) : 𝓜 (n-d) →ₗ[k]
    subPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a)) n :=
  { toFun := fun m => ⟨⟨a • m.val,⟨m.val,rfl⟩⟩,by
      change a • m.val ∈ 𝓜 n
      simpa using SetLike.GradedSMul.smul_mem ha m.property⟩
    map_add' := by intros; ext; exact smul_add _ _ _
    map_smul' := by intros; ext; exact smul_comm _ _ _ }

 theorem scalarDegreeMap_surjective (n : ℤ) :
    Function.Surjective (scalarDegreeMap 𝓐 𝓜 a d ha n) := by
  rintro ⟨⟨m,v,hv⟩,hm⟩
  refine ⟨DirectSum.decompose 𝓜 v (n-d), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change a • component 𝓜 (n-d) v = m
  rw [← component_homogeneous_smul 𝓐 𝓜 d a ha n v]
  change (DirectSum.decompose 𝓜 (a • v) n : M) = m
  change a • v = m at hv
  rw [hv]
  exact DirectSum.decompose_of_mem_same 𝓜 hm

omit [DirectSum.Decomposition 𝓜] in
 theorem scalarDegreeMap_injective (hinj : Function.Injective (fun m : M => a • m)) (n : ℤ) :
    Function.Injective (scalarDegreeMap 𝓐 𝓜 a d ha n) := by
  intro v w h
  apply Subtype.ext
  apply hinj
  exact congrArg (fun t => t.val.val) h

noncomputable def scalarDegreeEquiv
    (hinj : Function.Injective (fun m : M => a • m)) (n : ℤ) :
    𝓜 (n-d) ≃ₗ[k] subPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a)) n :=
  LinearEquiv.ofBijective (scalarDegreeMap 𝓐 𝓜 a d ha n)
    ⟨scalarDegreeMap_injective 𝓐 𝓜 a d ha hinj n,
      scalarDegreeMap_surjective 𝓐 𝓜 a d ha n⟩

include ha in
 theorem scalar_value
    (hinj : Function.Injective (fun m : M => a • m)) {q : ℝ} (hq : q ≠ 0)
    (hs : Summable (term 𝓜 ⊤ q)) :
    value (subPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a))) ⊤ q =
      q^d * value 𝓜 ⊤ q := by
  have h := (hs.hasSum.mul_left (q^d))
  have hh : HasSum
      (fun n : ℤ => (Module.finrank k (𝓜 (n-d)) : ℝ)*q^n)
      (q^d * value 𝓜 ⊤ q) := by
    apply (Equiv.addRight d).hasSum_iff.mp
    apply h.congr_fun
    intro n
    rw [term_top]
    change (Module.finrank k (𝓜 (n+d-d)) : ℝ)*q^(n+d) =
      q^d * ((Module.finrank k (𝓜 n) : ℝ)*q^n)
    rw [add_sub_cancel_right,zpow_add₀ hq]
    ring
  apply HasSum.tsum_eq
  apply hh.congr_fun
  intro n
  rw [term_top,← LinearEquiv.finrank_eq (scalarDegreeEquiv 𝓐 𝓜 a d ha hinj n)]

include ha in


 theorem scalarQuotient_value [∀ n, Module.Finite k (𝓜 n)]
    (hinj : Function.Injective (fun m : M => a • m)) {q : ℝ} (hq : 0 < q)
    (hs : Summable (term 𝓜 ⊤ q)) :
    value (quotientPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a))) ⊤ q =
      (1-q^d) * value 𝓜 ⊤ q := by
  let S := LinearMap.range (LinearMap.lsmul A M a)
  let : DirectSum.Decomposition (quotientPiece 𝓜 S) :=
    (quotient_isInternal 𝓜 S (scalar_range_homogeneous 𝓐 𝓜 d a ha)).chooseDecomposition
  have h := value_exact_of_summable 𝓜 (quotientPiece 𝓜 S) S.mkQ
    (fun n m hm => Submodule.mem_map.mpr ⟨m,hm,rfl⟩) S.mkQ_surjective hq hs
  rw [Submodule.ker_mkQ] at h
  change value 𝓜 ⊤ q = value (subPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a))) ⊤ q + _ at h
  rw [scalar_value 𝓐 𝓜 a d ha hinj hq.ne' hs] at h
  change value (quotientPiece 𝓜 S) ⊤ q = _
  linarith

end KLInvariance.Hilbert

end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

 def imageMap (S : Submodule A M) (f : M →ₗ[A] N) : S →ₗ[A] S.map f where
  toFun v := ⟨f v.val,Submodule.mem_map.mpr ⟨_,v.property,rfl⟩⟩
  map_add' _ _ := by ext; exact map_add f _ _
  map_smul' _ _ := by ext; exact map_smul f _ _

 theorem imageMap_surjective (S : Submodule A M) (f : M →ₗ[A] N) :
    Function.Surjective (imageMap S f) := by
  rintro ⟨m,hm⟩
  obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hm
  exact ⟨⟨v,hv⟩,rfl⟩

 theorem imageMap_ker (S : Submodule A M) (f : M →ₗ[A] N) (a : A)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v = a • w)
    (hS : ∀ v, a • v ∈ S → v ∈ S) :
    LinearMap.ker (imageMap S f) = LinearMap.range (LinearMap.lsmul A S a) := by
  ext v
  constructor
  · intro hv
    have hz : f v.val = 0 := congrArg Subtype.val hv
    obtain ⟨w,hw⟩ := (hf v.val).mp hz
    have hwS : w ∈ S := hS w (hw ▸ v.property)
    exact ⟨⟨w,hwS⟩,Subtype.ext hw.symm⟩
  · rintro ⟨w,rfl⟩
    apply Subtype.ext
    exact (hf (a • w.val)).mpr ⟨w.val,rfl⟩

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem map_homogeneous
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n) :
    ∀ n v, v ∈ S.map f → component 𝓝 n v ∈ S.map f := by
  intro n v hv
  obtain ⟨w,hw,rfl⟩ := Submodule.mem_map.mp hv
  refine Submodule.mem_map.mpr ⟨component 𝓜 n w,hS n w hw,?_⟩
  simpa using (map_component 𝓜 𝓝 f 0 (by simpa using hf) n w).symm

/-- The actual upper image of a saturated graded submodule has precisely
`(1-q^d)` times its Hilbert series. No choice of edge basis enters this identity. -/
theorem saturated_image_value
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [SetLike.GradedSMul 𝓐 𝓜] [∀ n, Module.Finite k (𝓜 n)]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (a : A) (d : ℤ) (ha : a ∈ 𝓐 d)
    (hk : ∀ v, f v = 0 ↔ ∃ w, v = a • w)
    (hsat : ∀ v, a • v ∈ S → v ∈ S)
    (hinj : Function.Injective (fun v : M => a • v))
    {q : ℝ} (hq : 0 < q) (hs : Summable (term 𝓜 (S.restrictScalars k) q)) :
    value 𝓝 ((S.map f).restrictScalars k) q =
      (1-q^d) * value 𝓜 (S.restrictScalars k) q := by
  let : DirectSum.Decomposition (subPiece 𝓜 S) := (sub_isInternal 𝓜 S hS).chooseDecomposition
  let : DirectSum.Decomposition (subPiece 𝓝 (S.map f)) :=
    (sub_isInternal 𝓝 (S.map f) (map_homogeneous 𝓜 𝓝 S hS f hf)).chooseDecomposition
  let (n : ℤ) : Module.Finite k (subPiece 𝓜 S n) := Module.Finite.of_surjective
    (subPieceEquiv 𝓜 S n).symm.toLinearMap (subPieceEquiv 𝓜 S n).symm.surjective
  have hs' : Summable (term (subPiece 𝓜 S) ⊤ q) :=
    hs.congr (fun n => (term_subPiece 𝓜 S q n).symm)
  have h := value_exact_of_summable (subPiece 𝓜 S) (subPiece 𝓝 (S.map f))
    (imageMap S f) (fun n v hv => hf n v.val hv) (imageMap_surjective S f) hq hs'
  rw [imageMap_ker S f a hk hsat] at h
  have hinj' : Function.Injective (fun v : S => a • v) := by
    intro v w hv
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hv
  rw [scalar_value 𝓐 (subPiece 𝓜 S) a d ha hinj' hq.ne' hs',
    value_subPiece,value_subPiece] at h
  linarith

end KLInvariance.Hilbert

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded _root_.OAI.KLInvariance.Hilbert
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)

 theorem upwardSubmodule_saturated (x : V) (F : Set (Sheaf.Outgoing (G := G) x))
    (a : A) (hreg : ∀ e ∈ F, Function.Injective (fun v : B.edge e.val => a • v)) :
    ∀ v, a • v ∈ B.upwardSubmodule x F → v ∈ B.upwardSubmodule x F := by
  intro v hv e he
  have hz : (B.lowerAt x e).map (a • v) = 0 :=
    (B.lowerAt_map x e (a • v)).trans (hv e he)
  have hz' : (B.lowerAt x e).map v = 0 := by
    apply hreg e he
    change a • (B.lowerAt x e).map v = a • (0 : B.edge e.val)
    simpa only [map_smul,smul_zero] using hz
  exact (B.lowerAt_map x e v).symm.trans hz'


 theorem upper_image_value (α : E → A) (hquot : B.UpperQuotient α)
    (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.target e)))
    [∀ n, Module.Finite k ((B.vertex (G.target e)).piece n)]
    (ha : α e ∈ 𝓐 1)
    (hreg : ∀ f ∈ F, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    {q : ℝ} (hq : 0 < q)
    (hs : Summable (term (B.vertex (G.target e)).piece
      ((B.upwardSubmodule (G.target e) F).restrictScalars k) q)) :
    value (B.edge e).piece
        (((B.upwardSubmodule (G.target e) F).map (B.upper e).map).restrictScalars k) q =
      (1-q) * value (B.vertex (G.target e)).piece
        ((B.upwardSubmodule (G.target e) F).restrictScalars k) q := by
  simpa only [zpow_one] using saturated_image_value 𝓐
    (B.vertex (G.target e)).piece (B.edge e).piece
    (B.upwardSubmodule (G.target e) F) (B.upwardKernel_homogeneous (G.target e) F)
    (B.upper e).map (B.upper e).graded (α e) 1 ha (hquot e).2
    (B.upwardSubmodule_saturated (G.target e) F (α e) hreg) hinj hq hs

end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
 theorem label_regular_stalk (e : Edge cs u b) (x : Interval cs u b) :
    Function.Injective (fun v : B.sheaf.vertex x => polynomialLabel cs u b basis e • v) := by
  let := B.free x
  exact smul_right_injective _ (polynomialLabel_ne_zero cs u b basis e)

omit [Fintype σ] in


 theorem incoming_label_regular_outgoing (e f : Edge cs u b)
    (h : (graph cs u b).source f = (graph cs u b).target e) :
    Function.Injective (fun v : B.sheaf.edge f => polynomialLabel cs u b basis e • v) := by
  let := B.free ((graph cs u b).target f)
  exact FiniteFreeScalar.scalar_quotient_regular
    (Module.Free.chooseBasis (Coefficient (σ := σ)) (B.sheaf.vertex ((graph cs u b).target f)))
    (B.sheaf.upper f).map (B.quotient f).1
    (polynomialLabel cs u b basis f) (polynomialLabel cs u b basis e)
    (polynomialLabel_prime cs u b basis f)
    (outgoing_incoming_not_dvd cs u b basis _ f e h rfl) (B.quotient f).2

 theorem upper_image_hilbert (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    [∀ n, Module.Finite ℝ ((B.sheaf.vertex ((graph cs u b).target e)).piece n)]
    {q : ℝ} (hq : 0 < q)
    (hs : Summable (Hilbert.term (B.sheaf.vertex ((graph cs u b).target e)).piece
      ((B.sheaf.upwardSubmodule ((graph cs u b).target e) F).restrictScalars ℝ) q)) :
    Hilbert.value (B.sheaf.edge e).piece
      (((B.sheaf.upwardSubmodule ((graph cs u b).target e) F).map
        (B.sheaf.upper e).map).restrictScalars ℝ) q =
      (1-q) * Hilbert.value (B.sheaf.vertex ((graph cs u b).target e)).piece
        ((B.sheaf.upwardSubmodule ((graph cs u b).target e) F).restrictScalars ℝ) q := by
  apply B.sheaf.upper_image_value (polynomialLabel cs u b basis) B.quotient e F
    (polynomialLabel_homogeneous cs u b basis e)
  · intro f _
    exact incoming_label_regular_outgoing cs u b basis hub B e f.val f.property
  · exact label_regular_stalk cs u b basis hub B e _
  · exact hq
  · exact hs

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

 def kernelEquivSingleSupport (x : Interval cs u b) :
    LinearMap.ker (B.sheaf.forget.stalkMap x) ≃ₗ[Coefficient (σ := σ)]
      IntegralSupport.supported (B.sheaf.forget.sections Set.univ) x := by
  let _ (x : Interval cs u b) : Module.Free (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) := B.free x
  let _ (x : Interval cs u b) : Module.Finite (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) :=
    (B.sheaf.vertex x).finite
  let _ (x : Interval cs u b) : Fintype (Module.Free.ChooseBasisIndex
      (Coefficient (σ := σ)) (B.sheaf.forget.vertex x)) := Fintype.ofFinite _
  let bs := fun x : Interval cs u b =>
    Module.Free.chooseBasis (Coefficient (σ := σ)) (B.sheaf.forget.vertex x)
  exact (B.sheaf.forget.kernelEquivSingleStalk (polynomialLabel cs u b basis)
    (polynomialLabel_prime cs u b basis) (fun e => (B.quotient e).2) bs x
    (incoming_pairwise_relPrime cs u b basis x)
    (B.sheaf.forget.outgoing_product_regular (polynomialLabel cs u b basis)
      (polynomialLabel_prime cs u b basis) (fun e => (B.quotient e).1)
      (fun e => (B.quotient e).2) bs x
      (outgoing_incoming_not_dvd cs u b basis x))).trans
        (B.sheaf.forget.singleStalkEquivSupport x)


structure SectionDuality where
  pairing : B.sheaf.forget.sections Set.univ ≃ₗ[Coefficient (σ := σ)]
    Dual (Coefficient (σ := σ)) (B.sheaf.forget.sections Set.univ)
  balanced : ∀ x m n,
    pairing (IntegralSupport.cut (B.sheaf.forget.sections Set.univ)
      (Sheaf.labelProduct (polynomialLabel cs u b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x m) n =
    pairing m (IntegralSupport.cut (B.sheaf.forget.sections Set.univ)
      (Sheaf.labelProduct (polynomialLabel cs u b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x n)

 def costalkEquivDual (d : SectionDuality cs u b basis hub B) (x : Interval cs u b) :
    LinearMap.ker (B.sheaf.forget.stalkMap x) ≃ₗ[Coefficient (σ := σ)]
      Dual (Coefficient (σ := σ)) (B.sheaf.vertex x) := by
  let _ (x : Interval cs u b) : Module.Free (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) := B.free x
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  exact (kernelEquivSingleSupport cs u b basis hub B x).trans
    (B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced B.generated x)

 theorem costalk_free_of_duality (d : SectionDuality cs u b basis hub B)
    (x : Interval cs u b) :
    Module.Free (Coefficient (σ := σ)) (LinearMap.ker (B.sheaf.forget.stalkMap x)) := by
  let _ := B.free x
  exact Module.Free.of_equiv (costalkEquivDual cs u b basis hub B d x).symm

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.MomentGraph.GradedSheaf
open Module _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐]
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E] [DecidableEq V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)
  [IsNoetherianRing A] [IsDomain A]
  [∀ x, Module.IsTorsionFree A (B.forget.vertex x)]
  (α : E → A) (hα : ∀ e, α e ≠ 0) (ha : ∀ e (v : B.edge e), α e • v = 0)
  (p : B.forget.sections Set.univ ≃ₗ[A] Dual A (B.forget.sections Set.univ))
  (hbalanced : ∀ x m n,
    p (IntegralSupport.cut (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha)) x m) n =
    p m (IntegralSupport.cut (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha)) x n))
noncomputable section

 theorem dualToSupport_homogeneous (l : ℤ)
    (hp : ∀ i j (m n : B.sections Set.univ),
      m ∈ (B.sections Set.univ).piece i → n ∈ (B.sections Set.univ).piece j →
      p m n ∈ 𝓐 (i+j-l))
    (x : V) (r : ℤ) (lam : Dual A (B.vertex x))
    (hlam : ∀ j (v : B.vertex x), v ∈ (B.vertex x).piece j → lam v ∈ 𝓐 (j+r)) :
    (IntegralSupport.dualToSupport (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha))
      (Sheaf.labelProduct_ne_zero α hα) p hbalanced x lam).val ∈
        (B.sections Set.univ).piece (r+l) := by
  apply perfect_inverse_of_homogeneous_functional 𝓐 (B.sections Set.univ).piece p l hp r
  intro j n hn
  exact hlam j (n.val x) (hn x (Set.mem_univ x))

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]

/-- Cancellation of an injective homogeneous scalar action includes the
inverse grading shift. It does not require the scalar to be a unit. -/
 theorem mem_of_homogeneous_smul (d : ℤ) (a : A) (ha : a ∈ 𝓐 d)
    (hinj : Function.Injective (fun m : M => a • m))
    (n : ℤ) (m : M) (hm : a • m ∈ 𝓜 n) : m ∈ 𝓜 (n-d) := by
  have hc : component 𝓜 (n-d) m = m := by
    apply hinj
    change a • component 𝓜 (n-d) m = a • m
    rw [← component_homogeneous_smul 𝓐 𝓜 d a ha]
    exact DirectSum.decompose_of_mem_same 𝓜 hm
  rw [← hc]
  exact (DirectSum.decompose 𝓜 m (n-d)).property

end KLInvariance.Graded

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [Fintype (Interval cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

omit [Fintype (Interval cs u b)] in
 theorem incomingProduct_homogeneous (x : Interval cs u b) :
    Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x ∈
      polynomialGrading ℝ σ ((Sheaf.incoming (G := graph cs u b) x).card : ℤ) := by
  simpa only [Sheaf.incomingProduct,Finset.sum_const,Int.natCast_one,mul_one,nsmul_eq_mul] using
    SetLike.prod_mem_graded (polynomialGrading ℝ σ) (fun _ : Edge cs u b => (1 : ℤ))
      (polynomialLabel cs u b basis)
      (F := Sheaf.incoming (G := graph cs u b) x)
      (fun e _ => polynomialLabel_homogeneous cs u b basis e)

omit [Fintype σ] [Fintype (Interval cs u b)] in
 theorem kernelEquivSingleSupport_apply (x : Interval cs u b)
    (v : LinearMap.ker (B.sheaf.forget.stalkMap x)) :
    ((kernelEquivSingleSupport cs u b basis hub B x) v).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val := by
  change (Pi.single x
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val) :
      B.sheaf.forget.Assignment) x = _
  exact Pi.single_eq_same _ _

 theorem costalkEquivDual_inverse_homogeneous
    (d : SectionDuality cs u b basis hub B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (r : ℤ) (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v ∈ (B.sheaf.vertex x).piece j →
      lam v ∈ polynomialGrading ℝ σ (j+r)) :
    ((costalkEquivDual cs u b basis hub B d x).symm lam).val ∈
      (B.sheaf.vertex x).piece
        (r+l-(Sheaf.incoming (G := graph cs u b) x).card) := by
  let _ (y : Interval cs u b) : Module.Free (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := B.free y
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  let S := B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
    (polynomialLabel_ne_zero cs u b basis)
    (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
    d.pairing d.balanced B.generated x
  have hs : (S.symm lam).val ∈ (B.sheaf.sections Set.univ).piece (r+l) := by
    exact B.sheaf.dualToSupport_homogeneous (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced l hd x r lam hlam
  have hv := hs x (Set.mem_univ x)
  have he : (S.symm lam).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x •
      ((costalkEquivDual cs u b basis hub B d x).symm lam).val := by
    rw [← kernelEquivSingleSupport_apply cs u b basis hub B x]
    change (S.symm lam).val.val x =
      ((kernelEquivSingleSupport cs u b basis hub B x)
        ((kernelEquivSingleSupport cs u b basis hub B x).symm (S.symm lam))).val.val x
    rw [LinearEquiv.apply_symm_apply]
  change (S.symm lam).val.val x ∈ (B.sheaf.vertex x).piece (r+l) at hv
  rw [he] at hv
  apply mem_of_homogeneous_smul (polynomialGrading ℝ σ) (B.sheaf.vertex x).piece
    ((Sheaf.incoming (G := graph cs u b) x).card : ℤ)
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x)
    (incomingProduct_homogeneous cs u b basis x) _ (r+l) _ hv
  let _ := B.free x
  exact smul_right_injective _ (Sheaf.incomingProduct_ne_zero
    (polynomialLabel cs u b basis) (polynomialLabel_prime cs u b basis) x)

end
end KLInvariance.BruhatGraph

end


section

/-! The degree of the actual incoming root product on [1,b].  This is not
asserted for truncated intervals with arbitrary bottom. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (b : W)
noncomputable section

 def incomingEquivInversions (x : Interval cs 1 b) :
    {e : Edge cs 1 b // target cs 1 b e = x} ≃ {t : W // cs.IsLeftInversion x.val t} where
  toFun e := ⟨label cs 1 b e.val, label_isReflection cs 1 b e.val, by
    have hx : (target cs 1 b e.val).val = x.val := congrArg Subtype.val e.property
    have he := label_mul_target cs 1 b e.val
    rw [hx] at he
    rw [he]
    have h := e.val.property.1
    change cs.length (source cs 1 b e.val).val < cs.length (target cs 1 b e.val).val at h
    simpa only [hx] using h⟩
  invFun t := by
    have hstep : BruhatStep cs (t.val*x.val) x.val := by
      refine ⟨t.property.2,t.val,t.property.1,?_⟩
      rw [← mul_assoc,t.property.1.mul_self,one_mul]
    let y : Interval cs 1 b := ⟨t.val*x.val,one_bruhat cs _,
      (Relation.ReflTransGen.single hstep).trans x.property.2⟩
    exact ⟨⟨(y,x),hstep⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply eq_of_label_target_eq cs 1 b
    · change x.val * (label cs 1 b e.val*x.val)⁻¹ = label cs 1 b e.val
      rw [mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul,
        (label_isReflection cs 1 b e.val).inv]
    · exact e.property.symm
  right_inv t := by
    apply Subtype.ext
    change x.val * (t.val*x.val)⁻¹=t.val
    rw [mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul,t.property.1.inv]

 theorem incoming_card [Fintype (Edge cs 1 b)] [DecidableEq (Interval cs 1 b)]
    (x : Interval cs 1 b) : (Sheaf.incoming (G := graph cs 1 b) x).card = cs.length x.val := by
  classical
  calc
    _ = Nat.card {e : Edge cs 1 b // target cs 1 b e = x} := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      rfl
    _ = Nat.card {t : W // cs.IsLeftInversion x.val t} := Nat.card_congr (incomingEquivInversions cs b x)
    _ = Nat.card (RootInversions M cs x.val) := Nat.card_congr (rootInversionEquiv M cs x.val).symm
    _ = cs.length x.val := card_rootInversions M cs x.val

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [Fintype (Interval cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

 def fullSubmodule (x : Interval cs u b) : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex x) :=
    LinearMap.ker (B.sheaf.forget.stalkMap x)

omit [Fintype σ] [Fintype (Edge cs u b)] [Fintype (Interval cs u b)]
  [DecidableEq (Interval cs u b)] in
 theorem fullKernel_eq (x : Interval cs u b) :
    B.sheaf.upwardSubmodule x Set.univ = fullSubmodule cs u b basis hub B x := by
  ext m
  change (∀ e ∈ Set.univ, B.sheaf.forget.stalkMap x m e = 0) ↔ B.sheaf.forget.stalkMap x m = 0
  simp only [Set.mem_univ,forall_const]
  exact funext_iff.symm

 def fullKernel (x : Interval cs u b) : ModuleData (polynomialGrading ℝ σ) :=
  ModuleData.sub (B.sheaf.vertex x) (fullSubmodule cs u b basis hub B x) (by
    simpa only [fullKernel_eq cs u b basis hub B x] using
      B.sheaf.upwardKernel_homogeneous x Set.univ)

 theorem costalk_hilbert_of_duality
    (d : SectionDuality cs u b basis hub B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (c : NonnegativeBasis (σ := σ) (B.sheaf.vertex x).piece)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Hilbert.value (B.sheaf.vertex x).piece
      ((fullSubmodule cs u b basis hub B x).restrictScalars ℝ) q =
      q^(l-(Sheaf.incoming (G := graph cs u b) x).card) *
        Polynomial.eval₂ (Int.castRingHom ℝ) q⁻¹ c.polynomial *
        (1-q)⁻¹ ^ Fintype.card σ := by
  classical
  let K := fullKernel cs u b basis hub B x
  let cb : Basis c.index (Coefficient (σ := σ)) K :=
    c.basis.dualBasis.map (costalkEquivDual cs u b basis hub B d x).symm
  have hcb (i : c.index) : cb i ∈ K.piece
      (l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ)) := by
    change ((costalkEquivDual cs u b basis hub B d x).symm (c.basis.dualBasis i)).val ∈
      (B.sheaf.vertex x).piece _
    have h := costalkEquivDual_inverse_homogeneous cs u b basis hub B d l hd x
      (-(c.degree i : ℤ)) (c.basis.dualBasis i)
      (dualBasis_homogeneous (polynomialGrading ℝ σ) (B.sheaf.vertex x).piece
        c.basis (fun i => (c.degree i : ℤ)) c.homogeneous i)
    simpa only [show -(c.degree i : ℤ)+l-(Sheaf.incoming (G := graph cs u b) x).card =
      l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ) by omega] using h
  have hs := Hilbert.hasSum_homogeneous_basis K.piece cb
    (fun i => l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ)) hcb hq hq1
  have hv : Hilbert.value K.piece ⊤ q =
      (∑ i, q^(l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ))) *
        (1-q)⁻¹ ^ Fintype.card σ := by
    simpa only [Hilbert.value,Hilbert.term_top] using hs.tsum_eq
  change Hilbert.value (B.sheaf.vertex x).piece
    ((fullSubmodule cs u b basis hub B x).restrictScalars ℝ) q = _
  rw [← Hilbert.value_subPiece]
  change Hilbert.value K.piece ⊤ q = _
  rw [hv,c.eval₂_eq,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_sub₀ hq.ne',zpow_natCast,div_eq_mul_inv,inv_pow]

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.CoefficientChange
open Module
universe uk ua ub um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {B : Type ub} [CommRing B] [Algebra k B]
  (e : A ≃ₐ[k] B) {M : Type um} [AddCommGroup M] [Module A M]
  [Module k M] [IsScalarTower k A M]
noncomputable section

 def mapEquiv {N : Type un} [AddCommGroup N] [Module A N] [Module k N]
    [IsScalarTower k A N] (f : M ≃ₗ[A] N) : CoefficientChange e M ≃ₗ[B] CoefficientChange e N where
  toLinearMap := map e f.toLinearMap
  invFun n := mk (f.symm n.val)
  left_inv m := CoefficientChange.ext (f.symm_apply_apply m.val)
  right_inv n := CoefficientChange.ext (f.apply_symm_apply n.val)

 def dualTo (f : CoefficientChange e (Dual A M)) : Dual B (CoefficientChange e M) where
  toFun m := e (f.val m.val)
  map_add' m n := by change e (f.val (m.val+n.val))=_; rw [map_add,map_add]
  map_smul' b m := by
    change e (f.val (e.symm b • m.val))=b * e (f.val m.val)
    rw [map_smul]
    change e (e.symm b * f.val m.val)=_
    rw [map_mul,e.apply_symm_apply]

 def dualFrom (f : Dual B (CoefficientChange e M)) : Dual A M where
  toFun m := e.symm (f (mk m))
  map_add' m n := by
    change e.symm (f (mk m+mk n))=_
    rw [map_add,map_add]
  map_smul' a m := by
    change e.symm (f (mk (a • m)))=a * e.symm (f (mk m))
    rw [show (mk (a • m) : CoefficientChange e M)=e a • mk m from by
      apply CoefficientChange.ext
      change a • m=e.symm (e a) • m
      rw [e.symm_apply_apply],
      map_smul]
    change e.symm (e a * f (mk m))=_
    rw [map_mul,e.symm_apply_apply]

 def dualEquiv : CoefficientChange e (Dual A M) ≃ₗ[B] Dual B (CoefficientChange e M) where
  toFun := dualTo e
  invFun f := mk (dualFrom e f)
  left_inv f := by
    apply CoefficientChange.ext
    apply LinearMap.ext
    intro m
    exact e.symm_apply_apply (f.val m)
  right_inv f := by
    apply LinearMap.ext
    intro m
    exact e.apply_symm_apply (f m)
  map_add' f g := by
    apply LinearMap.ext
    intro m
    exact map_add e (f.val m.val) (g.val m.val)
  map_smul' b f := by
    apply LinearMap.ext
    intro m
    change e (e.symm b * f.val m.val)=b * e (f.val m.val)
    rw [map_mul,e.apply_symm_apply]

 def pairingEquiv (d : M ≃ₗ[A] Dual A M) :
    CoefficientChange e M ≃ₗ[B] Dual B (CoefficientChange e M) :=
  (mapEquiv e d).trans (dualEquiv e)

 omit [Module k M] [IsScalarTower k A M] in
 theorem pairingEquiv_apply (d : M ≃ₗ[A] Dual A M) (m n : CoefficientChange e M) :
    pairingEquiv e d m n=e (d m.val n.val) := rfl

end
end KLInvariance.CoefficientChange

end


section

/-! A genuine homogeneous integral perfect pairing with vertex-support
orthogonality on both sides. Transport does not identify unequal lattices. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section

 structure PerfectPairing (S : GradedSheaf (𝓐 := 𝓐) G) (d : ℤ) where
  pairing : S.forget.sections Set.univ ≃ₗ[A] Dual A (S.forget.sections Set.univ)
  homogeneous : ∀ i j (m n : S.forget.sections Set.univ),
    (∀ x, m.val x∈(S.vertex x).piece i) → (∀ x, n.val x∈(S.vertex x).piece j) →
    pairing m n∈𝓐 (i+j-d)
  left_orthogonal : ∀ (x : V) (m n : S.forget.sections Set.univ),
    (∀ y, y≠x → m.val y=0) → n.val x=0 → pairing m n=0
  right_orthogonal : ∀ (x : V) (m n : S.forget.sections Set.univ),
    m.val x=0 → (∀ y, y≠x → n.val y=0) → pairing m n=0

 def PerfectPairing.pullback {S T : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : PerfectPairing T d) (j : Iso S T) : PerfectPairing S d where
  pairing := (j.toIso.sections Set.univ).trans
    (p.pairing.trans (j.toIso.sections Set.univ).dualMap)
  homogeneous i q m n hm hn := p.homogeneous i q _ _
    (fun x => j.vertex_graded x i _ (hm x)) (fun x => j.vertex_graded x q _ (hn x))
  left_orthogonal x m n hm hn := by
    apply p.left_orthogonal x
    · intro y hy
      change j.vertex y (m.val y)=0
      rw [hm y hy,map_zero]
    · change j.vertex x (n.val x)=0
      rw [hn,map_zero]
  right_orthogonal x m n hm hn := by
    apply p.right_orthogonal x
    · change j.vertex x (m.val x)=0
      rw [hm,map_zero]
    · intro y hy
      change j.vertex y (n.val y)=0
      rw [hn y hy,map_zero]

 variable {B : Type ua} [CommRing B] [Algebra k B] {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)

 def PerfectPairing.coefficientChange {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : PerfectPairing S d) : PerfectPairing (coefficientChange e he S) d where
  pairing := (coefficientChangeSections e he S Set.univ).symm.trans
    ((CoefficientChange.pairingEquiv e p.pairing).trans
      (coefficientChangeSections e he S Set.univ).symm.dualMap)
  homogeneous i j m n hm hn := by
    apply (he (i+j-d) _).mp
    exact p.homogeneous i j _ _
      (fun x => (ModuleData.mem_changePiece e (S.vertex x) i (m.val x)).mp (hm x))
      (fun x => (ModuleData.mem_changePiece e (S.vertex x) j (n.val x)).mp (hn x))
  left_orthogonal x m n hm hn := by
    change e (p.pairing _ _)=0
    apply (congrArg e ?_).trans (map_zero e)
    apply p.left_orthogonal x
    · intro y hy
      exact congrArg (fun v : CoefficientChange e (S.vertex y) => v.val) (hm y hy)
    · exact congrArg (fun v : CoefficientChange e (S.vertex x) => v.val) hn
  right_orthogonal x m n hm hn := by
    change e (p.pairing _ _)=0
    apply (congrArg e ?_).trans (map_zero e)
    apply p.right_orthogonal x
    · exact congrArg (fun v : CoefficientChange e (S.vertex x) => v.val) hm
    · intro y hy
      exact congrArg (fun v : CoefficientChange e (S.vertex y) => v.val) (hn y hy)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section


end

end OAI
