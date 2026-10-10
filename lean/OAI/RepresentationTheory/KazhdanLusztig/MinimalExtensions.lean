import OAI.RepresentationTheory.KazhdanLusztig.HilbertSeries
import OAI.RepresentationTheory.KazhdanLusztig.Comparison

namespace OAI

/-!
Minimal-boundary extension sheaves, graded splittings and sheaf decomposition.
-/

section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded _root_.OAI.KLInvariance.Hilbert
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)

/-- The actual lower restriction, with its source explicitly identified. -/
def lowerAt (x : V) (e : Sheaf.Outgoing (G := G) x) :
    ModuleData.Hom (B.vertex x) (B.edge e.val) := by
  rcases e with ⟨e,rfl⟩
  exact B.lower e

 theorem lowerAt_map (x : V) (e : Sheaf.Outgoing (G := G) x) (v : B.vertex x) :
    (B.lowerAt x e).map v = B.forget.stalkMap x v e := by
  rcases e with ⟨e,rfl⟩
  rfl

/-- The same kernel, typed in the graded stalk so base-field instances are explicit. -/
def upwardSubmodule (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) :
    Submodule A (B.vertex x) := B.forget.upwardKernel x F

 theorem upwardKernel_homogeneous (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) :
    ∀ n v, v ∈ B.upwardSubmodule x F →
      component (B.vertex x).piece n v ∈ B.upwardSubmodule x F := by
  intro n v hv e he
  rw [← B.lowerAt_map]
  rw [← (B.lowerAt x e).component]
  rw [B.lowerAt_map,hv e he]
  exact map_zero (component (B.edge e.val).piece n)

noncomputable def upwardKernel [IsNoetherianRing A]
    (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.sub (B.vertex x) (B.upwardSubmodule x F) (B.upwardKernel_homogeneous x F)

 theorem upwardKernel_insert (x : V) (F : Set (Sheaf.Outgoing (G := G) x))
    (e : Sheaf.Outgoing (G := G) x) :
    B.upwardSubmodule x (insert e F) =
      B.upwardSubmodule x F ⊓ LinearMap.ker (B.lowerAt x e).map := by
  ext v
  change (∀ a ∈ insert e F, B.forget.stalkMap x v a = 0) ↔
    (∀ a ∈ F, B.forget.stalkMap x v a = 0) ∧ (B.lowerAt x e).map v = 0
  rw [B.lowerAt_map]
  simp only [Set.mem_insert_iff,forall_eq_or_imp]
  exact and_comm


 theorem hilbert_edge_increment
    (x : V) (F : Set (Sheaf.Outgoing (G := G) x))
    (e : Sheaf.Outgoing (G := G) x)
    [∀ n, Module.Finite k ((B.vertex x).piece n)]
    {q : ℝ} (hq : 0 < q)
    (hs : Summable (term (B.vertex x).piece
      ((B.upwardSubmodule x F).restrictScalars k) q)) :
    value (B.vertex x).piece ((B.upwardSubmodule x F).restrictScalars k) q =
      value (B.vertex x).piece
        ((B.upwardSubmodule x (insert e F)).restrictScalars k) q +
      value (B.edge e.val).piece
        (((B.upwardSubmodule x F).map (B.lowerAt x e).map).restrictScalars k) q := by
  rw [B.upwardKernel_insert]
  exact value_image_exact (B.vertex x).piece (B.edge e.val).piece
    (B.upwardSubmodule x F) (B.upwardKernel_homogeneous x F)
    (B.lowerAt x e).map (B.lowerAt x e).graded hq hs

end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Graded uniqueness/recognition for the genuinely constructed minimal
boundary covers. Character and self-duality are not included in this data. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} [Fintype V] [Fintype E]
  (B : GradedSheaf (𝓐 := 𝓐) G)

noncomputable def stalkHom (x : V) : ModuleData.Hom (B.vertex x) (B.boundary x) where
  map := B.forget.stalkMap x
  graded := by
    intro n v hv e _
    change B.forget.stalkMap x v e ∈ (B.edge e.val).piece n
    rw [← B.lowerAt_map]
    exact (B.lowerAt x e).graded n v hv

end KLInvariance.MomentGraph.GradedSheaf

namespace KLInvariance.MomentGraph.Sheaf.AboveIso
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  [Fintype E] [IsNoetherianRing A] [IsDomain A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {B C : GradedSheaf (𝓐 := 𝓐) G} {x : V}
  (j : AboveIso B.forget C.forget x)

include hneg hzero in
 theorem extend_stalk_graded
    (hj : ∀ e (h : x < G.target e) n v, v ∈ (B.edge e).piece n →
      j.edge e h v ∈ (C.edge e).piece n)
    (hBfree : Module.Free A (B.vertex x)) (hCfree : Module.Free A (C.vertex x))
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hBmin : B.KernelMinimal x) (hCmin : C.KernelMinimal x) :
    ∃ e : B.vertex x ≃ₗ[A] C.vertex x,
      (∀ n v, v ∈ (B.vertex x).piece n → e v ∈ (C.vertex x).piece n) ∧
      ∀ v, j.boundary (B.forget.stalkMap x v) = C.forget.stalkMap x (e v) := by
  let T := ModuleData.range (C.stalkHom x)
  let f : ModuleData.Hom (B.vertex x) T :=
    { map := LinearMap.codRestrict (LinearMap.range (C.forget.stalkMap x))
        (j.boundary.toLinearMap.comp (B.forget.stalkMap x)) (by
          intro v
          rw [← j.map_stalk_image hBf hBg hCf hCg]
          exact ⟨B.forget.stalkMap x v,⟨v,rfl⟩,rfl⟩)
      graded := by
        intro n v hv e _
        exact hj e.val _ n _ ((B.stalkHom x).graded n v hv e (Set.mem_univ e)) }
  let g : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hfs : Function.Surjective f.map := by
    intro v
    have hv : v.val ∈ (LinearMap.range (B.forget.stalkMap x)).map j.boundary.toLinearMap := by
      rw [j.map_stalk_image hBf hBg hCf hCg]
      exact v.property
    obtain ⟨w,⟨z,rfl⟩,hz⟩ := hv
    exact ⟨z,Subtype.ext hz⟩
  have hgs : Function.Surjective g.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  have hfm : LinearMap.ker f.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x)) := by
    intro v hv
    apply (B.kernelMinimal_iff x).mp hBmin
    apply LinearMap.mem_ker.mpr
    apply j.boundary.injective
    rw [map_zero]
    have hh : f.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  have hgm : LinearMap.ker g.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (C.vertex x)) := by
    intro v hv
    apply (C.kernelMinimal_iff x).mp hCmin
    have hh : g.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  let F : ModuleData.MinimalCover T := ⟨B.vertex x,hBfree,f,hfs,hfm⟩
  let D : ModuleData.MinimalCover T := ⟨C.vertex x,hCfree,g,hgs,hgm⟩
  obtain ⟨e,he,hef⟩ := ModuleData.MinimalCover.equiv hneg hzero F D
  refine ⟨e,he,?_⟩
  intro v
  exact (congrArg Subtype.val (LinearMap.congr_fun hef v)).symm

end KLInvariance.MomentGraph.Sheaf.AboveIso

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

def equivOfEq {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) : M ≃ₗ[A] N :=
  h ▸ LinearEquiv.refl A M

 theorem equivOfEq_graded {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N)
    (n : ℤ) (v : M) (hv : v ∈ M.piece n) : equivOfEq h v ∈ N.piece n := by
  subst N
  exact hv

 theorem quotient_iso_graded {M N E F : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M E) (g : Hom N F) (hf : Function.Surjective f.map)
    (hg : Function.Surjective g.map) (e : M ≃ₗ[A] N)
    (he : ∀ n v, v ∈ M.piece n → e v ∈ N.piece n)
    (hk : (LinearMap.ker f.map).map e.toLinearMap = LinearMap.ker g.map)
    (n : ℤ) (v : E) (hv : v ∈ E.piece n) :
    QuotientEdge.iso f.map g.map hf hg e hk v ∈ F.piece n := by
  obtain ⟨w,hw,rfl⟩ := f.homogeneous_preimage hf n v hv
  rw [QuotientEdge.iso_apply]
  exact g.graded n _ (he n w hw)

end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

structure Iso (B C : GradedSheaf (𝓐 := 𝓐) G) extends Sheaf.Iso B.forget C.forget where
  vertex_graded : ∀ x n v, v ∈ (B.vertex x).piece n → vertex x v ∈ (C.vertex x).piece n
  edge_graded : ∀ e n v, v ∈ (B.edge e).piece n → edge e v ∈ (C.edge e).piece n

structure OnIso (B C : GradedSheaf (𝓐 := 𝓐) G) (U : Set V)
    extends Sheaf.OnIso B.forget C.forget U where
  vertex_graded : ∀ x (hx : x ∈ U) n v,
    v ∈ (B.vertex x).piece n → vertex x hx v ∈ (C.vertex x).piece n
  edge_graded : ∀ e (he : G.target e ∈ U) n v,
    v ∈ (B.edge e).piece n → edge e he v ∈ (C.edge e).piece n

namespace OnIso
variable {B C : GradedSheaf (𝓐 := 𝓐) G} {U : Set V} (j : OnIso B C U)

 def ofUniv (j : OnIso B C Set.univ) : Iso B C where
  toIso := j.toOnIso.ofUniv
  vertex_graded x := j.vertex_graded x (Set.mem_univ x)
  edge_graded e := j.edge_graded e (Set.mem_univ _)

noncomputable def extend (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : B.vertex x ≃ₗ[A] C.vertex x)
    (hjv : ∀ n v, v ∈ (B.vertex x).piece n → jv v ∈ (C.vertex x).piece n)
    (hout : ∀ e (he : G.source e = x) v,
      j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.forget.lower e v) = C.forget.lower e (Sheaf.castStalkIso B.forget C.forget he.symm jv v)) :
    OnIso B C (insert x U) := by
  classical
  let p := j.toOnIso.extend hU x hx hmax α hBq hCq jv hout
  have hvp : ∀ y (hy : y ∈ insert x U) n v,
      v ∈ (B.vertex y).piece n → p.vertex y hy v ∈ (C.vertex y).piece n := by
    intro y hy n v hv
    dsimp only [p,Sheaf.OnIso.extend]
    split_ifs with h
    · subst y
      exact hjv n v hv
    · exact j.vertex_graded y _ n v hv
  refine ⟨p,hvp,?_⟩
  intro e he n v hv
  dsimp only [p,Sheaf.OnIso.extend]
  split_ifs with h
  · apply ModuleData.quotient_iso_graded (B.upper e) (C.upper e) (hBq e).1 (hCq e).1
    · subst x
      exact hjv
    · exact hv
  · exact j.edge_graded e _ n v hv

end OnIso
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}

 def zero : Sheaf.{u,v,w,z} (R := R) G where
  vertex _ := ModuleCat.of R PUnit.{z+1}
  edge _ := ModuleCat.of R PUnit.{z+1}
  lower _ := 0
  upper _ := 0

 def prod (B C : Sheaf.{u,v,w,z} (R := R) G) : Sheaf.{u,v,w,z} (R := R) G where
  vertex x := ModuleCat.of R (B.vertex x × C.vertex x)
  edge e := ModuleCat.of R (B.edge e × C.edge e)
  lower e := (B.lower e).prodMap (C.lower e)
  upper e := (B.upper e).prodMap (C.upper e)

lemma prod_generated (B C : Sheaf.{u,v,w,z} (R := R) G)
    (hB : B.Generated) (hC : C.Generated) : (prod B C).Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hB x v.1
  obtain ⟨g,hg,hgx⟩ := hC x v.2
  exact ⟨fun y => (f y,g y),fun e hs ht => Prod.ext (hf e hs ht) (hg e hs ht),Prod.ext hfx hgx⟩

lemma prod_flabby (B C : Sheaf.{u,v,w,z} (R := R) G)
    (hB : B.Flabby) (hC : C.Flabby) : (prod B C).Flabby := by
  intro U hU f hf
  obtain ⟨g,hg,hgf⟩ := hB U hU (fun y => (f y).1) (fun e hs ht => congrArg Prod.fst (hf e hs ht))
  obtain ⟨t,ht,htf⟩ := hC U hU (fun y => (f y).2) (fun e hs htt => congrArg Prod.snd (hf e hs htt))
  exact ⟨fun y => (g y,t y),fun e hs htt => Prod.ext (hg e hs htt) (ht e hs htt),
    fun y hy => Prod.ext (hgf y hy) (htf y hy)⟩

lemma prod_upperQuotient (B C : Sheaf.{u,v,w,z} (R := R) G) (α : E → R)
    (hB : B.UpperQuotient α) (hC : C.UpperQuotient α) : (prod B C).UpperQuotient α := by
  intro e
  refine ⟨?_,?_⟩
  · intro v
    obtain ⟨b,hb⟩ := (hB e).1 v.1
    obtain ⟨c,hc⟩ := (hC e).1 v.2
    exact ⟨(b,c),Prod.ext hb hc⟩
  · intro v
    constructor
    · intro h
      obtain ⟨b,hb⟩ := (hB e).2 v.1 |>.mp (congrArg Prod.fst h)
      obtain ⟨c,hc⟩ := (hC e).2 v.2 |>.mp (congrArg Prod.snd h)
      exact ⟨(b,c),Prod.ext hb hc⟩
    · rintro ⟨⟨b,c⟩,rfl⟩
      exact Prod.ext ((hB e).2 _ |>.mpr ⟨b,rfl⟩) ((hC e).2 _ |>.mpr ⟨c,rfl⟩)

lemma pi_upperQuotient {ι : Type*} (B : ι → Sheaf.{u,v,w,z} (R := R) G) (α : E → R)
    (hB : ∀ i, (B i).UpperQuotient α) : (pi B).UpperQuotient α := by
  classical
  intro e
  refine ⟨?_,?_⟩
  · intro v
    choose b hb using fun i => (hB i e).1 (v i)
    exact ⟨b,funext hb⟩
  · intro v
    constructor
    · intro h
      choose b hb using fun i => (hB i e).2 (v i) |>.mp (congrFun h i)
      exact ⟨b,funext hb⟩
    · rintro ⟨b,rfl⟩
      funext i
      exact (hB i e).2 _ |>.mpr ⟨b i,rfl⟩

lemma prod_kernel_iff (B C : Sheaf.{u,v,w,z} (R := R) G) (x : V) (v : (prod B C).vertex x) :
    v ∈ LinearMap.ker ((prod B C).stalkMap x) ↔
      v.1 ∈ LinearMap.ker (B.stalkMap x) ∧ v.2 ∈ LinearMap.ker (C.stalkMap x) := by
  constructor
  · intro h
    constructor <;> apply LinearMap.mem_ker.mpr <;> funext e
    · rcases e with ⟨e,he⟩
      subst x
      exact congrArg Prod.fst (congrFun (LinearMap.mem_ker.mp h) ⟨e,rfl⟩)
    · rcases e with ⟨e,he⟩
      subst x
      exact congrArg Prod.snd (congrFun (LinearMap.mem_ker.mp h) ⟨e,rfl⟩)
  · rintro ⟨hB,hC⟩
    apply LinearMap.mem_ker.mpr
    funext e
    rcases e with ⟨e,he⟩
    subst x
    exact Prod.ext (congrFun (LinearMap.mem_ker.mp hB) ⟨e,rfl⟩)
      (congrFun (LinearMap.mem_ker.mp hC) ⟨e,rfl⟩)

lemma prod_minimal (B C : Sheaf.{u,v,w,z} (R := R) G) (x : V) (I : Ideal R)
    (hB : LinearMap.ker (B.stalkMap x) ≤ I • (⊤ : Submodule R (B.vertex x)))
    (hC : LinearMap.ker (C.stalkMap x) ≤ I • (⊤ : Submodule R (C.vertex x))) :
    LinearMap.ker ((prod B C).stalkMap x) ≤ I • (⊤ : Submodule R ((prod B C).vertex x)) := by
  intro v hv
  obtain ⟨hvB,hvC⟩ := (prod_kernel_iff B C x v).mp hv
  have h (M N : Type z) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
      (f : M →ₗ[R] N) : (I • (⊤ : Submodule R M)).map f ≤ I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hb := h _ _ (LinearMap.inl R (B.vertex x) (C.vertex x)) ⟨v.1,hB hvB,rfl⟩
  have hc := h _ _ (LinearMap.inr R (B.vertex x) (C.vertex x)) ⟨v.2,hC hvC,rfl⟩
  have heq : (v.1,0) + (0,v.2) = v := Prod.ext (add_zero _) (zero_add _)
  have hh := (I • (⊤ : Submodule R ((prod B C).vertex x))).add_mem hb hc
  change (v.1,0) + (0,v.2) ∈ I • (⊤ : Submodule R ((prod B C).vertex x)) at hh
  exact heq ▸ hh

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  {B C : Sheaf.{u,v,w,z} (R := R) G} (D : Sheaf.{u,v,w,z} (R := R) G)

noncomputable def addZeroRight (M N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton N] : M ≃ₗ[R] M × N where
  toFun m := (m,0)
  invFun := Prod.fst
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  map_add' _ _ := Prod.ext rfl (zero_add _).symm
  map_smul' _ _ := Prod.ext rfl (smul_zero _).symm

@[simp] lemma addZeroRight_apply (M N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton N] (m : M) :
    addZeroRight (R := R) M N m = (m,0) := rfl

noncomputable def OnIso.prodZero {U : Set V} (j : OnIso B C U)
    (hV : ∀ x ∈ U, Subsingleton (D.vertex x))
    (hE : ∀ e, G.target e ∈ U → Subsingleton (D.edge e)) : OnIso B (prod C D) U where
  vertex x hx := by
    letI := hV x hx
    exact (j.vertex x hx).trans (addZeroRight _ _)
  edge e he := by
    letI := hE e he
    exact (j.edge e he).trans (addZeroRight _ _)
  lower e hs ht v := by
    apply Prod.ext
    · exact j.lower e hs ht v
    · exact (D.lower e).map_zero.symm
  upper e ht v := by
    apply Prod.ext
    · exact j.upper e ht v
    · exact (D.upper e).map_zero.symm

lemma pi_subsingleton_vertex {ι : Type*} (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (x : V) (h : ∀ i, Subsingleton ((B i).vertex x)) : Subsingleton ((pi B).vertex x) := by
  exact ⟨fun f g => funext (fun i => @Subsingleton.elim _ (h i) (f i) (g i))⟩

lemma pi_subsingleton_edge {ι : Type*} (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (e : E) (h : ∀ i, Subsingleton ((B i).edge e)) : Subsingleton ((pi B).edge e) := by
  exact ⟨fun f g => funext (fun i => @Subsingleton.elim _ (h i) (f i) (g i))⟩

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
noncomputable section
 def zero : ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A PUnit.{max ua um+1}
  kModule := inferInstance
  tower := inferInstance
  piece _ := ⊥
  decomposition := (show DirectSum.IsInternal (fun _ : ℤ => (⊥ : Submodule k PUnit.{max ua um+1})) from by
    apply internal_of_components _ (fun _ => 0)
    · intro _ _; exact Submodule.zero_mem _
    · intro _ _ _; exact Subsingleton.elim _ _
    · intro _ _ _ _ _; rfl
    · intro m; exact ⟨∅,Subsingleton.elim _ _⟩).chooseDecomposition
  graded := ⟨by intro _ _ _ _ _ _; exact Subsingleton.elim _ _⟩
  nonneg _ _ := rfl
  finite := inferInstance

 def Hom.zero (M N : ModuleData.{uk,ua,um} 𝓐) : Hom M N :=
  ⟨0,fun _ _ _ => Submodule.zero_mem _⟩

 def Hom.pi {ι : Type um} [Fintype ι] {M N : ι → ModuleData.{uk,ua,um} 𝓐}
    (f : ∀ i, Hom (M i) (N i)) : Hom (ModuleData.pi M) (ModuleData.pi N) where
  map := LinearMap.pi fun i => (f i).map.comp (LinearMap.proj i)
  graded n _ hm i hi := (f i).graded n _ (hm i hi)
end
end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section
 def shift (B : GradedSheaf (𝓐 := 𝓐) G) (d : ℕ) : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := (B.vertex x).shift d
  edge e := (B.edge e).shift d
  lower e := (B.lower e).shift d
  upper e := (B.upper e).shift d

 def zero : GradedSheaf (𝓐 := 𝓐) G where
  vertex _ := ModuleData.zero
  edge _ := ModuleData.zero
  lower _ := ModuleData.Hom.zero _ _
  upper _ := ModuleData.Hom.zero _ _

 def prod (B C : GradedSheaf (𝓐 := 𝓐) G) : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := (B.vertex x).prod (C.vertex x)
  edge e := (B.edge e).prod (C.edge e)
  lower e := (B.lower e).prodMap (C.lower e)
  upper e := (B.upper e).prodMap (C.upper e)

 def pi {ι : Type um} [Fintype ι] (B : ι → GradedSheaf (𝓐 := 𝓐) G) :
    GradedSheaf (𝓐 := 𝓐) G where
  vertex x := ModuleData.pi (fun i => (B i).vertex x)
  edge e := ModuleData.pi (fun i => (B i).edge e)
  lower e := ModuleData.Hom.pi (fun i => (B i).lower e)
  upper e := ModuleData.Hom.pi (fun i => (B i).upper e)

 def OnIso.prodZero {B C : GradedSheaf (𝓐 := 𝓐) G} {U : Set V} (j : OnIso B C U)
    (D : GradedSheaf (𝓐 := 𝓐) G)
    (hV : ∀ x ∈ U, Subsingleton (D.vertex x))
    (hE : ∀ e, G.target e ∈ U → Subsingleton (D.edge e)) : OnIso B (prod C D) U where
  toOnIso := j.toOnIso.prodZero D.forget hV hE
  vertex_graded x hx n v hv := ⟨j.vertex_graded x hx n v hv,Submodule.zero_mem _⟩
  edge_graded e he n v hv := ⟨j.edge_graded e he n v hv,Submodule.zero_mem _⟩

 theorem shift_forget (B : GradedSheaf (𝓐 := 𝓐) G) (d : ℕ) :
    (B.shift d).forget=B.forget := rfl
 theorem zero_forget : (zero (𝓐 := 𝓐) (G := G)).forget=Sheaf.zero := rfl
 theorem prod_forget (B C : GradedSheaf (𝓐 := 𝓐) G) :
    (prod B C).forget=Sheaf.prod B.forget C.forget := rfl
 theorem pi_forget {ι : Type um} [Fintype ι] (B : ι → GradedSheaf (𝓐 := 𝓐) G) :
    (pi B).forget=Sheaf.pi (fun i => (B i).forget) := rfl
end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Extension by zero from a full lower ideal. Proof-indexed finite products
avoid informal identifications of the integral stalks at boundary vertices. -/
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  (G : OrderedGraph V E) (K : Set V) (hK : IsLowerSet K)

 def lowerGraph : OrderedGraph K {e : E // G.target e ∈ K} where
  source e := ⟨G.source e.val,hK (G.increasing e.val).le e.property⟩
  target e := ⟨G.target e.val,e.property⟩
  increasing e := G.increasing e.val

namespace GradedSheaf
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Witness (p : Prop) := ULift.{um} (PLift p)

variable {G K hK} (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))

 def lowerExtend : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := ModuleData.pi (fun h : Witness.{um} (x ∈ K) => B.vertex ⟨x,h.down.down⟩)
  edge e := ModuleData.pi (fun h : Witness.{um} (G.target e ∈ K) => B.edge ⟨e,h.down.down⟩)
  lower e :=
    { map := LinearMap.pi (fun h => (B.lower ⟨e,h.down.down⟩).map.comp
        (LinearMap.proj ⟨⟨hK (G.increasing e).le h.down.down⟩⟩))
      graded n _v hv h _ := (B.lower ⟨e,h.down.down⟩).graded n _ (hv _ (Set.mem_univ _)) }
  upper e :=
    { map := LinearMap.pi (fun h => (B.upper ⟨e,h.down.down⟩).map.comp (LinearMap.proj h))
      graded n _v hv h _ := (B.upper ⟨e,h.down.down⟩).graded n _ (hv _ (Set.mem_univ _)) }

 def lowerExtendVertex (x : K) : (B.lowerExtend.vertex x.val) ≃ₗ[A] B.vertex x where
  toFun f := f ⟨⟨x.property⟩⟩
  invFun v _ := v
  left_inv f := by
    funext h
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem lowerExtendVertex_graded (x : K) (n : ℤ) (v : B.lowerExtend.vertex x.val)
    (hv : v ∈ (B.lowerExtend.vertex x.val).piece n) :
    B.lowerExtendVertex x v ∈ (B.vertex x).piece n := hv _ (Set.mem_univ _)

 theorem lowerExtend_support (x : V) (hx : x ∉ K) : Subsingleton (B.lowerExtend.vertex x) :=
  ⟨fun _f _g => funext (fun h => (hx h.down.down).elim)⟩

 theorem lowerExtend_free (hb : ∀ x, Module.Free A (B.vertex x)) (x : V) :
    Module.Free A (B.lowerExtend.vertex x) := by
  let : ∀ h : Witness.{um} (x ∈ K), Module.Free A (B.vertex ⟨x,h.down.down⟩) := fun h => hb _
  change Module.Free A (∀ h : Witness.{um} (x ∈ K), B.vertex ⟨x,h.down.down⟩)
  infer_instance

 def liftLowerAssignment (f : B.forget.Assignment) : B.lowerExtend.forget.Assignment :=
  fun x h => f ⟨x,h.down.down⟩

 def projectLowerAssignment (f : B.lowerExtend.forget.Assignment) : B.forget.Assignment :=
  fun x => f x.val ⟨⟨x.property⟩⟩

 theorem projectLower_compatible {U : Set V} {f : B.lowerExtend.forget.Assignment}
    (hf : B.lowerExtend.forget.CompatibleOn U f) :
    B.forget.CompatibleOn (Subtype.val ⁻¹' U) (B.projectLowerAssignment f) := by
  intro e hs ht
  exact congrFun (hf e.val hs ht) ⟨⟨e.property⟩⟩

 theorem liftLower_compatible {U : Set V} {f : B.forget.Assignment}
    (hf : B.forget.CompatibleOn (Subtype.val ⁻¹' U) f) :
    B.lowerExtend.forget.CompatibleOn U (B.liftLowerAssignment f) := by
  intro e hs ht
  funext h
  exact hf ⟨e,h.down.down⟩ hs ht

 theorem lowerExtend_generated (hb : B.forget.Generated) : B.lowerExtend.forget.Generated := by
  intro x v
  by_cases hx : x ∈ K
  · obtain ⟨f,hf,hfx⟩ := hb ⟨x,hx⟩ (v ⟨⟨hx⟩⟩)
    refine ⟨B.liftLowerAssignment f,B.liftLower_compatible hf,?_⟩
    funext h
    exact hfx
  · let : Subsingleton (B.lowerExtend.forget.vertex x) := B.lowerExtend_support x hx
    exact ⟨0,fun _ _ _ => by simp,Subsingleton.elim _ _⟩

 theorem lowerExtend_flabby (hb : B.forget.Flabby) : B.lowerExtend.forget.Flabby := by
  intro U hU f hf
  have hu : IsUpperSet (Subtype.val ⁻¹' U : Set K) := fun _ _ hab ha => hU hab ha
  obtain ⟨g,hg,hgf⟩ := hb (Subtype.val ⁻¹' U) hu (B.projectLowerAssignment f) (B.projectLower_compatible hf)
  refine ⟨B.liftLowerAssignment g,B.liftLower_compatible hg,?_⟩
  intro x hx
  funext h
  exact hgf ⟨x,h.down.down⟩ hx

 theorem lowerExtend_quotient (α : E → A)
    (hb : B.UpperQuotient (fun e => α e.val)) : B.lowerExtend.UpperQuotient α := by
  intro e
  constructor
  · intro v
    have hh : ∀ h : Witness.{um} (G.target e ∈ K), ∃ w, (B.upper ⟨e,h.down.down⟩).map w=v h :=
      fun h => (hb ⟨e,h.down.down⟩).1 (v h)
    choose w hw using hh
    exact ⟨w,funext hw⟩
  · intro v
    constructor
    · intro hv
      have hh : ∀ h : Witness.{um} (G.target e ∈ K), ∃ w, v h=α e • w :=
        fun h => (hb ⟨e,h.down.down⟩).2 (v h) |>.mp (congrFun hv h)
      choose w hw using hh
      exact ⟨w,funext hw⟩
    · rintro ⟨w,rfl⟩
      funext h
      exact (hb ⟨e,h.down.down⟩).2 _ |>.mpr ⟨w h,rfl⟩

 theorem lowerExtend_minimal (x : V)
    (hb : ∀ hx : x ∈ K, B.KernelMinimal ⟨x,hx⟩) : B.lowerExtend.KernelMinimal x := by
  intro f hf
  apply LocalCover.pi_mem_ideal_smul
  intro h
  apply hb h.down.down (B.projectLowerAssignment f)
  intro e he
  have hes : G.source e.val=x := congrArg Subtype.val he
  exact congrFun (hf e.val hes) ⟨⟨e.property⟩⟩

end
end GradedSheaf
end KLInvariance.MomentGraph

end


section

/-! Finite sums of honest shifted normalized boundary models. A model family
is data for the decomposition lemma, not an assumption of the KL main. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}

instance zeroVertex_subsingleton (x : V) : Subsingleton ((zero (𝓐 := 𝓐) (G := G)).vertex x) :=
  inferInstanceAs (Subsingleton PUnit.{max ua um+1})
instance zeroEdge_subsingleton (e : E) : Subsingleton ((zero (𝓐 := 𝓐) (G := G)).edge e) :=
  inferInstanceAs (Subsingleton PUnit.{max ua um+1})

structure BoundaryModels (α : E → A) where
  sheaf : V → GradedSheaf (𝓐 := 𝓐) G
  free : ∀ c x, Module.Free A ((sheaf c).vertex x)
  quotient : ∀ c, (sheaf c).UpperQuotient α
  generated : ∀ c, (sheaf c).forget.Generated
  flabby : ∀ c, (sheaf c).forget.Flabby
  support : ∀ c x, ¬x ≤ c → Subsingleton ((sheaf c).vertex x)
  top : ∀ c, (sheaf c).vertex c ≃ₗ[A] ModuleData.unit.{uk,ua,um} hneg
  top_graded : ∀ c n v, v ∈ ((sheaf c).vertex c).piece n → top c v ∈ (ModuleData.unit.{uk,ua,um} hneg).piece n
  minimal : ∀ c x, x ≠ c → (sheaf c).KernelMinimal x

inductive ModelSum (O : V → GradedSheaf (𝓐 := 𝓐) G) (U : Set V) :
    GradedSheaf (𝓐 := 𝓐) G → Prop where
  | zero : ModelSum O U zero
  | add {B} : ModelSum O U B → ∀ c ∈ U, ∀ (n : ℕ) (d : ULift.{um} (Fin n) → ℕ),
      ModelSum O U (prod B (pi (fun i => (O c).shift (d i))))

namespace ModelSum
variable {hneg} {α : E → A} (O : BoundaryModels hneg (G := G) α)
  {U : Set V} {B : GradedSheaf (𝓐 := 𝓐) G}

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] in
lemma mono {O : V → GradedSheaf (𝓐 := 𝓐) G} (h : ModelSum O U B)
    {T : Set V} (hUT : U ⊆ T) : ModelSum O T B := by
  induction h with
  | zero => exact .zero
  | add _ c hc n d ih => exact .add ih c (hUT hc) n d

lemma free (h : ModelSum O.sheaf U B) (x : V) : Module.Free A (B.vertex x) := by
  induction h with
  | zero => exact inferInstanceAs (Module.Free A PUnit.{max ua um+1})
  | @add C _ c _ n d ih =>
    let _ : Module.Free A (C.vertex x) := ih
    let _ := O.free c x
    change Module.Free A (C.vertex x × (ULift.{um} (Fin n) → (O.sheaf c).vertex x))
    infer_instance

lemma quotient (h : ModelSum O.sheaf U B) : B.UpperQuotient α := by
  induction h with
  | zero =>
    intro e
    exact ⟨fun v => ⟨0,Subsingleton.elim _ _⟩,fun v => ⟨fun _ => ⟨0,Subsingleton.elim _ _⟩,fun _ => Subsingleton.elim _ _⟩⟩
  | @add C _ c _ n d ih =>
    exact Sheaf.prod_upperQuotient C.forget (Sheaf.pi (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget)) α ih
      (Sheaf.pi_upperQuotient (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget) α (fun _ => O.quotient c))

lemma generated (h : ModelSum O.sheaf U B) : B.forget.Generated := by
  induction h with
  | zero =>
    intro x v
    let : Subsingleton ((GradedSheaf.zero (𝓐 := 𝓐) (G := G)).forget.vertex x) := zeroVertex_subsingleton (𝓐 := 𝓐) (G := G) x
    exact ⟨0,fun _ _ _ => rfl,Subsingleton.elim _ _⟩
  | add _ c _ n d ih => exact Sheaf.prod_generated _ _ ih (Sheaf.pi_generated _ (fun _ => O.generated c))

lemma flabby (h : ModelSum O.sheaf U B) : B.forget.Flabby := by
  induction h with
  | zero => exact fun U _ f _ => ⟨f,fun _ _ _ => rfl,fun _ _ => rfl⟩
  | add _ c _ n d ih => exact Sheaf.prod_flabby _ _ ih (Sheaf.pi_flabby _ (fun _ => O.flabby c))

lemma minimal (h : ModelSum O.sheaf U B) (x : V) (hx : x ∉ U) : B.KernelMinimal x := by
  induction h with
  | zero =>
    apply (GradedSheaf.zero.kernelMinimal_iff x).mpr
    intro v _
    let : Subsingleton ((GradedSheaf.zero (𝓐 := 𝓐) (G := G)).forget.vertex x) := zeroVertex_subsingleton (𝓐 := 𝓐) (G := G) x
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _
  | @add C _ c hc n d ih =>
    apply ((prod C (pi (fun i => (O.sheaf c).shift (d i)))).kernelMinimal_iff x).mpr
    exact Sheaf.prod_minimal C.forget (Sheaf.pi (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget)) x _ ((C.kernelMinimal_iff x).mp ih)
      (Sheaf.pi_minimal (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget) x _ (fun _ =>
        ((O.sheaf c).kernelMinimal_iff x).mp (O.minimal c x (fun he => hx (he ▸ hc)))))

end ModelSum
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Actual normalized BMP models at every vertex of a finite ordered graph,
constructed on its lower ideal and extended by zero. -/
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  (G : OrderedGraph V E) (α : E → A) (hα : ∀ e, α e ∈ 𝓐 1)
noncomputable section
attribute [local instance] Classical.propDecidable

 def lowerBoundary (c : V) : BoundarySheaf hneg (lowerGraph G (Set.Iic c) (isLowerSet_Iic c))
    (fun e => α e.val) ⟨c,le_rfl⟩ :=
  (exists_boundarySheaf hneg (lowerGraph G (Set.Iic c) (isLowerSet_Iic c)) hscalar
    ⟨c,le_rfl⟩ (fun x => x.property) (fun e => α e.val) (fun e => hα e.val)).some

 def actualBoundaryModels : GradedSheaf.BoundaryModels hneg (G := G) α where
  sheaf c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend
  free c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_free
    (lowerBoundary hneg hscalar G α hα c).free
  quotient c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_quotient α
    (lowerBoundary hneg hscalar G α hα c).quotient
  generated c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_generated
    (lowerBoundary hneg hscalar G α hα c).generated
  flabby c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_flabby
    (lowerBoundary hneg hscalar G α hα c).flabby.flabby
  support c x hx := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_support x hx
  top c := ((lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtendVertex ⟨c,le_rfl⟩).trans
    (ModuleData.equivOfEq (lowerBoundary hneg hscalar G α hα c).top)
  top_graded c n v hv := ModuleData.equivOfEq_graded
    (lowerBoundary hneg hscalar G α hα c).top n _
    ((lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtendVertex_graded ⟨c,le_rfl⟩ n v hv)
  minimal c x hx := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_minimal x
    (fun hxc => (lowerBoundary hneg hscalar G α hα c).minimal ⟨x,hxc⟩
      (fun hh => hx (congrArg Subtype.val hh)))

end
end KLInvariance.MomentGraph

end


section

/-! Recognition of the actual finite minimal boundary sheaf. This proves
choice-independence of the constructed graded object, not its KL character. -/
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B C : BoundarySheaf hneg G α b) (hb : ∀ x, x ≤ b)

omit [Fintype V] in
include hzero hb in
 theorem extend_iso {U : Set V} (hU : IsUpperSet U)
    (j : GradedSheaf.OnIso B.sheaf C.sheaf U)
    (x : V) (hx : x ∉ U) (hmax : Set.Ioi x ⊆ U) :
    Nonempty (GradedSheaf.OnIso B.sheaf C.sheaf (insert x U)) := by
  classical
  by_cases hxb : x=b
  · subst x
    let eqv := ModuleData.equivOfEq (B.top.trans C.top.symm)
    have heqv := ModuleData.equivOfEq_graded (B.top.trans C.top.symm)
    refine ⟨j.extend hU b hx hmax α B.quotient C.quotient eqv heqv ?_⟩
    intro e he
    exact False.elim ((not_lt_of_ge (hb (G.target e))) (he ▸ G.increasing e))
  · let ja := j.toOnIso.above x hmax
    obtain ⟨e,he,hcomm⟩ := ja.extend_stalk_graded hneg hzero
      (fun e ht => j.edge_graded e (hmax ht)) (B.free x) (C.free x)
      B.flabby.flabby B.generated C.flabby.flabby C.generated
      (B.minimal x hxb) (C.minimal x hxb)
    refine ⟨j.extend hU x hx hmax α B.quotient C.quotient e he ?_⟩
    intro f hf v
    subst x
    exact congrFun (hcomm v) ⟨f,rfl⟩

include hzero hb in
 theorem exists_gradedIso : Nonempty (GradedSheaf.Iso B.sheaf C.sheaf) := by
  classical
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      GradedSheaf.OnIso B.sheaf C.sheaf ((s : Set V)ᶜ) →
      Nonempty (GradedSheaf.Iso B.sheaf C.sheaf) := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hU j
      by_cases hs : s=∅
      · subst s
        have heq : ((∅ : Finset V) : Set V)ᶜ=Set.univ := by simp
        exact ⟨GradedSheaf.OnIso.ofUniv (heq ▸ j)⟩
      · obtain ⟨x,hxs,hxmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
        have hx : x ∉ ((s : Set V)ᶜ) := by simpa using hxs
        have hmax : Set.Ioi x ⊆ ((s : Set V)ᶜ) := by
          intro y hy
          change y ∉ s
          intro hys
          exact (not_le_of_gt hy) (hxmax hys hy.le)
        obtain ⟨jj⟩ := B.extend_iso hzero C hb hU j x hx hmax
        have heq : insert x ((s : Set V)ᶜ) = ((s.erase x : Finset V) : Set V)ᶜ := by
          ext y
          simp only [Set.mem_insert_iff,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_erase]
          tauto
        have hU' : IsUpperSet (insert x ((s : Set V)ᶜ)) := by
          intro y t hyt hy
          rcases Set.mem_insert_iff.mp hy with hy | hy
          · subst y
            by_cases htx : t=x
            · exact Set.mem_insert_iff.mpr (Or.inl htx)
            · exact Set.mem_insert_of_mem x (hmax (lt_of_le_of_ne hyt (Ne.symm htx)))
          · exact Set.mem_insert_of_mem x (hU hyt hy)
        exact ih (s.erase x) (Finset.erase_ssubset hxs) (heq ▸ hU') (heq ▸ jj)
  have hset : ((Finset.univ : Finset V) : Set V)ᶜ = ∅ := by simp
  have hj : GradedSheaf.OnIso B.sheaf C.sheaf (∅ : Set V) := by
    refine { toOnIso := ?_, vertex_graded := ?_, edge_graded := ?_ }
    · exact ⟨fun x hx => False.elim hx, fun e he => False.elim he,
        fun e hs => False.elim hs, fun e ht => False.elim ht⟩
    · intro x hx; exact False.elim hx
    · intro e he; exact False.elim he
  have hh := h Finset.univ
  rw [hset] at hh
  exact hh isUpperSet_empty hj

end KLInvariance.MomentGraph.BoundarySheaf

end


section


namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

private def quotientLinear (e : E) : R →ₗ[R] R ⧸ Ideal.span {α e} :=
  (Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap

 def structureSheaf : Sheaf (R := R) G where
  vertex x := ModuleCat.of R (PLift (x ≤ c) → R)
  edge e := ModuleCat.of R (PLift (G.target e ≤ c) → R ⧸ Ideal.span {α e})
  upper e := LinearMap.pi (fun h => (quotientLinear α e).comp (LinearMap.proj h))
  lower e := LinearMap.pi (fun h => (quotientLinear α e).comp
    (LinearMap.proj ⟨(G.increasing e).le.trans h.down⟩))

 theorem structureSheaf_free (x : V) : Module.Free R ((structureSheaf G α c).vertex x) :=
  inferInstanceAs (Module.Free R (PLift (x ≤ c) → R))

 theorem structureSheaf_finite (x : V) : Module.Finite R ((structureSheaf G α c).vertex x) :=
  inferInstanceAs (Module.Finite R (PLift (x ≤ c) → R))

 theorem structureSheaf_support (x : V) (hx : ¬ x ≤ c) :
    Subsingleton ((structureSheaf G α c).vertex x) := by
  refine ⟨fun f g => funext fun h => False.elim (hx h.down)⟩

 def structureVertexIso (x : V) (hx : x ≤ c) :
    (structureSheaf G α c).vertex x ≃ₗ[R] R where
  toFun f := f ⟨hx⟩
  invFun r := fun _ => r
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem structureSheaf_generated : (structureSheaf G α c).Generated := by
  classical
  intro x v
  by_cases hx : x ≤ c
  · refine ⟨fun _ _ => v ⟨hx⟩, fun _ _ _ => rfl, rfl⟩
  · let _ := structureSheaf_support G α c x hx
    exact ⟨0,fun _ _ _ => rfl,Subsingleton.elim _ _⟩

 theorem structureSheaf_upperQuotient : (structureSheaf G α c).UpperQuotient α := by
  classical
  intro e
  refine ⟨?_,?_⟩
  · intro v
    choose r hr using fun h : PLift (G.target e ≤ c) => Ideal.Quotient.mk_surjective (v h)
    exact ⟨r,funext hr⟩
  · intro v
    constructor
    · intro hv
      have hh (h : PLift (G.target e ≤ c)) :
          v h ∈ Ideal.span {α e} := Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hv h)
      choose r hr using fun h => Ideal.mem_span_singleton.mp (hh h)
      exact ⟨r,funext hr⟩
    · rintro ⟨w,rfl⟩
      funext h
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr ⟨w h,rfl⟩)

 theorem structureSheaf_minimal [IsLocalRing R]
    (hα : ∀ e, α e ∈ IsLocalRing.maximalIdeal R)
    (hreach : ∀ x, x < c → ∃ e, G.source e = x ∧ G.target e ≤ c)
    (x : V) (hxc : x ≠ c) :
    LinearMap.ker ((structureSheaf G α c).stalkMap x) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R ((structureSheaf G α c).vertex x)) := by
  classical
  intro v hv
  by_cases hx : x ≤ c
  · obtain ⟨e,he,het⟩ := hreach x (lt_of_le_of_ne hx hxc)
    subst x
    have heq := congrFun (LinearMap.mem_ker.mp hv) ⟨e,rfl⟩
    have hvα : v ⟨hx⟩ ∈ Ideal.span {α e} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (congrFun heq ⟨het⟩)
    have hm : v ⟨hx⟩ ∈ IsLocalRing.maximalIdeal R :=
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hα e))) hvα
    let one : (structureSheaf G α c).vertex (G.source e) := fun _ => 1
    have hs : v ⟨hx⟩ • one ∈ IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R ((structureSheaf G α c).vertex (G.source e))) :=
      Submodule.smul_mem_smul hm (show one ∈
        (⊤ : Submodule R ((structureSheaf G α c).vertex (G.source e))) from Submodule.mem_top)
    have heqv : v = v ⟨hx⟩ • one := by
      funext h
      exact (mul_one _).symm
    rw [heqv]
    exact hs
  · let _ := structureSheaf_support G α c x hx
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _

end
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)

noncomputable def baseChange : Sheaf (R := S) G where
  vertex x := ModuleCat.of S (S ⊗[R] B.vertex x)
  edge e := ModuleCat.of S (S ⊗[R] B.edge e)
  lower e := AlgebraTensorModule.lTensor S S (B.lower e)
  upper e := AlgebraTensorModule.lTensor S S (B.upper e)

noncomputable def tensorAssignments : S ⊗[R] B.Assignment →ₗ[S] (B.baseChange S).Assignment :=
  TensorProduct.piRightHom R S S (fun x => B.vertex x)

@[simp] theorem tensorAssignments_tmul (s : S) (f : B.Assignment) (x : V) :
    B.tensorAssignments S (s ⊗ₜ f) x = s ⊗ₜ f x := rfl

lemma baseChange_tmul_compatible (Ω : Set V) (s : S) (f : B.Assignment)
    (hf : B.CompatibleOn Ω f) : (B.baseChange S).CompatibleOn Ω (fun x => s ⊗ₜ f x) := by
  intro e hs ht
  change s ⊗ₜ[R] B.lower e (f (G.source e)) = s ⊗ₜ[R] B.upper e (f (G.target e))
  rw [hf e hs ht]

noncomputable def tensorSections (Ω : Set V) :
    S ⊗[R] B.sections Ω →ₗ[S] (B.baseChange S).sections Ω :=
  ((B.tensorAssignments S).comp (AlgebraTensorModule.lTensor S S (B.sections Ω).subtype)).codRestrict
    ((B.baseChange S).sections Ω) (by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul s f => exact B.baseChange_tmul_compatible S Ω s f.val f.property
      | add z t hz ht => simpa only [map_add] using Submodule.add_mem _ hz ht)

@[simp] theorem tensorSections_tmul (Ω : Set V) (s : S) (f : B.sections Ω) (x : V) :
    (B.tensorSections S Ω (s ⊗ₜ f)).val x = s ⊗ₜ f.val x := rfl

theorem baseChange_generated (h : B.Generated) : (B.baseChange S).Generated := by
  intro x v
  induction v using TensorProduct.inductionOn with
  | tmul s v =>
    obtain ⟨f,hf,hx⟩ := h x v
    exact ⟨fun y => s ⊗ₜ f y,B.baseChange_tmul_compatible S Set.univ s f hf,congrArg (fun v => s ⊗ₜ[R] v) hx⟩
  | add v w hv hw =>
    obtain ⟨f,hf,hfv⟩ := hv
    obtain ⟨g,hg,hgw⟩ := hw
    exact ⟨f+g,Submodule.add_mem ((B.baseChange S).sections Set.univ) hf hg,congrArg₂ (·+·) hfv hgw⟩

/-- The finite section constraint whose kernel is the actual section module. -/
noncomputable def constraint (Ω : Set V) : B.Assignment →ₗ[R]
    (∀ e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω}, B.edge e.val) :=
  LinearMap.pi (fun e => (B.lower e.val).comp (LinearMap.proj (G.source e.val)) -
    (B.upper e.val).comp (LinearMap.proj (G.target e.val)))

lemma ker_constraint (Ω : Set V) : LinearMap.ker (B.constraint Ω) = B.sections Ω := by
  ext f
  constructor
  · intro h e hs ht
    have hh := congrFun (LinearMap.mem_ker.mp h) ⟨e,hs,ht⟩
    exact sub_eq_zero.mp hh
  · intro h
    apply LinearMap.mem_ker.mpr
    funext e
    exact sub_eq_zero.mpr (h e.val e.property.1 e.property.2)

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)

 theorem baseChange_vertex_free (x : V) [Module.Free R (B.vertex x)] :
    Module.Free S ((B.baseChange S).vertex x) :=
  inferInstanceAs (Module.Free S (S ⊗[R] B.vertex x))

 theorem baseChange_vertex_finite (x : V) [Module.Finite R (B.vertex x)] :
    Module.Finite S ((B.baseChange S).vertex x) :=
  inferInstanceAs (Module.Finite S (S ⊗[R] B.vertex x))

 theorem baseChange_upperQuotient [Module.Flat R S] (α : E → R)
    (h : B.UpperQuotient α) : (B.baseChange S).UpperQuotient (fun e => algebraMap R S (α e)) := by
  intro e
  refine ⟨LinearMap.lTensor_surjective S (h e).1, ?_⟩
  have hs : Function.Exact (DistribSMul.toLinearMap R (B.vertex (G.target e)) (α e))
      (B.upper e) := by
    intro v
    exact ((h e).2 v).trans (by simp only [Set.mem_range, DistribSMul.toLinearMap_apply,
      eq_comm])
  have ht := Module.Flat.lTensor_exact S hs
  intro v
  change (B.upper e).lTensor S v = 0 ↔ ∃ w, v = algebraMap R S (α e) • w
  rw [ht v, LinearMap.lTensor_smul_action]
  change (∃ w : S ⊗[R] B.vertex (G.target e), α e • w = v) ↔
    ∃ w : S ⊗[R] B.vertex (G.target e), v = algebraMap R S (α e) • w
  simp only [IsScalarTower.algebraMap_smul]
  constructor <;> rintro ⟨w,hw⟩ <;> exact ⟨w,hw.symm⟩

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
noncomputable section

 theorem tensorAssignments_bijective [Finite V] : Function.Bijective (B.tensorAssignments S) := by
  classical
  let := Fintype.ofFinite V
  exact (TensorProduct.piRight R S S (fun x => B.vertex x)).bijective

 theorem constraint_tensorAssignments (Ω : Set V) (z : S ⊗[R] B.Assignment) :
    (B.baseChange S).constraint Ω (B.tensorAssignments S z) =
      TensorProduct.piRightHom R S S (fun e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω} =>
        B.edge e.val) (AlgebraTensorModule.lTensor S S (B.constraint Ω) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s f =>
    ext e
    change s ⊗ₜ[R] B.lower e.val (f (G.source e.val)) -
      s ⊗ₜ[R] B.upper e.val (f (G.target e.val)) =
      s ⊗ₜ[R] (B.lower e.val (f (G.source e.val)) -
        B.upper e.val (f (G.target e.val)))
    exact (tmul_sub _ _ _).symm
  | add z w hz hw => simp only [map_add,hz,hw]; rfl

 theorem tensorSections_surjective [Finite V] [Finite E] [Module.Flat R S] (Ω : Set V) :
    Function.Surjective (B.tensorSections S Ω) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  intro f
  obtain ⟨z,hz⟩ := (B.tensorAssignments_bijective S).2 f.val
  have hc : (B.baseChange S).constraint Ω (B.tensorAssignments S z) = 0 := by
    rw [hz]
    apply LinearMap.mem_ker.mp
    rw [(B.baseChange S).ker_constraint Ω]
    exact f.property
  have he : AlgebraTensorModule.lTensor S S (B.constraint Ω) z = 0 := by
    apply (TensorProduct.piRight R S S
      (fun e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω} => B.edge e.val)).injective
    rw [map_zero]
    exact (B.constraint_tensorAssignments S Ω z).symm.trans hc
  have hex : Function.Exact (B.sections Ω).subtype (B.constraint Ω) := by
    rw [← B.ker_constraint Ω]
    exact (B.constraint Ω).exact_subtype_ker_map
  obtain ⟨w,hw⟩ := (Module.Flat.lTensor_exact S hex z).mp he
  refine ⟨w,?_⟩
  apply Subtype.ext
  change B.tensorAssignments S (AlgebraTensorModule.lTensor S S (B.sections Ω).subtype w) = _
  exact (congrArg (B.tensorAssignments S) hw).trans hz

 theorem tensorSections_injective [Finite V] [Module.Flat R S] (Ω : Set V) :
    Function.Injective (B.tensorSections S Ω) := by
  intro x y h
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (B.sections Ω).subtype (B.sections Ω).injective_subtype
  apply (B.tensorAssignments_bijective S).1
  exact congrArg Subtype.val h

/-- Sections over every vertex subset commute with flat extension of scalars
for a finite moment graph. No freeness or BMP character input is used. -/
 def tensorSectionsEquiv [Finite V] [Finite E] [Module.Flat R S] (Ω : Set V) :
    S ⊗[R] B.sections Ω ≃ₗ[S] (B.baseChange S).sections Ω :=
  LinearEquiv.ofBijective (B.tensorSections S Ω)
    ⟨B.tensorSections_injective S Ω,B.tensorSections_surjective S Ω⟩

 theorem baseChange_flabby [Finite V] [Finite E] [Module.Flat R S]
    (hb : B.Flabby) : (B.baseChange S).Flabby := by
  intro Ω hΩ f hf
  obtain ⟨z,hz⟩ := B.tensorSections_surjective S Ω ⟨f,hf⟩
  suffices ∃ g : (B.baseChange S).Assignment, (B.baseChange S).IsGlobal g ∧
      ∀ x ∈ Ω, g x = (B.tensorSections S Ω z).val x by
    simpa only [hz] using this
  clear hz f hf
  induction z using TensorProduct.inductionOn with
  | tmul s f =>
    obtain ⟨g,hg,hgf⟩ := hb Ω hΩ f.val f.property
    refine ⟨fun x => s ⊗ₜ g x,B.baseChange_tmul_compatible S Set.univ s g hg,?_⟩
    intro x hx
    change s ⊗ₜ[R] g x = s ⊗ₜ[R] f.val x
    rw [hgf x hx]
  | add z w hz hw =>
    obtain ⟨f,hf,hfz⟩ := hz
    obtain ⟨g,hg,hgw⟩ := hw
    refine ⟨f+g,Submodule.add_mem ((B.baseChange S).sections Set.univ) hf hg,?_⟩
    intro x hx
    simp only [map_add,Submodule.coe_add,Pi.add_apply]
    rw [hfz x hx,hgw x hx]

end
end KLInvariance.MomentGraph.Sheaf

end


section


namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um un
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}
noncomputable section

namespace Iso
variable {B : Sheaf.{ur,uv,ue,um} (R := R) G}
  {C : Sheaf.{ur,uv,ue,un} (R := R) G} (j : Iso B C)
include j

 theorem flabby (hb : B.Flabby) : C.Flabby := by
  intro Ω hΩ f hf
  have hsf : B.CompatibleOn Ω (j.symm.assignments f) :=
    (j.symm.compatible_iff Ω f).mpr hf
  obtain ⟨g,hg,hgf⟩ := hb Ω hΩ (j.symm.assignments f) hsf
  refine ⟨j.assignments g,(j.compatible_iff Set.univ g).mpr hg,?_⟩
  intro x hx
  change j.vertex x (g x) = f x
  rw [hgf x hx]
  exact (j.vertex x).apply_symm_apply _

 theorem generated (hb : B.Generated) : C.Generated := by
  intro x v
  obtain ⟨f,hf,hfv⟩ := hb x ((j.vertex x).symm v)
  refine ⟨j.assignments f,(j.compatible_iff Set.univ f).mpr hf,?_⟩
  change j.vertex x (f x) = v
  rw [hfv,LinearEquiv.apply_symm_apply]

end Iso

variable (S : Type us) [CommRing S] [Algebra R S]

def baseChangeScalar : S ⊗[R] R ≃ₗ[S] S := AlgebraTensorModule.rid R S S

@[simp] theorem baseChangeScalar_tmul (s : S) (r : R) :
    baseChangeScalar S (s ⊗ₜ[R] r) = s * algebraMap R S r := by
  change r • s = s * algebraMap R S r
  rw [Algebra.smul_def,mul_comm]

 theorem span_map (a : R) :
    (Ideal.span {a}).map (algebraMap R S) = Ideal.span {algebraMap R S a} := by
  rw [Ideal.map_span,Set.image_singleton]

 def baseChangeQuotient (a : R) :
    S ⊗[R] (R ⧸ Ideal.span {a}) ≃ₗ[S] S ⧸ Ideal.span {algebraMap R S a} :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (Ideal.span {a})).symm.toLinearEquiv.trans
    (Ideal.quotientEquivAlgOfEq S (span_map S a)).toLinearEquiv

@[simp] theorem baseChangeQuotient_tmul (a r : R) (s : S) :
    baseChangeQuotient S a (s ⊗ₜ[R] Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (s * algebraMap R S r) := by
  simp only [baseChangeQuotient,LinearEquiv.trans_apply,AlgEquiv.toLinearEquiv_apply,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  change Ideal.Quotient.mk _ (r • s) = Ideal.Quotient.mk _ (s * algebraMap R S r)
  rw [Algebra.smul_def,mul_comm]


 def baseChangePiScalar (p : Prop) :
    S ⊗[R] (PLift p → R) ≃ₗ[S] (PLift p → S) := by
  classical
  exact (TensorProduct.piRight R S S (fun _ : PLift p => R)).trans
    (LinearEquiv.piCongrRight (fun _ => baseChangeScalar S))

 def baseChangePiQuotient (a : R) (p : Prop) :
    S ⊗[R] (PLift p → R ⧸ Ideal.span {a}) ≃ₗ[S]
      (PLift p → S ⧸ Ideal.span {algebraMap R S a}) := by
  classical
  exact (TensorProduct.piRight R S S
    (fun _ : PLift p => R ⧸ Ideal.span {a})).trans
      (LinearEquiv.piCongrRight (fun _ => baseChangeQuotient S a))

 theorem baseChangePiScalar_tmul (p : Prop) (s : S) (v : PLift p → R) (h : PLift p) :
    baseChangePiScalar S p (s ⊗ₜ v) h = s * algebraMap R S (v h) :=
  baseChangeScalar_tmul S s (v h)

 theorem baseChangePiQuotient_tmul (a : R) (p : Prop)
    (s : S) (v : PLift p → R ⧸ Ideal.span {a}) (h : PLift p) :
    baseChangePiQuotient S a p (s ⊗ₜ v) h = baseChangeQuotient S a (s ⊗ₜ v h) := rfl

 def quotientPullback (a : R) (p q : Prop) (h : q → p) :
    (PLift p → R) →ₗ[R] (PLift q → R ⧸ Ideal.span {a}) :=
  LinearMap.pi fun t => (Ideal.Quotient.mkₐ R (Ideal.span {a})).toLinearMap.comp
    (LinearMap.proj ⟨h t.down⟩)

 theorem baseChangePi_natural (a : R) (p q : Prop) (h : q → p)
    (v : S ⊗[R] (PLift p → R)) :
    baseChangePiQuotient S a q
      (AlgebraTensorModule.lTensor S S (quotientPullback a p q h) v) =
      quotientPullback (algebraMap R S a) p q h (baseChangePiScalar S p v) := by
  induction v using TensorProduct.inductionOn with
  | tmul s v =>
    funext hh
    change baseChangePiQuotient S a q (s ⊗ₜ quotientPullback a p q h v) hh = _
    rw [baseChangePiQuotient_tmul]
    change baseChangeQuotient S a (s ⊗ₜ Ideal.Quotient.mk _ (v ⟨h hh.down⟩)) = _
    rw [baseChangeQuotient_tmul]
    exact congrArg (Ideal.Quotient.mk _) (baseChangePiScalar_tmul S p s v _).symm
  | add v w hv hw => simp only [map_add,hv,hw]

 def structureBaseChangeIso (G : OrderedGraph V E) (α : E → R) (c : V) :
    Iso ((structureSheaf G α c).baseChange S)
      (structureSheaf G (fun e => algebraMap R S (α e)) c) where
  vertex x := baseChangePiScalar S (x ≤ c)
  edge e := baseChangePiQuotient S (α e) (G.target e ≤ c)
  lower e v := baseChangePi_natural S (α e) (G.source e ≤ c) (G.target e ≤ c)
    ((G.increasing e).le.trans ·) v
  upper e v := baseChangePi_natural S (α e) (G.target e ≤ c) (G.target e ≤ c) id v

 theorem structureSheaf_flat_flabby [Finite V] [Finite E] [Module.Flat R S]
    (G : OrderedGraph V E) (α : E → R) (c : V) (hf : (structureSheaf G α c).Flabby) :
    (structureSheaf G (fun e => algebraMap R S (α e)) c).Flabby :=
  (structureBaseChangeIso S G α c).flabby ((structureSheaf G α c).baseChange_flabby S hf)

end
end KLInvariance.MomentGraph.Sheaf

end


section

/-! Restriction to a full vertex subgraph, including the relative-flabbiness
criterion used after plane localization. -/
namespace KLInvariance.MomentGraph
universe ur uv ue um
variable {V : Type uv} [PartialOrder V] {E : Type ue} (G : OrderedGraph V E)

 def inducedGraph (K : Set V) : OrderedGraph K {e : E // G.source e ∈ K ∧ G.target e ∈ K} where
  source e := ⟨G.source e.val,e.property.1⟩
  target e := ⟨G.target e.val,e.property.2⟩
  increasing e := G.increasing e.val

namespace Sheaf
variable {G} {R : Type ur} [CommRing R] (B : Sheaf.{ur,uv,ue,um} (R := R) G)
  (K : Set V)
noncomputable section

 def restrict : Sheaf (R := R) (inducedGraph G K) where
  vertex x := B.vertex x.val
  edge e := B.edge e.val
  lower e := B.lower e.val
  upper e := B.upper e.val

 def restrictAssignment (f : B.Assignment) : (B.restrict K).Assignment := fun x => f x.val

 def extendAssignment (f : (B.restrict K).Assignment) : B.Assignment := by
  classical
  exact fun x => if h : x ∈ K then f ⟨x,h⟩ else 0

@[simp] theorem extendAssignment_mem (f : (B.restrict K).Assignment) (x : K) :
    B.extendAssignment K f x.val = f x := by
  classical
  change (if h : x.val ∈ K then f ⟨x.val,h⟩ else 0) = f x
  split_ifs with h
  · rfl
  · exact (h x.property).elim

 theorem restrict_compatible {Ω : Set V} {f : B.Assignment} (hf : B.CompatibleOn Ω f) :
    (B.restrict K).CompatibleOn (Subtype.val ⁻¹' Ω) (B.restrictAssignment K f) := by
  intro e hs ht
  exact hf e.val hs ht

 theorem restrict_global (f : B.Assignment) (hf : B.IsGlobal f) :
    (B.restrict K).IsGlobal (B.restrictAssignment K f) := by
  intro e _ _
  exact hf e.val (Set.mem_univ _) (Set.mem_univ _)

 theorem restrict_generated (hg : B.Generated) : (B.restrict K).Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hg x.val v
  exact ⟨B.restrictAssignment K f,B.restrict_global K f hf,hfx⟩

 theorem extend_compatible (Ω : Set K) (f : (B.restrict K).Assignment)
    (hf : (B.restrict K).CompatibleOn Ω f) :
    B.CompatibleOn (Subtype.val '' Ω) (B.extendAssignment K f) := by
  intro e hs ht
  obtain ⟨x,hx,hxe⟩ := hs
  obtain ⟨y,hy,hye⟩ := ht
  have hsk : G.source e ∈ K := hxe ▸ x.property
  have htk : G.target e ∈ K := hye ▸ y.property
  let ee : {e : E // G.source e ∈ K ∧ G.target e ∈ K} := ⟨e,hsk,htk⟩
  have hsx : (inducedGraph G K).source ee = x := Subtype.ext hxe.symm
  have hty : (inducedGraph G K).target ee = y := Subtype.ext hye.symm
  have hh := hf ee (hsx ▸ hx) (hty ▸ hy)
  change B.lower e (f ⟨G.source e,hsk⟩) = B.upper e (f ⟨G.target e,htk⟩) at hh
  simpa only [← B.extendAssignment_mem K f] using hh

/-- The induced subgraph may use upper sets which are not ambient upper
sets. All nonzero exiting edges must stay in the subgraph. -/
 theorem restrict_flabby_live [Finite V] (hb : B.Flabby) (live : Set E)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hclosed : ∀ e ∈ live, G.source e ∈ K → G.target e ∈ K) :
    (B.restrict K).Flabby := by
  intro Ω hΩ f hf
  have hc : B.ClosedUnder live (Subtype.val '' Ω) := by
    intro e he hs
    obtain ⟨x,hx,hxe⟩ := hs
    have hsk : G.source e ∈ K := hxe ▸ x.property
    have htk := hclosed e he hsk
    refine ⟨⟨G.target e,htk⟩,?_,rfl⟩
    apply hΩ _ hx
    change x.val ≤ G.target e
    rw [hxe]
    exact (G.increasing e).le
  obtain ⟨g,hg,hgf⟩ := B.extend_closedUnder hb live hdead (Subtype.val '' Ω) hc
    (B.extendAssignment K f) (B.extend_compatible K Ω f hf)
  refine ⟨B.restrictAssignment K g,B.restrict_global K g hg,?_⟩
  intro x hx
  exact (hgf x.val ⟨x,hx,rfl⟩).trans (B.extendAssignment_mem K f x)

 theorem restrict_quotient (α : E → R) (hB : B.UpperQuotient α) :
    (B.restrict K).UpperQuotient (fun e => α e.val) := fun e => hB e.val

end
end Sheaf
end KLInvariance.MomentGraph

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (K : Set V)
noncomputable section

 def structureRestrictIso (c : K) :
    Iso ((structureSheaf G α c.val).restrict K)
      (structureSheaf (inducedGraph G K) (fun e => α e.val) c) where
  vertex _ := LinearEquiv.refl R _
  edge _ := LinearEquiv.refl R _
  lower _ _ := rfl
  upper _ _ := rfl

 theorem structureSheaf_edge_subsingleton (c : V) (e : E) (he : ¬ G.target e ≤ c) :
    Subsingleton ((structureSheaf G α c).edge e) :=
  ⟨fun _ _ => funext (fun h => False.elim (he h.down))⟩

 theorem structureSheaf_lowerIdeal_flabby [Finite V] (hK : IsLowerSet K) (c : K)
    (hf : (structureSheaf G α c.val).Flabby) :
    (structureSheaf (inducedGraph G K) (fun e => α e.val) c).Flabby := by
  apply (structureRestrictIso G α K c).flabby
  apply (structureSheaf G α c.val).restrict_flabby_live K hf {e | G.target e ∈ K}
  · intro e he
    exact structureSheaf_edge_subsingleton G α c.val e (fun hc => he (hK hc c.property))
  · intro e he _
    exact he

end
end KLInvariance.MomentGraph.Sheaf

end


section

/-! Pullback along a directed graph map. Relative-order flabbiness requires
only outgoing completeness for the surviving edges, not equality of the two
orders on a coset. -/
namespace KLInvariance.MomentGraph
universe ur uv ue uw uf um
variable {V : Type uv} [PartialOrder V] {E : Type ue}
  {W : Type uw} [PartialOrder W] {F : Type uf}

structure GraphMap (G : OrderedGraph V E) (H : OrderedGraph W F) where
  vertex : V → W
  edge : E → F
  source : ∀ e, vertex (G.source e) = H.source (edge e)
  target : ∀ e, vertex (G.target e) = H.target (edge e)

namespace Sheaf
variable {R : Type ur} [CommRing R] {G : OrderedGraph V E} {H : OrderedGraph W F}
  (B : Sheaf.{ur,uw,uf,um} (R := R) H) (f : GraphMap G H)
noncomputable section

 def moduleEq {M N : ModuleCat.{um} R} (h : M=N) : M ≃ₗ[R] N := h ▸ LinearEquiv.refl R M

 theorem moduleEq_apply {X : Type*} (M : X → ModuleCat.{um} R) {x y : X} (h : x=y)
    (s : ∀ z, M z) : moduleEq (congrArg M h) (s x) = s y := by subst y; rfl

 def pullback : Sheaf (R := R) G where
  vertex x := B.vertex (f.vertex x)
  edge e := B.edge (f.edge e)
  lower e := (B.lower (f.edge e)).comp (moduleEq (congrArg B.vertex (f.source e))).toLinearMap
  upper e := (B.upper (f.edge e)).comp (moduleEq (congrArg B.vertex (f.target e))).toLinearMap

 def pullAssignment (s : B.Assignment) : (B.pullback f).Assignment := fun x => s (f.vertex x)

@[simp] theorem pull_lower (e : E) (s : B.Assignment) :
    (B.pullback f).lower e (B.pullAssignment f s (G.source e)) =
      B.lower (f.edge e) (s (H.source (f.edge e))) := by
  exact congrArg (B.lower (f.edge e)) (moduleEq_apply B.vertex (f.source e) s)

@[simp] theorem pull_upper (e : E) (s : B.Assignment) :
    (B.pullback f).upper e (B.pullAssignment f s (G.target e)) =
      B.upper (f.edge e) (s (H.target (f.edge e))) := by
  exact congrArg (B.upper (f.edge e)) (moduleEq_apply B.vertex (f.target e) s)

 theorem pull_global (s : B.Assignment) (hs : B.IsGlobal s) :
    (B.pullback f).IsGlobal (B.pullAssignment f s) := by
  intro e _ _
  rw [pull_lower,pull_upper]
  exact hs (f.edge e) (Set.mem_univ _) (Set.mem_univ _)

 theorem pullback_generated (hg : B.Generated) : (B.pullback f).Generated := by
  intro x v
  obtain ⟨s,hs,hx⟩ := hg (f.vertex x) v
  exact ⟨B.pullAssignment f s,B.pull_global f s hs,hx⟩

 def pushAssignment (s : (B.pullback f).Assignment) : B.Assignment := by
  classical
  exact fun y => if h : ∃ x, f.vertex x=y then
    moduleEq (congrArg B.vertex h.choose_spec) (s h.choose) else 0

 theorem pull_push (hi : Function.Injective f.vertex) (s : (B.pullback f).Assignment) :
    B.pullAssignment f (B.pushAssignment f s) = s := by
  classical
  change (∀ x, B.vertex (f.vertex x)) at s
  funext x
  have h : ∃ z, f.vertex z=f.vertex x := ⟨x,rfl⟩
  change @Eq (B.vertex (f.vertex x))
    (if hh : ∃ z, f.vertex z=f.vertex x then
      moduleEq (congrArg B.vertex hh.choose_spec) (s hh.choose) else 0) (s x)
  rw [dite_eq_left h]
  have hx : h.choose=x := hi h.choose_spec
  exact moduleEq_apply (fun z => B.vertex (f.vertex z)) hx s

 theorem pullback_flabby_live [Finite W] (hb : B.Flabby)
    (hi : Function.Injective f.vertex) (live : Set F)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hlift : ∀ e ∈ live, ∀ x, f.vertex x = H.source e →
      ∃ a, f.edge a=e ∧ G.source a=x) : (B.pullback f).Flabby := by
  intro Ω hΩ s hs
  have hc : B.ClosedUnder live (f.vertex '' Ω) := by
    intro e he hsource
    obtain ⟨x,hx,hxe⟩ := hsource
    obtain ⟨a,rfl,rfl⟩ := hlift e he x hxe
    exact ⟨G.target a,hΩ (G.increasing a).le hx,f.target a⟩
  have hcompat : B.CompatibleOn (f.vertex '' Ω) (B.pushAssignment f s) := by
    intro e hsource htarget
    by_cases he : e ∈ live
    · obtain ⟨x,hx,hxe⟩ := hsource
      obtain ⟨a,rfl,rfl⟩ := hlift e he x hxe
      obtain ⟨y,hy,hye⟩ := htarget
      have hya : y=G.target a := hi (hye.trans (f.target a).symm)
      subst y
      have hh := hs a hx hy
      rw [← B.pull_push f hi s] at hh
      change (B.pullback f).lower a (B.pullAssignment f (B.pushAssignment f s) (G.source a)) =
        (B.pullback f).upper a (B.pullAssignment f (B.pushAssignment f s) (G.target a)) at hh
      rw [pull_lower,pull_upper] at hh
      exact hh
    · exact @Subsingleton.elim _ (hdead e he) _ _
  obtain ⟨t,ht,hts⟩ := B.extend_closedUnder hb live hdead (f.vertex '' Ω) hc
    (B.pushAssignment f s) hcompat
  refine ⟨B.pullAssignment f t,B.pull_global f t ht,?_⟩
  intro x hx
  change t (f.vertex x) = s x
  rw [hts (f.vertex x) ⟨x,hx,rfl⟩]
  exact congrFun (B.pull_push f hi s) x

 theorem pullback_quotient (α : F → R) (hq : B.UpperQuotient α) :
    (B.pullback f).UpperQuotient (fun e => α (f.edge e)) := by
  intro e
  let j := moduleEq (congrArg B.vertex (f.target e))
  refine ⟨?_,?_⟩
  · exact (hq (f.edge e)).1.comp j.surjective
  · intro v
    change B.upper (f.edge e) (j v) = 0 ↔ _
    rw [(hq (f.edge e)).2]
    constructor
    · rintro ⟨w,hw⟩
      refine ⟨j.symm w,?_⟩
      apply j.injective
      change j v = j (α (f.edge e) • j.symm w)
      rw [map_smul,LinearEquiv.apply_symm_apply]
      exact hw
    · rintro ⟨w,rfl⟩
      exact ⟨j w,j.map_smul _ _⟩

end
end Sheaf
end KLInvariance.MomentGraph

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue uw uf um
variable {R : Type ur} [CommRing R]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  {W : Type uw} [PartialOrder W] {F : Type uf} {H : OrderedGraph W F}
  (B : Sheaf.{ur,uw,uf,um} (R := R) H) (f : GraphMap G H)
noncomputable section

 theorem stalkMap_assignment (s : B.Assignment) (x : W) (e : Outgoing (G := H) x) :
    B.stalkMap x (s x) e = B.lower e.val (s (H.source e.val)) := by
  rcases e with ⟨e,he⟩
  subst x
  rfl

 theorem pullback_kernel (x : V) (T : Set F)
    (live : Set F) (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hlift : ∀ e ∈ live, f.vertex x = H.source e →
      ∃ a, f.edge a=e ∧ G.source a=x) :
    (B.pullback f).upwardKernel x {e | f.edge e.val ∈ T} =
      B.upwardKernel (f.vertex x) {e | e.val ∈ T} := by
  classical
  ext v
  change B.vertex (f.vertex x) at v
  let s : B.Assignment := Function.update (fun _ => 0) (f.vertex x) v
  have hs : s (f.vertex x)=v := Function.update_self (β := fun y => B.vertex y) (f.vertex x) v (fun _ => 0)
  have hxs : B.pullAssignment f s x = v := hs
  constructor
  · intro hv e he
    rw [← hs,B.stalkMap_assignment s]
    by_cases hl : e.val ∈ live
    · obtain ⟨a,ha,hax⟩ := hlift e.val hl e.property.symm
      have hh := hv ⟨a,hax⟩ (show f.edge a ∈ T from ha.symm ▸ he)
      rw [← hxs,(B.pullback f).stalkMap_assignment (B.pullAssignment f s)] at hh
      rw [B.pull_lower f] at hh
      exact (congrArg (fun q : F => B.lower q (s (H.source q)) = 0) ha).mp hh
    · exact @Subsingleton.elim _ (hdead e.val hl) _ _
  · intro hv e he
    have hh := hv ⟨f.edge e.val,(f.source e.val).symm.trans (congrArg f.vertex e.property)⟩ he
    rw [← hs,B.stalkMap_assignment s] at hh
    rw [← hxs,(B.pullback f).stalkMap_assignment (B.pullAssignment f s),B.pull_lower f]
    exact hh

end
end KLInvariance.MomentGraph.Sheaf

end


section

/-! Restriction along an outgoing-complete actual graph embedding.  In
particular this supports passage from [1,b] to [u,b] without changing stalks. -/
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}
namespace GradedSheaf
variable (B : GradedSheaf (𝓐 := 𝓐) H) (f : GraphMap G H)

 theorem moduleEq_graded {x y : W} (h : x=y) (n : ℤ)
    (v : B.vertex x) (hv : v ∈ (B.vertex x).piece n) :
    Sheaf.moduleEq (congrArg B.forget.vertex h) v ∈ (B.vertex y).piece n := by
  subst y
  exact hv

 def pullback : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := B.vertex (f.vertex x)
  edge e := B.edge (f.edge e)
  lower e := ⟨(B.forget.pullback f).lower e,fun n v hv =>
    (B.lower (f.edge e)).graded n _ (B.moduleEq_graded (f.source e) n v hv)⟩
  upper e := ⟨(B.forget.pullback f).upper e,fun n v hv =>
    (B.upper (f.edge e)).graded n _ (B.moduleEq_graded (f.target e) n v hv)⟩

@[simp] theorem forget_pullback : (B.pullback f).forget = B.forget.pullback f := rfl

 theorem pullback_edgeFlabby (hb : B.EdgeFlabby)
    (hi : Function.Injective f.vertex)
    (hlift : ∀ e x, f.vertex x = H.source e → ∃ a, f.edge a=e ∧ G.source a=x) :
    (B.pullback f).EdgeFlabby := by
  intro Ω hΩ s hs
  have hc : B.forget.ClosedUnder Set.univ (f.vertex '' Ω) := by
    intro e _ hsource
    obtain ⟨x,hx,hxe⟩ := hsource
    obtain ⟨a,rfl,rfl⟩ := hlift e x hxe
    exact ⟨G.target a,hΩ a (Set.mem_univ a) hx,f.target a⟩
  have hcompat : B.forget.CompatibleOn (f.vertex '' Ω) (B.forget.pushAssignment f s) := by
    intro e hsource htarget
    obtain ⟨x,hx,hxe⟩ := hsource
    obtain ⟨a,rfl,rfl⟩ := hlift e x hxe
    obtain ⟨y,hy,hye⟩ := htarget
    have hya : y=G.target a := hi (hye.trans (f.target a).symm)
    subst y
    have hh := hs a hx hy
    change (B.forget.pullback f).lower a (s (G.source a)) =
      (B.forget.pullback f).upper a (s (G.target a)) at hh
    rw [← B.forget.pull_push f hi s] at hh
    rw [Sheaf.pull_lower,Sheaf.pull_upper] at hh
    exact hh
  obtain ⟨t,ht,hts⟩ := hb (f.vertex '' Ω) hc (B.forget.pushAssignment f s) hcompat
  refine ⟨B.forget.pullAssignment f t,B.forget.pull_global f t ht,?_⟩
  intro x hx
  change t (f.vertex x) = s x
  rw [hts (f.vertex x) ⟨x,hx,rfl⟩]
  exact congrFun (B.forget.pull_push f hi s) x

 theorem pullback_kernelMinimal (hi : Function.Injective f.vertex)
    (hlift : ∀ e x, f.vertex x = H.source e → ∃ a, f.edge a=e ∧ G.source a=x)
    (x : V) (hx : B.KernelMinimal (f.vertex x)) :
    (B.pullback f).KernelMinimal x := by
  intro s hs
  have h := hx (B.forget.pushAssignment f s) (by
    intro e he
    obtain ⟨a,rfl,hax⟩ := hlift e x he.symm
    have hh := hs a hax
    change (B.forget.pullback f).lower a (s (G.source a)) = 0 at hh
    rw [← B.forget.pull_push f hi s,Sheaf.pull_lower] at hh
    exact hh)
  have he : B.forget.pushAssignment f s (f.vertex x)=s x :=
    congrFun (B.forget.pull_push f hi s) x
  rwa [he] at h

end GradedSheaf

namespace BoundarySheaf
variable [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {hneg : ∀ n < 0, 𝓐 n = ⊥} {α : F → A} {b : W}
  (B : BoundarySheaf hneg H α b) (f : GraphMap G H)
  (hi : Function.Injective f.vertex)
  (hlift : ∀ e x, f.vertex x = H.source e → ∃ a, f.edge a=e ∧ G.source a=x)
  (c : V) (hc : f.vertex c=b)

 def pullback : BoundarySheaf hneg G (fun e => α (f.edge e)) c where
  sheaf := B.sheaf.pullback f
  free x := B.free (f.vertex x)
  quotient := B.sheaf.forget.pullback_quotient f α B.quotient
  flabby := B.sheaf.pullback_edgeFlabby f B.flabby hi hlift
  generated := B.sheaf.forget.pullback_generated f B.generated
  top := by change B.sheaf.vertex (f.vertex c)=_; rw [hc,B.top]
  minimal x hx := B.sheaf.pullback_kernelMinimal f hi hlift x
    (B.minimal (f.vertex x) (fun h => hx (hi (h.trans hc.symm))))

end BoundarySheaf
end KLInvariance.MomentGraph

end


section

/-! The actual polynomial character of a nonnegative finite graded free module.
This is not a definition of KL polynomials, and includes no character identity. -/

end

end OAI
