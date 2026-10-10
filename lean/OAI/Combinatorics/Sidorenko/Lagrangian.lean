import OAI.Combinatorics.Sidorenko.Grassmann

namespace OAI

namespace SidorenkoCounterexample
open Module
section LagrangianCharts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]


def canonicalSymplectic : LinearMap.BilinForm K (V × Module.Dual K V) where
  toFun p := {
    toFun := fun q => q.2 p.1 - p.2 q.1
    map_add' := by intros; simp; ring
    map_smul' := by intros; simp; ring }
  map_add' := by
    intro p q
    apply LinearMap.ext
    intro z
    change z.2 (p.1+q.1) - (p.2+q.2) z.1 =
      (z.2 p.1 - p.2 z.1) + (z.2 q.1 - q.2 z.1)
    simp
    ring
  map_smul' := by
    intro a p
    apply LinearMap.ext
    intro z
    change z.2 (a • p.1) - (a • p.2) z.1 = a * (z.2 p.1-p.2 z.1)
    simp
    ring

@[simp] theorem canonicalSymplectic_apply (p q : V × Module.Dual K V) :
    canonicalSymplectic p q = q.2 p.1 - p.2 q.1 := rfl

 theorem canonicalSymplectic_alt : (canonicalSymplectic (K := K) (V := V)).IsAlt := by
  intro p
  simp

 theorem canonicalSymplectic_nondegenerate :
    (canonicalSymplectic (K := K) (V := V)).Nondegenerate := by
  have hleft : ∀ p : V × Module.Dual K V,
      (∀ q, canonicalSymplectic p q = 0) → p = 0 := by
    rintro ⟨x,f⟩ hp
    have hx : x = 0 := (Module.forall_dual_apply_eq_zero_iff K x).mp (fun g => by
      simpa using hp (0,g))
    have hf : f = 0 := by
      ext y
      simpa using hp (y,0)
    simp [hx,hf]
  refine ⟨hleft, ?_⟩
  intros p hp
  apply hleft
  intro q
  exact canonicalSymplectic_alt.isRefl _ _ (hp q)

variable [FiniteDimensional K V]

/-- Lagrangians are self-orthogonal subspaces, equivalently isotropic
subspaces of half the ambient dimension. -/
abbrev Lagrangian := {L : Submodule K (V × Module.Dual K V) //
  canonicalSymplectic.orthogonal L = L}

 theorem lagrangian_finrank (L : Lagrangian (K := K) (V := V)) :
    finrank K L.val = finrank K V := by
  have h := LinearMap.BilinForm.finrank_orthogonal canonicalSymplectic_nondegenerate L.val
  rw [L.property, Module.finrank_prod, Subspace.dual_finrank_eq] at h
  have hle := Submodule.finrank_le L.val
  rw [Module.finrank_prod, Subspace.dual_finrank_eq] at hle
  omega

/-- The graph over a subspace, with its free vertical annihilator retained. -/
def formGraph (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    Submodule K (V × Module.Dual K V) where
  carrier := {p | ∃ u : U, u.val = p.1 ∧ p.2.comp U.subtype = B u}
  zero_mem' := ⟨0, rfl, by simp⟩
  add_mem' := by
    rintro p q ⟨u,hu,hf⟩ ⟨v,hv,hg⟩
    refine ⟨u+v, by simp [hu,hv], ?_⟩
    change (p.2+q.2).comp U.subtype = B (u+v)
    ext w
    simp only [LinearMap.add_comp, LinearMap.add_apply, map_add]
    exact congrArg (fun l : Module.Dual K U => l w) (congrArg₂ (·+·) hf hg)
  smul_mem' := by
    rintro a p ⟨u,hu,hf⟩
    refine ⟨a • u, by simp [hu], ?_⟩
    change (a • p.2).comp U.subtype = B (a • u)
    rw [map_smul, LinearMap.smul_comp, hf]

omit [FiniteDimensional K V] in
 theorem formGraph_fst_range (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    (formGraph U B).map (LinearMap.fst K V (Module.Dual K V)) = U := by
  ext x
  constructor
  · rintro ⟨p,⟨u,hu,_⟩,hp⟩
    have hp' : p.1 = x := hp
    rw [← hp', ← hu]
    exact u.property
  · intro hx
    obtain ⟨f,hf⟩ := (Subspace.dualRestrict_surjective (W := U)) (B ⟨x,hx⟩)
    exact ⟨(x,f),⟨⟨x,hx⟩,rfl,hf⟩,rfl⟩

omit [FiniteDimensional K V] in
 theorem formGraph_isotropic (U : Submodule K V) (B : SymForm K U) :
    formGraph U B.val ≤ canonicalSymplectic.orthogonal (formGraph U B.val) := by
  rintro p ⟨u,hu,hf⟩ q ⟨v,hv,hg⟩
  change p.2 q.1 - q.2 p.1 = 0
  rw [← hu, ← hv]
  have hf' := congrArg (fun l : Module.Dual K U => l v) hf
  have hg' := congrArg (fun l : Module.Dual K U => l u) hg
  exact sub_eq_zero.mpr (hf'.trans ((B.property.eq u v).trans hg'.symm))

def formGraphProjection (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    formGraph U B →ₗ[K] U where
  toFun p := ⟨p.val.1, by obtain ⟨u,hu,_⟩ := p.property; exact hu ▸ u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional K V] in
 theorem formGraphProjection_surj (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    Function.Surjective (formGraphProjection U B) := by
  intro u
  obtain ⟨f,hf⟩ := Subspace.dualRestrict_surjective (W := U) (B u)
  exact ⟨⟨(u.val,f),u,rfl,hf⟩,rfl⟩

noncomputable def graphVerticalEquiv (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    U.dualAnnihilator ≃ₗ[K] (formGraphProjection U B).ker where
  toFun f := ⟨⟨(0,f.val),0,rfl, by
    ext u
    simpa using ((Submodule.mem_dualAnnihilator (W := U) f.val).mp f.property) u u.property⟩, rfl⟩
  invFun p := ⟨p.val.val.2, by
    obtain ⟨u,hu,hf⟩ := p.val.property
    have hx : p.val.val.1 = 0 := congrArg Subtype.val p.property
    have hu0 : u = 0 := Subtype.ext (hu.trans hx)
    apply (Submodule.mem_dualAnnihilator (W := U) p.val.val.2).mpr
    intro x hxU
    have hf' := congrArg (fun l : Module.Dual K U => l ⟨x,hxU⟩) hf
    simpa [hu0] using hf'⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg Subtype.val p.property).symm
    · rfl
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_smul' a f := by
    apply Subtype.ext
    apply Subtype.ext
    simp

 theorem surjective_finrank_eq {E F : Type*} [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E]
    (p : E →ₗ[K] F) (hp : Function.Surjective p) :
    finrank K E = finrank K F + finrank K p.ker := by
  have h := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top] at h
  exact h.symm

 theorem formGraph_finrank (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    finrank K (formGraph U B) = finrank K V := by
  have h := surjective_finrank_eq (K := K) (E := formGraph U B) (F := U)
    (formGraphProjection U B) (formGraphProjection_surj U B)
  rw [← (graphVerticalEquiv U B).finrank_eq] at h
  exact h.trans (Subspace.finrank_add_finrank_dualAnnihilator_eq U)

noncomputable def graphLagrangian (U : Submodule K V) (B : SymForm K U) :
    Lagrangian (K := K) (V := V) :=
  ⟨formGraph U B.val, by
    apply (Submodule.eq_of_le_of_finrank_eq (formGraph_isotropic U B) _).symm
    rw [formGraph_finrank, LinearMap.BilinForm.finrank_orthogonal canonicalSymplectic_nondegenerate,
      Module.finrank_prod, Subspace.dual_finrank_eq, formGraph_finrank, Nat.add_sub_cancel_left]⟩

 theorem graphLagrangian_form_injective (U : Submodule K V) :
    Function.Injective (graphLagrangian (K := K) U) := by
  intro B C h
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  obtain ⟨f,hf⟩ := Subspace.dualRestrict_surjective (W := U) (B.val u)
  have hp : (u.val,f) ∈ formGraph U B.val := ⟨u,rfl,hf⟩
  have he : formGraph U B.val = formGraph U C.val := congrArg Subtype.val h
  rw [he] at hp
  obtain ⟨v,hv,hg⟩ := hp
  have hv' : v = u := Subtype.ext hv
  exact hf.symm.trans (hv' ▸ hg)

omit [FiniteDimensional K V] in
 theorem lagrangian_pairing_zero (L : Lagrangian (K := K) (V := V))
    {p q : V × Module.Dual K V} (hp : p ∈ L.val) (hq : q ∈ L.val) :
    canonicalSymplectic p q = 0 := by
  have hq' : q ∈ canonicalSymplectic.orthogonal L.val := L.property.symm ▸ hq
  exact hq' p hp

/-- Every Lagrangian is the graph of a unique symmetric form over its
first-coordinate projection. This includes nontransverse charts. -/
 theorem graphLagrangian_surjective :
    Function.Surjective (fun S : Σ U : Submodule K V, SymForm K U => graphLagrangian S.1 S.2) := by
  intro L
  let U := L.val.map (LinearMap.fst K V (Module.Dual K V))
  let p : L.val →ₗ[K] U := {
    toFun := fun x => ⟨x.val.1, ⟨x.val,x.property,rfl⟩⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hp : Function.Surjective p := by
    rintro ⟨x,y,hy,hyx⟩
    exact ⟨⟨y,hy⟩,Subtype.ext hyx⟩
  obtain ⟨s,hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  have hsfst (u : U) : (s u).val.1 = u.val := congrArg Subtype.val (LinearMap.congr_fun hs u)
  let C : LinearMap.BilinForm K U :=
    (((LinearMap.snd K V (Module.Dual K V)).comp L.val.subtype).comp s).compl₂ U.subtype
  have hC : C.IsSymm := by
    constructor
    intro u v
    change (s u).val.2 v.val = (s v).val.2 u.val
    have h := lagrangian_pairing_zero L (s u).property (s v).property
    change (s v).val.2 (s u).val.1 - (s u).val.2 (s v).val.1 = 0 at h
    rw [hsfst, hsfst] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨⟨U,⟨C,hC⟩⟩, ?_⟩
  apply Subtype.ext
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    let u : U := ⟨x.1,⟨x,hx,rfl⟩⟩
    refine ⟨u,rfl,?_⟩
    apply LinearMap.ext
    intro y
    have h := lagrangian_pairing_zero L hx (s y).property
    change (s y).val.2 x.1 - x.2 (s y).val.1 = 0 at h
    rw [hsfst] at h
    change x.2 y.val = (s u).val.2 y.val
    exact (sub_eq_zero.mp h).symm.trans (hC.eq y u)
  · exact (lagrangian_finrank L).trans (formGraph_finrank U C).symm

noncomputable def lagrangianGraphEquiv :
    (Σ U : Submodule K V, SymForm K U) ≃ Lagrangian (K := K) (V := V) :=
  Equiv.ofBijective (fun S => graphLagrangian S.1 S.2) ⟨by
    rintro ⟨U,B⟩ ⟨W,C⟩ he
    have h : U = W := by
      rw [← formGraph_fst_range U B.val, ← formGraph_fst_range W C.val]
      exact congrArg (fun L : Lagrangian (K := K) (V := V) =>
        L.val.map (LinearMap.fst K V (Module.Dual K V))) he
    cases h
    congr 1
    exact graphLagrangian_form_injective U he,
    graphLagrangian_surjective⟩

/-- Exact chart decomposition count: the vertical-annihilator stratum is
retained rather than discarded as a negligible exceptional event. -/
 theorem lagrangian_card_sum [Fintype K] [Finite V] :
    letI := Fintype.ofFinite (Submodule K V)
    Nat.card (Lagrangian (K := K) (V := V)) =
      ∑ U : Submodule K V, (Fintype.card K)^((finrank K U+1).choose 2) := by
  classical
  let := Fintype.ofFinite (Submodule K V)
  rw [← Nat.card_congr (lagrangianGraphEquiv (K := K) (V := V)), Nat.card_sigma]
  simp only [symForm_card]

end LagrangianCharts
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section NormalCoordinates
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (L : Submodule K E)

def symplecticProjection : E →ₗ[K] Module.Dual K L := ω.flip.compl₂ L.subtype

omit [FiniteDimensional K E] in
@[simp] theorem symplecticProjection_apply (x : E) (l : L) :
    symplecticProjection ω L x l = ω l.val x := rfl

 theorem symplecticProjection_surjective (hω : ω.Nondegenerate) :
    Function.Surjective (symplecticProjection ω L) := by
  intro f
  obtain ⟨g,hg⟩ := Subspace.dualRestrict_surjective (W := L) f
  let e := ω.flip.toDual (LinearMap.BilinForm.nondegenerate_flip_iff.mpr hω)
  refine ⟨e.symm g, ?_⟩
  apply LinearMap.ext
  intro l
  change ω.flip (e.symm g) l.val = f l
  have he : ω.flip (e.symm g) l.val = g l.val := by
    exact congrArg (fun f : Module.Dual K E => f l.val) (e.apply_symm_apply g)
  exact he.trans (LinearMap.congr_fun hg l)

omit [FiniteDimensional K E] in
 theorem symplecticProjection_ker (hL : ω.orthogonal L = L) :
    (symplecticProjection ω L).ker = L := by
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    rw [← hL]
    intro l hl
    exact LinearMap.congr_fun h ⟨l,hl⟩
  · intro hx
    apply LinearMap.ext
    intro l
    have hx' : x ∈ ω.orthogonal L := hL.symm ▸ hx
    exact hx' l.val l.property

/-- A section of the projection can be corrected by half its alternating
Gram form, retaining its projection and making its image isotropic. -/
 theorem exists_isotropic_section (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hL : ω.orthogonal L = L) :
    ∃ s : Module.Dual K L →ₗ[K] E,
      (symplecticProjection ω L).comp s = LinearMap.id ∧
      ∀ f g, ω (s f) (s g) = 0 := by
  obtain ⟨s,hs⟩ := (symplecticProjection ω L).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (symplecticProjection_surjective ω L hω))
  let A : LinearMap.BilinForm K (Module.Dual K L) := ω.compl₁₂ s s
  let t : Module.Dual K L →ₗ[K] L :=
    (-(2 : K)⁻¹) • ((Module.evalEquiv K L).symm.toLinearMap.comp A)
  have ht (f g : Module.Dual K L) : g (t f) = -(2 : K)⁻¹ * ω (s f) (s g) := by
    simp [t,A]
  have hproj (f : Module.Dual K L) (l : L) : ω l.val (s f) = f l := by
    exact LinearMap.congr_fun (LinearMap.congr_fun hs f) l
  have hLL (l m : L) : ω l.val m.val = 0 := by
    have hm : m.val ∈ ω.orthogonal L := hL.symm ▸ m.property
    exact hm l.val l.property
  refine ⟨s + L.subtype.comp t, ?_, ?_⟩
  · apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro l
    change ω l.val (s f + (t f).val) = f l
    rw [map_add, hproj, hLL, add_zero]
  · intro f g
    change ω (s f + (t f).val) (s g + (t g).val) = 0
    simp only [map_add, LinearMap.add_apply]
    rw [hproj, hLL, ← ha.neg_eq (t g).val (s f), hproj, ht, ht,
      ← ha.neg_eq (s f) (s g)]
    field_simp
    ring

/-- Relative Darboux coordinates for any fixed Lagrangian. No transitivity
or symplectic basis theorem is assumed. -/
 theorem exists_lagrangian_coordinates (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hL : ω.orthogonal L = L) :
    ∃ e : (L × Module.Dual K L) ≃ₗ[K] E,
      (∀ l : L, e (l,0) = l.val) ∧
      ∀ x y, ω (e x) (e y) = canonicalSymplectic x y := by
  obtain ⟨s,hs,hiso⟩ := exists_isotropic_section ω L h2 ha hω hL
  let e : (L × Module.Dual K L) →ₗ[K] E :=
    L.subtype.comp (LinearMap.fst K L (Module.Dual K L)) +
    s.comp (LinearMap.snd K L (Module.Dual K L))
  have hp (l : L) : symplecticProjection ω L l.val = 0 := by
    exact (symplecticProjection_ker ω L hL).ge l.property
  have heproj (x : L × Module.Dual K L) : symplecticProjection ω L (e x) = x.2 := by
    change symplecticProjection ω L (x.1.val + s x.2) = x.2
    rw [map_add, hp, zero_add]
    exact LinearMap.congr_fun hs x.2
  have hinj : Function.Injective e := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hx0 : e x = 0 := hx
    have hf : x.2 = 0 := by rw [← heproj x, hx0, map_zero]
    apply Prod.ext
    · apply Subtype.ext
      simpa [e,hf] using hx0
    · exact hf
  have hsurj : Function.Surjective e := by
    intro x
    let f := symplecticProjection ω L x
    have hz : x - s f ∈ L := by
      apply (symplecticProjection_ker ω L hL).le
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr (LinearMap.congr_fun hs f).symm
    refine ⟨(⟨x-s f,hz⟩,f), ?_⟩
    change x - s f + s f = x
    exact sub_add_cancel x (s f)
  refine ⟨LinearEquiv.ofBijective e ⟨hinj,hsurj⟩, ?_, ?_⟩
  · intro l
    change l.val + s 0 = l.val
    simp
  · rintro ⟨l,f⟩ ⟨m,g⟩
    change ω (l.val + s f) (m.val + s g) = g l - f m
    have hLL : ω l.val m.val = 0 := by
      have hm : m.val ∈ ω.orthogonal L := hL.symm ▸ m.property
      exact hm l.val l.property
    have hfg (f : Module.Dual K L) (l : L) : ω l.val (s f) = f l :=
      LinearMap.congr_fun (LinearMap.congr_fun hs f) l
    simp only [map_add, LinearMap.add_apply]
    rw [hLL, hfg,
      ← ha.neg_eq m.val (s f), hfg, hiso]
    ring


 theorem self_orthogonal_twice_finrank (hω : ω.Nondegenerate)
    (hL : ω.orthogonal L = L) : 2 * finrank K L = finrank K E := by
  have h := LinearMap.BilinForm.finrank_orthogonal hω L
  rw [hL] at h
  have hle := Submodule.finrank_le L
  omega

/-- Isometries act transitively on Lagrangians, proved by the corrected
sections above. This is needed to use uniform pair laws in the planted model. -/
 theorem lagrangian_transitivity (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hL : ω.orthogonal L = L)
    (M : Submodule K E) (hM : ω.orthogonal M = M) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧ L.map e.toLinearMap = M := by
  obtain ⟨eL,hEL,hωL⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  obtain ⟨eM,hEM,hωM⟩ := exists_lagrangian_coordinates ω M h2 ha hω hM
  have hdim : finrank K L = finrank K M := by
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω M hω hM
    omega
  let f : L ≃ₗ[K] M := LinearEquiv.ofFinrankEq L M hdim
  let c : (L × Module.Dual K L) ≃ₗ[K] (M × Module.Dual K M) :=
    f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      canonicalSymplectic (c x) (c y) = canonicalSymplectic x y := by
    simp [c,canonicalSymplectic_apply]
  let e := eL.symm.trans (c.trans eM)
  have he (l : L) : e l.val = (f l).val := by
    change eM (c (eL.symm l.val)) = (f l).val
    rw [← hEL l, eL.symm_apply_apply]
    simpa [c] using hEM (f l)
  refine ⟨e, ?_, ?_⟩
  · intro x y
    change ω (eM (c (eL.symm x))) (eM (c (eL.symm y))) = ω x y
    rw [hωM, hc, ← hωL, eL.apply_symm_apply, eL.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change e y ∈ M
      rw [he ⟨y,hy⟩]
      exact (f ⟨y,hy⟩).property
    · intro hx
      let l := f.symm ⟨x,hx⟩
      refine ⟨l.val,l.property, ?_⟩
      change e l.val = x
      rw [he]
      exact congrArg Subtype.val (f.apply_symm_apply ⟨x,hx⟩)

omit [FiniteDimensional K E] in
/-- Orthogonal complement commutes with any form-preserving equivalence. -/
 theorem orthogonal_map_of_isometry (e : E ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = ω x y) (U : Submodule K E) :
    ω.orthogonal (U.map e.toLinearMap) = (ω.orthogonal U).map e.toLinearMap := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro u hu
    rw [← he, e.apply_symm_apply]
    exact hx (e u) ⟨u,hu,rfl⟩
  · rintro ⟨y,hy,rfl⟩ _ ⟨u,hu,rfl⟩
    change ω (e u) (e y) = 0
    rw [he]
    exact hy u hu

noncomputable def lagrangianIsometryEquiv (e : E ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = ω x y) :
    {U : Submodule K E // ω.orthogonal U = U} ≃
    {U : Submodule K E // ω.orthogonal U = U} :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (by
    intro U
    change ω.orthogonal U = U ↔ ω.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap
    rw [orthogonal_map_of_isometry ω e he]
    exact (Submodule.orderIsoMapComap e).injective.eq_iff.symm)

end NormalCoordinates
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section PairCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def verticalSpace : Submodule K (V × Module.Dual K V) :=
  (LinearMap.fst K V (Module.Dual K V)).ker

omit [FiniteDimensional K V] in
@[simp] theorem mem_verticalSpace (p : V × Module.Dual K V) :
    p ∈ verticalSpace (K := K) ↔ p.1 = 0 := Iff.rfl

omit [FiniteDimensional K V] in
 theorem verticalSpace_graph : verticalSpace (K := K) (V := V) = formGraph ⊥ 0 := by
  ext p
  constructor
  · intro hp
    refine ⟨0,hp.symm,?_⟩
    ext u
    change p.2 u.val = 0
    have hu : u.val = 0 := u.property
    rw [hu,map_zero]
  · rintro ⟨u,hu,_⟩
    change p.1 = 0
    exact hu.symm.trans u.property

noncomputable def verticalLagrangian : Lagrangian (K := K) (V := V) :=
  ⟨verticalSpace, by
    rw [verticalSpace_graph]
    exact (graphLagrangian ⊥ ⟨0, LinearMap.BilinForm.isSymm_zero⟩).property⟩

noncomputable def graphVerticalIntersectionEquiv (U : Submodule K V)
    (B : LinearMap.BilinForm K U) :
    U.dualAnnihilator ≃ₗ[K] ↥(formGraph U B ⊓ verticalSpace (K := K) (V := V)) where
  toFun f := ⟨(0,f.val),⟨⟨0,rfl, by
    ext u
    simpa using ((Submodule.mem_dualAnnihilator (W := U) f.val).mp f.property) u u.property⟩,rfl⟩⟩
  invFun p := ⟨p.val.2, by
    obtain ⟨u,hu,hf⟩ := p.property.1
    have hu0 : u = 0 := Subtype.ext (hu.trans p.property.2)
    apply (Submodule.mem_dualAnnihilator (W := U) p.val.2).mpr
    intro x hxU
    have hf' := congrArg (fun l : Module.Dual K U => l ⟨x,hxU⟩) hf
    simpa [hu0] using hf'⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext p.property.2.symm rfl
  map_add' f g := by apply Subtype.ext; simp
  map_smul' a f := by apply Subtype.ext; simp

 theorem graph_vertical_intersection_finrank (U : Submodule K V)
    (B : LinearMap.BilinForm K U) :
    finrank K ↥(formGraph U B ⊓ verticalSpace (K := K) (V := V)) = finrank K V - finrank K U := by
  rw [← (graphVerticalIntersectionEquiv U B).finrank_eq]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  omega

/-- The exact stratum bijection for the intersection with a coordinate
Lagrangian: dimension h is neither approximated nor dropped. -/
noncomputable def pairStratumEquiv (h : ℕ) (hh : h ≤ finrank K V) :
    (Σ U : {U : Submodule K V // finrank K U = finrank K V-h}, SymForm K U.val) ≃
    {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = h} := by
  classical
  let e : (Σ U : {U : Submodule K V // finrank K U = finrank K V-h}, SymForm K U.val) →
      Lagrangian (K := K) (V := V) := fun S => graphLagrangian S.1.val S.2
  have he (S) : finrank K ↥((e S).val ⊓ verticalSpace (K := K) (V := V)) = h := by
    exact (graph_vertical_intersection_finrank S.1.val S.2.val).trans (by
      rw [S.1.property, Nat.sub_sub_self hh])
  refine Equiv.ofBijective (fun S => ⟨e S,he S⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨U,hU⟩,B⟩ ⟨⟨W,hW⟩,C⟩ hEq
    have h : graphLagrangian U B = graphLagrangian W C := congrArg Subtype.val hEq
    have hUW : U = W := by
      have hs : (⟨U,B⟩ : Σ U : Submodule K V, SymForm K U) = ⟨W,C⟩ :=
        (lagrangianGraphEquiv (K := K) (V := V)).injective h
      exact congrArg Sigma.fst hs
    cases hUW
    have hBC := graphLagrangian_form_injective U h
    cases hBC
    rfl
  · rintro ⟨L,hL⟩
    obtain ⟨⟨U,B⟩,hUB⟩ := graphLagrangian_surjective (K := K) (V := V) L
    have hU : finrank K U = finrank K V-h := by
      have hdim : finrank K V-finrank K U = h := by
        rw [← graph_vertical_intersection_finrank U B.val]
        have heq := congrArg (fun L : Lagrangian (K := K) (V := V) =>
          finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V))) hUB
        exact heq.trans hL
      have hle := Submodule.finrank_le U
      omega
    refine ⟨⟨⟨U,hU⟩,B⟩, Subtype.ext hUB⟩

 theorem vertical_pair_count [Fintype K] [Finite V] (h : ℕ) (hh : h ≤ finrank K V) :
    Nat.card {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = h} =
    Nat.card {U : Submodule K V // finrank K U = finrank K V-h} *
      (Fintype.card K)^((finrank K V-h+1).choose 2) := by
  classical
  let := Fintype.ofFinite {U : Submodule K V // finrank K U = finrank K V-h}
  rw [← Nat.card_congr (pairStratumEquiv (K := K) (V := V) h hh), Nat.card_sigma]
  simp only [symForm_card]
  have hd (U : {U : Submodule K V // finrank K U = finrank K V-h}) :
      finrank K U.val = finrank K V-h := U.property
  simp_rw [hd]
  simp [Nat.card_eq_fintype_card]


omit [FiniteDimensional K V] in
 theorem pair_stratum_card_congr (A B : Lagrangian (K := K) (V := V))
    (e : (V × Module.Dual K V) ≃ₗ[K] (V × Module.Dual K V))
    (he : ∀ x y, canonicalSymplectic (e x) (e y) = canonicalSymplectic x y)
    (hAB : A.val.map e.toLinearMap = B.val) (h : ℕ) :
    Nat.card {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ A.val) = h} =
    Nat.card {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ B.val) = h} := by
  let f := lagrangianIsometryEquiv canonicalSymplectic e he
  apply Nat.card_congr (f.subtypeEquiv _)
  intro L
  have hdim : finrank K ↥((f L).val ⊓ B.val) = finrank K ↥(L.val ⊓ A.val) := by
    change finrank K ↥(L.val.map e.toLinearMap ⊓ B.val) = _
    rw [← hAB, ← Submodule.map_inf e.toLinearMap e.injective]
    exact (Submodule.equivMapOfInjective e.toLinearMap e.injective (L.val ⊓ A.val)).finrank_eq.symm
  rw [hdim]



 theorem lagrangian_pair_count [Fintype K] [Finite V] (h2 : (2 : K) ≠ 0)
    (A : Lagrangian (K := K) (V := V)) (h : ℕ) (hh : h ≤ finrank K V) :
    Nat.card {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ A.val) = h} =
    Nat.card {U : Submodule K V // finrank K U = finrank K V-h} *
      (Fintype.card K)^((finrank K V-h+1).choose 2) := by
  obtain ⟨e,he,hAe⟩ := lagrangian_transitivity canonicalSymplectic A.val h2
    canonicalSymplectic_alt canonicalSymplectic_nondegenerate A.property
    verticalLagrangian.val verticalLagrangian.property
  exact (pair_stratum_card_congr A verticalLagrangian e he hAe h).trans
    (vertical_pair_count (K := K) (V := V) h hh)

end PairCounts
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section LinearGlue
variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]
 theorem linear_functional_descend (f : E →ₗ[K] V) (g : E →ₗ[K] K)
    (hk : f.ker ≤ g.ker) : ∃ h : V →ₗ[K] K, h.comp f = g := by
  obtain ⟨p,hp⟩ := f.range.subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr f.range.subtype_injective)
  let e := f.quotKerEquivRange
  let a : V →ₗ[K] E ⧸ f.ker := e.symm.toLinearMap.comp p
  have he (x : E) : a (f x) = f.ker.mkQ x := by
    apply e.injective
    change e (e.symm (p (f x))) = e (f.ker.mkQ x)
    rw [e.apply_symm_apply]
    exact LinearMap.congr_fun hp (f.rangeRestrict x)
  refine ⟨(f.ker.liftQ g hk).comp a, ?_⟩
  ext x
  change f.ker.liftQ g hk (a (f x)) = g x
  rw [he]
  rfl

 theorem linear_functional_glue (U W : Submodule K V) (f : U →ₗ[K] K) (g : W →ₗ[K] K)
    (hfg : ∀ x : ↥(U ⊓ W), f (Submodule.inclusion inf_le_left x) =
      g (Submodule.inclusion inf_le_right x)) :
    ∃ h : V →ₗ[K] K, h.comp U.subtype = f ∧ h.comp W.subtype = g := by
  let a : U × W →ₗ[K] V := U.subtype.comp (LinearMap.fst K U W) +
    W.subtype.comp (LinearMap.snd K U W)
  let b : U × W →ₗ[K] K := f.comp (LinearMap.fst K U W) + g.comp (LinearMap.snd K U W)
  have hab : a.ker ≤ b.ker := by
    rintro x hx
    have hh : x.1.val + x.2.val = 0 := hx
    have he : x.1.val = -x.2.val := eq_neg_of_add_eq_zero_left hh
    let s : ↥(U ⊓ W) := ⟨x.1.val,x.1.property,he ▸ W.neg_mem x.2.property⟩
    have h₁ : Submodule.inclusion (show U ⊓ W ≤ U from inf_le_left) s = x.1 := rfl
    have h₂ : Submodule.inclusion (show U ⊓ W ≤ W from inf_le_right) s = -x.2 := Subtype.ext he
    have hf := hfg s
    rw [h₁,h₂,map_neg] at hf
    change f x.1 + g x.2 = 0
    rw [hf,neg_add_cancel]
  obtain ⟨h,hh⟩ := linear_functional_descend a b hab
  refine ⟨h,?_,?_⟩ <;> ext x
  · have he := LinearMap.congr_fun hh (x,0)
    simpa [a,b] using he
  · have he := LinearMap.congr_fun hh (0,x)
    simpa [a,b] using he
end LinearGlue

section PairLift
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (U W : Submodule K V) (B : LinearMap.BilinForm K U) (C : LinearMap.BilinForm K W)
def graphDifference : LinearMap.BilinForm K ↥(U ⊓ W) :=
  B.compl₁₂ (Submodule.inclusion inf_le_left) (Submodule.inclusion inf_le_left) -
  C.compl₁₂ (Submodule.inclusion inf_le_right) (Submodule.inclusion inf_le_right)

def graphPairProjection : ↥(formGraph U B ⊓ formGraph W C) →ₗ[K] ↥(graphDifference U W B C).ker where
  toFun p := ⟨⟨p.val.1,by
    obtain ⟨u,hu,_⟩ := p.property.1
    obtain ⟨w,hw,_⟩ := p.property.2
    exact ⟨hu ▸ u.property,hw ▸ w.property⟩⟩,by
    apply LinearMap.mem_ker.mpr
    ext z
    obtain ⟨u,hu,hf⟩ := p.property.1
    obtain ⟨w,hw,hg⟩ := p.property.2
    have e₁ : (Submodule.inclusion inf_le_left : ↥(U ⊓ W) →ₗ[K] U) ⟨p.val.1,by
      exact ⟨hu ▸ u.property,hw ▸ w.property⟩⟩ = u := Subtype.ext hu.symm
    have e₂ : (Submodule.inclusion inf_le_right : ↥(U ⊓ W) →ₗ[K] W) ⟨p.val.1,by
      exact ⟨hu ▸ u.property,hw ▸ w.property⟩⟩ = w := Subtype.ext hw.symm
    change B _ _ - C _ _ = 0
    rw [e₁,e₂]
    have h₁ := LinearMap.congr_fun hf (Submodule.inclusion inf_le_left z)
    have h₂ := LinearMap.congr_fun hg (Submodule.inclusion inf_le_right z)
    exact sub_eq_zero.mpr (h₁.symm.trans h₂)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem graphPairProjection_surjective : Function.Surjective (graphPairProjection U W B C) := by
  rintro ⟨x,hx⟩
  have hc (z : ↥(U ⊓ W)) : B (Submodule.inclusion inf_le_left x) (Submodule.inclusion inf_le_left z) =
      C (Submodule.inclusion inf_le_right x) (Submodule.inclusion inf_le_right z) := by
    have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) z
    exact sub_eq_zero.mp h
  obtain ⟨f,hf,hg⟩ := linear_functional_glue U W (B (Submodule.inclusion inf_le_left x))
    (C (Submodule.inclusion inf_le_right x)) hc
  refine ⟨⟨(x.val,f),⟨⟨Submodule.inclusion inf_le_left x,rfl,hf⟩,
    ⟨Submodule.inclusion inf_le_right x,rfl,hg⟩⟩⟩,rfl⟩

noncomputable def graphPairKernelEquiv : (U ⊔ W).dualAnnihilator ≃ₗ[K]
    (graphPairProjection U W B C).ker where
  toFun f := ⟨⟨(0,f.val),⟨⟨0,rfl,by
    ext x
    change f.val x.val = B 0 x
    rw [map_zero,LinearMap.zero_apply]
    exact (Submodule.mem_dualAnnihilator (W := U ⊔ W) f.val).mp f.property x.val ((show U ≤ U ⊔ W from le_sup_left) x.property)⟩,
    ⟨0,rfl,by
    ext x
    change f.val x.val = C 0 x
    rw [map_zero,LinearMap.zero_apply]
    exact (Submodule.mem_dualAnnihilator (W := U ⊔ W) f.val).mp f.property x.val ((show W ≤ U ⊔ W from le_sup_right) x.property)⟩⟩⟩,rfl⟩
  invFun p := ⟨p.val.val.2, by
    apply (Submodule.mem_dualAnnihilator (W := U ⊔ W) p.val.val.2).mpr
    have hzero : p.val.val.1 = 0 := congrArg (fun z : (graphDifference U W B C).ker => z.val.val) p.property
    obtain ⟨u,hu,hf⟩ := p.val.property.1
    obtain ⟨w,hw,hg⟩ := p.val.property.2
    have hu0 : u = 0 := Subtype.ext (hu.trans hzero)
    have hw0 : w = 0 := Subtype.ext (hw.trans hzero)
    intro x hx
    obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    have h₁ := LinearMap.congr_fun hf ⟨y,hy⟩
    have h₂ := LinearMap.congr_fun hg ⟨z,hz⟩
    simp only [hu0,hw0,map_zero,LinearMap.zero_apply,LinearMap.comp_apply,Submodule.subtype_apply] at h₁ h₂
    rw [h₁,h₂,add_zero]⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z : (graphDifference U W B C).ker => z.val.val) p.property).symm rfl
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; simp

 theorem graph_pair_intersection_finrank [FiniteDimensional K V] :
    finrank K ↥(formGraph U B ⊓ formGraph W C) =
      finrank K ↥(U.dualAnnihilator ⊓ W.dualAnnihilator) + finrank K (graphDifference U W B C).ker := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := K)
    (V := ↥(formGraph U B ⊓ formGraph W C)) (V₂ := ↥(graphDifference U W B C).ker)
    (graphPairProjection U W B C)
  rw [LinearMap.range_eq_top.mpr (graphPairProjection_surjective U W B C),finrank_top] at h
  rw [←(graphPairKernelEquiv U W B C).finrank_eq] at h
  rw [Submodule.dualAnnihilator_sup_eq] at h
  omega
end PairLift
end SidorenkoCounterexample

end OAI
