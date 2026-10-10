import Mathlib

namespace OAI

/-! Projective coset transport and subgroup graph orbit calculations. -/

noncomputable section

namespace TwistedCorrespondences

universe u v w

structure ScalarCocycle (G : Type u) [Group G] where
  toFun : G → G → Circle
  one_left' : ∀ g, toFun 1 g = 1
  one_right' : ∀ g, toFun g 1 = 1
  cocycle' : ∀ g h k, toFun g h * toFun (g * h) k = toFun h k * toFun g (h * k)

namespace ScalarCocycle

variable {G : Type u} {H : Type v} {K : Type w}
variable [Group G] [Group H] [Group K]

instance : CoeFun (ScalarCocycle G) (fun _ => G → G → Circle) := ⟨toFun⟩

@[simp] theorem one_left (α : ScalarCocycle G) (g : G) : α 1 g = 1 := α.one_left' g
@[simp] theorem one_right (α : ScalarCocycle G) (g : G) : α g 1 = 1 := α.one_right' g

theorem cocycle (α : ScalarCocycle G) (g h k : G) :
    α g h * α (g * h) k = α h k * α g (h * k) := α.cocycle' g h k

@[ext] theorem ext {α β : ScalarCocycle G} (h : ∀ g k, α g k = β g k) : α = β := by
  cases α
  cases β
  congr
  exact funext fun g => funext (h g)

def trivial (G : Type u) [Group G] : ScalarCocycle G where
  toFun _ _ := 1
  one_left' _ := rfl
  one_right' _ := rfl
  cocycle' _ _ _ := rfl

@[simp] theorem trivial_apply (g h : G) : trivial G g h = 1 := rfl

def pullback (α : ScalarCocycle H) (f : G →* H) : ScalarCocycle G where
  toFun g h := α (f g) (f h)
  one_left' g := by simp
  one_right' g := by simp
  cocycle' g h k := by simpa using α.cocycle (f g) (f h) (f k)

@[simp] theorem pullback_apply (α : ScalarCocycle H) (f : G →* H) (g h : G) :
    α.pullback f g h = α (f g) (f h) := rfl

def mul (α β : ScalarCocycle G) : ScalarCocycle G where
  toFun g h := α g h * β g h
  one_left' g := by simp
  one_right' g := by simp
  cocycle' g h k := by
    calc
      (α g h * β g h) * (α (g * h) k * β (g * h) k) =
          (α g h * α (g * h) k) * (β g h * β (g * h) k) := by ac_rfl
      _ = (α h k * α g (h * k)) * (β h k * β g (h * k)) := by
        rw [α.cocycle, β.cocycle]
      _ = (α h k * β h k) * (α g (h * k) * β g (h * k)) := by ac_rfl

@[simp] theorem mul_apply (α β : ScalarCocycle G) (g h : G) :
    α.mul β g h = α g h * β g h := rfl

def inv (α : ScalarCocycle G) : ScalarCocycle G where
  toFun g h := (α g h)⁻¹
  one_left' g := by simp
  one_right' g := by simp
  cocycle' g h k := by
    simpa only [mul_inv] using congrArg Inv.inv (α.cocycle g h k)

@[simp] theorem inv_apply (α : ScalarCocycle G) (g h : G) :
    α.inv g h = (α g h)⁻¹ := rfl

theorem inv_apply_coe (α : ScalarCocycle G) (g h : G) :
    (α.inv g h : ℂ) = star (α g h : ℂ) := Circle.coe_inv_eq_conj _

def joint (μ : ScalarCocycle G) (ω : ScalarCocycle H) : ScalarCocycle (G × H) :=
  (μ.pullback (MonoidHom.fst G H)).mul ((ω.pullback (MonoidHom.snd G H)).inv)

@[simp] theorem joint_apply (μ : ScalarCocycle G) (ω : ScalarCocycle H)
    (g g' : G) (h h' : H) :
    joint μ ω (g, h) (g', h') = μ g g' * (ω h h')⁻¹ := rfl

theorem joint_apply_coe (μ : ScalarCocycle G) (ω : ScalarCocycle H)
    (g g' : G) (h h' : H) :
    (joint μ ω (g, h) (g', h') : ℂ) = (μ g g' : ℂ) * star (ω h h' : ℂ) := by
  simp only [joint_apply, Circle.coe_mul, Circle.coe_inv_eq_conj, Complex.star_def]

@[simp] theorem joint_mixed (μ : ScalarCocycle G) (ω : ScalarCocycle H)
    (g : G) (h : H) : joint μ ω (g, 1) (1, h) = 1 := by simp

@[simp] theorem joint_mixed_rev (μ : ScalarCocycle G) (ω : ScalarCocycle H)
    (g : G) (h : H) : joint μ ω (1, h) (g, 1) = 1 := by simp

def matchedRatio (μ : ScalarCocycle G) (ω : ScalarCocycle H)
    {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B) : ScalarCocycle A :=
  (μ.pullback A.subtype).mul ((ω.pullback (B.subtype.comp δ.toMonoidHom)).inv)

@[simp] theorem matchedRatio_apply (μ : ScalarCocycle G) (ω : ScalarCocycle H)
    {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B) (a b : A) :
    matchedRatio μ ω δ a b = μ a b / ω (δ a) (δ b) := rfl

end ScalarCocycle

structure ProjectiveUnitaryRepresentation {G : Type u} [Group G]
    (α : ScalarCocycle G) (V : Type v) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  op : G → V ≃ₗᵢ[ℂ] V
  op_one : op 1 = LinearIsometryEquiv.refl ℂ V
  op_mul : ∀ g h ξ, op g (op h ξ) = (α g h : ℂ) • op (g * h) ξ

namespace ProjectiveUnitaryRepresentation

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {V : Type w} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def pullback {α : ScalarCocycle H} (π : ProjectiveUnitaryRepresentation α V)
    (f : G →* H) : ProjectiveUnitaryRepresentation (α.pullback f) V where
  op g := π.op (f g)
  op_one := by simpa using π.op_one
  op_mul g h ξ := by simpa using π.op_mul (f g) (f h) ξ

def joint {μ : ScalarCocycle G} {ω : ScalarCocycle H}
    (π : ProjectiveUnitaryRepresentation μ V)
    (ρ : ProjectiveUnitaryRepresentation ω.inv V)
    (comm : ∀ g h ξ, ρ.op h (π.op g ξ) = π.op g (ρ.op h ξ)) :
    ProjectiveUnitaryRepresentation (μ.joint ω) V where
  op s := (ρ.op s.2).trans (π.op s.1)
  op_one := by
    ext ξ
    simp [π.op_one, ρ.op_one]
  op_mul s t ξ := by
    change π.op s.1 (ρ.op s.2 (π.op t.1 (ρ.op t.2 ξ))) =
      ((μ.joint ω) s t : ℂ) • π.op (s.1 * t.1) (ρ.op (s.2 * t.2) ξ)
    rw [comm, π.op_mul, ρ.op_mul, map_smul, smul_smul]
    rfl

end ProjectiveUnitaryRepresentation

section Graphs

variable {G : Type u} {H : Type v} [Group G] [Group H]

def graphHom {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B) : A →* G × H :=
  A.subtype.prod (B.subtype.comp δ.toMonoidHom)

@[simp] theorem graphHom_apply {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B)
    (a : A) : graphHom δ a = ((a : G), (δ a : H)) := rfl

def graphSubgroup {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B) : Subgroup (G × H) :=
  (graphHom δ).range

@[simp] theorem mem_graphSubgroup {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B)
    (s : G × H) : s ∈ graphSubgroup δ ↔ ∃ a : A, ((a : G), (δ a : H)) = s := Iff.rfl

theorem graph_kernel_left {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B)
    {g : G} (hg : (g, (1 : H)) ∈ graphSubgroup δ) : g = 1 := by
  obtain ⟨a, ha⟩ := (mem_graphSubgroup δ _).1 hg
  have hδ : δ a = 1 := Subtype.ext (congrArg Prod.snd ha)
  have ha₁ : a = 1 := δ.injective (hδ.trans (map_one δ).symm)
  simpa [ha₁] using (congrArg Prod.fst ha).symm

theorem graph_kernel_right {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B)
    {h : H} (hh : ((1 : G), h) ∈ graphSubgroup δ) : h = 1 := by
  obtain ⟨a, ha⟩ := (mem_graphSubgroup δ _).1 hh
  have ha₁ : a = 1 := Subtype.ext (congrArg Prod.fst ha)
  simpa [ha₁] using (congrArg Prod.snd ha).symm

theorem graph_map_fst {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B) :
    (graphSubgroup δ).map (MonoidHom.fst G H) = A := by
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_graphSubgroup δ _).1 hs
    exact a.property
  · intro hg
    refine ⟨((g : G), (δ ⟨g, hg⟩ : H)), ?_, rfl⟩
    exact (mem_graphSubgroup δ _).2 ⟨⟨g, hg⟩, rfl⟩

theorem graph_map_snd {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B) :
    (graphSubgroup δ).map (MonoidHom.snd G H) = B := by
  ext h
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_graphSubgroup δ _).1 hs
    exact (δ a).property
  · intro hh
    refine ⟨((δ.symm ⟨h, hh⟩ : G), h), ?_, rfl⟩
    refine (mem_graphSubgroup δ _).2 ⟨δ.symm ⟨h, hh⟩, ?_⟩
    simp

theorem joint_pullback_graph (μ : ScalarCocycle G) (ω : ScalarCocycle H)
    {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B) :
    (μ.joint ω).pullback (graphHom δ) = μ.matchedRatio ω δ := by
  ext a b
  rfl

theorem graph_multiplier {V : Type w} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {μ : ScalarCocycle G} {ω : ScalarCocycle H}
    (π : ProjectiveUnitaryRepresentation μ V)
    (ρ : ProjectiveUnitaryRepresentation ω.inv V)
    (comm : ∀ g h ξ, ρ.op h (π.op g ξ) = π.op g (ρ.op h ξ))
    {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B) (a b : A) (ξ : V) :
    π.op a (ρ.op (δ a) (π.op b (ρ.op (δ b) ξ))) =
      ((μ a b : ℂ) / (ω (δ a) (δ b) : ℂ)) •
        π.op (a * b) (ρ.op (δ (a * b)) ξ) := by
  simpa [ProjectiveUnitaryRepresentation.joint, div_eq_mul_inv, map_mul] using
    (π.joint ρ comm).op_mul (graphHom δ a) (graphHom δ b) ξ

theorem exists_graph_of_coordinate_kernels (C : Subgroup (G × H))
    (hG : ∀ g : G, (g, (1 : H)) ∈ C → g = 1)
    (hH : ∀ h : H, ((1 : G), h) ∈ C → h = 1) :
    ∃ δ : C.map (MonoidHom.fst G H) ≃* C.map (MonoidHom.snd G H),
      C = graphSubgroup δ := by
  let p := (MonoidHom.fst G H).subgroupMap C
  let q := (MonoidHom.snd G H).subgroupMap C
  have hp : Function.Injective p := by
    apply (injective_iff_map_eq_one p).2
    intro c hc
    have hc₁ : (c : G × H).1 = 1 := congrArg Subtype.val hc
    have hc₂ : (c : G × H).2 = 1 := by
      apply hH
      simpa only [← hc₁, Prod.mk.eta] using c.property
    apply Subtype.ext
    exact Prod.ext hc₁ hc₂
  have hq : Function.Injective q := by
    apply (injective_iff_map_eq_one q).2
    intro c hc
    have hc₂ : (c : G × H).2 = 1 := congrArg Subtype.val hc
    have hc₁ : (c : G × H).1 = 1 := by
      apply hG
      simpa only [← hc₂, Prod.mk.eta] using c.property
    apply Subtype.ext
    exact Prod.ext hc₁ hc₂
  let ep : C ≃* C.map (MonoidHom.fst G H) :=
    MulEquiv.ofBijective p ⟨hp, (MonoidHom.fst G H).subgroupMap_surjective C⟩
  let eq : C ≃* C.map (MonoidHom.snd G H) :=
    MulEquiv.ofBijective q ⟨hq, (MonoidHom.snd G H).subgroupMap_surjective C⟩
  let δ := ep.symm.trans eq
  refine ⟨δ, ?_⟩
  ext s
  rw [mem_graphSubgroup]
  constructor
  · intro hs
    let c : C := ⟨s, hs⟩
    refine ⟨ep c, ?_⟩
    have hc : δ (ep c) = eq c := by simp [δ]
    simp only [hc]
    rfl
  · rintro ⟨a, ha⟩
    have hc : ((ep.symm a : C) : G × H) = ((a : G), (δ a : H)) := by
      apply Prod.ext
      · exact congrArg Subtype.val (ep.apply_symm_apply a)
      · rfl
    rw [← ha, ← hc]
    exact (ep.symm a).property

theorem stabilizer_is_graph {X : Type w} [MulAction (G × H) X] (x : X)
    (hG : ∀ g : G, (g, (1 : H)) • x = x → g = 1)
    (hH : ∀ h : H, ((1 : G), h) • x = x → h = 1) :
    ∃ δ : (MulAction.stabilizer (G × H) x).map (MonoidHom.fst G H) ≃*
        (MulAction.stabilizer (G × H) x).map (MonoidHom.snd G H),
      MulAction.stabilizer (G × H) x = graphSubgroup δ := by
  apply exists_graph_of_coordinate_kernels
  · exact hG
  · exact hH

end Graphs

section GraphCosets

variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem graph_cosets_free_left {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B)
    (g : G) (x : (G × H) ⧸ graphSubgroup δ)
    (hg : (g, (1 : H)) • x = x) : g = 1 := by
  induction x using Quotient.inductionOn with
  | h r =>
    change (((g, (1 : H)) * r : G × H) : (G × H) ⧸ graphSubgroup δ) =
      (r : (G × H) ⧸ graphSubgroup δ) at hg
    have hr := QuotientGroup.eq.mp hg
    have heq : ((g, (1 : H)) * r)⁻¹ * r = (r.1⁻¹ * g⁻¹ * r.1, (1 : H)) := by
      apply Prod.ext <;> simp [mul_inv_rev, mul_assoc]
    have hk : (r.1⁻¹ * g⁻¹ * r.1, (1 : H)) ∈ graphSubgroup δ := heq ▸ hr
    have hk₁ := graph_kernel_left δ hk
    have hi : g⁻¹ = 1 := by
      calc
        g⁻¹ = r.1 * (r.1⁻¹ * g⁻¹ * r.1) * r.1⁻¹ := by group
        _ = 1 := by rw [hk₁]; group
    simpa using hi

theorem graph_cosets_free_right {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B)
    (h : H) (x : (G × H) ⧸ graphSubgroup δ)
    (hh : ((1 : G), h) • x = x) : h = 1 := by
  induction x using Quotient.inductionOn with
  | h r =>
    change ((((1 : G), h) * r : G × H) : (G × H) ⧸ graphSubgroup δ) =
      (r : (G × H) ⧸ graphSubgroup δ) at hh
    have hr := QuotientGroup.eq.mp hh
    have heq : (((1 : G), h) * r)⁻¹ * r = ((1 : G), r.2⁻¹ * h⁻¹ * r.2) := by
      apply Prod.ext <;> simp [mul_inv_rev, mul_assoc]
    have hk : ((1 : G), r.2⁻¹ * h⁻¹ * r.2) ∈ graphSubgroup δ := heq ▸ hr
    have hk₂ := graph_kernel_right δ hk
    have hi : h⁻¹ = 1 := by
      calc
        h⁻¹ = r.2 * (r.2⁻¹ * h⁻¹ * r.2) * r.2⁻¹ := by group
        _ = 1 := by rw [hk₂]; group
    simpa using hi

def leftCosetOrbitRel (C : Subgroup (G × H)) : Setoid ((G × H) ⧸ C) :=
  letI := MulAction.compHom ((G × H) ⧸ C) (MonoidHom.inl G H)
  MulAction.orbitRel G ((G × H) ⧸ C)

@[simp] theorem leftCosetOrbitRel_iff (C : Subgroup (G × H)) (x y : (G × H) ⧸ C) :
    leftCosetOrbitRel C x y ↔ ∃ g : G, (g, (1 : H)) • y = x := Iff.rfl

def sndCosetProjection (C : Subgroup (G × H)) :
    (G × H) ⧸ C → H ⧸ C.map (MonoidHom.snd G H) :=
  Quotient.lift (fun r : G × H => (r.2 : H ⧸ C.map (MonoidHom.snd G H))) (by
    intro r s hrs
    apply QuotientGroup.eq.mpr
    exact ⟨r⁻¹ * s, QuotientGroup.leftRel_apply.mp hrs, rfl⟩)

@[simp] theorem sndCosetProjection_mk (C : Subgroup (G × H)) (r : G × H) :
    sndCosetProjection C (r : (G × H) ⧸ C) =
      (r.2 : H ⧸ C.map (MonoidHom.snd G H)) := rfl

@[simp] theorem sndCosetProjection_smul (C : Subgroup (G × H)) (g : G)
    (x : (G × H) ⧸ C) :
    sndCosetProjection C ((g, (1 : H)) • x) = sndCosetProjection C x := by
  induction x using Quotient.inductionOn with
  | h r =>
    change ((((g, (1 : H)) * r).2 : H) : H ⧸ C.map (MonoidHom.snd G H)) =
      (r.2 : H ⧸ C.map (MonoidHom.snd G H))
    simp

theorem sndCosetProjection_eq_iff (C : Subgroup (G × H)) (x y : (G × H) ⧸ C) :
    sndCosetProjection C x = sndCosetProjection C y ↔ leftCosetOrbitRel C x y := by
  constructor
  · induction x using Quotient.inductionOn with
    | h r =>
      induction y using Quotient.inductionOn with
      | h s =>
        intro hrs
        obtain ⟨c, hc, hc₂⟩ := QuotientGroup.eq.mp hrs
        refine ⟨r.1 * c.1 * s.1⁻¹, ?_⟩
        change ((((r.1 * c.1 * s.1⁻¹, (1 : H)) * s : G × H)) : (G × H) ⧸ C) =
          (r : (G × H) ⧸ C)
        apply Eq.symm
        apply QuotientGroup.eq.mpr
        have heq : r⁻¹ * ((r.1 * c.1 * s.1⁻¹, (1 : H)) * s) = c := by
          apply Prod.ext
          · simp [mul_assoc]
          · simpa using hc₂.symm
        rw [heq]
        exact hc
  · rintro ⟨g, rfl⟩
    exact sndCosetProjection_smul C g y

def leftCosetOrbitEquiv (C : Subgroup (G × H)) :
    Quotient (leftCosetOrbitRel C) ≃ H ⧸ C.map (MonoidHom.snd G H) := by
  let f : Quotient (leftCosetOrbitRel C) → H ⧸ C.map (MonoidHom.snd G H) :=
    Quotient.lift (sndCosetProjection C)
      (fun x y hxy => (sndCosetProjection_eq_iff C x y).mpr hxy)
  apply Equiv.ofBijective f
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h r =>
      induction y using Quotient.inductionOn with
      | h s =>
        intro hrs
        exact Quotient.sound ((sndCosetProjection_eq_iff C r s).mp hrs)
  · intro y
    induction y using Quotient.inductionOn with
    | h h =>
      exact ⟨Quotient.mk _ (((1 : G), h) : (G × H) ⧸ C), rfl⟩

theorem graph_left_orbit_count {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B) :
    Nat.card (Quotient (leftCosetOrbitRel (graphSubgroup δ))) = B.index := by
  calc
    _ = Nat.card (H ⧸ (graphSubgroup δ).map (MonoidHom.snd G H)) :=
      Nat.card_congr (leftCosetOrbitEquiv (graphSubgroup δ))
    _ = B.index := by rw [graph_map_snd]; rfl

theorem snd_finiteIndex_of_finite_orbits (C : Subgroup (G × H))
    [Finite (Quotient (leftCosetOrbitRel C))] :
    (C.map (MonoidHom.snd G H)).FiniteIndex := by
  have : Finite (H ⧸ C.map (MonoidHom.snd G H)) :=
    Finite.of_equiv (Quotient (leftCosetOrbitRel C)) (leftCosetOrbitEquiv C)
  exact Subgroup.finiteIndex_of_finite_quotient

def rightCosetOrbitRel (C : Subgroup (G × H)) : Setoid ((G × H) ⧸ C) :=
  letI := MulAction.compHom ((G × H) ⧸ C) (MonoidHom.inr G H)
  MulAction.orbitRel H ((G × H) ⧸ C)

@[simp] theorem rightCosetOrbitRel_iff (C : Subgroup (G × H)) (x y : (G × H) ⧸ C) :
    rightCosetOrbitRel C x y ↔ ∃ h : H, ((1 : G), h) • y = x := Iff.rfl

def fstCosetProjection (C : Subgroup (G × H)) :
    (G × H) ⧸ C → G ⧸ C.map (MonoidHom.fst G H) :=
  Quotient.lift (fun r : G × H => (r.1 : G ⧸ C.map (MonoidHom.fst G H))) (by
    intro r s hrs
    apply QuotientGroup.eq.mpr
    exact ⟨r⁻¹ * s, QuotientGroup.leftRel_apply.mp hrs, rfl⟩)

@[simp] theorem fstCosetProjection_mk (C : Subgroup (G × H)) (r : G × H) :
    fstCosetProjection C (r : (G × H) ⧸ C) =
      (r.1 : G ⧸ C.map (MonoidHom.fst G H)) := rfl

@[simp] theorem fstCosetProjection_smul (C : Subgroup (G × H)) (h : H)
    (x : (G × H) ⧸ C) :
    fstCosetProjection C (((1 : G), h) • x) = fstCosetProjection C x := by
  induction x using Quotient.inductionOn with
  | h r =>
    change (((((1 : G), h) * r).1 : G) : G ⧸ C.map (MonoidHom.fst G H)) =
      (r.1 : G ⧸ C.map (MonoidHom.fst G H))
    simp

theorem fstCosetProjection_eq_iff (C : Subgroup (G × H)) (x y : (G × H) ⧸ C) :
    fstCosetProjection C x = fstCosetProjection C y ↔ rightCosetOrbitRel C x y := by
  constructor
  · induction x using Quotient.inductionOn with
    | h r =>
      induction y using Quotient.inductionOn with
      | h s =>
        intro hrs
        obtain ⟨c, hc, hc₁⟩ := QuotientGroup.eq.mp hrs
        refine ⟨r.2 * c.2 * s.2⁻¹, ?_⟩
        change (((((1 : G), r.2 * c.2 * s.2⁻¹) * s : G × H)) : (G × H) ⧸ C) =
          (r : (G × H) ⧸ C)
        apply Eq.symm
        apply QuotientGroup.eq.mpr
        have heq : r⁻¹ * (((1 : G), r.2 * c.2 * s.2⁻¹) * s) = c := by
          apply Prod.ext
          · simpa using hc₁.symm
          · simp [mul_assoc]
        rw [heq]
        exact hc
  · rintro ⟨h, rfl⟩
    exact fstCosetProjection_smul C h y

def rightCosetOrbitEquiv (C : Subgroup (G × H)) :
    Quotient (rightCosetOrbitRel C) ≃ G ⧸ C.map (MonoidHom.fst G H) := by
  let f : Quotient (rightCosetOrbitRel C) → G ⧸ C.map (MonoidHom.fst G H) :=
    Quotient.lift (fstCosetProjection C)
      (fun x y hxy => (fstCosetProjection_eq_iff C x y).mpr hxy)
  apply Equiv.ofBijective f
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h r =>
      induction y using Quotient.inductionOn with
      | h s =>
        intro hrs
        exact Quotient.sound ((fstCosetProjection_eq_iff C r s).mp hrs)
  · intro y
    induction y using Quotient.inductionOn with
    | h g =>
      exact ⟨Quotient.mk _ ((g, (1 : H)) : (G × H) ⧸ C), rfl⟩

theorem graph_right_orbit_count {A : Subgroup G} {B : Subgroup H} (δ : A ≃* B) :
    Nat.card (Quotient (rightCosetOrbitRel (graphSubgroup δ))) = A.index := by
  calc
    _ = Nat.card (G ⧸ (graphSubgroup δ).map (MonoidHom.fst G H)) :=
      Nat.card_congr (rightCosetOrbitEquiv (graphSubgroup δ))
    _ = A.index := by rw [graph_map_fst]; rfl

theorem fst_finiteIndex_of_finite_orbits (C : Subgroup (G × H))
    [Finite (Quotient (rightCosetOrbitRel C))] :
    (C.map (MonoidHom.fst G H)).FiniteIndex := by
  have : Finite (G ⧸ C.map (MonoidHom.fst G H)) :=
    Finite.of_equiv (Quotient (rightCosetOrbitRel C)) (rightCosetOrbitEquiv C)
  exact Subgroup.finiteIndex_of_finite_quotient

theorem finiteIndex_graph_of_coordinate_kernels (C : Subgroup (G × H))
    (hG : ∀ g : G, (g, (1 : H)) ∈ C → g = 1)
    (hH : ∀ h : H, ((1 : G), h) ∈ C → h = 1)
    [Finite (Quotient (leftCosetOrbitRel C))]
    [Finite (Quotient (rightCosetOrbitRel C))] :
    ∃ (A : Subgroup G) (B : Subgroup H),
      A.FiniteIndex ∧ B.FiniteIndex ∧ ∃ δ : A ≃* B, C = graphSubgroup δ := by
  exact ⟨C.map (MonoidHom.fst G H), C.map (MonoidHom.snd G H),
    fst_finiteIndex_of_finite_orbits C, snd_finiteIndex_of_finite_orbits C,
    exists_graph_of_coordinate_kernels C hG hH⟩

end GraphCosets

namespace ScalarCocycle
variable {D : Type*} [Group D]

theorem induction_scalar (α : ScalarCocycle D) (s t r₀ r₁ r₂ : D) :
    let a := r₂⁻¹ * s * r₁
    let b := r₁⁻¹ * t * r₀
    (α s r₁ / α r₂ a) * (α t r₀ / α r₁ b) * α a b =
      α s t * (α (s * t) r₀ / α r₂ (a * b)) := by
  dsimp only
  let a := r₂⁻¹ * s * r₁
  let b := r₁⁻¹ * t * r₀
  change (α s r₁ / α r₂ a) * (α t r₀ / α r₁ b) * α a b =
    α s t * (α (s * t) r₀ / α r₂ (a * b))
  have ha : r₂ * a = s * r₁ := by dsimp [a]; group
  have hb : r₁ * b = t * r₀ := by dsimp [b]; group
  have h₃ := α.cocycle r₂ a b
  rw [ha] at h₃
  have h₂ := α.cocycle s r₁ b
  rw [hb] at h₂
  have hx : α a b = (α r₂ a * α (s * r₁) b) / α r₂ (a * b) :=
    eq_div_iff_mul_eq'.mpr h₃.symm
  calc
    _ = α t r₀ * ((α s r₁ * α (s * r₁) b) / α r₁ b) / α r₂ (a * b) := by
      rw [hx]
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ = (α t r₀ * α s (t * r₀)) / α r₂ (a * b) := by
      rw [h₂]
      simp [div_eq_mul_inv, mul_comm, mul_assoc]
    _ = (α s t * α (s * t) r₀) / α r₂ (a * b) := by rw [← α.cocycle]
    _ = _ := by simp only [mul_div_assoc]
end ScalarCocycle

def circleSmul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (z : Circle) : V ≃ₗᵢ[ℂ] V where
  toFun ξ := (z : ℂ) • ξ
  invFun ξ := ((z⁻¹ : Circle) : ℂ) • ξ
  left_inv ξ := by simp [smul_smul]
  right_inv ξ := by simp [smul_smul]
  map_add' ξ η := smul_add _ _ _
  map_smul' c ξ := by simp only [RingHom.id_apply, smul_smul, mul_comm]
  norm_map' ξ := by simp [norm_smul, Circle.norm_coe]

@[simp] theorem circleSmul_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (z : Circle) (ξ : V) : circleSmul z ξ = (z : ℂ) • ξ := rfl

structure CosetSection {D : Type*} [Group D] (C : Subgroup D) where
  rep : D ⧸ C → D
  rep_spec : ∀ x, (rep x : D ⧸ C) = x
  rep_one : rep ((1 : D) : D ⧸ C) = 1

namespace CosetSection
variable {D : Type*} [Group D] {C : Subgroup D}

noncomputable def choose (C : Subgroup D) : CosetSection C := by
  classical
  exact {
    rep := fun x => if x = ((1 : D) : D ⧸ C) then 1 else x.out
    rep_spec := fun x => by
      split_ifs with h
      · exact h.symm
      · exact Quotient.out_eq' x
    rep_one := by simp }

def correction (r : CosetSection C) (s : D) (x : D ⧸ C) : C := by
  refine ⟨(r.rep (s • x))⁻¹ * s * r.rep x, ?_⟩
  have heq : (r.rep (s • x) : D ⧸ C) = (s * r.rep x : D) := by
    rw [r.rep_spec]
    change s • x = s • (r.rep x : D ⧸ C)
    rw [r.rep_spec]
  simpa only [mul_assoc] using QuotientGroup.eq.mp heq

@[simp] theorem correction_coe (r : CosetSection C) (s : D) (x : D ⧸ C) :
    (r.correction s x : D) = (r.rep (s • x))⁻¹ * s * r.rep x := rfl

@[simp] theorem correction_one (r : CosetSection C) (x : D ⧸ C) :
    r.correction 1 x = 1 := by
  apply Subtype.ext
  simp

theorem correction_mul (r : CosetSection C) (s t : D) (x : D ⧸ C) :
    r.correction s (t • x) * r.correction t x = r.correction (s * t) x := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, correction_coe, mul_smul]
  group

def transportScalar (r : CosetSection C) (α : ScalarCocycle D) (s : D) (x : D ⧸ C) :
    Circle := α s (r.rep x) / α (r.rep (s • x)) (r.correction s x)

@[simp] theorem transportScalar_one (r : CosetSection C) (α : ScalarCocycle D)
    (x : D ⧸ C) : r.transportScalar α 1 x = 1 := by
  simp [transportScalar]

theorem transportScalar_mul (r : CosetSection C) (α : ScalarCocycle D)
    (s t : D) (x : D ⧸ C) :
    r.transportScalar α s (t • x) * r.transportScalar α t x *
        α (r.correction s (t • x)) (r.correction t x) =
      α s t * r.transportScalar α (s * t) x := by
  have hc : ((r.correction s (t • x) : D) * r.correction t x) =
      (r.correction (s * t) x : D) := congrArg Subtype.val (r.correction_mul s t x)
  have h := α.induction_scalar s t (r.rep x) (r.rep (t • x)) (r.rep (s • t • x))
  change r.transportScalar α s (t • x) * r.transportScalar α t x *
      α (r.correction s (t • x)) (r.correction t x) =
    _ at h
  change _ = α s t * (α (s * t) (r.rep x) /
    α (r.rep (s • t • x)) ((r.correction s (t • x) : D) * r.correction t x)) at h
  rw [hc] at h
  simpa only [transportScalar, mul_smul] using h

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def transport (r : CosetSection C) {α : ScalarCocycle D}
    (γ : ProjectiveUnitaryRepresentation (α.pullback C.subtype) V)
    (s : D) (x : D ⧸ C) : V ≃ₗᵢ[ℂ] V :=
  (γ.op (r.correction s x)).trans (circleSmul (r.transportScalar α s x))

@[simp] theorem transport_apply (r : CosetSection C) {α : ScalarCocycle D}
    (γ : ProjectiveUnitaryRepresentation (α.pullback C.subtype) V)
    (s : D) (x : D ⧸ C) (ξ : V) :
    r.transport γ s x ξ =
      (r.transportScalar α s x : ℂ) • (γ.op (r.correction s x) ξ) := rfl

@[simp] theorem transport_one (r : CosetSection C) {α : ScalarCocycle D}
    (γ : ProjectiveUnitaryRepresentation (α.pullback C.subtype) V) (x : D ⧸ C) :
    r.transport γ 1 x = LinearIsometryEquiv.refl ℂ V := by
  ext ξ
  simp [γ.op_one]

theorem transport_mul (r : CosetSection C) {α : ScalarCocycle D}
    (γ : ProjectiveUnitaryRepresentation (α.pullback C.subtype) V)
    (s t : D) (x : D ⧸ C) (ξ : V) :
    r.transport γ s (t • x) (r.transport γ t x ξ) =
      (α s t : ℂ) • r.transport γ (s * t) x ξ := by
  have hscalar : (r.transportScalar α s (t • x) : ℂ) *
      (r.transportScalar α t x : ℂ) *
      (α (r.correction s (t • x)) (r.correction t x) : ℂ) =
      (α s t : ℂ) * (r.transportScalar α (s * t) x : ℂ) := by
    simpa only [Circle.coe_mul] using
      congrArg (fun z : Circle => (z : ℂ)) (r.transportScalar_mul α s t x)
  change (r.transportScalar α s (t • x) : ℂ) •
      γ.op (r.correction s (t • x))
        ((r.transportScalar α t x : ℂ) • γ.op (r.correction t x) ξ) =
    (α s t : ℂ) • ((r.transportScalar α (s * t) x : ℂ) •
      γ.op (r.correction (s * t) x) ξ)
  rw [map_smul, γ.op_mul]
  simp only [ScalarCocycle.pullback_apply, Subgroup.coe_subtype, smul_smul]
  rw [← mul_assoc, hscalar, r.correction_mul]
end CosetSection

end TwistedCorrespondences

end

end OAI
