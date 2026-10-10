import Mathlib
import OAI.GroupTheory.ArithmeticGerms.Basic

namespace OAI

/-! Projective Hilbert bundles and exact induction. -/

namespace GermBundles
attribute [local instance] Classical.propDecidable
open scoped BigOperators InnerProductSpace

structure ScalarCocycle (K : Type*) [Group K] where
  val : K → K → Circle
  mul_assoc : ∀ g h j, val g h * val (g * h) j = val h j * val g (h * j)
  one_left : ∀ g, val 1 g = 1
  one_right : ∀ g, val g 1 = 1

section Bundles

variable {K X : Type*} [Group K] [MulAction K X]
variable (α : ScalarCocycle K) (E : X → Type*)
variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]

attribute [local instance] Classical.propDecidable

structure ProjectiveBundle where
  action : K → lp E 2 ≃ₗᵢ[ℂ] lp E 2
  fibre : ∀ (k : K) (x y : X), k • x = y → E x ≃ₗᵢ[ℂ] E y
  action_single : ∀ (k : K) (x y : X) (h : k • x = y) (v : E x),
    action k (lp.single 2 x v) = lp.single 2 y (fibre k x y h v)
  action_one : ∀ v, action 1 v = v
  action_mul : ∀ g h v, action g (action h v) =
    (α.val g h : ℂ) • action (g * h) v

variable {α E}

variable {F : X → Type*}
variable [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]

def Intertwines (B : ProjectiveBundle α E) (C : ProjectiveBundle α F)
    (T : lp E 2 →L[ℂ] lp F 2) : Prop :=
  ∀ k v, T (B.action k v) = C.action k (T v)

end Bundles

section BuildBundle

variable {X : Type*} {E F : X → Type*}
variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
variable [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]

private theorem relabel_pi_apply (e : X ≃ X)
    (u : ∀ x y, e x = y → E x ≃ₗᵢ[ℂ] F y) (f : ∀ x, E x) (x : X) :
    u (e.symm (e x)) (e x) (e.apply_symm_apply (e x)) (f (e.symm (e x))) =
      u x (e x) rfl (f x) := by
  have haux (z : X) (hz : z = x) (he : e z = e x) :
      u z (e x) he (f z) = u x (e x) rfl (f x) := by
    subst z
    rfl
  exact haux (e.symm (e x)) (e.symm_apply_apply x) (e.apply_symm_apply (e x))

private theorem relabel_pi_right (e : X ≃ X)
    (u : ∀ x y, e x = y → E x ≃ₗᵢ[ℂ] F y) (f : ∀ x, F x) (y : X) :
    u (e.symm y) y (e.apply_symm_apply y)
      ((u (e.symm y) (e (e.symm y)) rfl).symm (f (e (e.symm y)))) = f y := by
  have haux (x y : X) (he : e x = y) :
      u x y he ((u x (e x) rfl).symm (f (e x))) = f y := by
    subst y
    exact (u x (e x) rfl).apply_symm_apply _
  exact haux (e.symm y) y (e.apply_symm_apply y)

noncomputable def relabel (e : X ≃ X)
    (u : ∀ x y, e x = y → E x ≃ₗᵢ[ℂ] F y) : lp E 2 ≃ₗᵢ[ℂ] lp F 2 where
  toLinearEquiv :=
    { toFun := fun v => ⟨fun y => u (e.symm y) y (e.apply_symm_apply y) (v (e.symm y)), by
        apply memℓp_gen
        convert! ((lp.memℓp v).summable (by norm_num)).comp_injective e.symm.injective using 1
        all_goals first | rfl | (simp only [LinearIsometryEquiv.norm_map]; rfl)⟩
      invFun := fun v => ⟨fun x => (u x (e x) rfl).symm (v (e x)), by
        apply memℓp_gen
        convert! ((lp.memℓp v).summable (by norm_num)).comp_injective e.injective using 1
        all_goals first | rfl | (simp only [LinearIsometryEquiv.norm_map]; rfl)⟩
      left_inv := by
        intro v
        apply lp.ext
        funext x
        change (u x (e x) rfl).symm
          (u (e.symm (e x)) (e x) (e.apply_symm_apply (e x)) (v.val (e.symm (e x)))) = v.val x
        exact (congrArg (u x (e x) rfl).symm (relabel_pi_apply e u (fun i => v i) x)).trans
          ((u x (e x) rfl).symm_apply_apply (v x))
      right_inv := by
        intro v
        apply lp.ext
        funext y
        exact relabel_pi_right e u (fun i => v i) y
      map_add' := by
        intro v w
        apply lp.ext
        funext y
        change u _ _ _ (v _ + w _) = u _ _ _ (v _) + u _ _ _ (w _)
        exact map_add _ _ _
      map_smul' := by
        intro a v
        apply lp.ext
        funext y
        change u _ _ _ (a • v _) = a • u _ _ _ (v _)
        exact map_smul _ _ _ }
  norm_map' := by
    intro v
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    change (∑' y, ‖u (e.symm y) y (e.apply_symm_apply y) (v (e.symm y))‖ ^ (2 : ENNReal).toReal) = _
    simp only [LinearIsometryEquiv.norm_map]
    convert! e.symm.tsum_eq (fun x => ‖v x‖ ^ (2 : ENNReal).toReal) using 1

theorem relabel_apply (e : X ≃ X) (u : ∀ x y, e x = y → E x ≃ₗᵢ[ℂ] F y)
    (v : lp E 2) (x y : X) (h : e x = y) : relabel e u v y = u x y h (v x) := by
  subst y
  change u (e.symm (e x)) (e x) (e.apply_symm_apply (e x)) (v.val (e.symm (e x))) = u x (e x) rfl (v.val x)
  exact relabel_pi_apply e u (fun i => v i) x

theorem relabel_single (e : X ≃ X) (u : ∀ x y, e x = y → E x ≃ₗᵢ[ℂ] F y)
    (x y : X) (h : e x = y) (v : E x) :
    relabel e u (lp.single 2 x v) = lp.single 2 y (u x y h v) := by
  apply lp.ext
  funext z
  by_cases hz : z = y
  · subst z
    rw [relabel_apply e u _ x y h, lp.single_apply_self, lp.single_apply_self]
  · have hn : e.symm z ≠ x := by
      intro he
      apply hz
      rw [← h, ← he, e.apply_symm_apply]
    change u (e.symm z) z (e.apply_symm_apply z) ((lp.single 2 x v) (e.symm z)) = _
    rw [lp.single_apply_ne 2 x v hn, map_zero, lp.single_apply_ne 2 y _ hz]

end BuildBundle

section FibreSystem

variable {K X : Type*} [Group K] [MulAction K X]
variable (α : ScalarCocycle K) (E : X → Type*)
variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]

structure FibreSystem where
  unitary : ∀ (k : K) (x y : X), k • x = y → E x ≃ₗᵢ[ℂ] E y
  one : ∀ x v, unitary 1 x x (one_smul K x) v = v
  mul : ∀ g h x y z (hy : h • x = y) (hz : g • y = z) (hgh : (g * h) • x = z) v,
    unitary g y z hz (unitary h x y hy v) = (α.val g h : ℂ) • unitary (g * h) x z hgh v

variable {α E}

noncomputable def FibreSystem.toBundle (U : FibreSystem α E) : ProjectiveBundle α E where
  action k := relabel (MulAction.toPerm k) (U.unitary k)
  fibre := U.unitary
  action_single k x y h v := relabel_single (MulAction.toPerm k) (U.unitary k) x y h v
  action_one := by
    intro v
    have he : (relabel (MulAction.toPerm (1 : K)) (U.unitary 1)).toContinuousLinearEquiv.toContinuousLinearMap =
        ContinuousLinearMap.id ℂ (lp E 2) := by
      apply lp.ext_continuousLinearMap (by norm_num)
      intro x
      apply ContinuousLinearMap.ext
      intro w
      change relabel (MulAction.toPerm (1 : K)) (U.unitary 1) (lp.single 2 x w) = lp.single 2 x w
      rw [relabel_single (MulAction.toPerm (1 : K)) (U.unitary 1) x x (one_smul K x), U.one]
    exact DFunLike.congr_fun he v
  action_mul := by
    intro g h v
    have he :
        (relabel (MulAction.toPerm g) (U.unitary g)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (relabel (MulAction.toPerm h) (U.unitary h)).toContinuousLinearEquiv.toContinuousLinearMap =
        (α.val g h : ℂ) • (relabel (MulAction.toPerm (g * h)) (U.unitary (g * h))).toContinuousLinearEquiv.toContinuousLinearMap := by
      apply lp.ext_continuousLinearMap (by norm_num)
      intro x
      apply ContinuousLinearMap.ext
      intro w
      change relabel (MulAction.toPerm g) (U.unitary g)
        (relabel (MulAction.toPerm h) (U.unitary h) (lp.single 2 x w)) =
        (α.val g h : ℂ) • relabel (MulAction.toPerm (g * h)) (U.unitary (g * h)) (lp.single 2 x w)
      rw [relabel_single (MulAction.toPerm h) (U.unitary h) x (h • x) rfl,
        relabel_single (MulAction.toPerm g) (U.unitary g) (h • x) ((g * h) • x) (mul_smul g h x).symm,
        relabel_single (MulAction.toPerm (g * h)) (U.unitary (g * h)) x ((g * h) • x) rfl]
      erw [U.mul g h x (h • x) ((g * h) • x) rfl (mul_smul g h x).symm rfl w,
        lp.single_smul]
    exact DFunLike.congr_fun he v

end FibreSystem

noncomputable section ExactInduction

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Group K]

def ScalarCocycle.restrict (α : ScalarCocycle K) (C : Subgroup K) : ScalarCocycle C where
  val g h := α.val g h
  mul_assoc g h j := α.mul_assoc g h j
  one_left g := α.one_left g
  one_right g := α.one_right g

structure ProjectiveRepresentation (α : ScalarCocycle K) (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  unitary : K → V ≃ₗᵢ[ℂ] V
  one : ∀ v, unitary 1 v = v
  mul : ∀ g h v, unitary g (unitary h v) = (α.val g h : ℂ) • unitary (g * h) v

variable (C : Subgroup K)

structure CosetSection where
  repr : K ⧸ C → K
  repr_spec : ∀ x, QuotientGroup.mk (repr x) = x
  repr_one : repr (QuotientGroup.mk 1) = 1

noncomputable def chooseCosetSection : CosetSection C where
  repr x := if x = QuotientGroup.mk 1 then 1 else x.out
  repr_spec x := by
    split_ifs with h
    · exact h.symm
    · exact QuotientGroup.out_eq' x
  repr_one := by simp

variable {C}

def CosetSection.correction (r : CosetSection C) (s : K) (x : K ⧸ C) : C :=
  ⟨(r.repr (s • x))⁻¹ * s * r.repr x, by
    rw [mul_assoc]
    apply QuotientGroup.eq.mp
    rw [r.repr_spec, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, r.repr_spec]⟩

@[simp] theorem CosetSection.correction_val (r : CosetSection C) (s : K) (x : K ⧸ C) :
    (r.correction s x : K) = (r.repr (s • x))⁻¹ * s * r.repr x := rfl

@[simp] theorem CosetSection.repr_mul_correction (r : CosetSection C) (s : K) (x : K ⧸ C) :
    r.repr (s • x) * (r.correction s x : K) = s * r.repr x := by
  rw [correction_val]
  group

@[simp] theorem CosetSection.correction_one (r : CosetSection C) (x : K ⧸ C) :
    r.correction 1 x = 1 := by
  apply Subtype.ext
  simp [correction]

@[simp] theorem CosetSection.correction_mul (r : CosetSection C) (s t : K) (x : K ⧸ C) :
    r.correction s (t • x) * r.correction t x = r.correction (s * t) x := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, correction_val, mul_smul]
  group

def CosetSection.phase (r : CosetSection C) (α : ScalarCocycle K) (s : K) (x : K ⧸ C) : Circle :=
  α.val s (r.repr x) / α.val (r.repr (s • x)) (r.correction s x)

@[simp] theorem CosetSection.phase_one (r : CosetSection C) (α : ScalarCocycle K) (x : K ⧸ C) :
    r.phase α 1 x = 1 := by
  simp [phase, α.one_left, α.one_right]

theorem cocycle_transport_phase (α : ScalarCocycle K) (s t x y z a b : K)
    (ha : z * a = s * y) (hb : y * b = t * x) :
    (α.val s y / α.val z a) * (α.val t x / α.val y b) * α.val a b =
      α.val s t * (α.val (s * t) x / α.val z (a * b)) := by
  have hid : α.val s y * α.val t x * α.val a b * α.val z (a * b) =
      α.val s t * α.val (s * t) x * (α.val z a * α.val y b) := by
    calc
      _ = α.val t x * α.val s y * (α.val a b * α.val z (a * b)) := by ac_rfl
      _ = α.val t x * α.val s y * (α.val z a * α.val (z * a) b) := by
        rw [α.mul_assoc z a b]
      _ = α.val z a * α.val t x * (α.val s y * α.val (s * y) b) := by
        rw [ha]
        ac_rfl
      _ = α.val z a * α.val t x * (α.val y b * α.val s (y * b)) := by
        rw [α.mul_assoc s y b]
      _ = (α.val t x * α.val s (t * x)) * (α.val z a * α.val y b) := by
        rw [hb]
        ac_rfl
      _ = _ := by rw [← α.mul_assoc s t x]
  rw [div_mul_div_comm, div_mul_eq_mul_div, mul_div_assoc]
  simpa only [mul_div_assoc] using div_eq_div_iff_mul_eq_mul.mpr hid

theorem CosetSection.phase_mul (r : CosetSection C) (α : ScalarCocycle K) (s t : K)
    (x : K ⧸ C) :
    r.phase α s (t • x) * r.phase α t x * α.val (r.correction s (t • x)) (r.correction t x) =
      α.val s t * r.phase α (s * t) x := by
  unfold phase
  have h := cocycle_transport_phase α s t (r.repr x) (r.repr (t • x))
    (r.repr (s • t • x)) (r.correction s (t • x)) (r.correction t x)
    (r.repr_mul_correction s (t • x)) (r.repr_mul_correction t x)
  simpa only [← Subgroup.coe_mul, correction_mul, mul_smul] using h

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def circleUnitary (z : Circle) : V ≃ₗᵢ[ℂ] V where
  toLinearEquiv :=
    { toFun := fun v => (z : ℂ) • v
      invFun := fun v => ((z⁻¹ : Circle) : ℂ) • v
      left_inv := by intro v; simp [smul_smul]
      right_inv := by intro v; simp [smul_smul]
      map_add' := by intro v w; exact smul_add _ _ _
      map_smul' := by intro a v; exact smul_comm _ _ _ }
  norm_map' := by intro v; simp [norm_smul, Circle.norm_coe]

@[simp] theorem circleUnitary_apply (z : Circle) (v : V) : circleUnitary z v = (z : ℂ) • v := rfl

def CosetSection.inducedUnitary (r : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) (s : K) (x : K ⧸ C) : V ≃ₗᵢ[ℂ] V :=
  (γ.unitary (r.correction s x)).trans (circleUnitary (r.phase α s x))

@[simp] theorem CosetSection.inducedUnitary_apply (r : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) (s : K) (x : K ⧸ C) (v : V) :
    r.inducedUnitary α γ s x v = (r.phase α s x : ℂ) • γ.unitary (r.correction s x) v := rfl

@[simp] theorem CosetSection.inducedUnitary_one (r : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) (x : K ⧸ C) (v : V) :
    r.inducedUnitary α γ 1 x v = v := by
  simp [γ.one]

theorem CosetSection.inducedUnitary_mul (r : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) (s t : K) (x : K ⧸ C) (v : V) :
    r.inducedUnitary α γ s (t • x) (r.inducedUnitary α γ t x v) =
      (α.val s t : ℂ) • r.inducedUnitary α γ (s * t) x v := by
  simp only [inducedUnitary_apply, map_smul, γ.mul, smul_smul]
  rw [correction_mul]
  congr 1
  have hp := congrArg (fun z : Circle => (z : ℂ)) (r.phase_mul α s t x)
  simpa only [Circle.coe_mul, ScalarCocycle.restrict, mul_assoc, mul_left_comm] using hp

def CosetSection.change (r r' : CosetSection C) (x : K ⧸ C) : C :=
  ⟨(r.repr x)⁻¹ * r'.repr x, QuotientGroup.eq.mp ((r.repr_spec x).trans (r'.repr_spec x).symm)⟩

@[simp] theorem CosetSection.repr_mul_change (r r' : CosetSection C) (x : K ⧸ C) :
    r.repr x * (r.change r' x : K) = r'.repr x := by
  simp [change]

theorem CosetSection.change_correction (r r' : CosetSection C) (s : K) (x : K ⧸ C) :
    r.change r' (s • x) * r'.correction s x = r.correction s x * r.change r' x := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, change, correction]
  group

theorem cocycle_change_phase (α : ScalarCocycle K) (s x y c k l c' : K)
    (hc : y * c = s * x) (hk : l * c' = c * k) :
    (α.val y l)⁻¹ * (α.val s (x * k) / α.val (y * l) c') * α.val l c' =
      (α.val s x / α.val y c) * (α.val x k)⁻¹ * α.val c k := by
  have hid : α.val s (x * k) * α.val l c' * (α.val y c * α.val x k) =
      α.val s x * α.val c k * (α.val (y * l) c' * α.val y l) := by
    calc
      _ = α.val l c' * α.val y c * (α.val x k * α.val s (x * k)) := by ac_rfl
      _ = α.val l c' * α.val y c * (α.val s x * α.val (s * x) k) := by
        rw [α.mul_assoc s x k]
      _ = α.val s x * α.val l c' * (α.val y c * α.val (y * c) k) := by
        rw [← hc]
        ac_rfl
      _ = α.val s x * α.val l c' * (α.val c k * α.val y (c * k)) := by
        rw [α.mul_assoc y c k]
      _ = α.val s x * α.val c k * (α.val l c' * α.val y (l * c')) := by
        rw [← hk]
        ac_rfl
      _ = _ := by rw [← α.mul_assoc y l c']; ac_rfl
  have hr := div_eq_div_iff_mul_eq_mul.mpr hid
  convert hr using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

def CosetSection.changeUnitary (r r' : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) (x : K ⧸ C) : V ≃ₗᵢ[ℂ] V :=
  (γ.unitary (r.change r' x)).trans
    (circleUnitary (α.val (r.repr x) (r.change r' x))⁻¹)

@[simp] theorem CosetSection.changeUnitary_apply (r r' : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) (x : K ⧸ C) (v : V) :
    r.changeUnitary r' α γ x v = ((α.val (r.repr x) (r.change r' x))⁻¹ : Circle) •
      γ.unitary (r.change r' x) v := rfl

theorem CosetSection.change_phase (r r' : CosetSection C) (α : ScalarCocycle K)
    (s : K) (x : K ⧸ C) :
    (α.val (r.repr (s • x)) (r.change r' (s • x)))⁻¹ * r'.phase α s x *
        α.val (r.change r' (s • x)) (r'.correction s x) =
      r.phase α s x * (α.val (r.repr x) (r.change r' x))⁻¹ *
        α.val (r.correction s x) (r.change r' x) := by
  have h := cocycle_change_phase α s (r.repr x) (r.repr (s • x))
    (r.correction s x) (r.change r' x) (r.change r' (s • x)) (r'.correction s x)
    (r.repr_mul_correction s x) (congrArg Subtype.val (r.change_correction r' s x))
  simpa only [phase, repr_mul_change] using h

theorem CosetSection.changeUnitary_intertwines (r r' : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) (s : K) (x : K ⧸ C) (v : V) :
    r.changeUnitary r' α γ (s • x) (r'.inducedUnitary α γ s x v) =
      r.inducedUnitary α γ s x (r.changeUnitary r' α γ x v) := by
  change ((α.val (r.repr (s • x)) (r.change r' (s • x)))⁻¹ : Circle) •
    γ.unitary (r.change r' (s • x)) ((r'.phase α s x : ℂ) • γ.unitary (r'.correction s x) v) =
    (r.phase α s x : ℂ) • γ.unitary (r.correction s x)
      (((α.val (r.repr x) (r.change r' x))⁻¹ : Circle) • γ.unitary (r.change r' x) v)
  simp only [Circle.smul_def, map_smul, γ.mul, smul_smul]
  rw [change_correction]
  congr 1
  have hp := congrArg (fun z : Circle => (z : ℂ)) (r.change_phase r' α s x)
  simpa only [Circle.coe_mul, ScalarCocycle.restrict, mul_assoc] using hp

end ExactInduction

noncomputable section InducedBundle

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Group K] {C : Subgroup K}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

local instance : DecidableEq (K ⧸ C) := Classical.decEq _

def CosetSection.inducedFibreSystem (r : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) :
    FibreSystem α (fun _ : K ⧸ C => V) where
  unitary s x _ _ := r.inducedUnitary α γ s x
  one x v := r.inducedUnitary_one α γ x v
  mul s t x y z hy hz hst v := by
    subst y
    exact r.inducedUnitary_mul α γ s t x v

def CosetSection.inducedBundle (r : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) :
    ProjectiveBundle α (fun _ : K ⧸ C => V) :=
  (r.inducedFibreSystem α γ).toBundle

theorem CosetSection.inducedBundle_single (r : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) (s : K) (x : K ⧸ C) (v : V) :
    (r.inducedBundle α γ).action s (lp.single 2 x v) =
      lp.single 2 (s • x) ((r.phase α s x : ℂ) • γ.unitary (r.correction s x) v) := by
  exact (r.inducedBundle α γ).action_single s x (s • x) rfl v

def CosetSection.changeBundleUnitary (r r' : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) :
    lp (fun _ : K ⧸ C => V) 2 ≃ₗᵢ[ℂ] lp (fun _ : K ⧸ C => V) 2 :=
  relabel (Equiv.refl _) (fun x _ _ => r.changeUnitary r' α γ x)

@[simp] theorem CosetSection.changeBundleUnitary_single (r r' : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) (x : K ⧸ C) (v : V) :
    r.changeBundleUnitary r' α γ (lp.single 2 x v) =
      lp.single 2 x (r.changeUnitary r' α γ x v) := by
  exact relabel_single (Equiv.refl _) (fun x _ _ => r.changeUnitary r' α γ x) x x rfl v

theorem CosetSection.changeBundleUnitary_intertwines (r r' : CosetSection C) (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) :
    Intertwines (r'.inducedBundle α γ) (r.inducedBundle α γ)
      (r.changeBundleUnitary r' α γ).toContinuousLinearEquiv.toContinuousLinearMap := by
  intro s v
  have he :
      (r.changeBundleUnitary r' α γ).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((r'.inducedBundle α γ).action s).toContinuousLinearEquiv.toContinuousLinearMap =
      ((r.inducedBundle α γ).action s).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (r.changeBundleUnitary r' α γ).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro x
    apply ContinuousLinearMap.ext
    intro w
    change r.changeBundleUnitary r' α γ ((r'.inducedBundle α γ).action s (lp.single 2 x w)) =
      (r.inducedBundle α γ).action s (r.changeBundleUnitary r' α γ (lp.single 2 x w))
    rw [(r'.inducedBundle α γ).action_single s x (s • x) rfl,
      changeBundleUnitary_single, changeBundleUnitary_single,
      (r.inducedBundle α γ).action_single s x (s • x) rfl]
    exact congrArg (lp.single 2 (s • x)) (r.changeUnitary_intertwines r' α γ s x w)
  exact DFunLike.congr_fun he v

theorem exact_projective_induction (α : ScalarCocycle K)
    (γ : ProjectiveRepresentation (α.restrict C) V) :
    (∃ B : ProjectiveBundle α (fun _ : K ⧸ C => V),
      ∀ s x v, B.action s (lp.single 2 x v) =
        lp.single 2 (s • x) (((chooseCosetSection C).phase α s x : ℂ) •
          γ.unitary ((chooseCosetSection C).correction s x) v)) ∧
    ∀ r r' : CosetSection C,
      Intertwines (r'.inducedBundle α γ) (r.inducedBundle α γ)
        (r.changeBundleUnitary r' α γ).toContinuousLinearEquiv.toContinuousLinearMap := by
  refine ⟨⟨(chooseCosetSection C).inducedBundle α γ, ?_⟩, ?_⟩
  · exact (chooseCosetSection C).inducedBundle_single α γ
  · exact fun r r' => r.changeBundleUnitary_intertwines r' α γ

end InducedBundle

end GermBundles

end OAI
