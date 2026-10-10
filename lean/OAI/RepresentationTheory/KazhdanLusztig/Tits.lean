import OAI.RepresentationTheory.KazhdanLusztig.Bruhat
import OAI.RepresentationTheory.KazhdanLusztig.Dihedral
import OAI.RepresentationTheory.KazhdanLusztig.ReflectionPlane
import OAI.RepresentationTheory.KazhdanLusztig.Sheaves

namespace OAI

/-!
Actual Bruhat graph labels, Tits realizations and extended root spaces, cotangent coordinates and standard parabolic support.
-/

section

namespace KLInvariance
namespace BruhatGraph
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
  (cs : CoxeterSystem M W) (u b : W)

/-- Actual finite directed moment-graph edges, including the non-cover
reflection edges. No reconstruction from the abstract poset is assumed. -/
def Edge := {p : Interval cs u b × Interval cs u b // BruhatStep cs p.1.val p.2.val}

instance : Finite (Edge cs u b) := by
  let := interval_finite cs u b
  unfold Edge
  infer_instance

def source (e : Edge cs u b) : Interval cs u b := e.val.1
def target (e : Edge cs u b) : Interval cs u b := e.val.2

def graph : MomentGraph.OrderedGraph (Interval cs u b) (Edge cs u b) where
  source := source cs u b
  target := target cs u b
  increasing e := by
    refine ⟨Relation.ReflTransGen.single e.property, ?_⟩
    intro h
    exact (not_lt_of_ge (length_le_of_bruhat cs h)) e.property.1

/-- Genuine left reflection label; uniquely determined by the endpoints. -/
def label (e : Edge cs u b) : W := (target cs u b e).val * (source cs u b e).val⁻¹

theorem label_isReflection (e : Edge cs u b) : cs.IsReflection (label cs u b e) := by
  obtain ⟨t, ht, htx⟩ := e.property.2
  simpa [label, source, target, htx, mul_assoc] using ht

@[simp] theorem label_mul_source (e : Edge cs u b) :
    label cs u b e * (source cs u b e).val = (target cs u b e).val := by
  simp [label, mul_assoc]

@[simp] theorem label_mul_target (e : Edge cs u b) :
    label cs u b e * (target cs u b e).val = (source cs u b e).val := by
  rw [← label_mul_source cs u b e, ← mul_assoc,
    (label_isReflection cs u b e).mul_self, one_mul]

theorem eq_of_label_source_eq {e f : Edge cs u b}
    (hl : label cs u b e = label cs u b f)
    (hs : source cs u b e = source cs u b f) : e = f := by
  have ht : target cs u b e = target cs u b f := by
    apply Subtype.ext
    rw [← label_mul_source cs u b e, ← label_mul_source cs u b f, hl, hs]
  apply Subtype.ext
  exact Prod.ext hs ht

theorem eq_of_label_target_eq {e f : Edge cs u b}
    (hl : label cs u b e = label cs u b f)
    (ht : target cs u b e = target cs u b f) : e = f := by
  have hs : source cs u b e = source cs u b f := by
    apply Subtype.ext
    rw [← label_mul_target cs u b e, ← label_mul_target cs u b f, hl, ht]
  exact eq_of_label_source_eq cs u b hl hs

theorem source_ne_target_of_label_eq {e f : Edge cs u b}
    (hl : label cs u b e = label cs u b f) :
    source cs u b e ≠ target cs u b f := by
  intro h
  have ht : target cs u b e = source cs u b f := by
    apply Subtype.ext
    rw [← label_mul_source cs u b e, hl, h, label_mul_target]
  have he := (graph cs u b).increasing e
  have hf := (graph cs u b).increasing f
  change source cs u b e < target cs u b e at he
  change source cs u b f < target cs u b f at hf
  rw [h, ht] at he
  exact lt_asymm he hf


theorem endpoints_disjoint_of_label_eq {e f : Edge cs u b} (hef : e ≠ f)
    (hl : label cs u b e = label cs u b f) :
    Disjoint ({source cs u b e, target cs u b e} : Set _)
      {source cs u b f, target cs u b f} := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with hy | hy
  · exact hef (eq_of_label_source_eq cs u b hl hy)
  · exact source_ne_target_of_label_eq cs u b hl hy
  · exact source_ne_target_of_label_eq cs u b hl.symm hy.symm
  · exact hef (eq_of_label_target_eq cs u b hl hy)

end BruhatGraph
end KLInvariance


namespace KLInvariance.Realization
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An actual rank-one perturbation that preserves a nondegenerate symmetric
form is an orthogonal reflection, not a unipotent transvection. -/
theorem orthogonal_rank_one_form
    (B : LinearMap.BilinForm ℝ V) (hs : B.IsSymm) (hn : B.Nondegenerate)
    (u : V) (hu : u ≠ 0) (f : Module.Dual ℝ V) (hf : f ≠ 0)
    (hg : ∀ v w, B (v + f v • u) (w + f w • u) = B v w) :
    f u = -2 ∧ B u u ≠ 0 ∧
      ∀ v, v + f v • u = Module.preReflection u ((2 / B u u) • B u) v := by
  obtain ⟨v, hv⟩ : ∃ v, f v = 1 := by
    have hex : ∃ w, f w ≠ 0 := by
      by_contra! h
      exact hf (LinearMap.ext h)
    obtain ⟨w, hw⟩ := hex
    exact ⟨(f w)⁻¹ • w, by simp [hw]⟩
  have hz (z : V) (h : f z = 0) : B u z = 0 := by
    have h' := hg v z
    simpa [hv, h, map_add] using h'
  have hprop (z : V) : B u z = f z * B u v := by
    have h := hz (z - f z • v) (by simp [hv])
    exact sub_eq_zero.mp (by simpa [map_sub, map_smul] using h)
  have hc : B u v ≠ 0 := by
    intro h
    apply hu
    exact hn.1 u (fun z => by rw [hprop z, h, mul_zero])
  have hself := hg v v
  simp only [hv, one_smul, map_add, LinearMap.add_apply] at hself
  rw [hs.eq v u] at hself
  have hfu : f u = -2 := by
    rw [hprop u] at hself
    apply (mul_right_cancel₀ hc)
    linarith
  have hne : B u u ≠ 0 := by
    rw [hprop u, hfu]
    exact mul_ne_zero (by norm_num) hc
  refine ⟨hfu, hne, fun z => ?_⟩
  rw [Module.preReflection_apply]
  have heq : ((2 / B u u) • B u) z = -f z := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [hprop z, hprop u, hfu]
    field_simp [hc]
  rw [heq, neg_smul, sub_neg_eq_add]

/-- This is the rank-one assertion in `bg:realization` stated without a chosen
rank-one normal form. Its conclusion uses the library's actual reflection. -/
theorem orthogonal_finrank_one
    (B : LinearMap.BilinForm ℝ V) (hs : B.IsSymm) (hn : B.Nondegenerate)
    (g : V ≃ₗ[ℝ] V) (hg : ∀ v w, B (g v) (g w) = B v w)
    (hr : Module.finrank ℝ (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1) :
    ∃ u : V, B u u ≠ 0 ∧
      ∀ v, g v = Module.preReflection u ((2 / B u u) • B u) v := by
  let d : V →ₗ[ℝ] V := g.toLinearMap - LinearMap.id
  obtain ⟨e⟩ := nonempty_linearEquiv_of_finrank_eq_one hr
  let u : V := (e 1).val
  let f : Module.Dual ℝ V := e.symm.toLinearMap.comp d.rangeRestrict
  have hu : u ≠ 0 := by
    intro h
    have : e 1 = 0 := Subtype.ext h
    have := e.injective (this.trans e.map_zero.symm)
    norm_num at this
  have hform (v : V) : f v • u = d v := by
    change f v • (e 1).val = d v
    have h := congrArg Subtype.val (e.apply_symm_apply (d.rangeRestrict v))
    have he : e (f v) = f v • e 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [show e.symm (d.rangeRestrict v) = f v from rfl, he] at h
    exact h
  have hf : f ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := (e 1).property
    have hh := hform v
    rw [h, LinearMap.zero_apply, zero_smul, hv] at hh
    exact hu hh.symm
  have hgform (v : V) : g v = v + f v • u := by
    rw [hform]
    change g v = v + (g v - v)
    abel
  obtain ⟨_, hnonzero, hreflection⟩ := orthogonal_rank_one_form B hs hn u hu f hf
    (fun v w => by rw [← hgform, ← hgform]; exact hg v w)
  exact ⟨u, hnonzero, fun v => (hgform v).trans (hreflection v)⟩
end KLInvariance.Realization

/-! The finite Coxeter relations for the actual real geometric reflection
operators required in `bg:realization`. Faithfulness is not assumed or claimed. -/
namespace KLInvariance.Realization
open Module Polynomial.Chebyshev
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem reflection_pow_even_eq_one
    {α β : V} {f g : Module.Dual ℝ V} (hf : f α = 2) (hg : g β = 2)
    (k : ℕ) (hS : (S ℝ ((k : ℤ) - 1)).eval (f β * g α - 2) = 0) :
    (Module.reflection hf * Module.reflection hg) ^ (2 * k) = 1 := by
  ext v
  rw [Module.reflection_mul_reflection_pow_apply hf hg]
  have h₁ : ((↑(2 * k) : ℤ) - 2) / 2 = (k : ℤ) - 1 := by omega
  have h₂ : ((↑(2 * k) : ℤ) - 1) / 2 = (k : ℤ) - 1 := by omega
  rw [h₁, h₂, hS]
  simp

private theorem reflection_pow_odd_eq_one
    {α β : V} {f g : Module.Dual ℝ V} (hf : f α = 2) (hg : g β = 2)
    (k : ℕ)
    (hS : (S ℝ (k : ℤ)).eval (f β * g α - 2) +
      (S ℝ ((k : ℤ) - 1)).eval (f β * g α - 2) = 0) :
    (Module.reflection hf * Module.reflection hg) ^ (2 * k + 1) = 1 := by
  ext v
  rw [Module.reflection_mul_reflection_pow_apply hf hg]
  have h₀ : (↑(2 * k + 1) : ℤ) / 2 = (k : ℤ) := by omega
  have h₁ : ((↑(2 * k + 1) : ℤ) - 2) / 2 = (k : ℤ) - 1 := by omega
  have h₂ : ((↑(2 * k + 1) : ℤ) - 1) / 2 = (k : ℤ) := by omega
  have h₃ : ((↑(2 * k + 1) : ℤ) - 3) / 2 = (k : ℤ) - 1 := by omega
  rw [h₀, h₁, h₂, h₃, hS]
  simp

/-- If the two simple roots have the exact Tits pairing, the corresponding
linear equivalences satisfy their finite Coxeter relation on the entire
ambient space, not just on the root plane. -/
theorem geometric_reflection_relation
    {α β : V} {f g : Module.Dual ℝ V} (hf : f α = 2) (hg : g β = 2)
    (m : ℕ) (hm : 2 ≤ m)
    (hfg : f β = -2 * Real.cos (Real.pi / m))
    (hgf : g α = -2 * Real.cos (Real.pi / m)) :
    (Module.reflection hf * Module.reflection hg) ^ m = 1 := by
  by_cases hm2 : m = 2
  · subst m
    have hfg0 : f β = 0 := by simpa using hfg
    have hgf0 : g α = 0 := by simpa using hgf
    ext v
    change ((Module.reflection hf * Module.reflection hg) ^ 2) v = v
    simp only [pow_two, LinearEquiv.mul_apply, Module.reflection_apply,
      map_sub, map_smul, hf, hg, hfg0, hgf0, ]
    module
  have hm3 : 2 < m := by omega
  have hmR : (2 : ℝ) < m := by exact_mod_cast hm3
  let θ : ℝ := Real.pi / m
  have hθ : (m : ℝ) * θ = Real.pi := by dsimp [θ]; field_simp
  have hθpos : 0 < θ := div_pos Real.pi_pos (by positivity)
  have hθlt : 2 * θ < Real.pi := by
    dsimp [θ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (show (0 : ℝ) < m by positivity)).2
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) hθlt)
  have ht : f β * g α - 2 = 2 * Real.cos (2 * θ) := by
    rw [hfg, hgf, Real.cos_two_mul]
    dsimp [θ]
    ring
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨k, hk⟩ := he
    have hm' : m = 2 * k := by omega
    clear hk
    subst m
    apply reflection_pow_even_eq_one hf hg k
    rw [ht]
    have h := S_two_mul_real_cos (2 * θ) ((k : ℤ) - 1)
    have ha : (((k : ℤ) - 1 : ℤ) + 1 : ℝ) * (2 * θ) = Real.pi := by
      push_cast
      push_cast at hθ
      nlinarith [hθ]
    rw [ha, Real.sin_pi] at h
    exact (mul_eq_zero.mp h).resolve_right hsin
  · obtain ⟨k, hk⟩ := ho
    have hm' : m = 2 * k + 1 := by omega
    clear hk
    subst m
    apply reflection_pow_odd_eq_one hf hg k
    rw [ht]
    have h₁ := S_two_mul_real_cos (2 * θ) (k : ℤ)
    have h₂ := S_two_mul_real_cos (2 * θ) ((k : ℤ) - 1)
    have ha : ((k : ℤ) + 1 : ℝ) * (2 * θ) = Real.pi + θ := by
      push_cast
      push_cast at hθ
      nlinarith [hθ]
    have hb : (((k : ℤ) - 1 : ℤ) + 1 : ℝ) * (2 * θ) = Real.pi - θ := by
      push_cast
      push_cast at hθ
      nlinarith [hθ]
    rw [ha] at h₁
    simp only [Real.sin_add, Real.sin_pi, Real.cos_pi, zero_mul, neg_one_mul,
      zero_add] at h₁
    rw [hb, Real.sin_pi_sub] at h₂
    apply (mul_eq_zero.mp (show
      ((S ℝ (k : ℤ)).eval (2 * Real.cos (2 * θ)) +
      (S ℝ ((k : ℤ) - 1)).eval (2 * Real.cos (2 * θ))) *
      Real.sin (2 * θ) = 0 by nlinarith [h₁, h₂])).resolve_right hsin
end KLInvariance.Realization

namespace KLInvariance.Realization
open Module
universe u v z
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W)
variable {V : Type z} [AddCommGroup V] [Module ℝ V]
variable (B : LinearMap.BilinForm ℝ V) (α : I → V)
variable (hα : ∀ i j, B (α i) (α j) = -2 * Real.cos (Real.pi / M i j))

include hα

lemma simple_normal_value (i : I) : B (α i) (α i) = 2 := by
  rw [hα]
  simp

noncomputable def geometricSimple (i : I) : V ≃ₗ[ℝ] V :=
  Module.reflection (simple_normal_value B α hα i)

theorem geometricSimple_liftable : M.IsLiftable (geometricSimple B α hα) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [M.diagonal, pow_one]
    ext v
    exact Module.involutive_reflection (simple_normal_value B α hα i) v
  by_cases hm0 : M i j = 0
  · rw [hm0, pow_zero]
  have hm2 : 2 ≤ M i j := by
    have := M.off_diagonal i j hij
    omega
  exact geometric_reflection_relation (simple_normal_value B α hα i)
    (simple_normal_value B α hα j) (M i j) hm2 (hα i j)
    (by rw [hα j i, M.symmetric j i])

/-- The genuine geometric reflection action. Each relation has been proved;
this definition does not presuppose a faithful representation. -/
noncomputable def geometricAction : W →* (V ≃ₗ[ℝ] V) :=
  cs.lift ⟨geometricSimple B α hα, geometricSimple_liftable B α hα⟩

@[simp] theorem geometricAction_simple (i : I) :
    geometricAction cs B α hα (cs.simple i) = geometricSimple B α hα i :=
  cs.lift_apply_simple (geometricSimple_liftable B α hα) i

theorem geometricSimple_preserves (hs : B.IsSymm) (i : I) (v w : V) :
    B (geometricSimple B α hα i v) (geometricSimple B α hα i w) = B v w := by
  simp only [geometricSimple, Module.reflection_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hs.eq v (α i), simple_normal_value B α hα i]
  ring

theorem geometricAction_preserves (hs : B.IsSymm) (w : W) (v z : V) :
    B (geometricAction cs B α hα w v) (geometricAction cs B α hα w z) = B v z := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul]
    simp only [LinearEquiv.mul_apply, geometricAction_simple]
    rw [geometricSimple_preserves B α hα hs, ih]

end KLInvariance.Realization

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
noncomputable section


def gram (i j : I) : ℝ := -2 * Real.cos (Real.pi / M i j)

def root (i : I) : I → ℝ := by
  classical
  exact Pi.single i 1

def normal (i : I) : Module.Dual ℝ (I → ℝ) :=
  ∑ j, gram M i j • LinearMap.proj j

def form : LinearMap.BilinForm ℝ (I → ℝ) :=
  ∑ i, (LinearMap.proj i).smulRight (normal M i)

@[simp] theorem normal_root (i j : I) : normal M i (root j) = gram M i j := by
  classical
  simp only [normal, root, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [hbj]
  · simp

@[simp] theorem form_root (i : I) (v : I → ℝ) : form M (root i) v = normal M i v := by
  classical
  simp [form, root, LinearMap.sum_apply]

theorem form_symm : (form M).IsSymm := by
  constructor
  intro v w
  simp only [form, normal, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show gram M j i = gram M i j by simp only [gram, M.symmetric j i]]
  ring

theorem form_roots (i j : I) : form M (root i) (root j) =
    -2 * Real.cos (Real.pi / M i j) := by simp [gram]

theorem root_linearIndependent : LinearIndependent ℝ (root (I := I)) := by
  classical
  have heq : (root (I := I)) = (Pi.basisFun ℝ I : I → I → ℝ) := by
    funext i
    simp [root, Pi.basisFun_apply]
  rw [heq]
  exact (Pi.basisFun ℝ I).linearIndependent

/-- A concrete action on the ordinary geometric root space over ℝ. Its
faithfulness and the root-sign theorem are still required for the main proof. -/
def action {W : Type v} [Group W] (cs : CoxeterSystem M W) :
    W →* ((I → ℝ) ≃ₗ[ℝ] (I → ℝ)) :=
  Realization.geometricAction cs (form M) root (form_roots M)

@[simp] theorem action_simple {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (i : I) (v : I → ℝ) :
    action M cs (cs.simple i) v = v - normal M i v • root i := by
  simp [action, Realization.geometricAction_simple, Realization.geometricSimple,
    Module.reflection_apply]

theorem action_preserves {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (w : W) (v z : I → ℝ) : form M (action M cs w v) (action M cs w z) = form M v z :=
  Realization.geometricAction_preserves cs (form M) root (form_roots M) (form_symm M) w v z
end
end KLInvariance.TitsSpace

namespace KLInvariance.Realization
universe u
variable {V : Type u} [AddCommGroup V] [Module ℝ V]


abbrev Extension (B : LinearMap.BilinForm ℝ V) := V × Module.Dual ℝ (LinearMap.ker B)

noncomputable def extensionForm (B : LinearMap.BilinForm ℝ V)
    (p : V →ₗ[ℝ] LinearMap.ker B) : LinearMap.BilinForm ℝ (Extension B) where
  toFun x :=
    { toFun := fun y => B x.1 y.1 + x.2 (p y.1) + y.2 (p x.1)
      map_add' := by intro y z; simp [map_add]; ring
      map_smul' := by intro t y; simp [map_smul]; ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change B (x.1 + y.1) z.1 + (x.2 + y.2) (p z.1) + z.2 (p (x.1 + y.1)) = _
    simp [map_add]
    ring
  map_smul' := by
    intro t x
    apply LinearMap.ext
    intro z
    change B (t • x.1) z.1 + (t • x.2) (p z.1) + z.2 (p (t • x.1)) = _
    simp [map_smul]
    ring

@[simp] theorem extensionForm_apply (B : LinearMap.BilinForm ℝ V)
    (p : V →ₗ[ℝ] LinearMap.ker B) (x y : Extension B) :
    extensionForm B p x y = B x.1 y.1 + x.2 (p y.1) + y.2 (p x.1) := rfl

@[simp] theorem extensionForm_inl (B : LinearMap.BilinForm ℝ V)
    (p : V →ₗ[ℝ] LinearMap.ker B) (v w : V) :
    extensionForm B p (v, 0) (w, 0) = B v w := by simp

theorem extensionForm_symm (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (p : V →ₗ[ℝ] LinearMap.ker B) : (extensionForm B p).IsSymm := by
  constructor
  intro x y
  simp only [extensionForm_apply]
  rw [hB.eq x.1 y.1]
  ring

theorem extensionForm_nondegenerate (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsSymm) (p : V →ₗ[ℝ] LinearMap.ker B)
    (hp : ∀ k : LinearMap.ker B, p k.val = k) : (extensionForm B p).Nondegenerate := by
  have hf : ∀ x : Extension B, (∀ y, extensionForm B p x y = 0) → x = 0 := by
    rintro ⟨v, φ⟩ hx
    have hpv : p v = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ (p v)).mp
      intro ψ
      simpa using hx (0, ψ)
    have hφ : φ = 0 := by
      ext k
      have hbk : B k.val = 0 := k.property
      have hvk : B v k.val = 0 := by
        rw [hB.eq v k.val, hbk]
        rfl
      simpa [hvk, hp k, hpv] using hx (k.val, 0)
    have hbv : v ∈ LinearMap.ker B := by
      change B v = 0
      ext w
      simpa [hφ, hpv] using hx (w, 0)
    have hv : v = 0 := by
      have h := hp ⟨v, hbv⟩
      rw [hpv] at h
      exact (congrArg Subtype.val h).symm
    simp [hv, hφ]
  exact ⟨hf, fun x hx => hf x (fun y => by
    rw [(extensionForm_symm B hB p).eq]
    exact hx y)⟩

theorem exists_minimal_nondegenerate_extension (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsSymm) :
    ∃ C : LinearMap.BilinForm ℝ (Extension B), C.IsSymm ∧ C.Nondegenerate ∧
      ∀ v w, C (v, 0) (w, 0) = B v w := by
  obtain ⟨Q, hQ⟩ := (LinearMap.ker B).exists_isCompl
  let p := (LinearMap.ker B).projectionOnto Q hQ
  exact ⟨extensionForm B p, extensionForm_symm B hB p,
    extensionForm_nondegenerate B hB p (Submodule.projectionOnto_apply_left hQ),
    extensionForm_inl B p⟩

theorem extension_finrank [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) :
    Module.finrank ℝ (Extension B) = Module.finrank ℝ V + Module.finrank ℝ (LinearMap.ker B) := by
  rw [Module.finrank_prod, Subspace.dual_finrank_eq]


theorem extension_dimension_minimal [FiniteDimensional ℝ V]
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ E)
    (hC : C.Nondegenerate) (i : V →ₗ[ℝ] E) (hi : Function.Injective i)
    (hform : ∀ v w, C (i v) (i w) = B v w) :
    Module.finrank ℝ V + Module.finrank ℝ (LinearMap.ker B) ≤ Module.finrank ℝ E := by
  let f : LinearMap.ker B →ₗ[ℝ] E := i.comp (LinearMap.ker B).subtype
  have hf : Function.Injective f := hi.comp Subtype.val_injective
  have hsub : LinearMap.range i ≤ C.orthogonal (LinearMap.range f) := by
    rintro _ ⟨v, rfl⟩
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    rintro _ ⟨k, rfl⟩
    change C (i k.val) (i v) = 0
    rw [hform, show B k.val = 0 from k.property]
    rfl
  have hd := Submodule.finrank_mono hsub
  rw [LinearMap.finrank_range_of_inj hi, LinearMap.BilinForm.finrank_orthogonal hC,
    LinearMap.finrank_range_of_inj hf] at hd
  have hk : Module.finrank ℝ (LinearMap.ker B) ≤ Module.finrank ℝ E := by
    rw [← LinearMap.finrank_range_of_inj hf]
    exact Submodule.finrank_le _
  omega

end KLInvariance.Realization

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
noncomputable section

abbrev Extended := Realization.Extension (form M)

def extendedForm : LinearMap.BilinForm ℝ (Extended M) :=
  Classical.choose (Realization.exists_minimal_nondegenerate_extension (form M) (form_symm M))

theorem extendedForm_spec : (extendedForm M).IsSymm ∧ (extendedForm M).Nondegenerate ∧
    ∀ v w, extendedForm M (v, 0) (w, 0) = form M v w :=
  Classical.choose_spec (Realization.exists_minimal_nondegenerate_extension (form M) (form_symm M))

def extendedRoot (i : I) : Extended M := (root i, 0)

@[simp] theorem extendedForm_roots (i j : I) :
    extendedForm M (extendedRoot M i) (extendedRoot M j) =
      -2 * Real.cos (Real.pi / M i j) := by
  rw [extendedRoot, extendedRoot, (extendedForm_spec M).2.2, form_roots]

theorem extendedRoot_linearIndependent : LinearIndependent ℝ (extendedRoot M) := by
  exact (root_linearIndependent (I := I)).map'
    (LinearMap.inl ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))
    (LinearMap.ker_eq_bot.mpr LinearMap.inl_injective)

/-- Both roots and coroots are independent in the actual minimal extension. -/
theorem extendedNormal_linearIndependent :
    LinearIndependent ℝ (fun i => extendedForm M (extendedRoot M i)) :=
  (extendedRoot_linearIndependent M).map' (extendedForm M) (extendedForm_spec M).2.1.ker_eq_bot

def extendedAction {W : Type v} [Group W] (cs : CoxeterSystem M W) :
    W →* (Extended M ≃ₗ[ℝ] Extended M) :=
  Realization.geometricAction cs (extendedForm M) (extendedRoot M) (extendedForm_roots M)

theorem extendedAction_preserves {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (w : W) (v z : Extended M) :
    extendedForm M (extendedAction M cs w v) (extendedAction M cs w z) = extendedForm M v z :=
  Realization.geometricAction_preserves cs (extendedForm M) (extendedRoot M)
    (extendedForm_roots M) (extendedForm_spec M).1 w v z

@[simp] theorem extendedAction_simple {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (i : I) (v : Extended M) :
    extendedAction M cs (cs.simple i) v =
      v - extendedForm M (extendedRoot M i) v • extendedRoot M i := by
  simp only [extendedAction, Realization.geometricAction_simple,
    Realization.geometricSimple, Module.reflection_apply]

/-- The extended action genuinely restricts to the ordinary geometric action.
Injectivity of that latter action is an outstanding obligation, not a hypothesis
hidden in the construction of this extension. -/
theorem extendedAction_restrict {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (w : W) (v : I → ℝ) :
    extendedAction M cs w (v, 0) = (action M cs w v, 0) := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  induction ω generalizing v with
  | nil => simp
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul, map_mul]
    simp only [LinearEquiv.mul_apply, ih, extendedAction_simple, action_simple]
    change (action M cs (cs.wordProd ω) v, 0) -
      extendedForm M (root i, 0) (action M cs (cs.wordProd ω) v, 0) • (root i, 0) = _
    rw [(extendedForm_spec M).2.2, form_root]
    ext <;> simp

theorem extended_finrank : Module.finrank ℝ (Extended M) =
    Fintype.card I + Module.finrank ℝ (LinearMap.ker (form M)) := by
  rw [Realization.extension_finrank, Module.finrank_pi]


def dominant : Module.Dual ℝ (Extended M) :=
  (∑ i : I, LinearMap.proj i).comp
    (LinearMap.fst ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))

@[simp] theorem dominant_root (i : I) : dominant M (extendedRoot M i) = 1 := by
  classical
  simp [dominant, extendedRoot, root]

end
end KLInvariance.TitsSpace

namespace KLInvariance
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}

namespace ParabolicSupport
open CoxeterSystem

variable (cs : CoxeterSystem M W) (J : Set B)

/-- The genuine subgroup generated by a subset of simple reflections. -/
def subgroup : Subgroup W := Subgroup.closure (cs.simple '' J)

theorem word_mem {ν : List B} (hν : ∀ i ∈ ν, i ∈ J) :
    cs.wordProd ν ∈ subgroup cs J := by
  induction ν with
  | nil => exact (subgroup cs J).one_mem
  | cons i ν ih =>
    rw [cs.wordProd_cons]
    exact (subgroup cs J).mul_mem
      (Subgroup.subset_closure ⟨i, hν i (by simp), rfl⟩)
      (ih fun j hj => hν j (by simp [hj]))

theorem exists_word {w : W} (hw : w ∈ subgroup cs J) :
    ∃ ν : List B, (∀ i ∈ ν, i ∈ J) ∧ cs.wordProd ν = w := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨i, hi, rfl⟩ := hw
    exact ⟨[i], by simpa using hi, by simp⟩
  | one => exact ⟨[], by simp, by simp⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨ω, hω, rfl⟩ := ihx
    obtain ⟨ν, hν, rfl⟩ := ihy
    exact ⟨ω ++ ν, fun i hi => (List.mem_append.mp hi).elim (hω i) (hν i),
      cs.wordProd_append ω ν⟩
  | inv x hx ih =>
    obtain ⟨ω, hω, rfl⟩ := ih
    exact ⟨ω.reverse, by simpa using hω, cs.wordProd_reverse ω⟩

theorem exists_reduced_word {w : W} (hw : w ∈ subgroup cs J) :
    ∃ ν : List B, (∀ i ∈ ν, i ∈ J) ∧ cs.IsReduced ν ∧ cs.wordProd ν = w := by
  obtain ⟨ω, hω, hprod⟩ := exists_word cs J hw
  obtain ⟨ν, hsub, hν, heq⟩ := exists_reduced_subword cs ω
  exact ⟨ν, fun i hi => hω i (hsub.subset hi), hν, heq.trans hprod⟩

/-- A minimal right-coset representative concatenates with every reduced
word in the parabolic generators without cancellations. -/
theorem reduced_append_of_minimal {u : W}
    (hmin : ∀ v ∈ subgroup cs J, cs.length u ≤ cs.length (u * v))
    {ω ν : List B} (hω : cs.IsReduced ω) (hu : cs.wordProd ω = u)
    (hν : cs.IsReduced ν) (hJ : ∀ i ∈ ν, i ∈ J) :
    cs.IsReduced (ω ++ ν) := by
  obtain ⟨τ, hsub, hτ, hprod⟩ := exists_reduced_subword cs (ω ++ ν)
  obtain ⟨ω', ν', rfl, hωsub, hνsub⟩ := List.sublist_append_iff.mp hsub
  have hprod' : cs.wordProd ω' * cs.wordProd ν' = u * cs.wordProd ν := by
    simpa [cs.wordProd_append, hu] using hprod
  have hω' : cs.wordProd ω' = u * (cs.wordProd ν * (cs.wordProd ν')⁻¹) := by
    rw [← mul_assoc, ← hprod']
    group
  have hlen := hmin (cs.wordProd ν * (cs.wordProd ν')⁻¹)
    ((subgroup cs J).mul_mem (word_mem cs J hJ)
      ((subgroup cs J).inv_mem (word_mem cs J fun i hi => hJ i (hνsub.subset hi))))
  rw [← hω'] at hlen
  have hbound := cs.length_wordProd_le ω'
  have homega := hω.eq
  rw [hu] at homega
  have hle := hωsub.length_le
  have heqω := hωsub.eq_of_length (by omega)
  subst ω'
  have heqν : cs.wordProd ν' = cs.wordProd ν := by
    rw [hu] at hprod'
    exact mul_left_cancel hprod'
  have hboundν := cs.length_wordProd_le ν'
  rw [heqν, hν.eq] at hboundν
  have heqν' := hνsub.eq_of_length (by have := hνsub.length_le; omega)
  simpa [heqν'] using hτ

theorem length_mul_of_minimal {u v : W}
    (hmin : ∀ z ∈ subgroup cs J, cs.length u ≤ cs.length (u * z))
    (hv : v ∈ subgroup cs J) : cs.length (u * v) = cs.length u + cs.length v := by
  obtain ⟨ω, hω, hu⟩ := cs.exists_isReduced u
  obtain ⟨ν, hJ, hν, hvprod⟩ := exists_reduced_word cs J hv
  have h := (reduced_append_of_minimal cs J hmin hω hu.symm hν hJ).eq
  simpa [cs.wordProd_append, hu, ← hvprod, hω.eq, hν.eq] using h

/-- Every right parabolic coset has a minimal representative. -/
theorem exists_minimal (w : W) :
    ∃ u v : W, v ∈ subgroup cs J ∧ w = u * v ∧
      ∀ z ∈ subgroup cs J, cs.length u ≤ cs.length (u * z) := by
  classical
  have hex : ∃ n : ℕ, ∃ u v : W, v ∈ subgroup cs J ∧ w = u * v ∧ cs.length u = n :=
    ⟨cs.length w, w, 1, (subgroup cs J).one_mem, by simp, rfl⟩
  obtain ⟨u, v, hv, hw, hu⟩ := Nat.find_spec hex
  refine ⟨u, v, hv, hw, fun z hz => ?_⟩
  rw [hu]
  apply Nat.find_min' hex
  refine ⟨u * z, z⁻¹ * v, (subgroup cs J).mul_mem ((subgroup cs J).inv_mem hz) hv, ?_, rfl⟩
  simpa [mul_assoc] using hw

theorem minimal_simple_ascent {u : W}
    (hmin : ∀ z ∈ subgroup cs J, cs.length u ≤ cs.length (u * z))
    {i : B} (hi : i ∈ J) : cs.length (u * cs.simple i) = cs.length u + 1 := by
  have h := length_mul_of_minimal cs J hmin (Subgroup.subset_closure ⟨i, hi, rfl⟩)
  simpa using h

/-- The decomposition is length-additive, including after multiplying by
any of the chosen simple generators. This is used in the root-sign induction. -/
theorem exists_length_additive_decomposition (w : W) :
    ∃ u v : W, v ∈ subgroup cs J ∧ w = u * v ∧
      cs.length w = cs.length u + cs.length v ∧
      (∀ i ∈ J, cs.length (u * cs.simple i) = cs.length u + 1) ∧
      (∀ i ∈ J, cs.length (w * cs.simple i) = cs.length u + cs.length (v * cs.simple i)) := by
  obtain ⟨u, v, hv, hw, hmin⟩ := exists_minimal cs J w
  refine ⟨u, v, hv, hw, ?_, (fun i hi => minimal_simple_ascent cs J hmin hi), ?_⟩
  · rw [hw]
    exact length_mul_of_minimal cs J hmin hv
  · intro i hi
    rw [hw, mul_assoc]
    exact length_mul_of_minimal cs J hmin
      ((subgroup cs J).mul_mem hv (Subgroup.subset_closure ⟨i, hi, rfl⟩))

end ParabolicSupport

end KLInvariance

namespace KLInvariance.ParabolicSupport
open CoxeterSystem
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

theorem reduced_of_append {ω ν : List B} (h : cs.IsReduced (ω ++ ν)) :
    cs.IsReduced ω := by
  simpa using h.take ω.length

/-- A reduced two-letter word followed by `i` must alternate and end in `j`. -/
theorem reduced_pair_eq_alternating {ω : List B} {i j : B} (hij : i ≠ j)
    (hJ : ∀ k ∈ ω, k = i ∨ k = j) (hred : cs.IsReduced (ω ++ [i])) :
    ω = alternatingWord i j ω.length := by
  induction ω using List.reverseRecOn generalizing i j with
  | nil => rfl
  | append_singleton ω k ih =>
    have hk : k = i ∨ k = j := hJ k (by simp)
    have hki : k ≠ i := by
      rintro rfl
      have hlen := hred.eq
      simp only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
        List.length_singleton, mul_assoc, cs.simple_mul_simple_self, mul_one] at hlen
      have := cs.length_wordProd_le ω
      omega
    have hkj : k = j := hk.resolve_left hki
    subst k
    have hprefix : cs.IsReduced (ω ++ [j]) := reduced_of_append cs hred
    rw [List.length_append, List.length_singleton, alternatingWord_succ, List.concat_eq_append]
    congr 1
    apply ih hij.symm
    · intro k hk
      exact (hJ k (List.mem_append.mpr (Or.inl hk))).symm
    · exact hprefix

/-- The coefficients in the root formula are controlled by genuine reducedness,
not by a separate rank-two length assumption. -/
theorem alternating_length_bound {ω : List B} {i j : B} (hij : i ≠ j)
    (hJ : ∀ k ∈ ω, k = i ∨ k = j) (hred : cs.IsReduced (ω ++ [i])) :
    M i j = 0 ∨ ω.length + 1 ≤ M i j := by
  by_cases hm : M i j = 0
  · exact Or.inl hm
  · right
    have heq := reduced_pair_eq_alternating cs hij hJ hred
    have hr : cs.IsReduced (alternatingWord j i (ω.length + 1)) := by
      rw [alternatingWord_succ, ← heq]
      simpa [List.concat_eq_append] using hred
    by_contra hn
    apply cs.not_isReduced_alternatingWord j i (by simpa [M.symmetric] using hm)
      (by simpa [M.symmetric] using (show M i j < ω.length + 1 by omega)) hr

end KLInvariance.ParabolicSupport

namespace KLInvariance.TitsSpace
open CoxeterSystem Polynomial Polynomial.Chebyshev
universe u v
variable {I : Type u} [klPreservedInstance5 : Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

def rootCoeff (i j : I) (n : ℤ) : ℝ :=
  (S ℝ n).eval (2 * Real.cos (Real.pi / M i j))

include klPreservedInstance5 in
@[simp] theorem rootCoeff_zero (i j : I) : rootCoeff M i j 0 = 1 := by
  have _ := klPreservedInstance5
  simp [rootCoeff]
include klPreservedInstance5 in
@[simp] theorem rootCoeff_neg_one (i j : I) : rootCoeff M i j (-1) = 0 := by
  have _ := klPreservedInstance5
  simp [rootCoeff]

include klPreservedInstance5 in
theorem rootCoeff_succ (i j : I) (n : ℤ) :
    rootCoeff M i j (n + 1) =
      (2 * Real.cos (Real.pi / M i j)) * rootCoeff M i j n - rootCoeff M i j (n-1) := by
  have _ := klPreservedInstance5
  simp [rootCoeff, S_add_one]

include klPreservedInstance5 in
@[simp] theorem gram_diag (i : I) : gram M i i = 2 := by
  have _ := klPreservedInstance5
  simp [gram]

/-- Exact rank-two root formula, including the infinite pairing. -/
theorem alternating_root (i j : I) (n : ℕ) :
    action M cs (cs.wordProd (alternatingWord i j n)) (root i) =
      if Even n then
        rootCoeff M i j n • root i + rootCoeff M i j ((n : ℤ)-1) • root j
      else rootCoeff M i j ((n : ℤ)-1) • root i + rootCoeff M i j n • root j := by
  induction n with
  | zero => simp [alternatingWord]
  | succ n ih =>
    rw [alternatingWord_succ', cs.wordProd_cons, map_mul, LinearEquiv.mul_apply, ih]
    have hrec := rootCoeff_succ M i j (n : ℤ)
    have hsymm : gram M j i = gram M i j := by simp [gram, M.symmetric j i]
    by_cases hn : Even n
    · simp only [hn, ite_true, Nat.even_add_one, not_true_eq_false, ite_false]
      rw [action_simple]
      simp only [map_add, map_smul, normal_root, gram_diag, hsymm]
      push_cast
      rw [show (n : ℤ) + 1 - 1 = n by omega, hrec]
      simp only [gram]
      module
    · simp only [hn, ite_false, Nat.even_add_one, not_false_eq_true, ite_true]
      rw [action_simple]
      simp only [map_add, map_smul, normal_root, gram_diag]
      push_cast
      rw [show (n : ℤ) + 1 - 1 = n by omega, hrec]
      simp only [gram]
      module

/-- For a reduced alternating word followed by the other generator, both
rank-two coefficients are nonnegative. -/
theorem rootCoeff_nonneg (i j : I) {n : ℤ} (hn : -1 ≤ n)
    (hm : M i j = 0 ∨ n + 1 ≤ (M i j : ℤ)) (hij : i ≠ j) :
    0 ≤ rootCoeff M i j n := by
  rcases hm with hm | hm
  · simp only [rootCoeff, hm, Nat.cast_zero, div_zero, Real.cos_zero, mul_one, S_eval_two]
    exact_mod_cast (by omega : (0 : ℤ) ≤ n + 1)
  · by_cases hn0 : n = -1
    · simp [hn0]
    have hn1 : 0 < n + 1 := by omega
    have hMpos : (0 : ℝ) < M i j := by exact_mod_cast (by omega : 0 < M i j)
    have hM2 : 2 ≤ M i j := by
      have := M.off_diagonal i j hij
      omega
    let θ : ℝ := Real.pi / M i j
    have hθpos : 0 < θ := div_pos Real.pi_pos hMpos
    have hθlt : θ < Real.pi := by
      dsimp [θ]
      apply (div_lt_iff₀ hMpos).2
      have : (2 : ℝ) ≤ M i j := by exact_mod_cast hM2
      nlinarith [Real.pi_pos]
    have hsin := Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
    have heq := S_two_mul_real_cos θ n
    have hargpos : 0 ≤ ((n : ℝ) + 1) * θ := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast hn1
      positivity
    have hargle : ((n : ℝ) + 1) * θ ≤ Real.pi := by
      dsimp [θ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hMpos).2
      have : (n : ℝ) + 1 ≤ M i j := by exact_mod_cast hm
      nlinarith [Real.pi_pos]
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hargpos hargle
    change 0 ≤ (S ℝ n).eval (2 * Real.cos θ)
    nlinarith [heq]
end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open CoxeterSystem
universe u v
variable {I : Type u} [klPreservedInstance6 : Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

include klPreservedInstance6 in
@[simp] theorem root_nonneg (i k : I) : 0 ≤ root i k := by
  have _ := klPreservedInstance6
  classical
  simp only [root, Pi.single_apply]
  split_ifs <;> norm_num

/-- Positivity of a rank-two reduced tail after an already positive prefix. -/
theorem pair_image_nonneg (u : W) {i j : I} (hij : i ≠ j)
    (hi : ∀ k, 0 ≤ action M cs u (root i) k)
    (hj : ∀ k, 0 ≤ action M cs u (root j) k)
    {ω : List I} (hJ : ∀ k ∈ ω, k = i ∨ k = j)
    (hred : cs.IsReduced (ω ++ [i])) :
    ∀ k, 0 ≤ action M cs (u * cs.wordProd ω) (root i) k := by
  have heq := ParabolicSupport.reduced_pair_eq_alternating cs hij hJ hred
  have hbound := ParabolicSupport.alternating_length_bound cs hij hJ hred
  have hn : 0 ≤ rootCoeff M i j (ω.length : ℤ) :=
    rootCoeff_nonneg M i j (by omega) (by rcases hbound with h|h; exact Or.inl h; right; omega) hij
  have hn' : 0 ≤ rootCoeff M i j ((ω.length : ℤ)-1) :=
    rootCoeff_nonneg M i j (by omega) (by rcases hbound with h|h; exact Or.inl h; right; omega) hij
  intro k
  rw [map_mul, LinearEquiv.mul_apply, heq, alternating_root]
  split_ifs
  all_goals
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (by assumption) (by exact hi k))
      (mul_nonneg (by assumption) (by first | exact hi k | exact hj k))

/-- The genuine Tits root-sign theorem for ascents, proved from exchange,
minimal parabolic cosets and the rank-two trigonometric formulas. -/
theorem action_root_nonneg_of_ascent (w : W) (i : I)
    (hasc : cs.length (w * cs.simple i) = cs.length w + 1) :
    ∀ k, 0 ≤ action M cs w (root i) k := by
  suffices ∀ n : ℕ, ∀ w : W, cs.length w = n → ∀ i : I,
      cs.length (w * cs.simple i) = cs.length w + 1 →
      ∀ k, 0 ≤ action M cs w (root i) k by
    exact this (cs.length w) w rfl i hasc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hwlen i hasc
    by_cases hw : w = 1
    · subst w
      simp
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one hw
    change cs.length (w * cs.simple j) < cs.length w at hj
    have hij : i ≠ j := by rintro rfl; omega
    obtain ⟨u, v, hv, huv, hlen, huasc, hmul⟩ :=
      ParabolicSupport.exists_length_additive_decomposition cs ({i, j} : Set I) w
    have himem : i ∈ ({i, j} : Set I) := by simp
    have hjmem : j ∈ ({i, j} : Set I) := by simp
    have hult : cs.length u < n := by
      have h := hmul j hjmem
      omega
    have hui := ih (cs.length u) hult u rfl i (huasc i himem)
    have huj := ih (cs.length u) hult u rfl j (huasc j hjmem)
    obtain ⟨ω, hJ, hω, hprod⟩ := ParabolicSupport.exists_reduced_word cs ({i,j} : Set I) hv
    have hvi : cs.length (v * cs.simple i) = cs.length v + 1 := by
      have h := hmul i himem
      omega
    have hωi : cs.IsReduced (ω ++ [i]) := by
      change cs.length (cs.wordProd (ω ++ [i])) = (ω ++ [i]).length
      simp only [cs.wordProd_append, cs.wordProd_singleton, hprod, List.length_append,
        List.length_singleton]
      rw [hvi, ← hprod, hω.eq]
    have hJ' : ∀ k ∈ ω, k = i ∨ k = j := by simpa using hJ
    rw [huv, ← hprod]
    exact pair_image_nonneg M cs u hij hui huj hJ' hωi

@[simp] theorem action_simple_root (i : I) : action M cs (cs.simple i) (root i) = -root i := by
  rw [action_simple, normal_root, gram_diag]
  module

/-- Descents carry a simple root into the negative cone. -/
theorem action_root_nonpos_of_descent (w : W) (i : I)
    (hdesc : cs.length (w * cs.simple i) < cs.length w) :
    ∀ k, action M cs w (root i) k ≤ 0 := by
  have hasc : cs.length ((w * cs.simple i) * cs.simple i) = cs.length (w * cs.simple i) + 1 := by
    rcases cs.length_mul_simple w i with h|h
    · omega
    · simpa [mul_assoc] using h.symm
  have h := action_root_nonneg_of_ascent M cs (w * cs.simple i) i hasc
  simpa only [map_mul, LinearEquiv.mul_apply, action_simple_root, map_neg,
    Pi.neg_apply, neg_nonneg] using h

/-- Faithfulness of the actual ordinary Tits action, not an added axiom. -/
theorem action_injective : Function.Injective (action M cs) := by
  apply (MonoidHom.ker_eq_bot_iff _).1
  apply (Subgroup.eq_bot_iff_forall _).2
  intro w hw
  by_contra hne
  obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hne
  have h := action_root_nonpos_of_descent M cs w i hi i
  have hw' : action M cs w = 1 := hw
  rw [hw'] at h
  norm_num [root] at h
end
end KLInvariance.TitsSpace

namespace KLInvariance.Realization
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Rank of the moving subspace is unchanged by conjugacy. -/
theorem finrank_moving_conj (g h : V ≃ₗ[ℝ] V) :
    Module.finrank ℝ (LinearMap.range ((h * g * h⁻¹).toLinearMap - LinearMap.id)) =
      Module.finrank ℝ (LinearMap.range (g.toLinearMap - LinearMap.id)) := by
  have heq : (h * g * h⁻¹).toLinearMap - LinearMap.id =
      h.toLinearMap.comp ((g.toLinearMap - LinearMap.id).comp h.symm.toLinearMap) := by
    ext v
    simp
  rw [heq, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ h.symm.range,
    h.finrank_map_eq]

/-- An orthogonal rank-one map negating a norm-two vector is its exact reflection. -/
theorem rank_one_eq_reflection_of_negates [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (g : V ≃ₗ[ℝ] V)
    (hg : ∀ v w, B (g v) (g w) = B v w)
    (hr : Module.finrank ℝ (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1)
    (e : V) (he : B e e = 2) (hge : g e = -e) :
    ∀ v, g v = Module.preReflection e (B e) v := by
  let d : V →ₗ[ℝ] V := g.toLinearMap - LinearMap.id
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  have hemem : e ∈ LinearMap.range d := by
    refine ⟨(- (1 / 2 : ℝ)) • e, ?_⟩
    change g (- (1 / 2 : ℝ) • e) - (- (1 / 2 : ℝ) • e) = e
    rw [map_smul, hge]
    module
  have hspan : Submodule.span ℝ {e} = LinearMap.range d := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by simpa using hemem)
    · rw [finrank_span_singleton he0]
      exact hr.symm
  intro v
  have hv : d v ∈ Submodule.span ℝ {e} := by rw [hspan]; exact LinearMap.mem_range_self _ v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  have hgform : g v = v + c • e := by
    change c • e = g v - v at hc
    rw [hc]
    abel
  have hB := hg e v
  rw [hge, hgform] at hB
  simp only [map_neg, LinearMap.neg_apply, map_add, map_smul, he, smul_eq_mul] at hB
  have hc' : c = - B e v := by linarith
  rw [hgform, hc', Module.preReflection_apply, neg_smul, sub_eq_add_neg]

/-- Commutation with a reflection makes its negative eigenspace invariant;
a nonpositive coordinate selects the negative, rather than positive, sign. -/
theorem negates_of_commutes_nonpos
    (B : LinearMap.BilinForm ℝ V) (g : V ≃ₗ[ℝ] V)
    (hg : ∀ v w, B (g v) (g w) = B v w)
    (e : V) (he : B e e = 2)
    (hcomm : g * Module.reflection he = Module.reflection he * g)
    (f : Module.Dual ℝ V) (hfe : f e = 1) (hfg : f (g e) ≤ 0) :
    g e = -e := by
  have h := LinearEquiv.congr_fun hcomm e
  simp only [LinearEquiv.mul_apply, Module.reflection_apply_self, map_neg,
    Module.reflection_apply] at h
  let c : ℝ := B e (g e) / 2
  have hge : g e = c • e := by
    dsimp [c]
    linear_combination (norm := module) (- (1 / 2 : ℝ)) • h
  have hc : c ≤ 0 := by simpa [hge, hfe] using hfg
  have hnorm := hg e e
  rw [hge] at hnorm
  simp only [map_smul, LinearMap.smul_apply, he, smul_eq_mul] at hnorm
  have hc' : c = -1 := by nlinarith [sq_nonneg (c + 1)]
  rw [hge, hc', neg_one_smul]
/-- The moving subspace of a genuine reflection is exactly its root line. -/
theorem range_reflection_sub_id (e : V) (f : Module.Dual ℝ V) (h : f e = 2) :
    LinearMap.range ((Module.reflection h).toLinearMap - LinearMap.id) =
      Submodule.span ℝ {e} := by
  apply le_antisymm
  · rintro z ⟨v, rfl⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨-f v, ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      Module.reflection_apply, neg_smul]
    abel
  · apply Submodule.span_le.mpr
    intro z hz
    have hz' : z = e := Set.mem_singleton_iff.mp hz
    rw [hz']
    refine ⟨(- (1 / 2 : ℝ)) • e, ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      Module.reflection_apply, map_smul, h]
    module

theorem finrank_reflection_sub_id (e : V) (f : Module.Dual ℝ V) (h : f e = 2) :
    Module.finrank ℝ (LinearMap.range
      ((Module.reflection h).toLinearMap - LinearMap.id)) = 1 := by
  rw [range_reflection_sub_id]
  apply finrank_span_singleton
  intro he
  simp [he] at h

end KLInvariance.Realization

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- Faithfulness persists in the actual nondegenerate extension. -/
theorem extendedAction_injective : Function.Injective (extendedAction M cs) := by
  intro w z h
  apply action_injective M cs
  ext v i
  have hv := congrArg (fun g : Extended M ≃ₗ[ℝ] Extended M => (g (v, 0)).1 i) h
  simpa only [extendedAction_restrict] using hv

@[simp] theorem extendedForm_root_self (i : I) :
    extendedForm M (extendedRoot M i) (extendedRoot M i) = 2 := by
  rw [extendedForm_roots, M.diagonal]
  norm_num

@[simp] theorem extendedAction_simple_eq (i : I) :
    extendedAction M cs (cs.simple i) = Module.reflection (extendedForm_root_self M i) := by
  apply LinearEquiv.ext
  intro v
  rw [extendedAction_simple, Module.reflection_apply]

/-- A rank-one element of the actual extended action is an involution. -/
theorem involution_of_moving_rank_one (w : W)
    (hr : Module.finrank ℝ (LinearMap.range
      ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1) : w⁻¹ = w := by
  obtain ⟨e, he, hform⟩ := Realization.orthogonal_finrank_one
    (extendedForm M) (extendedForm_spec M).1 (extendedForm_spec M).2.1
    (extendedAction M cs w) (extendedAction_preserves M cs w) hr
  have he2 : ((2 / extendedForm M e e) • extendedForm M e) e = 2 := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    field_simp
  have hw2 : w * w = 1 := by
    apply extendedAction_injective M cs
    apply LinearEquiv.ext
    intro v
    simp only [map_mul, map_one, LinearEquiv.mul_apply, hform]
    change _ = v
    exact Module.involutive_preReflection he2 v
  exact inv_eq_of_mul_eq_one_left hw2

/-- Reflection faithfulness, the difficult converse, proved by length descent.
This avoids assuming the finite-subgroup theorem cited in the manuscript. -/
theorem isReflection_of_moving_rank_one (w : W)
    (hr : Module.finrank ℝ (LinearMap.range
      ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1) :
    cs.IsReflection w := by
  suffices ∀ n : ℕ, ∀ w : W, cs.length w = n →
      Module.finrank ℝ (LinearMap.range
        ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1 →
      cs.IsReflection w from this (cs.length w) w rfl hr
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hlen hr
    have hwne : w ≠ 1 := by
      intro h
      subst w
      have heq : (extendedAction M cs 1).toLinearMap - LinearMap.id = 0 := by
        apply LinearMap.ext
        intro v
        change (extendedAction M cs 1) v - v = 0
        rw [map_one]
        change v - v = 0
        abel
      rw [heq, LinearMap.range_zero, finrank_bot] at hr
      omega
    have hwinv := involution_of_moving_rank_one M cs w hr
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hwne
    change cs.length (w * cs.simple i) < cs.length w at hi
    have hleft : cs.length (cs.simple i * w) < cs.length w := by
      have h := cs.length_inv (w * cs.simple i)
      simp only [mul_inv_rev, cs.inv_simple, hwinv] at h
      omega
    by_cases hcomm : cs.simple i * w = w * cs.simple i
    · have hcomm' : extendedAction M cs w * Module.reflection (extendedForm_root_self M i) =
          Module.reflection (extendedForm_root_self M i) * extendedAction M cs w := by
        rw [← extendedAction_simple_eq M cs i, ← map_mul, ← map_mul, hcomm]
      let f : Module.Dual ℝ (Extended M) := (LinearMap.proj i).comp
        (LinearMap.fst ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))
      have hf : f (extendedRoot M i) = 1 := by simp [f, extendedRoot, root]
      have hfg : f (extendedAction M cs w (extendedRoot M i)) ≤ 0 := by
        have hn := action_root_nonpos_of_descent M cs w i hi i
        simpa only [f, LinearMap.comp_apply, extendedRoot, extendedAction_restrict,
          LinearMap.fst_apply, LinearMap.proj_apply] using hn
      have hneg := Realization.negates_of_commutes_nonpos (extendedForm M)
        (extendedAction M cs w) (extendedAction_preserves M cs w)
        (extendedRoot M i) (extendedForm_root_self M i) hcomm' f hf hfg
      have heq : extendedAction M cs w = extendedAction M cs (cs.simple i) := by
        apply LinearEquiv.ext
        intro v
        rw [extendedAction_simple]
        exact Realization.rank_one_eq_reflection_of_negates (extendedForm M)
          (extendedAction M cs w) (extendedAction_preserves M cs w) hr
          (extendedRoot M i) (extendedForm_root_self M i) hneg v
      rw [extendedAction_injective M cs heq]
      exact cs.isReflection_simple i
    · let z := cs.simple i * w * cs.simple i
      have hzlt : cs.length z < n := by
        have hz := (right_descent_simple_mul_iff cs i i w hcomm).2 hi
        dsimp [z]
        omega
      have hzrank : Module.finrank ℝ (LinearMap.range
          ((extendedAction M cs z).toLinearMap - LinearMap.id)) = 1 := by
        have hc := Realization.finrank_moving_conj (extendedAction M cs w)
          (extendedAction M cs (cs.simple i))
        have hgi : (extendedAction M cs (cs.simple i))⁻¹ = extendedAction M cs (cs.simple i) := by
          rw [← map_inv, cs.inv_simple]
        have heq : extendedAction M cs z =
            extendedAction M cs (cs.simple i) * extendedAction M cs w *
              (extendedAction M cs (cs.simple i))⁻¹ := by
          dsimp [z]
          rw [map_mul, map_mul, hgi]
        rw [heq]
        exact hc.trans hr
      have hz := ih (cs.length z) hzlt z rfl hzrank
      have hc := hz.conj (w := cs.simple i)
      simpa [z, mul_assoc] using hc

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- The other direction of reflection faithfulness for the actual action. -/
theorem moving_rank_one_of_isReflection (w : W) (hw : cs.IsReflection w) :
    Module.finrank ℝ (LinearMap.range
      ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1 := by
  obtain ⟨z, i, rfl⟩ := hw
  have hc := Realization.finrank_moving_conj (extendedAction M cs (cs.simple i))
    (extendedAction M cs z)
  have heq : extendedAction M cs (z * cs.simple i * z⁻¹) =
      extendedAction M cs z * extendedAction M cs (cs.simple i) *
        (extendedAction M cs z)⁻¹ := by rw [map_mul, map_mul, map_inv]
  rw [heq, hc, extendedAction_simple_eq]
  exact Realization.finrank_reflection_sub_id _ _ _

theorem reflectionFaithful (w : W) :
    Module.finrank ℝ (LinearMap.range
      ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1 ↔ cs.IsReflection w :=
  ⟨isReflection_of_moving_rank_one M cs w, moving_rank_one_of_isReflection M cs w⟩

@[simp] theorem dominant_action_root (w : W) (i : I) :
    dominant M (extendedAction M cs w (extendedRoot M i)) =
      ∑ k, action M cs w (root i) k := by
  simp [extendedRoot, extendedAction_restrict, dominant]

/-- Strict dominant sign, not merely closed-cone positivity. -/
theorem dominant_pos_iff_ascent (w : W) (i : I) :
    0 < dominant M (extendedAction M cs w (extendedRoot M i)) ↔
      cs.length w < cs.length (w * cs.simple i) := by
  classical
  rw [dominant_action_root]
  rcases cs.length_mul_simple w i with h | h
  · have ha := action_root_nonneg_of_ascent M cs w i h
    have hv : action M cs w (root i) ≠ 0 := by
      apply (action M cs w).map_ne_zero_iff.mpr
      intro hz
      have hz' := congrFun hz i
      simp [root] at hz'
    have hex : ∃ k, 0 < action M cs w (root i) k := by
      by_contra! hn
      apply hv
      funext k
      exact le_antisymm (hn k) (ha k)
    have hs : 0 < ∑ k, action M cs w (root i) k := by
      apply (Finset.sum_pos_iff_of_nonneg (fun k _ => ha k)).mpr
      obtain ⟨k, hk⟩ := hex
      exact ⟨k, Finset.mem_univ _, hk⟩
    exact iff_of_true hs (by omega)
  · have hn := action_root_nonpos_of_descent M cs w i (by omega)
    have hs : ∑ k, action M cs w (root i) k ≤ 0 := Finset.sum_nonpos (fun k _ => hn k)
    exact iff_of_false (by linarith) (by omega)

/-- The strictly dominant linear form in the convention `(w ρ)(αᵢ)=ρ(w⁻¹αᵢ)`
has exactly the source manuscript's left-ascent sign. -/
theorem dominant_dual_pos_iff_left_ascent (w : W) (i : I) :
    0 < dominant M (extendedAction M cs w⁻¹ (extendedRoot M i)) ↔
      cs.length w < cs.length (cs.simple i * w) := by
  rw [dominant_pos_iff_ascent, cs.length_inv]
  have h : cs.length (w⁻¹ * cs.simple i) = cs.length (cs.simple i * w) := by
    rw [← cs.length_inv (cs.simple i * w)]
    simp
  rw [h]

end
end KLInvariance.TitsSpace

/-! Coordinate-dual geometric action. This exists in arbitrary rank and is
used only to prove the finite standard-parabolic reduction of the main goal. -/
namespace KLInvariance.Cotangent
open Module
universe u v
variable {I : Type u} (M : CoxeterMatrix I)
noncomputable section

def root (i : I) : I → ℝ := fun j => -2 * Real.cos (Real.pi / M i j)

lemma normal_root (i : I) : (LinearMap.proj i : (I → ℝ) →ₗ[ℝ] ℝ) (root M i) = 2 := by
  simp [root]

def simple (i : I) : (I → ℝ) ≃ₗ[ℝ] (I → ℝ) := Module.reflection (normal_root M i)

theorem simple_liftable : M.IsLiftable (simple M) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [M.diagonal, pow_one]
    apply LinearEquiv.ext
    intro v
    exact Module.involutive_reflection (normal_root M i) v
  by_cases hm0 : M i j = 0
  · rw [hm0, pow_zero]
  have hm2 : 2 ≤ M i j := by
    have := M.off_diagonal i j hij
    omega
  apply Realization.geometric_reflection_relation (normal_root M i) (normal_root M j)
    (M i j) hm2
  · simp [root, M.symmetric j i]
  · rfl

def action {W : Type v} [Group W] (cs : CoxeterSystem M W) :
    W →* ((I → ℝ) ≃ₗ[ℝ] (I → ℝ)) := cs.lift ⟨simple M, simple_liftable M⟩

@[simp] theorem action_simple {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (i : I) (l : I → ℝ) :
    action M cs (cs.simple i) l = l - l i • root M i := by
  rw [action, cs.lift_apply_simple]
  rfl

section Finite
variable [Fintype I] {W : Type v} [Group W] (cs : CoxeterSystem M W)

lemma dot_root (l : I → ℝ) (i : I) : l ⬝ᵥ TitsSpace.root i = l i := by
  classical
  simp [TitsSpace.root, dotProduct, Pi.single_apply]

lemma root_dot (i : I) (v : I → ℝ) :
    root M i ⬝ᵥ v = TitsSpace.normal M i v := by
  simp [root, TitsSpace.normal, TitsSpace.gram, dotProduct]

lemma simple_pairing (i : I) (l v : I → ℝ) :
    (action M cs (cs.simple i) l) ⬝ᵥ (TitsSpace.action M cs (cs.simple i) v) =
      l ⬝ᵥ v := by
  rw [action_simple, TitsSpace.action_simple]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    dot_root, root_dot]
  have hd : root M i i = 2 := by simp [root]
  rw [hd]
  simp only [smul_eq_mul]
  ring

theorem pairing (w : W) (l v : I → ℝ) :
    (action M cs w l) ⬝ᵥ (TitsSpace.action M cs w v) = l ⬝ᵥ v := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  induction ω generalizing l v with
  | nil => simp
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul, map_mul, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, simple_pairing, ih]

theorem action_injective : Function.Injective (action M cs) := by
  apply (injective_iff_map_eq_one _).2
  intro w hw
  apply TitsSpace.action_injective M cs
  rw [map_one]
  apply LinearEquiv.ext
  intro v
  apply dotProduct_eq
  intro l
  have h := pairing M cs w l v
  rw [hw] at h
  simpa [dotProduct_comm] using h
end Finite
end
end KLInvariance.Cotangent

namespace KLInvariance.StandardParabolic
open CoxeterSystem
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) (J : Set I)
noncomputable section

def matrix : CoxeterMatrix J where
  M i j := M i.val j.val
  isSymm := M.isSymm.submatrix Subtype.val
  diagonal i := M.diagonal i.val
  off_diagonal i j h := M.off_diagonal i.val j.val (fun h' => h (Subtype.ext h'))

abbrev system : CoxeterSystem (matrix (M := M) J) (matrix (M := M) J).Group :=
  (matrix (M := M) J).toCoxeterSystem

def inclusion : (matrix (M := M) J).Group →* W :=
  (system (M := M) J).lift ⟨fun i => cs.simple i.val,
    fun i j => cs.simple_mul_simple_pow i.val j.val⟩

@[simp] theorem inclusion_simple (i : J) :
    inclusion cs J ((system (M := M) J).simple i) = cs.simple i.val :=
  (system (M := M) J).lift_apply_simple _ i

lemma inclusion_word (ω : List J) :
    inclusion cs J ((system (M := M) J).wordProd ω) = cs.wordProd (ω.map Subtype.val) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [wordProd_cons, map_mul, inclusion_simple, List.map_cons, wordProd_cons, ih]

def restrictVec (l : I → ℝ) : J → ℝ := fun j => l j.val

lemma simple_restrict (i : J) (l : I → ℝ) :
    restrictVec J (Cotangent.action M cs (cs.simple i.val) l) =
      Cotangent.action (matrix (M := M) J) (system (M := M) J)
        ((system (M := M) J).simple i) (restrictVec J l) := by
  rw [Cotangent.action_simple, Cotangent.action_simple]
  funext j
  rfl

theorem action_restrict (w : (matrix (M := M) J).Group) (l : I → ℝ) :
    restrictVec J (Cotangent.action M cs (inclusion cs J w) l) =
      Cotangent.action (matrix (M := M) J) (system (M := M) J) w (restrictVec J l) := by
  obtain ⟨ω, rfl⟩ := (system (M := M) J).wordProd_surjective w
  induction ω generalizing l with
  | nil => simp
  | cons i ω ih =>
    rw [wordProd_cons, map_mul, inclusion_simple, map_mul, map_mul,
      LinearEquiv.mul_apply, LinearEquiv.mul_apply, simple_restrict, ih]

theorem inclusion_injective [Fintype J] : Function.Injective (inclusion cs J) := by
  classical
  apply (injective_iff_map_eq_one _).2
  intro w hw
  apply Cotangent.action_injective (matrix (M := M) J) (system (M := M) J)
  rw [map_one]
  apply LinearEquiv.ext
  intro l
  let l' : I → ℝ := fun i => if hi : i ∈ J then l ⟨i, hi⟩ else 0
  have hr : restrictVec J l' = l := by ext j; simp [restrictVec, l', j.property]
  have h := action_restrict cs J w l'
  rw [hw, map_one] at h
  change restrictVec J l' = _ at h
  rw [hr] at h
  exact h.symm

lemma lift_word {ω : List I} (hω : ∀ i ∈ ω, i ∈ J) :
    ∃ ν : List J, ν.map Subtype.val = ω := by
  induction ω with
  | nil => exact ⟨[], rfl⟩
  | cons i ω ih =>
    obtain ⟨ν, rfl⟩ := ih (fun j hj => hω j (by simp [hj]))
    exact ⟨⟨i, hω i (by simp)⟩ :: ν, rfl⟩

theorem inclusion_mem (w : (matrix (M := M) J).Group) :
    inclusion cs J w ∈ ParabolicSupport.subgroup cs J := by
  obtain ⟨ω, rfl⟩ := (system (M := M) J).wordProd_surjective w
  rw [inclusion_word]
  apply ParabolicSupport.word_mem
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  exact j.property

theorem inclusion_range : (inclusion cs J).range = ParabolicSupport.subgroup cs J := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact inclusion_mem cs J w
  · intro w hw
    obtain ⟨ω, hω, rfl⟩ := ParabolicSupport.exists_word cs J hw
    obtain ⟨ν, rfl⟩ := lift_word J hω
    exact ⟨(system (M := M) J).wordProd ν, inclusion_word cs J ν⟩

theorem length_inclusion [Fintype J] (w : (matrix (M := M) J).Group) :
    cs.length (inclusion cs J w) = (system (M := M) J).length w := by
  apply le_antisymm
  · obtain ⟨ω, hω, rfl⟩ := (system (M := M) J).exists_isReduced w
    rw [inclusion_word, hω.eq]
    simpa using cs.length_wordProd_le (ω.map Subtype.val)
  · obtain ⟨ω, hω, hred, hprod⟩ := ParabolicSupport.exists_reduced_word cs J
      (inclusion_mem cs J w)
    obtain ⟨ν, rfl⟩ := lift_word J hω
    have heq : (system (M := M) J).wordProd ν = w :=
      inclusion_injective cs J ((inclusion_word cs J ν).trans hprod)
    have hb := (system (M := M) J).length_wordProd_le ν
    rw [heq] at hb
    have hr := hred.eq
    rw [hprod, List.length_map] at hr
    omega

lemma reduced_map_iff [Fintype J] (ω : List J) :
    cs.IsReduced (ω.map Subtype.val) ↔ (system (M := M) J).IsReduced ω := by
  simp only [CoxeterSystem.IsReduced, List.length_map, ← inclusion_word, length_inclusion]

end
end KLInvariance.StandardParabolic

namespace KLInvariance.StandardParabolic
open CoxeterSystem
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) (J : Set I) [Fintype J]
noncomputable section

theorem bruhat_inclusion_iff (x y : (matrix (M := M) J).Group) :
    BruhatLE cs (inclusion cs J x) (inclusion cs J y) ↔
      BruhatLE (system (M := M) J) x y := by
  obtain ⟨ω, hω, rfl⟩ := (system (M := M) J).exists_isReduced y
  rw [inclusion_word]
  constructor
  · intro h
    obtain ⟨ν, hsub, _, hprod⟩ := (bruhat_iff_reduced_subword cs
      ((reduced_map_iff cs J ω).2 hω)).1 h
    obtain ⟨τ, hτ, rfl⟩ := List.sublist_map_iff.mp hsub
    have hx : (system (M := M) J).wordProd τ = x :=
      inclusion_injective cs J ((inclusion_word cs J τ).trans hprod)
    rw [← hx]
    exact bruhat_of_subword _ hτ hω
  · intro h
    obtain ⟨ν, hsub, _, rfl⟩ := (bruhat_iff_reduced_subword _ hω).1 h
    rw [inclusion_word]
    exact bruhat_of_subword cs (hsub.map Subtype.val) ((reduced_map_iff cs J ω).2 hω)

theorem lower_range (y : (matrix (M := M) J).Group) {z : W}
    (hzy : BruhatLE cs z (inclusion cs J y)) :
    ∃ x, inclusion cs J x = z := by
  obtain ⟨ω, hω, rfl⟩ := (system (M := M) J).exists_isReduced y
  rw [inclusion_word] at hzy
  obtain ⟨ν, hsub, _, hprod⟩ := (bruhat_iff_reduced_subword cs
    ((reduced_map_iff cs J ω).2 hω)).1 hzy
  obtain ⟨τ, _, rfl⟩ := List.sublist_map_iff.mp hsub
  exact ⟨(system (M := M) J).wordProd τ, (inclusion_word cs J τ).trans hprod⟩

def intervalMap (x y : (matrix (M := M) J).Group) :
    Interval (system (M := M) J) x y →
      Interval cs (inclusion cs J x) (inclusion cs J y) :=
  fun z => ⟨inclusion cs J z.val, (bruhat_inclusion_iff cs J x z.val).2 z.property.1,
    (bruhat_inclusion_iff cs J z.val y).2 z.property.2⟩

lemma intervalMap_bijective (x y : (matrix (M := M) J).Group) :
    Function.Bijective (intervalMap cs J x y) := by
  constructor
  · intro z t h
    exact Subtype.ext (inclusion_injective cs J (congrArg Subtype.val h))
  · intro z
    obtain ⟨w, hw⟩ := lower_range cs J y z.property.2
    refine ⟨⟨w, ?_, ?_⟩, Subtype.ext hw⟩
    · apply (bruhat_inclusion_iff cs J x w).1
      rw [hw]
      exact z.property.1
    · apply (bruhat_inclusion_iff cs J w y).1
      rw [hw]
      exact z.property.2

/-- The exact unlabelled interval identification used in the finite-rank
reduction; it arises from a proved embedding, not an added main hypothesis. -/
def intervalIso (x y : (matrix (M := M) J).Group) :
    Interval (system (M := M) J) x y ≃o
      Interval cs (inclusion cs J x) (inclusion cs J y) where
  toEquiv := Equiv.ofBijective _ (intervalMap_bijective cs J x y)
  map_rel_iff' := by
    intro z t
    exact bruhat_inclusion_iff cs J z.val t.val

@[simp] theorem intervalIso_val (x y : (matrix (M := M) J).Group)
    (z : Interval (system (M := M) J) x y) :
    (intervalIso cs J x y z).val = inclusion cs J z.val := rfl

lemma rankDifference_inclusion (x y : (matrix (M := M) J).Group) :
    rankDifference cs (inclusion cs J x) (inclusion cs J y) =
      rankDifference (system (M := M) J) x y := by
  simp only [rankDifference, length_inclusion]

/-- Restriction of the actual normalized families satisfies their exact
recurrence, degree bound and interval reciprocity in the standard parabolic. -/
theorem normalized_restriction {RP : PolynomialFamilies W} (hRP : NormalizedKL cs RP) :
    NormalizedKL (system (M := M) J)
      (fun x y => RP.1 (inclusion cs J x) (inclusion cs J y),
       fun x y => RP.2 (inclusion cs J x) (inclusion cs J y)) where
  R_diagonal x := hRP.R_diagonal _
  R_zero x y hxy := hRP.R_zero _ _ (fun h => hxy ((bruhat_inclusion_iff cs J x y).1 h))
  R_recursion := by
    intro x y i hy
    have hs (z : (matrix (M := M) J).Group) :
        inclusion cs J ((system (M := M) J).simple i * z) =
          cs.simple i.val * inclusion cs J z := by rw [map_mul, inclusion_simple]
    have hl (z : (matrix (M := M) J).Group) :
        cs.length (cs.simple i.val * inclusion cs J z) =
          (system (M := M) J).length ((system (M := M) J).simple i * z) := by
      rw [← hs, length_inclusion]
    have h := hRP.R_recursion (inclusion cs J x) (inclusion cs J y) i.val
      (by rwa [hl, length_inclusion])
    simpa only [hs, hl, length_inclusion] using h
  P_diagonal x := hRP.P_diagonal _
  P_zero x y hxy := hRP.P_zero _ _ (fun h => hxy ((bruhat_inclusion_iff cs J x y).1 h))
  P_degree := by
    intro x y hxy hne
    have h := hRP.P_degree (inclusion cs J x) (inclusion cs J y)
      ((bruhat_inclusion_iff cs J x y).2 hxy) (fun h => hne (inclusion_injective cs J h))
    rwa [rankDifference_inclusion] at h
  reciprocity := by
    intro x y hxy
    have h := hRP.reciprocity (inclusion cs J x) (inclusion cs J y)
      ((bruhat_inclusion_iff cs J x y).2 hxy)
    rw [rankDifference_inclusion] at h
    rw [h]
    let := interval_finite cs (inclusion cs J x) (inclusion cs J y)
    let := interval_finite (system (M := M) J) x y
    let := Fintype.ofFinite (Interval cs (inclusion cs J x) (inclusion cs J y))
    let := Fintype.ofFinite (Interval (system (M := M) J) x y)
    simp only [finsum_eq_sum_of_fintype]
    exact ((intervalIso cs J x y).toEquiv.sum_comp
      (fun z => RP.1 (inclusion cs J x) z.val * RP.2 z.val (inclusion cs J y))).symm

theorem klFamilies_inclusion :
    (fun x y => rPolynomial cs (inclusion cs J x) (inclusion cs J y),
     fun x y => klPolynomial cs (inclusion cs J x) (inclusion cs J y)) =
      klFamilies (system (M := M) J) :=
  normalizedKL_unique _ (normalized_restriction cs J (klFamilies_spec cs))
    (klFamilies_spec _)

theorem klPolynomial_inclusion (x y : (matrix (M := M) J).Group) :
    klPolynomial cs (inclusion cs J x) (inclusion cs J y) =
      klPolynomial (system (M := M) J) x y :=
  congrFun (congrFun (congrArg Prod.snd (klFamilies_inclusion cs J)) x) y

theorem rPolynomial_inclusion (x y : (matrix (M := M) J).Group) :
    rPolynomial cs (inclusion cs J x) (inclusion cs J y) =
      rPolynomial (system (M := M) J) x y :=
  congrFun (congrFun (congrArg Prod.fst (klFamilies_inclusion cs J)) x) y

end
end KLInvariance.StandardParabolic

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- A genuine real root, obtained from a simple root by the Tits action. -/
def IsRoot (a : I → ℝ) : Prop := ∃ w : W, ∃ i : I, a = action M cs w (root i)

/-- A normalized real root representing a genuine Coxeter reflection. -/
def Represents (t : W) (a : I → ℝ) : Prop :=
  ∃ w : W, ∃ i : I, t = w * cs.simple i * w⁻¹ ∧ a = action M cs w (root i)

abbrev embed (a : I → ℝ) : Extended M := (a, 0)

@[simp] theorem form_root_self (i : I) : form M (root i) (root i) = 2 := by
  simp []

variable {M cs}

theorem IsRoot.norm {a : I → ℝ} (ha : IsRoot M cs a) : form M a a = 2 := by
  obtain ⟨w,i,rfl⟩ := ha
  rw [action_preserves, form_root_self]

theorem IsRoot.ne_zero {a : I → ℝ} (ha : IsRoot M cs a) : a ≠ 0 := by
  intro he
  have hn := ha.norm
  simp [he] at hn

theorem IsRoot.sign {a : I → ℝ} (ha : IsRoot M cs a) :
    (∀ i, 0 ≤ a i) ∨ (∀ i, a i ≤ 0) := by
  obtain ⟨w,i,rfl⟩ := ha
  rcases lt_or_gt_of_ne (cs.length_mul_simple_ne w i) with h|h
  · exact Or.inr (action_root_nonpos_of_descent M cs w i h)
  · exact Or.inl (action_root_nonneg_of_ascent M cs w i (by
      rcases cs.length_mul_simple w i with h'|h' <;> omega))

theorem IsRoot.neg {a : I → ℝ} (ha : IsRoot M cs a) : IsRoot M cs (-a) := by
  obtain ⟨w,i,rfl⟩ := ha
  refine ⟨w * cs.simple i, i, ?_⟩
  simp only [map_mul, LinearEquiv.mul_apply, action_simple_root, map_neg]

theorem IsRoot.act {a : I → ℝ} (ha : IsRoot M cs a) (w : W) :
    IsRoot M cs (action M cs w a) := by
  obtain ⟨z,i,rfl⟩ := ha
  exact ⟨w*z, i, by simp only [map_mul, LinearEquiv.mul_apply]⟩

theorem Represents.isRoot {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    IsRoot M cs a := by
  obtain ⟨w,i,_,h⟩ := ha
  exact ⟨w,i,h⟩

theorem Represents.isReflection {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    cs.IsReflection t := by
  obtain ⟨w,i,h,_⟩ := ha
  exact ⟨w,i,h⟩

theorem Represents.neg {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    Represents M cs t (-a) := by
  obtain ⟨w,i,rfl,rfl⟩ := ha
  refine ⟨w * cs.simple i, i, ?_, ?_⟩
  · simp [mul_assoc]
  · simp only [map_mul, LinearEquiv.mul_apply, action_simple_root, map_neg]

theorem Represents.act {t : W} {a : I → ℝ} (ha : Represents M cs t a) (w : W) :
    Represents M cs (w*t*w⁻¹) (action M cs w a) := by
  obtain ⟨z,i,rfl,rfl⟩ := ha
  refine ⟨w*z,i,?_,?_⟩
  · group
  · simp only [map_mul, LinearEquiv.mul_apply]

/-- The actual reflection formula for every conjugate root in the minimal
nondegenerate extension, not merely for simple roots. -/
theorem Represents.formula {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (v : Extended M) :
    extendedAction M cs t v = v - extendedForm M (embed M a) v • embed M a := by
  obtain ⟨w,i,rfl,rfl⟩ := ha
  have hv : extendedAction M cs w (extendedAction M cs w⁻¹ v) = v := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hp := extendedAction_preserves M cs w (extendedRoot M i)
    (extendedAction M cs w⁻¹ v)
  rw [hv] at hp
  rw [map_mul, map_mul]
  simp only [LinearEquiv.mul_apply, extendedAction_simple, map_sub, map_smul]
  rw [hv, ← hp, extendedRoot, extendedAction_restrict]

theorem Represents.action_formula {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (v : I → ℝ) : action M cs t v = v - form M a v • a := by
  have h := congrArg Prod.fst (ha.formula (embed M v))
  simpa only [extendedAction_restrict, embed, (extendedForm_spec M).2.2,
    Prod.fst_sub, Prod.smul_fst] using h

theorem Represents.unique_up_to_sign {t : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs t b) : a = b ∨ a = -b := by
  have hn := ha.isRoot.norm
  have hm := hb.isRoot.norm
  have hf := ha.action_formula a
  rw [hb.action_formula a, hn] at hf
  have hmul : form M b a • b = (2 : ℝ) • a := by
    have h := congrArg (fun z => a-z) hf
    simpa only [sub_sub_cancel] using h
  have hab : a = (form M b a / 2) • b := by
    calc
      a = (1/2 : ℝ) • ((2 : ℝ) • a) := by module
      _ = (1/2 : ℝ) • (form M b a • b) := by rw [hmul]
      _ = _ := by module
  have hc : (form M b a / 2) ^ 2 = 1 := by
    rw [hab] at hn
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hm] at hn
    nlinarith
  rcases sq_eq_one_iff.mp hc with h|h
  · exact Or.inl (by simpa [h] using hab)
  · exact Or.inr (by simpa [h] using hab)

theorem Represents.reflection_unique {t s : W} {a : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s a) : t = s := by
  apply extendedAction_injective M cs
  apply LinearEquiv.ext
  intro v
  rw [ha.formula, hb.formula]

theorem Represents.unique_positive {t : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs t b)
    (hpa : ∀ i, 0 ≤ a i) (hpb : ∀ i, 0 ≤ b i) : a = b := by
  rcases ha.unique_up_to_sign hb with h|h
  · exact h
  · exfalso
    apply ha.isRoot.ne_zero
    ext i
    have hi := congrFun h i
    simp only [Pi.neg_apply] at hi
    have := hpa i
    have := hpb i
    simp only [Pi.zero_apply]
    linarith

variable (M) (cs)

theorem exists_positive_root {t : W} (ht : cs.IsReflection t) :
    ∃ a : I → ℝ, Represents M cs t a ∧ ∀ i, 0 ≤ a i := by
  obtain ⟨w,i,rfl⟩ := ht
  have hr : Represents M cs (w * cs.simple i * w⁻¹) (action M cs w (root i)) :=
    ⟨w,i,rfl,rfl⟩
  rcases hr.isRoot.sign with h|h
  · exact ⟨_,hr,h⟩
  · exact ⟨_,hr.neg,fun i => by simpa only [Pi.neg_apply, neg_nonneg] using h i⟩

/-- Genuine positive roots, with their actual coordinate sign. -/
def PositiveRoot := {a : I → ℝ // IsRoot M cs a ∧ ∀ i, 0 ≤ a i}

def positiveRoot (t : {t : W // cs.IsReflection t}) : PositiveRoot M cs :=
  ⟨(exists_positive_root M cs t.property).choose,
    (exists_positive_root M cs t.property).choose_spec.1.isRoot,
    (exists_positive_root M cs t.property).choose_spec.2⟩

theorem positiveRoot_represents (t : {t : W // cs.IsReflection t}) :
    Represents M cs t.val (positiveRoot M cs t).val :=
  (exists_positive_root M cs t.property).choose_spec.1

def rootReflection (a : PositiveRoot M cs) : {t : W // cs.IsReflection t} := by
  let w := a.property.1.choose
  let i := a.property.1.choose_spec.choose
  exact ⟨w * cs.simple i * w⁻¹, w,i,rfl⟩

theorem rootReflection_represents (a : PositiveRoot M cs) :
    Represents M cs (rootReflection M cs a).val a.val := by
  refine ⟨a.property.1.choose, a.property.1.choose_spec.choose, rfl, ?_⟩
  exact a.property.1.choose_spec.choose_spec


def positiveRootEquiv : {t : W // cs.IsReflection t} ≃ PositiveRoot M cs where
  toFun := positiveRoot M cs
  invFun := rootReflection M cs
  left_inv t := Subtype.ext ((rootReflection_represents M cs _).reflection_unique
      (positiveRoot_represents M cs t))
  right_inv a := Subtype.ext ((positiveRoot_represents M cs _).unique_positive
      (rootReflection_represents M cs a) (positiveRoot M cs _).property.2 a.property.2)

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem IsRoot.not_both {a : I → ℝ} (ha : IsRoot M cs a)
    (hp : ∀ i, 0 ≤ a i) (hn : ∀ i, a i ≤ 0) : False := by
  apply ha.ne_zero
  ext i
  exact le_antisymm (hn i) (hp i)

/-- A simple reflection can turn a positive real root negative only on its
own root. This uses actual Tits coordinates and normalization. -/
theorem IsRoot.eq_simple_of_nonpos {a : I → ℝ} (ha : IsRoot M cs a)
    (hp : ∀ k, 0 ≤ a k) (i : I)
    (hn : ∀ k, action M cs (cs.simple i) a k ≤ 0) : a = root i := by
  classical
  have ha0 (k : I) (hk : k ≠ i) : a k = 0 := by
    have h := hn k
    simp only [action_simple, Pi.sub_apply, Pi.smul_apply, root,
      Pi.single_apply, hk, ↓reduceIte, smul_eq_mul, mul_zero, sub_zero] at h
    exact le_antisymm h (hp k)
  have heq : a = a i • root i := by
    ext k
    by_cases hki : k = i
    · subst k; simp [root]
    · simp [root, hki, ha0 k hki]
  have hnorm := ha.norm
  rw [heq] at hnorm
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, form_root_self] at hnorm
  have hai : a i = 1 := by nlinarith [hp i]
  simpa only [hai, one_smul] using heq

theorem Represents.simple_sign {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (hp : ∀ k, 0 ≤ a k) (i : I) :
    ((∀ k, action M cs (cs.simple i) a k ≤ 0) ↔ t = cs.simple i) ∧
    ((∀ k, 0 ≤ action M cs (cs.simple i) a k) ↔ t ≠ cs.simple i) := by
  have hi : Represents M cs (cs.simple i) (root i) := ⟨1,i,by simp,by simp⟩
  have hneg : (∀ k, action M cs (cs.simple i) a k ≤ 0) ↔ t = cs.simple i := by
    constructor
    · intro h
      have heq := ha.isRoot.eq_simple_of_nonpos hp i h
      exact ha.reflection_unique (heq.symm ▸ hi)
    · intro h
      have heq := (h ▸ ha).unique_positive hi hp (root_nonneg i)
      simpa only [heq, action_simple_root, Pi.neg_apply, neg_nonpos] using root_nonneg i
  refine ⟨hneg, ?_⟩
  constructor
  · intro h heq
    exact (ha.isRoot.act (cs.simple i)).not_both h (hneg.mpr heq)
  · intro h
    rcases (ha.isRoot.act (cs.simple i)).sign with hp|hn
    · exact hp
    · exact False.elim (h (hneg.mp hn))

/-- The signed combinatorial reflection action is the actual root sign
under the faithful Tits representation. -/
def SignedRepresents (p : W × ZMod 2) (a : I → ℝ) : Prop :=
  Represents M cs p.1 a ∧
    ((p.2 = 0 ∧ ∀ i, 0 ≤ a i) ∨ (p.2 = 1 ∧ ∀ i, a i ≤ 0))

theorem SignedRepresents.simple {p : W × ZMod 2} {a : I → ℝ}
    (ha : SignedRepresents (M := M) (cs := cs) p a) (i : I) :
    SignedRepresents (M := M) (cs := cs) (CoxeterSupport.simpleAction cs i p)
      (action M cs (cs.simple i) a) := by
  rcases p with ⟨t,z⟩
  rw [CoxeterSupport.simpleAction_apply]
  refine ⟨?_,?_⟩
  · simpa only [cs.inv_simple] using ha.1.act (cs.simple i)
  · rcases ha.2 with ⟨rfl,hp⟩|⟨rfl,hn⟩
    · by_cases heq : t = cs.simple i
      · exact Or.inr ⟨by simp [heq], (ha.1.simple_sign hp i).1.mpr heq⟩
      · exact Or.inl ⟨by simp [heq, ZModModule.add_self], (ha.1.simple_sign hp i).2.mpr heq⟩
    · have hp : ∀ k, 0 ≤ (-a) k := fun k => neg_nonneg.mpr (hn k)
      by_cases heq : t = cs.simple i
      · refine Or.inl ⟨by simp [heq, ZModModule.add_self], ?_⟩
        have h := (ha.1.neg.simple_sign hp i).1.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonpos] using h
      · refine Or.inr ⟨by simp [heq], ?_⟩
        have h := (ha.1.neg.simple_sign hp i).2.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonneg] using h

theorem SignedRepresents.act {p : W × ZMod 2} {a : I → ℝ}
    (ha : SignedRepresents (M := M) (cs := cs) p a) (w : W) :
    SignedRepresents (M := M) (cs := cs) (CoxeterSupport.reflectionAction cs w p)
      (action M cs w a) := by
  obtain ⟨ω,rfl⟩ := cs.wordProd_surjective w
  induction ω with
  | nil => simpa using ha
  | cons i ω ih =>
    simpa only [cs.wordProd_cons, map_mul, Equiv.Perm.mul_apply,
      CoxeterSupport.reflectionAction_simple, LinearEquiv.mul_apply] using ih.simple i


theorem Represents.inversion_iff {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (hp : ∀ i, 0 ≤ a i) (w : W) :
    (∀ i, action M cs w⁻¹ a i ≤ 0) ↔ cs.IsLeftInversion w t := by
  classical
  obtain ⟨ω,hω,heq⟩ := cs.exists_isReduced w
  rw [heq]
  let c : ZMod 2 := (cs.leftInvSeq ω).count t
  have hc : c+c=0 := ZModModule.add_self c
  have hrec := CoxeterSupport.wordAction_record cs ω t c
  rw [← CoxeterSupport.reflectionAction_wordProd] at hrec
  have hrec' : CoxeterSupport.reflectionAction cs (cs.wordProd ω)
      ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω, c) = (t,0) := by
    change CoxeterSupport.reflectionAction cs (cs.wordProd ω)
      ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω,c) = (t,c+c) at hrec
    rwa [hc] at hrec
  have hinv : CoxeterSupport.reflectionAction cs (cs.wordProd ω)⁻¹ (t,0) =
      ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω,c) := by
    rw [map_inv, ← hrec']
    exact Equiv.symm_apply_apply _ _
  have hs : SignedRepresents (M := M) (cs := cs) (t,0) a := ⟨ha,Or.inl ⟨rfl,hp⟩⟩
  have hsi := hs.act (cs.wordProd ω)⁻¹
  rw [hinv] at hsi
  have hcount : c = if t ∈ cs.leftInvSeq ω then 1 else 0 := by
    dsimp [c]
    by_cases hm : t ∈ cs.leftInvSeq ω
    · rw [ite_eq_left hm, List.count_eq_one_of_mem hω.nodup_leftInvSeq hm]
      norm_num
    · rw [ite_eq_right hm, List.count_eq_zero.mpr hm]
      rfl
  have hmem : (∀ i, action M cs (cs.wordProd ω)⁻¹ a i ≤ 0) ↔ t ∈ cs.leftInvSeq ω := by
    by_cases hm : t ∈ cs.leftInvSeq ω
    · have hc1 : c=1 := by simpa [hm] using hcount
      simp only [hc1] at hsi
      rcases hsi.2 with ⟨hbad,_⟩|⟨_,hn⟩
      · norm_num at hbad
      · exact iff_of_true hn hm
    · have hc0 : c=0 := by simpa [hm] using hcount
      simp only [hc0] at hsi
      rcases hsi.2 with ⟨_,hpos⟩|⟨hbad,_⟩
      · exact iff_of_false (fun hn => (ha.isRoot.act _).not_both hpos hn) hm
      · norm_num at hbad
  rw [hmem]
  exact ⟨cs.isLeftInversion_of_mem_leftInvSeq hω,
    CoxeterSupport.mem_leftInvSeq_of_inversion cs hω⟩

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem Represents.independent_of_ne {t s : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hts : t ≠ s) :
    LinearIndependent ℝ ![a,b] := by
  apply (LinearIndependent.pair_iff' ha.isRoot.ne_zero).mpr
  intro c heq
  have hn := hb.isRoot.norm
  rw [← heq] at hn
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ha.isRoot.norm] at hn
  have hc : c^2 = 1 := by nlinarith
  rcases sq_eq_one_iff.mp hc with hc|hc
  · have hab : a=b := by simpa only [hc,one_smul] using heq
    exact hts (ha.reflection_unique (hab.symm ▸ hb))
  · have hab : -a=b := by simpa only [hc,neg_one_smul] using heq
    exact hts (ha.neg.reflection_unique (hab.symm ▸ hb))

theorem Represents.extended_independent_of_ne {t s : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hts : t ≠ s) :
    LinearIndependent ℝ ![embed M a,embed M b] := by
  have h := (ha.independent_of_ne hb hts).map'
    (LinearMap.inl ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))
    (LinearMap.ker_eq_bot.mpr LinearMap.inl_injective)
  have heq : (⇑(LinearMap.inl ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M)))) ∘
      ![a,b]) = ![embed M a,embed M b] := by
    funext i
    fin_cases i <;> rfl
  rwa [heq] at h

theorem Represents.extendedAction_eq {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    extendedAction M cs t = Module.reflection
      (show extendedForm M (embed M a) (embed M a) = 2 by
        rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm) := by
  apply LinearEquiv.ext
  intro v
  exact ha.formula v


theorem Represents.plane_eq_of_product_eq {t s r q : W} {a b c d : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b)
    (hc : Represents M cs r c) (hd : Represents M cs q d)
    (hts : t ≠ s) (hrq : r ≠ q) (heq : t*s=r*q) :
    Submodule.span ℝ {embed M a, embed M b} =
      Submodule.span ℝ {embed M c, embed M d} := by
  apply ReflectionPlane.plane_eq_of_reflection_product_eq (extendedForm M)
    (extendedForm_spec M).2.1 (embed M a) (embed M b) (embed M c) (embed M d)
    (by rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hb.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hc.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hd.isRoot.norm)
    (ha.extended_independent_of_ne hb hts) (hc.extended_independent_of_ne hd hrq)
  have h := congrArg (extendedAction M cs) heq
  rw [map_mul, map_mul, ha.extendedAction_eq, hb.extendedAction_eq,
    hc.extendedAction_eq, hd.extendedAction_eq] at h
  exact congrArg LinearEquiv.toLinearMap h

variable (M) (cs)
/-- The actual positive ambient roots inverted by `w`. -/
def RootInversions (w : W) :=
  {a : PositiveRoot M cs // ∀ i, action M cs w⁻¹ a.val i ≤ 0}

def rootInversionEquiv (w : W) : RootInversions M cs w ≃ {t : W // cs.IsLeftInversion w t} where
  toFun a := ⟨(rootReflection M cs a.val).val,
    ((rootReflection_represents M cs a.val).inversion_iff a.val.property.2 w).mp a.property⟩
  invFun t := ⟨positiveRoot M cs ⟨t.val,t.property.1⟩,
    ((positiveRoot_represents M cs ⟨t.val,t.property.1⟩).inversion_iff
      (positiveRoot M cs ⟨t.val,t.property.1⟩).property.2 w).mpr t.property⟩
  left_inv a := by
    apply Subtype.ext
    exact (positiveRootEquiv M cs).apply_symm_apply a.val
  right_inv t := by
    apply Subtype.ext
    change (rootReflection M cs (positiveRoot M cs ⟨t.val,t.property.1⟩)).val = t.val
    exact congrArg (fun r : {r : W // cs.IsReflection r} => r.val)
      ((positiveRootEquiv M cs).symm_apply_apply ⟨t.val,t.property.1⟩)

def leftInversionListEquiv {ω : List I} (hω : cs.IsReduced ω) :
    {t : W // cs.IsLeftInversion (cs.wordProd ω) t} ≃ {t : W // t ∈ cs.leftInvSeq ω} where
  toFun t := ⟨t.val,CoxeterSupport.mem_leftInvSeq_of_inversion cs hω t.property⟩
  invFun t := ⟨t.val,cs.isLeftInversion_of_mem_leftInvSeq hω t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full ambient inversion count, not a cardinality assumption. -/
theorem rootInversions_finite (w : W) : Finite (RootInversions M cs w) := by
  classical
  obtain ⟨ω,hω,heq⟩ := cs.exists_isReduced w
  rw [heq]
  exact Finite.of_equiv (Fin (cs.leftInvSeq ω).length)
    ((List.Nodup.getEquiv (cs.leftInvSeq ω) hω.nodup_leftInvSeq).trans
      ((leftInversionListEquiv M cs hω).symm.trans (rootInversionEquiv M cs _).symm))

theorem card_rootInversions (w : W) : Nat.card (RootInversions M cs w) = cs.length w := by
  classical
  obtain ⟨ω,hω,heq⟩ := cs.exists_isReduced w
  rw [heq, Nat.card_congr (rootInversionEquiv M cs _),
    Nat.card_congr (leftInversionListEquiv M cs hω),
    ← Nat.card_congr (List.Nodup.getEquiv (cs.leftInvSeq ω) hω.nodup_leftInvSeq),
    Nat.card_fin, cs.length_leftInvSeq, hω.eq]

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- Elements whose actual linear displacement lies in `P`. This is a
subgroup even when the invariant bilinear form restricted to `P` is singular. -/
def movingSubgroup (P : Submodule ℝ (I → ℝ)) : Subgroup W where
  carrier := {w | ∀ v, action M cs w v - v ∈ P}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro w z hw hz v
    have h := P.add_mem (hw (action M cs z v)) (hz v)
    simpa only [map_mul, LinearEquiv.mul_apply, sub_add_sub_cancel] using h
  inv_mem' := by
    intro w hw v
    have h := P.neg_mem (hw (action M cs w⁻¹ v))
    have hv : action M cs w (action M cs w⁻¹ v) = v := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    simpa only [hv, neg_sub] using h

/-- The manuscript's maximal plane reflection subgroup, defined using
actual normalized roots, not by assuming a rank-two presentation. -/
def planeSubgroup (P : Submodule ℝ (I → ℝ)) : Subgroup W :=
  Subgroup.closure {t | ∃ a, Represents M cs t a ∧ a ∈ P}

theorem planeSubgroup_le_moving (P : Submodule ℝ (I → ℝ)) :
    planeSubgroup M cs P ≤ movingSubgroup M cs P := by
  apply (Subgroup.closure_le (movingSubgroup M cs P)).mpr
  rintro t ⟨a,ha,haP⟩ v
  rw [ha.action_formula]
  have heq : v - form M a v • a - v = (-form M a v) • a := by module
  rw [heq]
  exact P.smul_mem _ haP

theorem Represents.mem_of_moving {P : Submodule ℝ (I → ℝ)} {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (ht : t ∈ movingSubgroup M cs P) : a ∈ P := by
  have h := ht a
  change action M cs t a - a ∈ P at h
  rw [ha.action_formula,ha.isRoot.norm] at h
  have heq : a - (2 : ℝ) • a - a = (-2 : ℝ) • a := by module
  rw [heq] at h
  have h' := P.smul_mem (-1/2 : ℝ) h
  have heq' : (-1/2 : ℝ) • ((-2 : ℝ) • a) = a := by module
  rwa [heq'] at h'


theorem Represents.planeSubgroup_mem_iff {P : Submodule ℝ (I → ℝ)} {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) : t ∈ planeSubgroup M cs P ↔ a ∈ P := by
  constructor
  · intro ht
    exact Represents.mem_of_moving M cs ha (planeSubgroup_le_moving M cs P ht)
  · intro haP
    exact Subgroup.subset_closure ⟨a,ha,haP⟩

/-- Two ambient vertices in a left coset of this plane subgroup can have
no reflection edge except one whose actual root is in the plane. -/
theorem reflection_between_coset_mem {P : Submodule ℝ (I → ℝ)} {t g h a : W}
    (hg : g ∈ planeSubgroup M cs P) (hh : h ∈ planeSubgroup M cs P)
    (heq : h*a=t*(g*a)) {r : I → ℝ} (ht : Represents M cs t r) : r ∈ P := by
  have htg : t*g=h := by apply mul_right_cancel (b := a); simpa only [mul_assoc] using heq.symm
  have htG : t ∈ planeSubgroup M cs P := by
    have heq' : t=h*g⁻¹ := by rw [← htg]; group
    rw [heq']
    exact (planeSubgroup M cs P).mul_mem hh ((planeSubgroup M cs P).inv_mem hg)
  exact (Represents.planeSubgroup_mem_iff M cs ht).mp htG

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- Least ambient length in each actual left plane-subgroup coset. No
uniqueness or rank-two Coxeter presentation is smuggled into this definition. -/
theorem planeCoset_exists_minimal (P : Submodule ℝ (I → ℝ)) (a : W) :
    ∃ a₀ g : W, g ∈ planeSubgroup M cs P ∧ a = g*a₀ ∧
      ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀) := by
  classical
  have hex : ∃ n : ℕ, ∃ a₀ g : W, g ∈ planeSubgroup M cs P ∧
      a = g*a₀ ∧ cs.length a₀ = n :=
    ⟨cs.length a,a,1,(planeSubgroup M cs P).one_mem,by simp,rfl⟩
  obtain ⟨a₀,g,hg,ha,hlen⟩ := Nat.find_spec hex
  refine ⟨a₀,g,hg,ha,fun z hz => ?_⟩
  rw [hlen]
  apply Nat.find_min' hex
  refine ⟨z*a₀,g*z⁻¹,(planeSubgroup M cs P).mul_mem hg
    ((planeSubgroup M cs P).inv_mem hz),?_,rfl⟩
  simpa [mul_assoc] using ha

variable {M cs}

theorem planeSubgroup_preserves {P : Submodule ℝ (I → ℝ)} {g : W}
    (hg : g ∈ planeSubgroup M cs P) {a : I → ℝ} (ha : a ∈ P) :
    action M cs g a ∈ P := by
  have h := (planeSubgroup_le_moving M cs P hg) a
  simpa only [sub_add_cancel] using P.add_mem h ha

/-- A least coset representative sends every positive plane root to a
positive ambient root under its inverse, by the proved inversion criterion. -/
theorem root_nonneg_of_coset_minimal {P : Submodule ℝ (I → ℝ)} {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a : I → ℝ} (ha : IsRoot M cs a) (hp : ∀ i, 0 ≤ a i) (haP : a ∈ P) :
    ∀ i, 0 ≤ action M cs a₀⁻¹ a i := by
  let r : PositiveRoot M cs := ⟨a,ha,hp⟩
  have hr := rootReflection_represents M cs r
  have htP := (Represents.planeSubgroup_mem_iff M cs hr).mpr haP
  rcases (ha.act a₀⁻¹).sign with hpos|hneg
  · exact hpos
  · have hi := (hr.inversion_iff hp a₀).mp hneg
    exact (not_lt_of_ge (hmin _ htP) hi.2).elim


theorem root_nonpos_coset_minimal_iff {P : Submodule ℝ (I → ℝ)} {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a : I → ℝ} (ha : IsRoot M cs a) (haP : a ∈ P) :
    (∀ i, action M cs a₀⁻¹ a i ≤ 0) ↔ ∀ i, a i ≤ 0 := by
  rcases ha.sign with hp|hn
  · have hnew := root_nonneg_of_coset_minimal hmin ha hp haP
    exact iff_of_false ((ha.act _).not_both hnew) (ha.not_both hp)
  · have hnp : ∀ i, 0 ≤ (-a) i := fun i => neg_nonneg.mpr (hn i)
    have hh := root_nonneg_of_coset_minimal hmin ha.neg hnp (P.neg_mem haP)
    have hnew : ∀ i, action M cs a₀⁻¹ a i ≤ 0 := by
      intro i
      simpa only [map_neg, Pi.neg_apply, neg_nonneg] using hh i
    exact iff_of_true hnew hn

theorem root_inversion_coset_iff {P : Submodule ℝ (I → ℝ)} {a₀ g : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (hg : g ∈ planeSubgroup M cs P) {a : I → ℝ} (ha : IsRoot M cs a)
    (haP : a ∈ P) :
    (∀ i, action M cs (g*a₀)⁻¹ a i ≤ 0) ↔
      ∀ i, action M cs g⁻¹ a i ≤ 0 := by
  rw [mul_inv_rev, map_mul]
  change (∀ i, action M cs a₀⁻¹ (action M cs g⁻¹ a) i ≤ 0) ↔ _
  exact root_nonpos_coset_minimal_iff hmin (ha.act _)
    (planeSubgroup_preserves ((planeSubgroup M cs P).inv_mem hg) haP)

theorem leftInversion_coset_iff {P : Submodule ℝ (I → ℝ)} {a₀ g t : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (hg : g ∈ planeSubgroup M cs P) (ht : t ∈ planeSubgroup M cs P)
    (hr : cs.IsReflection t) :
    cs.IsLeftInversion (g*a₀) t ↔ cs.IsLeftInversion g t := by
  let a := positiveRoot M cs ⟨t,hr⟩
  have ha := positiveRoot_represents M cs ⟨t,hr⟩
  rw [← ha.inversion_iff a.property.2, ← ha.inversion_iff a.property.2]
  exact root_inversion_coset_iff hmin hg a.property.1
    ((Represents.planeSubgroup_mem_iff M cs ha).mp ht)

/-- The directed ambient reflection graph on any plane-subgroup coset is
exactly transported from that on the subgroup by a least coset representative.
Identifying this graph with a *dihedral Coxeter* graph still requires the
canonical rank-two reflection-subgroup theorem. -/
theorem bruhatStep_coset_iff {P : Submodule ℝ (I → ℝ)} {a₀ g h : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (hg : g ∈ planeSubgroup M cs P) (hh : h ∈ planeSubgroup M cs P) :
    BruhatStep cs (g*a₀) (h*a₀) ↔ BruhatStep cs g h := by
  have hn : ∀ {t : W}, h=t*g → cs.IsReflection t →
      (cs.length (g*a₀) < cs.length (h*a₀) ↔ cs.length g < cs.length h) := by
    intro t heq ht
    have htP : t ∈ planeSubgroup M cs P := by
      have htgh : t=h*g⁻¹ := by rw [heq]; group
      rw [htgh]
      exact (planeSubgroup M cs P).mul_mem hh ((planeSubgroup M cs P).inv_mem hg)
    have hi := leftInversion_coset_iff hmin hh htP ht
    have hth : t*h=g := by rw [heq,← mul_assoc,ht.mul_self,one_mul]
    simpa only [CoxeterSystem.IsLeftInversion, ht, true_and, ← mul_assoc, hth] using hi
  constructor
  · rintro ⟨hlen,t,ht,heq⟩
    have htg : h=t*g := by apply mul_right_cancel (b := a₀); simpa only [mul_assoc] using heq
    exact ⟨(hn htg ht).mp hlen,t,ht,htg⟩
  · rintro ⟨hlen,t,ht,heq⟩
    exact ⟨(hn heq ht).mpr hlen,t,ht,by rw [heq,mul_assoc]⟩

end
end KLInvariance.TitsSpace

/-! Construction of the source's geometric reflection schedule. The moment
curve avoids every forbidden hyperplane of a countable root set, using only
finite polynomial root sets and uncountability of the real field. -/

end

end OAI
