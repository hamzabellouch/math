import OAI.Combinatorics.Hamiltonian.Bonds

namespace OAI

/-! Vertex quotients and connected fibers of incidence networks. -/

namespace Barnette.Network
noncomputable section
variable {V W E K : Type*}
open scoped Classical

def push [Fintype V] (q : V → W) : (V → ℝ) →ₗ[ℝ] (W → ℝ) where
  toFun x w := ∑ v, if q v = w then x v else 0
  map_add' x y := by
    ext w
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  map_smul' c x := by
    ext w
    simp [Finset.mul_sum, mul_ite]

def pull (q : V → W) : (W → ℝ) →ₗ[ℝ] (V → ℝ) :=
  LinearMap.funLeft ℝ ℝ q

@[simp] theorem pull_apply (q : V → W) (f : W → ℝ) (v : V) :
    pull q f v = f (q v) := rfl

@[simp] theorem push_apply [Fintype V] (q : V → W) (x : V → ℝ) (w : W) :
    push q x w = ∑ v, if q v = w then x v else 0 := rfl

def mapVertices (N : Network V E) (q : V → W) : Network W E :=
  ⟨q ∘ N.tail, q ∘ N.head⟩

def restrict (N : Network V E) (j : K → E) : Network V K :=
  ⟨N.tail ∘ j, N.head ∘ j⟩

@[simp] theorem gradient_mapVertices (N : Network V E) (q : V → W) (f : W → ℝ) :
    (N.mapVertices q).gradient f = N.gradient (pull q f) := rfl

@[simp] theorem gradient_restrict (N : Network V E) (j : K → E) (f : V → ℝ) :
    (N.restrict j).gradient f = pull j (N.gradient f) := rfl

variable [Fintype V] [Fintype W] [Fintype E] [Fintype K]

lemma push_adjoint (q : V → W) (x : V → ℝ) (f : W → ℝ) :
    ∑ w, push q x w * f w = ∑ v, x v * pull q f v := by
  classical
  simp only [push_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

lemma push_surjective {q : V → W} (hq : Function.Surjective q) :
    Function.Surjective (push q) := by
  classical
  let r := Function.surjInv hq
  have hr : Function.RightInverse r q := Function.rightInverse_surjInv hq
  intro f
  refine ⟨fun v => if h : v ∈ Set.range r then f (q v) else 0, ?_⟩
  ext w
  simp only [push_apply]
  rw [Finset.sum_eq_single (r w)]
  · simp [hr w]
  · intro v _ hv
    by_cases h : v ∈ Set.range r
    · obtain ⟨z, rfl⟩ := h
      have hz : z ≠ w := fun he => hv (congrArg r he)
      simp [hr z, hz]
    · simp [h]
  · simp

omit [Fintype V] [Fintype W] in
lemma pull_injective {q : V → W} (hq : Function.Surjective q) :
    Function.Injective (pull q) := by
  intro f g h
  ext w
  obtain ⟨v, rfl⟩ := hq w
  exact congrFun h v

lemma eq_of_dot_eq (x y : V → ℝ)
    (h : ∀ f : V → ℝ, ∑ v, x v * f v = ∑ v, y v * f v) : x = y := by
  ext v
  have hh := h (fun w => if w = v then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using hh

lemma boundary_mapVertices (N : Network V E) (q : V → W) (x : E → ℝ) :
    (N.mapVertices q).boundary x = push q (N.boundary x) := by
  apply eq_of_dot_eq
  intro f
  rw [(N.mapVertices q).boundary_adjoint, N.gradient_mapVertices,
    push_adjoint, N.boundary_adjoint]

lemma boundary_restrict (N : Network V E) (j : K → E) (x : K → ℝ) :
    (N.restrict j).boundary x = N.boundary (push j x) := by
  apply eq_of_dot_eq
  intro f
  rw [(N.restrict j).boundary_adjoint, N.gradient_restrict,
    N.boundary_adjoint, push_adjoint]

omit [Fintype E] in
lemma pull_push_injective {j : K → E} (hj : Function.Injective j) (x : K → ℝ) :
    pull j (push j x) = x := by
  classical
  ext k
  simp [hj.eq_iff]

omit [Fintype E] in
lemma push_eq_zero_outside {j : K → E} (x : K → ℝ) {e : E} (he : e ∉ Set.range j) :
    push j x e = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k _
  have hk : j k ≠ e := fun h => he ⟨k, h⟩
  simp [hk]

lemma push_pull_subtype (s : Set E) (x : E → ℝ) :
    push (Subtype.val : s → E) (pull Subtype.val x) = fun e => if e ∈ s then x e else 0 := by
  classical
  ext e
  by_cases he : e ∈ s
  · change (pull Subtype.val (push Subtype.val (pull Subtype.val x))) ⟨e, he⟩ = _
    rw [pull_push_injective Subtype.val_injective]
    simp [he]
  · rw [push_eq_zero_outside _ (by simpa using he)]
    simp [he]

def internal (N : Network V E) (q : V → W) : Set E :=
  {e | q (N.tail e) = q (N.head e)}

lemma push_boundary_internal (N : Network V E) (q : V → W)
    (x : N.internal q → ℝ) :
    push q ((N.restrict Subtype.val).boundary x) = 0 := by
  apply eq_of_dot_eq
  intro f
  rw [push_adjoint, (N.restrict _).boundary_adjoint]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  apply Finset.sum_eq_zero
  intro e _
  have he : (N.restrict (Subtype.val : N.internal q → E)).gradient (pull q f) e = 0 := by
    change f (q (N.head e.val)) - f (q (N.tail e.val)) = 0
    rw [e.property]
    exact sub_self _
  rw [he, mul_zero]

def ConnectedFibers (N : Network V E) (q : V → W) : Prop :=
  ∀ v w, q v = q w → (N.restrict (Subtype.val : N.internal q → E)).graph.Reachable v w

omit [Fintype V] [Fintype W] [Fintype E] in
lemma ker_internal_gradient (N : Network V E) {q : V → W}
    (hq : Function.Surjective q) (hc : N.ConnectedFibers q) :
    (N.restrict (Subtype.val : N.internal q → E)).gradient.ker = (pull q).range := by
  classical
  ext f
  constructor
  · intro hf
    let r := Function.surjInv hq
    have hr := Function.rightInverse_surjInv hq
    refine ⟨fun w => f (r w), ?_⟩
    ext v
    exact (N.restrict _).gradient_zero_reachable hf (hc _ _ (hr (q v)))
  · rintro ⟨f, rfl⟩
    apply (N.restrict _).gradient_eq_zero_iff _ |>.mpr
    intro e
    exact congrArg f e.property.symm

lemma range_internal_boundary (N : Network V E) {q : V → W}
    (hq : Function.Surjective q) (hc : N.ConnectedFibers q) :
    (N.restrict (Subtype.val : N.internal q → E)).boundary.range = (push q).ker := by
  classical
  let : DecidableEq (N.internal q) := Classical.decEq _
  let I := N.restrict (Subtype.val : N.internal q → E)
  have hle : I.boundary.range ≤ (push q).ker := by
    rintro _ ⟨x, rfl⟩
    exact N.push_boundary_internal q x
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hk : Module.finrank ℝ I.gradient.ker = Fintype.card W := by
    rw [show I.gradient.ker = (pull q).range from N.ker_internal_gradient hq hc,
      LinearMap.finrank_range_of_inj (pull_injective hq), Module.finrank_pi]
  have hgrad := I.gradient.finrank_range_add_finrank_ker
  have hpush := (push q).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (push_surjective hq), finrank_top,
    Module.finrank_pi, Module.finrank_pi] at hpush
  have hr : Module.finrank ℝ I.boundary.range = Module.finrank ℝ I.gradient.range := by
    rw [I.gradient_matrix, boundary, Matrix.toLin'_apply', Matrix.toLin'_apply',
      ← Matrix.rank, ← Matrix.rank, Matrix.rank_transpose]
  rw [Module.finrank_pi, hk] at hgrad
  omega

end
end Barnette.Network

end OAI
