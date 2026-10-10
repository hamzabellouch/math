import Mathlib

namespace OAI

/-! Closed gradient subspaces of connected oriented multigraphs. -/

open scoped lp

noncomputable section

namespace SingerFour

structure OrientedGraph (V E : Type*) where
  tail : E → V
  head : E → V

namespace OrientedGraph

variable {V E : Type*} (G : OrientedGraph V E)

inductive Walk : V → V → Type _
  | nil (v : V) : Walk v v
  | forward {v : V} (e : E) (p : Walk v (G.tail e)) : Walk v (G.head e)
  | backward {v : V} (e : E) (p : Walk v (G.head e)) : Walk v (G.tail e)

def Connected : Prop := ∀ v w : V, Nonempty (G.Walk v w)

def gradients : Submodule ℝ (ℓ²(E, ℝ)) where
  carrier := {c | ∃ f : V → ℝ, ∀ e, c e = f (G.head e) - f (G.tail e)}
  zero_mem' := ⟨0, by intro e; simp⟩
  add_mem' := by
    rintro c d ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨f + g, ?_⟩
    intro e
    change c e + d e = (f (G.head e) + g (G.head e)) -
      (f (G.tail e) + g (G.tail e))
    rw [hf e, hg e]
    ring
  smul_mem' := by
    rintro r c ⟨f, hf⟩
    refine ⟨r • f, ?_⟩
    intro e
    change r * c e = r * f (G.head e) - r * f (G.tail e)
    rw [hf e, mul_sub]

@[simp]
theorem mem_gradients (c : ℓ²(E, ℝ)) :
    c ∈ G.gradients ↔ ∃ f : V → ℝ, ∀ e, c e = f (G.head e) - f (G.tail e) := Iff.rfl

def Walk.integral {G : OrientedGraph V E} {v w : V} : G.Walk v w → (ℓ²(E, ℝ) →L[ℝ] ℝ)
  | .nil _ => 0
  | .forward e p => p.integral + lp.evalCLM ℝ (fun _ : E => ℝ) 2 e
  | .backward e p => p.integral - lp.evalCLM ℝ (fun _ : E => ℝ) 2 e

theorem Walk.integral_gradient {G : OrientedGraph V E} {c : ℓ²(E, ℝ)} {f : V → ℝ}
    (hf : ∀ e, c e = f (G.head e) - f (G.tail e)) {v w : V}
    (p : G.Walk v w) : p.integral c = f w - f v := by
  induction p with
  | nil => simp [Walk.integral]
  | forward e p ih =>
    change p.integral c + c e = f (G.head e) - f v
    rw [ih, hf e]
    ring
  | backward e p ih =>
    change p.integral c - c e = f (G.tail e) - f v
    rw [ih, hf e]
    ring

theorem eq_of_zero_differences (hG : G.Connected) {f : V → ℝ}
    (hf : ∀ e, f (G.head e) = f (G.tail e)) (v w : V) : f v = f w := by
  have hgrad : ∀ e, (0 : ℓ²(E, ℝ)) e = f (G.head e) - f (G.tail e) := by
    intro e
    simp [hf e]
  have h := (Classical.choice (hG v w)).integral_gradient hgrad
  simpa only [map_zero, eq_comm, sub_eq_zero] using h.symm

theorem potential_unique (hG : G.Connected) (o : V) {f g : V → ℝ}
    (hedges : ∀ e, f (G.head e) - f (G.tail e) = g (G.head e) - g (G.tail e))
    (ho : f o = g o) : f = g := by
  funext v
  have hzero : ∀ e, (f - g) (G.head e) = (f - g) (G.tail e) := by
    intro e
    have := hedges e
    dsimp
    linarith
  have h := G.eq_of_zero_differences hG hzero o v
  dsimp at h
  linarith

theorem l2_eq_zero_of_constant [Infinite V] (f : ℓ²(V, ℝ)) {r : ℝ}
    (hf : ∀ v, f v = r) : f = 0 := by
  have hs : Summable (fun v : V => ‖r‖ ^ (2 : ℕ)) := by
    simpa only [hf, ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hr : r = 0 := by
    have h := (summable_const_iff (β := V) (‖r‖ ^ (2 : ℕ))).mp hs
    simpa using h
  apply lp.ext
  funext v
  simpa only [lp.coeFn_zero, Pi.zero_apply, hr] using hf v

theorem l2_eq_zero_of_zero_differences [Infinite V] (hG : G.Connected)
    (f : ℓ²(V, ℝ)) (hf : ∀ e, f (G.head e) = f (G.tail e)) : f = 0 := by
  let o : V := Classical.choice (inferInstance : Nonempty V)
  exact l2_eq_zero_of_constant f (fun v => G.eq_of_zero_differences hG hf v o)

noncomputable def normalizedPotential (hG : G.Connected) (o v : V) :
    ℓ²(E, ℝ) →L[ℝ] ℝ :=
  (Classical.choice (hG o v)).integral

theorem normalizedPotential_gradient (hG : G.Connected) (o v : V)
    {c : ℓ²(E, ℝ)} {f : V → ℝ}
    (hf : ∀ e, c e = f (G.head e) - f (G.tail e)) :
    G.normalizedPotential hG o v c = f v - f o :=
  Walk.integral_gradient hf _

theorem mem_gradients_iff_normalized (hG : G.Connected) (o : V) (c : ℓ²(E, ℝ)) :
    c ∈ G.gradients ↔ ∀ e,
      c e = G.normalizedPotential hG o (G.head e) c -
        G.normalizedPotential hG o (G.tail e) c := by
  constructor
  · rintro ⟨f, hf⟩ e
    rw [G.normalizedPotential_gradient hG o (G.head e) hf,
      G.normalizedPotential_gradient hG o (G.tail e) hf, hf e]
    ring
  · intro hc
    exact ⟨fun v => G.normalizedPotential hG o v c, hc⟩

theorem isClosed_gradients (hG : G.Connected) (o : V) :
    IsClosed (G.gradients : Set (ℓ²(E, ℝ))) := by
  have hset : (G.gradients : Set (ℓ²(E, ℝ))) =
      ⋂ e : E, {c : ℓ²(E, ℝ) | c e =
        G.normalizedPotential hG o (G.head e) c -
          G.normalizedPotential hG o (G.tail e) c} := by
    ext c
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred,
      G.mem_gradients_iff_normalized hG o c]
  rw [hset]
  apply isClosed_iInter
  intro e
  exact isClosed_eq (lp.evalCLM ℝ (fun _ : E => ℝ) 2 e).continuous
    ((G.normalizedPotential hG o (G.head e)).continuous.sub
      (G.normalizedPotential hG o (G.tail e)).continuous)

theorem completeSpace_gradients (hG : G.Connected) (o : V) :
    CompleteSpace G.gradients :=
  (G.isClosed_gradients hG o).completeSpace_coe

def finiteSupportGradients : Submodule ℝ (ℓ²(E, ℝ)) where
  carrier := {c | ∃ f : V →₀ ℝ, ∀ e, c e = f (G.head e) - f (G.tail e)}
  zero_mem' := ⟨0, by intro e; simp⟩
  add_mem' := by
    rintro c d ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨f + g, ?_⟩
    intro e
    change c e + d e = (f (G.head e) + g (G.head e)) -
      (f (G.tail e) + g (G.tail e))
    rw [hf e, hg e]
    ring
  smul_mem' := by
    rintro r c ⟨f, hf⟩
    refine ⟨r • f, ?_⟩
    intro e
    change r * c e = r * f (G.head e) - r * f (G.tail e)
    rw [hf e, mul_sub]

def LocallyFinite : Prop :=
  ∀ v : V, Set.Finite {e : E | G.tail e = v ∨ G.head e = v}

theorem hasFiniteSupport_differential (hG : G.LocallyFinite) (f : V →₀ ℝ) :
    (Function.support (fun e => f (G.head e) - f (G.tail e))).Finite := by
  classical
  have hfinite : (⋃ v ∈ (f.support : Set V),
      {e : E | G.tail e = v ∨ G.head e = v}).Finite :=
    f.support.finite_toSet.biUnion (fun v _ => hG v)
  apply hfinite.subset
  intro e he
  change f (G.head e) - f (G.tail e) ≠ 0 at he
  have hside : G.head e ∈ f.support ∨ G.tail e ∈ f.support := by
    by_contra h
    push Not at h
    simp [Finsupp.notMem_support_iff.mp h.1, Finsupp.notMem_support_iff.mp h.2] at he
  rcases hside with hh | ht
  · exact Set.mem_iUnion₂.mpr ⟨G.head e, hh, Or.inr rfl⟩
  · exact Set.mem_iUnion₂.mpr ⟨G.tail e, ht, Or.inl rfl⟩

def finiteSupportDifferential (hG : G.LocallyFinite) :
    (V →₀ ℝ) →ₗ[ℝ] ℓ²(E, ℝ) where
  toFun f := ⟨fun e => f (G.head e) - f (G.tail e),
    (memℓp_zero (G.hasFiniteSupport_differential hG f)).of_exponent_ge (by positivity)⟩
  map_add' f g := by
    apply lp.ext
    funext e
    change f (G.head e) + g (G.head e) - (f (G.tail e) + g (G.tail e)) =
      (f (G.head e) - f (G.tail e)) + (g (G.head e) - g (G.tail e))
    ring
  map_smul' r f := by
    apply lp.ext
    funext e
    exact mul_sub r (f (G.head e)) (f (G.tail e)) |>.symm

@[simp]
theorem finiteSupportDifferential_apply (hG : G.LocallyFinite) (f : V →₀ ℝ) (e : E) :
    G.finiteSupportDifferential hG f e = f (G.head e) - f (G.tail e) := rfl

theorem range_finiteSupportDifferential (hG : G.LocallyFinite) :
    LinearMap.range (G.finiteSupportDifferential hG) = G.finiteSupportGradients := by
  ext c
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, fun e => rfl⟩
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    apply lp.ext
    funext e
    exact (hf e).symm

def zeroBoundaryGradients : Submodule ℝ (ℓ²(E, ℝ)) :=
  G.finiteSupportGradients.topologicalClosure

theorem finiteSupportGradients_le : G.finiteSupportGradients ≤ G.gradients := by
  rintro c ⟨f, hf⟩
  exact ⟨f, hf⟩

theorem zeroBoundaryGradients_le (hG : G.Connected) (o : V) :
    G.zeroBoundaryGradients ≤ G.gradients :=
  G.finiteSupportGradients.topologicalClosure_minimal G.finiteSupportGradients_le
    (G.isClosed_gradients hG o)

end OrientedGraph
end SingerFour

end

end OAI
