import OAI.Probability.SwitchChain.Definitions

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315
namespace PairResampling

attribute [local instance] Classical.propDecidable

def SameFiber {n : ℕ} (a : Finset (Fin n)) (G H : SimpleGraph (Fin n)) : Prop :=
  (∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ w ∉ a, (a.filter (G.Adj w)).card = (a.filter (H.Adj w)).card)

@[refl] theorem SameFiber.refl {n : ℕ} (a : Finset (Fin n))
    (G : SimpleGraph (Fin n)) : SameFiber a G G := by
  unfold SameFiber
  exact ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩

@[symm] theorem SameFiber.symm {n : ℕ} {a : Finset (Fin n)}
    {G H : SimpleGraph (Fin n)} (h : SameFiber a G H) : SameFiber a H G :=
  ⟨fun u hu v hv => (h.1 u hu v hv).symm,
   fun u hu v hv => (h.2.1 u hu v hv).symm,
   fun w hw => (h.2.2 w hw).symm⟩

@[trans] theorem SameFiber.trans {n : ℕ} {a : Finset (Fin n)}
    {G H K : SimpleGraph (Fin n)} (h : SameFiber a G H) (k : SameFiber a H K) :
    SameFiber a G K :=
  ⟨fun u hu v hv => (h.1 u hu v hv).trans (k.1 u hu v hv),
   fun u hu v hv => (h.2.1 u hu v hv).trans (k.2.1 u hu v hv),
   fun w hw => (h.2.2 w hw).trans (k.2.2 w hw)⟩

theorem graphDegree_partition {n : ℕ} (a : Finset (Fin n))
    (G : SimpleGraph (Fin n)) (w : Fin n) :
    (a.filter (G.Adj w)).card + ((Finset.univ \ a).filter (G.Adj w)).card =
      graphDegree G w := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (G.Adj w)) (p := fun v => v ∈ a)
  have heq : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∈ a) = a.filter (G.Adj w) := by
    ext v
    simp [and_comm]
  have hneq : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a) =
      (Finset.univ \ a).filter (G.Adj w) := by
    ext v
    simp [and_comm]
  rw [heq, hneq] at h
  exact h

theorem sameFiber_of_fixed_edges {n : ℕ} (a : Finset (Fin n))
    {G H : SimpleGraph (Fin n)}
    (hdeg : ∀ w, graphDegree G w = graphDegree H w)
    (hout : ∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v)
    (hin : ∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v) :
    SameFiber a G H := by
  refine ⟨hout, hin, ?_⟩
  intro w hw
  have hext : (Finset.univ \ a).filter (G.Adj w) =
      (Finset.univ \ a).filter (H.Adj w) := by
    apply Finset.filter_congr
    intro v hv
    exact hout w hw v (Finset.mem_sdiff.mp hv).2
  have hG := graphDegree_partition a G w
  have hH := graphDegree_partition a H w
  rw [hext, hdeg w] at hG
  omega

theorem sameFiber_state_iff {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))
    (G H : GraphState n d) :
    SameFiber a G.val H.val ↔
      (∀ u ∉ a, ∀ v ∉ a, G.val.Adj u v ↔ H.val.Adj u v) ∧
      (∀ u ∈ a, ∀ v ∈ a, G.val.Adj u v ↔ H.val.Adj u v) := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ?_⟩
  apply sameFiber_of_fixed_edges a _ h.1 h.2
  intro w
  exact (G.property w).trans (H.property w).symm

abbrev StateSpace (n : ℕ) (d : Fin n → ℕ) := EuclideanSpace ℝ (GraphState n d)

def fiberSpace (n : ℕ) (d : Fin n → ℕ) (a : Finset (Fin n)) :
    Submodule ℝ (StateSpace n d) where
  carrier := {f | ∀ G H : GraphState n d, SameFiber a G.val H.val → f G = f H}
  zero_mem' := by intro G H h; rfl
  add_mem' := by
    intro f g hf hg G H h
    change f G + g G = f H + g H
    rw [hf G H h, hg G H h]
  smul_mem' := by
    intro c f hf G H h
    change c * f G = c * f H
    rw [hf G H h]

def expectation (n : ℕ) (d : Fin n → ℕ) (a : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d := (fiberSpace n d a).starProjection

def fluctuation (n : ℕ) (d : Fin n → ℕ) (a : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d := (fiberSpace n d a)ᗮ.starProjection

variable {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))

@[simp] theorem expectation_mem (f : StateSpace n d) :
    expectation n d a f ∈ fiberSpace n d a :=
  (fiberSpace n d a).starProjection_apply_mem f

@[simp] theorem expectation_eq_self_iff (f : StateSpace n d) :
    expectation n d a f = f ↔ f ∈ fiberSpace n d a :=
  (fiberSpace n d a).starProjection_eq_self_iff

theorem expectation_isSymmetric :
    (expectation n d a).toLinearMap.IsSymmetric :=
  (fiberSpace n d a).starProjection_isSymmetric

theorem fluctuation_isSymmetric :
    (fluctuation n d a).toLinearMap.IsSymmetric :=
  (fiberSpace n d a)ᗮ.starProjection_isSymmetric

@[simp] theorem expectation_idempotent (f : StateSpace n d) :
    expectation n d a (expectation n d a f) = expectation n d a f :=
  (expectation_eq_self_iff a _).mpr (expectation_mem a f)

@[simp] theorem fluctuation_idempotent (f : StateSpace n d) :
    fluctuation n d a (fluctuation n d a f) = fluctuation n d a f :=
  (Submodule.starProjection_eq_self_iff).mpr
    ((fiberSpace n d a)ᗮ.starProjection_apply_mem f)

theorem fluctuation_eq_sub (f : StateSpace n d) :
    fluctuation n d a f = f - expectation n d a f := by
  exact (fiberSpace n d a).starProjection_orthogonal_val f

@[simp] theorem fluctuation_eq_zero_iff (f : StateSpace n d) :
    fluctuation n d a f = 0 ↔ f ∈ fiberSpace n d a := by
  rw [fluctuation_eq_sub, sub_eq_zero, eq_comm, expectation_eq_self_iff]

theorem inner_fluctuation (f : StateSpace n d) :
    ⟪f, fluctuation n d a f⟫ = ‖fluctuation n d a f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := ((fluctuation_isSymmetric a) f (fluctuation n d a f)).symm
  change ⟪f, fluctuation n d a (fluctuation n d a f)⟫ =
    ⟪fluctuation n d a f, fluctuation n d a f⟫ at h
  simpa only [fluctuation_idempotent] using h

theorem fluctuation_nonneg (f : StateSpace n d) :
    0 ≤ ⟪f, fluctuation n d a f⟫ := by
  rw [inner_fluctuation]
  exact sq_nonneg _

def pairs (n : ℕ) : Finset (Finset (Fin n)) := Finset.univ.powersetCard 2

def generator (n : ℕ) (d : Fin n → ℕ) : StateSpace n d →L[ℝ] StateSpace n d :=
  ∑ a ∈ pairs n, fluctuation n d a

theorem generator_apply (f : StateSpace n d) :
    generator n d f = ∑ a ∈ pairs n, fluctuation n d a f := by
  simp [generator]

theorem generator_isSymmetric : (generator n d).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪generator n d f, g⟫ = ⟪f, generator n d g⟫
  simp only [generator_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact fluctuation_isSymmetric b f g

theorem inner_generator (f : StateSpace n d) :
    ⟪f, generator n d f⟫ = ∑ a ∈ pairs n, ‖fluctuation n d a f‖ ^ 2 := by
  simp only [generator_apply, inner_sum, inner_fluctuation]

theorem generator_nonneg (f : StateSpace n d) : 0 ≤ ⟪f, generator n d f⟫ := by
  rw [inner_generator]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem generator_eq_zero_iff (f : StateSpace n d) :
    generator n d f = 0 ↔ ∀ a ∈ pairs n, f ∈ fiberSpace n d a := by
  constructor
  · intro h a ha
    have hz : (∑ b ∈ pairs n, ‖fluctuation n d b f‖ ^ 2) = 0 := by
      rw [← inner_generator, h, inner_zero_right]
    have hterm : ‖fluctuation n d a f‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖fluctuation n d b f‖)).mp hz a ha
    exact (fluctuation_eq_zero_iff a f).mp
      (norm_eq_zero.mp (sq_eq_zero_iff.mp hterm))
  · intro h
    rw [generator_apply]
    apply Finset.sum_eq_zero
    intro a ha
    exact (fluctuation_eq_zero_iff a f).mpr (h a ha)

theorem state_inner (f g : StateSpace n d) :
    ⟪f, g⟫ = ∑ G : GraphState n d, f G * g G := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem constant_mem (c : ℝ) :
    WithLp.toLp 2 (fun _ : GraphState n d => c) ∈ fiberSpace n d a := by
  intro G H h
  rfl

@[simp] theorem generator_constant (c : ℝ) :
    generator n d (WithLp.toLp 2 (fun _ : GraphState n d => c)) = 0 := by
  apply (generator_eq_zero_iff _).mpr
  intro a ha
  exact constant_mem a c

def fiberStates (a : Finset (Fin n)) (G : GraphState n d) : Finset (GraphState n d) :=
  Finset.univ.filter (fun H => SameFiber a G.val H.val)

@[simp] theorem mem_fiberStates (G H : GraphState n d) :
    H ∈ fiberStates a G ↔ SameFiber a G.val H.val := by
  simp [fiberStates]

@[simp] theorem self_mem_fiberStates (G : GraphState n d) : G ∈ fiberStates a G := by
  exact (mem_fiberStates a G G).mpr (SameFiber.refl a G.val)

theorem fiberStates_nonempty (G : GraphState n d) : (fiberStates a G).Nonempty :=
  ⟨G, self_mem_fiberStates a G⟩

def fiberIndicator (a : Finset (Fin n)) (G : GraphState n d) : StateSpace n d :=
  WithLp.toLp 2 (fun H => if SameFiber a G.val H.val then 1 else 0)

theorem fiberIndicator_mem (G : GraphState n d) :
    fiberIndicator a G ∈ fiberSpace n d a := by
  intro H K hHK
  change (if SameFiber a G.val H.val then (1 : ℝ) else 0) =
    if SameFiber a G.val K.val then 1 else 0
  have hi : SameFiber a G.val H.val ↔ SameFiber a G.val K.val :=
    ⟨fun h => h.trans hHK, fun h => h.trans hHK.symm⟩
  simp only [hi]

theorem expectation_eq_average (f : StateSpace n d) (G : GraphState n d) :
    expectation n d a f G = (∑ H ∈ fiberStates a G, f H) / (fiberStates a G).card := by
  have horth := Submodule.starProjection_inner_eq_zero (K := fiberSpace n d a)
    f (fiberIndicator a G) (fiberIndicator_mem a G)
  change ⟪f - expectation n d a f, fiberIndicator a G⟫ = 0 at horth
  rw [state_inner] at horth
  have hsum : (∑ H ∈ fiberStates a G, (f H - expectation n d a f H)) = 0 := by
    calc
      _ = ∑ H : GraphState n d, (f - expectation n d a f) H * fiberIndicator a G H := by
        unfold fiberStates
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro H hH
        by_cases h : SameFiber a G.val H.val <;> simp [fiberIndicator, h]
      _ = 0 := horth
  have hequal : ∀ H ∈ fiberStates a G, expectation n d a f H = expectation n d a f G := by
    intro H hH
    exact (expectation_mem a f) H G ((mem_fiberStates a G H).mp hH).symm
  have hsconst : (∑ H ∈ fiberStates a G, expectation n d a f H) =
      (fiberStates a G).card * expectation n d a f G := by
    calc
      _ = ∑ _H ∈ fiberStates a G, expectation n d a f G := Finset.sum_congr rfl hequal
      _ = _ := by simp
  rw [Finset.sum_sub_distrib, hsconst] at hsum
  have hcard : (0 : ℝ) < (fiberStates a G).card := by
    exact_mod_cast Finset.card_pos.mpr (fiberStates_nonempty a G)
  apply (eq_div_iff (ne_of_gt hcard)).mpr
  linarith

end PairResampling
end Problem315

end

end OAI
