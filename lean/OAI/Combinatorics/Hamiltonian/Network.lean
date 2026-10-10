import OAI.Combinatorics.Hamiltonian.Model

namespace OAI

/-! Oriented finite networks, cycle and cut spaces, and graph realization. -/

namespace Barnette

structure Network (V E : Type*) where
  tail : E → V
  head : E → V

namespace Network
noncomputable section
variable {V E : Type*} (N : Network V E)

def graph : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ e, (N.tail e = v ∧ N.head e = w) ∨
    (N.tail e = w ∧ N.head e = v)
  symm := ⟨by rintro v w ⟨h, e, hi⟩; exact ⟨h.symm, e, hi.symm⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

theorem edge_reachable (e : E) : N.graph.Reachable (N.tail e) (N.head e) := by
  by_cases h : N.tail e = N.head e
  · rw [h]
  · exact (show N.graph.Adj (N.tail e) (N.head e) from
      ⟨h, e, Or.inl ⟨rfl, rfl⟩⟩).reachable

def gradient : (V → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun f e := f (N.head e) - f (N.tail e)
  map_add' f g := by ext e; dsimp; ring
  map_smul' c f := by ext e; dsimp; ring

@[simp] theorem gradient_apply (f : V → ℝ) (e : E) :
    N.gradient f e = f (N.head e) - f (N.tail e) := rfl

@[simp] theorem gradient_const (a : ℝ) : N.gradient (fun _ => a) = 0 := by
  ext e; simp

theorem gradient_eq_zero_iff (f : V → ℝ) :
    N.gradient f = 0 ↔ ∀ e, f (N.head e) = f (N.tail e) := by
  simp only [funext_iff, gradient_apply, Pi.zero_apply, sub_eq_zero]

theorem gradient_zero_adj {f : V → ℝ} (hf : N.gradient f = 0)
    {v w : V} (h : N.graph.Adj v w) : f v = f w := by
  obtain ⟨_, e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact ((N.gradient_eq_zero_iff f).mp hf e).symm
  · exact (N.gradient_eq_zero_iff f).mp hf e

theorem gradient_zero_reachable {f : V → ℝ} (hf : N.gradient f = 0)
    {v w : V} (h : N.graph.Reachable v w) : f v = f w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (N.gradient_zero_adj hf h).trans ih

def constant : ℝ →ₗ[ℝ] (V → ℝ) where
  toFun a _ := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_gradient (h : N.graph.Connected) :
    N.gradient.ker = (constant (V := V)).range := by
  obtain ⟨v⟩ := h.nonempty
  ext f
  constructor
  · intro hf
    refine ⟨f v, ?_⟩
    ext w
    exact N.gradient_zero_reachable hf (h v w)
  · rintro ⟨a, rfl⟩
    exact N.gradient_const a

variable [Fintype V] [Fintype E]
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableEq E := Classical.decEq _

def incidence : Matrix V E ℝ := fun v e =>
  (if N.head e = v then 1 else 0) - (if N.tail e = v then 1 else 0)

def boundary : (E → ℝ) →ₗ[ℝ] (V → ℝ) := Matrix.toLin' N.incidence

omit [Fintype V] in
@[simp] theorem boundary_apply (x : E → ℝ) (v : V) :
    N.boundary x v = ∑ e, ((if N.head e = v then x e else 0) -
      (if N.tail e = v then x e else 0)) := by
  classical
  simp [boundary, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, incidence,
    sub_mul, ite_mul]

omit [Fintype E] in
theorem gradient_matrix : N.gradient = Matrix.toLin' N.incidence.transpose := by
  classical
  apply LinearMap.ext
  intro f
  ext e
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, incidence,
    sub_mul, ite_mul, Finset.sum_sub_distrib]

theorem sum_boundary (x : E → ℝ) : ∑ v, N.boundary x v = 0 := by
  classical
  simp only [boundary_apply]
  rw [Finset.sum_comm]
  simp [Finset.sum_sub_distrib]

omit [Fintype E] in
theorem rank_gradient (h : N.graph.Connected) :
    Module.finrank ℝ N.gradient.range + 1 = Fintype.card V := by
  obtain ⟨v⟩ := h.nonempty
  have hi : Function.Injective (constant (V := V)) := by
    intro a b hab
    exact congrFun hab v
  have hk : Module.finrank ℝ N.gradient.ker = 1 := by
    rw [N.ker_gradient h, LinearMap.finrank_range_of_inj hi]
    exact Module.finrank_self ℝ
  have hh := N.gradient.finrank_range_add_finrank_ker
  simpa only [hk, Module.finrank_pi] using hh

theorem rank_boundary (h : N.graph.Connected) :
    Module.finrank ℝ N.boundary.range + 1 = Fintype.card V := by
  have hh := N.rank_gradient h
  have he : Module.finrank ℝ N.boundary.range = Module.finrank ℝ N.gradient.range := by
    rw [N.gradient_matrix, boundary, Matrix.toLin'_apply', Matrix.toLin'_apply',
      ← Matrix.rank, ← Matrix.rank, Matrix.rank_transpose]
  rwa [he]

theorem dim_cycles (h : N.graph.Connected) :
    Module.finrank ℝ N.boundary.ker + Fintype.card V = Fintype.card E + 1 := by
  have hr := N.rank_boundary h
  have hk := N.boundary.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hk
  omega

theorem boundary_adjoint (x : E → ℝ) (f : V → ℝ) :
    ∑ v, N.boundary x v * f v = ∑ e, x e * N.gradient f e := by
  classical
  simp only [boundary_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [sub_mul, ite_mul, Finset.sum_sub_distrib, mul_sub]

variable {F : Type*} [Fintype F] (D : Network F E)

theorem orthogonal_symm (h : ∀ f, N.boundary (D.gradient f) = 0) :
    ∀ f, D.boundary (N.gradient f) = 0 := by
  classical
  intro f
  ext y
  calc
    D.boundary (N.gradient f) y =
        ∑ z, D.boundary (N.gradient f) z * (fun z : F => if z = y then (1 : ℝ) else 0) z := by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = ∑ e, N.gradient f e * D.gradient ((fun z : F => if z = y then (1 : ℝ) else 0)) e :=
      D.boundary_adjoint _ _
    _ = ∑ e, D.gradient ((fun z : F => if z = y then (1 : ℝ) else 0)) e * N.gradient f e := by
      apply Finset.sum_congr rfl
      intro e _
      exact mul_comm _ _
    _ = ∑ v, N.boundary (D.gradient ((fun z : F => if z = y then (1 : ℝ) else 0))) v * f v :=
      (N.boundary_adjoint _ _).symm
    _ = 0 := by rw [h]; simp

structure Duality : Prop where
  connected : N.graph.Connected
  dual_connected : D.graph.Connected
  cycles_eq_cuts : N.boundary.ker = D.gradient.range
  dual_cycles_eq_cuts : D.boundary.ker = N.gradient.range

private theorem ker_eq_range_of_orth_card
    (hN : N.graph.Connected) (hD : D.graph.Connected)
    (hc : Fintype.card V + Fintype.card F = Fintype.card E + 2)
    (ho : ∀ f, N.boundary (D.gradient f) = 0) :
    N.boundary.ker = D.gradient.range := by
  have hle : D.gradient.range ≤ N.boundary.ker := by
    rintro _ ⟨f, rfl⟩
    exact ho f
  have hd₁ := N.dim_cycles hN
  have hd₂ := D.rank_gradient hD
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem duality_of_orth_card
    (hN : N.graph.Connected) (hD : D.graph.Connected)
    (hc : Fintype.card V + Fintype.card F = Fintype.card E + 2)
    (ho : ∀ f, N.boundary (D.gradient f) = 0) : N.Duality D where
  connected := hN
  dual_connected := hD
  cycles_eq_cuts := N.ker_eq_range_of_orth_card D hN hD hc ho
  dual_cycles_eq_cuts := D.ker_eq_range_of_orth_card N hD hN (by omega)
    (N.orthogonal_symm D ho)

theorem Duality.euler (h : N.Duality D) :
    Fintype.card V + Fintype.card F = Fintype.card E + 2 := by
  have h₁ := N.dim_cycles h.connected
  rw [h.cycles_eq_cuts] at h₁
  have h₂ := D.rank_gradient h.dual_connected
  omega

end
end Network
end Barnette

namespace Barnette
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma cubic_bipartite_order [Nonempty V] (hc : G.IsRegularOfDegree 3)
    (hb : G.IsBipartite) : 6 ≤ Fintype.card V := by
  obtain ⟨c⟩ := hb
  obtain ⟨v⟩ := ‹Nonempty V›
  have hp : (G.neighborFinset v).Nonempty := by
    apply Finset.card_pos.mp
    rw [G.card_neighborFinset_eq_degree, hc v]
    norm_num
  obtain ⟨w, hw⟩ := hp
  have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  have hd : Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have h₁ := c.valid hvw
    have h₂ := c.valid ((G.mem_neighborFinset v x).mp hx)
    have h₃ := c.valid ((G.mem_neighborFinset w x).mp hy)
    have hv := (c v).isLt
    have hw := (c w).isLt
    have hx := (c x).isLt
    have h₁' : (c v).val ≠ (c w).val := fun h => h₁ (Fin.ext h)
    have h₂' : (c v).val ≠ (c x).val := fun h => h₂ (Fin.ext h)
    have h₃' : (c w).val ≠ (c x).val := fun h => h₃ (Fin.ext h)
    omega
  have hle := Finset.card_le_card (Finset.subset_univ
    (G.neighborFinset v ∪ G.neighborFinset w))
  rw [Finset.card_union_of_disjoint hd, G.card_neighborFinset_eq_degree,
    G.card_neighborFinset_eq_degree, hc v, hc w, Finset.card_univ] at hle
  exact hle

omit [DecidableRel G.Adj] in

lemma boundary_cover_of_threeConnected (h : ThreeVertexConnected G)
    (A S : Finset V) (hS : S.card ≤ 2) (hSA : S ⊆ A)
    (hout : ∃ w, w ∉ A)
    (hboundary : ∀ v ∈ A, ∀ w, w ∉ A → G.Adj v w → v ∈ S) : A ⊆ S := by
  intro v hv
  by_contra hvS
  obtain ⟨w, hw⟩ := hout
  have hwS : w ∉ S := fun hs => hw (hSA hs)
  let H := G.induce {v | v ∉ S}
  have hr := (h.2 S hS) (⟨v,hvS⟩ : {v | v ∉ S}) ⟨w,hwS⟩
  obtain ⟨p⟩ := hr
  have hp : ∀ {a b : {v | v ∉ S}}, H.Walk a b → a.val ∈ A → b.val ∈ A := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a z b haz p ih =>
      intro ha
      apply ih
      by_contra hz
      exact a.property (hboundary a.val ha z.val hz haz)
  exact hw (hp p hv)

end
end Barnette

end OAI
