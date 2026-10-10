import OAI.GroupTheory.ArtinCAT0.Presentation

namespace OAI

namespace ArtinCAT0

/-- Oriented finite triangular incidence data. Faces/edges may have repeated
incidences; no topological assumption is built into this record. -/
structure TriangleMesh (F V : Type*) where
  mate : Equiv.Perm (F × Fin 3)
  mate_involutive : Function.Involutive mate
  mate_ne : ∀ d, mate d ≠ d
  tail : F × Fin 3 → V
  tail_mate : ∀ d, tail (mate d) = tail (d.1, d.2+1)

namespace TriangleMesh
variable {F V : Type*} (M : TriangleMesh F V)

abbrev Dart := F × Fin 3

def rotate : Equiv.Perm (Dart (F := F)) where
  toFun d := (d.1,d.2+1)
  invFun d := (d.1,d.2-1)
  left_inv d := by ext <;> simp
  right_inv d := by ext <;> simp

@[simp] lemma rotate_apply (d : Dart (F := F)) : rotate d = (d.1,d.2+1) := rfl
@[simp] lemma rotate_symm_apply (d : Dart (F := F)) : rotate.symm d = (d.1,d.2-1) := rfl

@[simp] lemma mate_mate (d : Dart (F := F)) : M.mate (M.mate d) = d := M.mate_involutive d

lemma tail_rotate_mate (d : Dart (F := F)) : M.tail (rotate (M.mate d)) = M.tail d := by
  rw [rotate_apply, ← M.tail_mate, M.mate_mate]

def turn : Equiv.Perm (Dart (F := F)) := M.mate * rotate.symm

@[simp] lemma turn_apply (d : Dart (F := F)) : M.turn d = M.mate (rotate.symm d) := rfl

@[simp] lemma tail_turn (d : Dart (F := F)) : M.tail (M.turn d) = M.tail d := by
  rw [turn_apply, M.tail_mate]
  simp

/-- A real edge cocycle is exact. This algebraic formulation allows the
fold-deletion proof to avoid any appeal to an unformalized planar theorem. -/
def Exact : Prop :=
  ∀ w : Dart (F := F) → ℝ,
    (∀ d, w (M.mate d) = -w d) →
    (∀ f, ∑ i : Fin 3, w (f,i) = 0) →
    ∃ p : V → ℝ, ∀ d, w d = p (M.tail (rotate d)) - p (M.tail d)

section OrientedEdges
variable [LinearOrder (Dart (F := F))]

abbrev Edge := {d : Dart (F := F) // d < M.mate d}

noncomputable def edgeRep (d : Dart (F := F)) : M.Edge :=
  if h : d < M.mate d then ⟨d,h⟩ else
    ⟨M.mate d, by rw [M.mate_mate]; exact lt_of_le_of_ne (le_of_not_gt h) (M.mate_ne d)⟩

lemma edgeRep_mate (d : Dart (F := F)) : M.edgeRep (M.mate d) = M.edgeRep d := by
  apply Subtype.ext
  unfold edgeRep
  by_cases h : d < M.mate d
  · simp [h, not_lt_of_gt h]
  · have h' : M.mate d < d := lt_of_le_of_ne (le_of_not_gt h) (M.mate_ne d)
    simp [h, h']

@[simp] lemma edgeRep_edge (e : M.Edge) : M.edgeRep e.val = e := by
  apply Subtype.ext
  simp [edgeRep, e.property]

noncomputable def extend (w : M.Edge → ℝ) (d : Dart (F := F)) : ℝ :=
  if d < M.mate d then w (M.edgeRep d) else -w (M.edgeRep d)

@[simp] lemma extend_edge (w : M.Edge → ℝ) (e : M.Edge) : M.extend w e.val = w e := by
  simp [extend, e.property]

lemma extend_mate (w : M.Edge → ℝ) (d : Dart (F := F)) : M.extend w (M.mate d) = -M.extend w d := by
  unfold extend
  rw [M.edgeRep_mate, M.mate_mate]
  by_cases h : d < M.mate d
  · simp [h, not_lt_of_gt h]
  · have h' : M.mate d < d := lt_of_le_of_ne (le_of_not_gt h) (M.mate_ne d)
    simp [h, h']

lemma extend_of_antisymmetric (w : Dart (F := F) → ℝ)
    (hw : ∀ d, w (M.mate d) = -w d) (d : Dart (F := F)) :
    M.extend (fun e => w e.val) d = w d := by
  unfold extend edgeRep
  split_ifs <;> simp_all

noncomputable def edgeDartEquiv : M.Edge × Bool ≃ Dart (F := F) where
  toFun p := if p.2 then M.mate p.1.val else p.1.val
  invFun d := (M.edgeRep d, decide (¬ d < M.mate d))
  left_inv p := by
    rcases p with ⟨e,b⟩
    cases b
    · simp [edgeRep, e.property]
    · have hn : ¬ M.mate e.val < e.val := not_lt_of_gt e.property
      simp [edgeRep, hn]
  right_inv d := by
    by_cases h : d < M.mate d
    · simp [h, edgeRep]
    · simp [h, edgeRep]

lemma edge_card [Fintype F] [Fintype M.Edge] : 2 * Fintype.card M.Edge = 3 * Fintype.card F := by
  have he := Fintype.card_congr M.edgeDartEquiv
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at he
  omega

noncomputable def coboundary : (V → ℝ) →ₗ[ℝ] (M.Edge → ℝ) where
  toFun p e := p (M.tail (rotate e.val)) - p (M.tail e.val)
  map_add' p q := by ext e; simp; ring
  map_smul' c p := by ext e; simp; ring

lemma extend_coboundary (p : V → ℝ) (d : Dart (F := F)) :
    M.extend (M.coboundary p) d = p (M.tail (rotate d)) - p (M.tail d) := by
  change M.extend (fun e => p (M.tail (rotate e.val)) - p (M.tail e.val)) d = _
  apply M.extend_of_antisymmetric (fun e => p (M.tail (rotate e)) - p (M.tail e))
  intro e
  rw [M.tail_rotate_mate, M.tail_mate, rotate_apply]
  ring

noncomputable def boundarySum : (M.Edge → ℝ) →ₗ[ℝ] (F → ℝ) where
  toFun w f := ∑ i : Fin 3, M.extend w (f,i)
  map_add' w z := by
    ext f
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold extend
    split_ifs <;> simp [add_comm]
  map_smul' c w := by
    ext f
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold extend
    split_ifs <;> simp

lemma boundarySum_coboundary (p : V → ℝ) : M.boundarySum (M.coboundary p) = 0 := by
  ext f
  change (∑ i : Fin 3, M.extend (M.coboundary p) (f,i)) = 0
  simp only [M.extend_coboundary, Fin.sum_univ_three, rotate_apply]
  change p (M.tail (f,1)) - p (M.tail (f,0)) +
    (p (M.tail (f,2)) - p (M.tail (f,1))) +
    (p (M.tail (f,0)) - p (M.tail (f,2))) = 0
  ring

lemma exact_iff : M.Exact ↔ M.boundarySum.ker = M.coboundary.range := by
  constructor
  · intro he
    apply le_antisymm
    · intro w hw
      rcases he (M.extend w) (M.extend_mate w) (congrFun hw) with ⟨p,hp⟩
      refine ⟨p, ?_⟩
      ext e
      change p (M.tail (rotate e.val)) - p (M.tail e.val) = w e
      simpa only [M.extend_edge] using (hp e.val).symm
    · rintro _ ⟨p,rfl⟩
      exact M.boundarySum_coboundary p
  · intro he w ha hf
    have hk : (fun e : M.Edge => w e.val) ∈ M.boundarySum.ker := by
      ext f
      change (∑ i : Fin 3, M.extend (fun e => w e.val) (f,i)) = 0
      simpa only [M.extend_of_antisymmetric w ha] using hf f
    rw [he] at hk
    rcases hk with ⟨p,hp⟩
    refine ⟨p, fun d => ?_⟩
    rw [← M.extend_of_antisymmetric w ha d, ← hp, M.extend_coboundary]

lemma sum_boundarySum [Fintype F] (w : M.Edge → ℝ) : ∑ f, M.boundarySum w f = 0 := by
  have h : (∑ d : Dart (F := F), M.extend w d) = -(∑ d : Dart (F := F), M.extend w d) := by
    calc
      _ = ∑ d : Dart (F := F), M.extend w (M.mate d) := (Equiv.sum_comp M.mate _).symm
      _ = _ := by simp [M.extend_mate]
  have hz : (∑ d : Dart (F := F), M.extend w d) = 0 := by linarith
  simpa only [boundarySum, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type] using hz

lemma exact_euler_inequality [Fintype F] [Fintype V] [Nonempty F] (he : M.Exact) :
    3 * Fintype.card F < 2 * (Fintype.card V + Fintype.card F) := by
  classical
  let : Fintype M.Edge := Fintype.ofFinite _
  have hproper : M.boundarySum.range ≠ ⊤ := by
    intro h
    have h1 : (fun _ : F => (1 : ℝ)) ∈ M.boundarySum.range := by rw [h]; trivial
    rcases h1 with ⟨w,hw⟩
    have hz := M.sum_boundarySum w
    rw [hw] at hz
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hz
    have hn := Fintype.card_pos (α := F)
    exact (Nat.ne_of_gt hn) (Nat.cast_eq_zero.mp hz)
  have hd := LinearMap.finrank_range_add_finrank_ker M.boundarySum
  have hr := Submodule.finrank_lt (K := ℝ) hproper
  have hk := LinearMap.finrank_range_le M.coboundary
  rw [← M.exact_iff.mp he] at hk
  simp only [Module.finrank_pi] at hd hr hk
  have hc := M.edge_card
  omega

end OrientedEdges

lemma tail_iterate_turn (d : Dart (F := F)) (n : ℕ) :
    M.tail (M.turn^[n] d) = M.tail d := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply', M.tail_turn] using ih

lemma six_turns_injective (direction : Dart (F := F) → LinkDirection)
    (hadj : ∀ d, direction (M.turn d) ∈ linkNeighbors (direction d))
    (hnob : ∀ d, direction (M.turn (M.turn d)) ≠ direction d)
    (d : Dart (F := F)) :
    Function.Injective (fun i : Fin 6 => M.turn^[i.val] d) := by
  have hn (i j : Fin 6) (hij : i.val < j.val) : M.turn^[i.val] d ≠ M.turn^[j.val] d := by
    intro he
    let v : ℕ → LinkDirection := fun k => direction (M.turn^[k] (M.turn^[i.val] d))
    have ha : ∀ k < j.val-i.val, v (k+1) ∈ linkNeighbors (v k) := by
      intro k _
      simpa only [v, Function.iterate_succ_apply'] using hadj (M.turn^[k] (M.turn^[i.val] d))
    have hb : ∀ k, k+2 ≤ j.val-i.val → v (k+2) ≠ v k := by
      intro k _
      simpa only [v, Function.iterate_succ_apply'] using hnob (M.turn^[k] (M.turn^[i.val] d))
    have hv : v (j.val-i.val) = v 0 := by
      dsimp only [v, Function.iterate_zero, id_eq]
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hij), ← he]
    have hg := link_closed_walk_length (j.val-i.val) (by omega) v ha hb hv
    omega
  intro i j he
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact False.elim (hn i j h he)
  · exact h
  · exact False.elim (hn j i h he.symm)

lemma degree_at_least_six [Fintype F] [Fintype V]
    (hs : Function.Surjective M.tail)
    (direction : Dart (F := F) → LinkDirection)
    (hadj : ∀ d, direction (M.turn d) ∈ linkNeighbors (direction d))
    (hnob : ∀ d, direction (M.turn (M.turn d)) ≠ direction d) :
    6 * Fintype.card V ≤ 3 * Fintype.card F := by
  classical
  have hb (v : V) : 6 ≤ Fintype.card {d // M.tail d = v} := by
    obtain ⟨d,hd⟩ := hs v
    let j : Fin 6 → {d // M.tail d = v} := fun i =>
      ⟨M.turn^[i.val] d, (M.tail_iterate_turn d i.val).trans hd⟩
    have hi : Function.Injective j := by
      intro a b hab
      exact M.six_turns_injective direction hadj hnob d (congrArg Subtype.val hab)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective j hi
  have he : (∑ v : V, Fintype.card {d // M.tail d = v}) = 3 * Fintype.card F := by
    have h := Fintype.sum_fiberwise M.tail (fun _ => (1 : ℕ))
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_prod, Fintype.card_fin, mul_comm, one_mul] using h
  have hh := Finset.sum_le_sum (fun (v : V) (_ : v ∈ Finset.univ) => hb v)
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, he, mul_comm] using hh

/-- Curvature forces a backtrack in any nonempty exact triangular mesh.
Only finite linear algebra, incidence counting, and the checked finite link
are used here, in place of a black-box planar Euler theorem. -/
theorem exists_link_backtrack [Fintype F] [Fintype V] [Nonempty F]
    (he : M.Exact) (hs : Function.Surjective M.tail)
    (direction : Dart (F := F) → LinkDirection)
    (hadj : ∀ d, direction (M.turn d) ∈ linkNeighbors (direction d)) :
    ∃ d, direction (M.turn (M.turn d)) = direction d := by
  classical
  by_contra hn
  have hb : ∀ d, direction (M.turn (M.turn d)) ≠ direction d := by simpa using hn
  have hd := M.degree_at_least_six hs direction hadj hb
  let : LinearOrder (Dart (F := F)) := (Fintype.equivFin _).linearOrder
  have hi := M.exact_euler_inequality he
  omega

end TriangleMesh
end ArtinCAT0

end OAI
