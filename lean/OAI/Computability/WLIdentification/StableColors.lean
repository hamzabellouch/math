import OAI.Computability.WLIdentification.ConstraintSchemas

namespace OAI

namespace WLIdentification

/-- Stable joint colors, transported to actual finite vertex types. -/
def SimpleStable {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) {k : ℕ}
    (v : Fin k → V) (w : Fin k → W) : Prop :=
  StableTuple (G := graphOfSimple G) (H := graphOfSimple H) k
    (fun i => Fintype.equivFin V (v i)) (fun i => Fintype.equivFin W (w i))

namespace SimpleStable
variable {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {k : ℕ} {v : Fin k → V} {w : Fin k → W}

theorem local_info (hk : 2 ≤ k) (h : SimpleStable G H v w) :
    (∀ i j, v i = v j ↔ w i = w j) ∧
    (∀ i j, G.Adj (v i) (v j) ↔ H.Adj (w i) (w j)) ∧
    (∀ i, G.degree (v i) = H.degree (w i)) := by
  obtain ⟨he, ha, hd⟩ := round_one_local hk (h 1)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    constructor
    · intro hh
      exact (Fintype.equivFin W).injective ((he i j).mp (congrArg (Fintype.equivFin V) hh))
    · intro hh
      exact (Fintype.equivFin V).injective ((he i j).mpr (congrArg (Fintype.equivFin W) hh))
  · intro i j
    simpa only [graphOfSimple_edge, decide_eq_decide] using ha i j
  · intro i
    simpa only [graphOfSimple_degree] using hd i

theorem extension (hk : 2 ≤ k) (h : SimpleStable G H v w) :
    ∃ e : V ≃ W,
      (∀ z i, SimpleStable G H (Function.update v i z) (Function.update w i (e z))) ∧
      (∀ i, e (v i) = w i) ∧
      (∀ z i, G.Adj (v i) z ↔ H.Adj (w i) (e z)) ∧
      (∀ z, G.degree z = H.degree (e z)) := by
  classical
  obtain ⟨f, hf, hfix, ha, hd⟩ := stableTuple_extension_local hk h
  change Fin (Fintype.card V) ≃ Fin (Fintype.card W) at f
  let e := (Fintype.equivFin V).trans (f.trans (Fintype.equivFin W).symm)
  have he (z : V) : Fintype.equivFin W (e z) = f (Fintype.equivFin V z) := by
    exact (Fintype.equivFin W).apply_symm_apply (f (Fintype.equivFin V z))
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro z i
    have h1 : (fun j => Fintype.equivFin V (Function.update v i z j)) =
        Function.update (fun j => Fintype.equivFin V (v j)) i (Fintype.equivFin V z) := by
      funext j; by_cases hj : j = i <;> simp [hj]
    have h2 : (fun j => Fintype.equivFin W (Function.update w i (e z) j)) =
        Function.update (fun j => Fintype.equivFin W (w j)) i (f (Fintype.equivFin V z)) := by
      funext j; by_cases hj : j = i <;> simp [hj, he]
    dsimp only [SimpleStable]
    rw [h1, h2]
    exact hf _ _
  · intro i
    apply (Fintype.equivFin W).injective
    exact (he (v i)).trans (hfix i)
  · intro z i
    have hh := (ha (Fintype.equivFin V z) i).trans
      (congrArg ((graphOfSimple H).edge (Fintype.equivFin W (w i))) (he z).symm)
    simpa only [graphOfSimple_edge, decide_eq_decide] using hh
  · intro z
    have hh := (hd (Fintype.equivFin V z)).trans
      (congrArg (degree (graphOfSimple H)) (he z).symm)
    simpa only [graphOfSimple_degree] using hh

end SimpleStable

/-- Testing degree intervals converts stable uncolored tuples back into their
named base classes, without assuming color information as a new WL hypothesis. -/
def TagStable {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (color : V → ℕ) (color' : W → ℕ)
    {k : ℕ} (v : Fin k → V) (w : Fin k → W) : Prop :=
  SimpleStable (withLeaves G (tagSize color)) (withLeaves H (tagSize color'))
    (fun i => .inl (v i)) (fun i => .inl (w i))

namespace TagStable
variable {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {color : V → ℕ} {color' : W → ℕ} {k : ℕ} {v : Fin k → V} {w : Fin k → W}

theorem colors (hk : 2 ≤ k) (hN : Fintype.card V = Fintype.card W)
    (h : TagStable G H color color' v w) (i : Fin k) : color (v i) = color' (w i) := by
  have hd := (SimpleStable.local_info hk h).2.2 i
  have hh := congrArg (fun n => n / (Fintype.card V + 1)) hd
  rw [tag_degree_color, hN, tag_degree_color] at hh
  exact hh

omit [DecidableRel H.Adj] in
theorem exists_of_equivalent (hk : 2 ≤ k) (hc : ∀ v, 0 < color v)
    (h : Equivalent k (taggedGraph G color) (taggedGraph H color')) (v : Fin k → V) :
    ∃ w : Fin k → W, TagStable G H color color' v w := by
  classical
  obtain ⟨f, hf⟩ := stableTuple_exists (by omega : k ≠ 1) h
    (fun i => Fintype.equivFin (LeafVertex (tagSize color)) (.inl (v i)))
  let w' (i : Fin k) := (Fintype.equivFin (LeafVertex (tagSize color'))).symm (f i)
  have hw : SimpleStable (withLeaves G (tagSize color)) (withLeaves H (tagSize color'))
      (fun i => .inl (v i)) w' := by
    dsimp only [SimpleStable, w']
    convert hf using 1
    apply Iff.of_eq
    congr 1
    funext i
    exact (Fintype.equivFin (LeafVertex (tagSize color'))).apply_symm_apply (f i)
  have hd := (SimpleStable.local_info hk hw).2.2
  have hb (i : Fin k) : ∃ x : W, w' i = .inl x := by
    cases hwi : w' i with
    | inl x => exact ⟨x, rfl⟩
    | inr p =>
      have hh := hd i
      rw [hwi, withLeaves_leaf_degree] at hh
      have := tag_base_degree_gt_one G color hc (v i)
      omega
  choose w hw' using hb
  refine ⟨w, ?_⟩
  have hh : w' = fun i => .inl (w i) := funext hw'
  rw [hh] at hw
  exact hw

theorem extension (hk : 2 ≤ k) (hc : ∀ v, 0 < color v)
    (hN : Fintype.card V = Fintype.card W) (h : TagStable G H color color' v w) :
    ∃ e : V → W,
      (∀ z i, TagStable G H color color' (Function.update v i z) (Function.update w i (e z))) ∧
      (∀ z, color z = color' (e z)) ∧
      (∀ z i, G.Adj (v i) z ↔ H.Adj (w i) (e z)) := by
  classical
  obtain ⟨f, hf, _, ha, hd⟩ := SimpleStable.extension hk h
  have hb (z : V) : ∃ x : W, f (.inl z) = .inl x := by
    cases hz : f (.inl z) with
    | inl x => exact ⟨x, rfl⟩
    | inr p =>
      have hh := hd (.inl z)
      rw [hz, withLeaves_leaf_degree] at hh
      have := tag_base_degree_gt_one G color hc z
      omega
  choose e he using hb
  refine ⟨e, ?_, ?_, ?_⟩
  · intro z i
    have hh := hf (.inl z) i
    rw [he] at hh
    have h1 : Function.update (fun j => Sum.inl (v j) : Fin k → LeafVertex (tagSize color)) i (.inl z) =
        fun j => .inl (Function.update v i z j) := by
      funext j; by_cases hj : j = i <;> simp [hj]
    have h2 : Function.update (fun j => Sum.inl (w j) : Fin k → LeafVertex (tagSize color')) i (.inl (e z)) =
        fun j => .inl (Function.update w i (e z) j) := by
      funext j; by_cases hj : j = i <;> simp [hj]
    rw [h1, h2] at hh
    exact hh
  · intro z
    have hh := hd (.inl z)
    rw [he] at hh
    have hh' := congrArg (fun n => n / (Fintype.card V + 1)) hh
    rw [tag_degree_color, hN, tag_degree_color] at hh'
    exact hh'
  · intro z i
    have hh := ha (.inl z) i
    rw [he] at hh
    exact hh

end TagStable

end WLIdentification

end OAI
