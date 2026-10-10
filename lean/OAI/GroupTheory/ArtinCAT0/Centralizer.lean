import OAI.GroupTheory.ArtinCAT0.TriangleMesh

namespace OAI

namespace ArtinCAT0

section RestrictedGeometry

variable {X : Type*} [MetricSpace X]

def GeodesicallyConvex (C : Set X) : Prop :=
  ∀ (a b : X), a ∈ C → b ∈ C → ∀ γ : ℝ → X, Segment a b γ →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ C

lemma CAT0_subtype (hX : CAT0 X) {C : Set X} (hC : GeodesicallyConvex C) : CAT0 C := by
  classical
  constructor
  · intro a b
    obtain ⟨γ, hγ⟩ := hX.1 a.val b.val
    let η : ℝ → C := fun t => if ht : t ∈ Set.Icc (0 : ℝ) 1
      then ⟨γ t, hC a b a.property b.property γ hγ t ht⟩ else a
    refine ⟨η, ?_, ?_, ?_⟩
    · apply Subtype.ext
      simp [η, hγ.1]
    · apply Subtype.ext
      simp [η, hγ.2.1]
    · intro s hs t ht
      change dist (η s).val (η t).val = |s-t| * dist a.val b.val
      simp only [η, dite_eq_left hs, dite_eq_left ht]
      exact hγ.2.2 s hs t ht
  · intro a b c γ η hγ hη t ht u hu
    have hg : Segment a.val b.val (fun s => (γ s).val) :=
      ⟨congrArg Subtype.val hγ.1, congrArg Subtype.val hγ.2.1, hγ.2.2⟩
    have he : Segment a.val c.val (fun s => (η s).val) :=
      ⟨congrArg Subtype.val hη.1, congrArg Subtype.val hη.2.1, hη.2.2⟩
    exact hX.2 a.val b.val c.val _ _ hg he t ht u hu

end RestrictedGeometry

section CommonCentralizerGeometry

variable {ι G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

def tupleCentralizer (q : ι → G) : Subgroup G where
  carrier := {g | ∀ i, Commute g (q i)}
  one_mem' := fun _ => Commute.one_left _
  mul_mem' := fun ha hb i => (ha i).mul_left (hb i)
  inv_mem' := fun ha i => (ha i).inv_left

def displacementSublevel (q : ι → G) (A : ℝ) : Set X :=
  {x | ∀ i, dist x (q i • x) ≤ A}

lemma displacementSublevel_closed (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (q : ι → G) (A : ℝ) : IsClosed (displacementSublevel (X := X) q A) := by
  have he : displacementSublevel (X := X) q A = ⋂ i, {x | dist x (q i • x) ≤ A} := by
    ext x
    simp [displacementSublevel]
  rw [he]
  exact isClosed_iInter (fun i => isClosed_le (continuous_id.dist (hi (q i)).continuous) continuous_const)

lemma displacementSublevel_convex (hX : CAT0 X)
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (q : ι → G) (A : ℝ) :
    GeodesicallyConvex (displacementSublevel (X := X) q A) := by
  intro a b ha hb γ hγ t ht i
  have hη := segment_isometry hγ (hi (q i))
  have hc := comparison_convexity hX hγ hη ht
  have hm₁ := mul_le_mul_of_nonneg_left (ha i) (show 0 ≤ 1-t by linarith [ht.2])
  have hm₂ := mul_le_mul_of_nonneg_left (hb i) ht.1
  change dist (γ t) (q i • γ t) ≤ A
  dsimp only [Function.comp_apply] at hc
  linarith

lemma displacementSublevel_smul (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (q : ι → G) (A : ℝ) (g : tupleCentralizer q)
    {x : X} (hx : x ∈ displacementSublevel q A) :
    g.val • x ∈ displacementSublevel q A := by
  intro i
  have he : q i • (g.val • x) = g.val • (q i • x) := by
    simp only [← mul_smul, (g.property i).eq]
  rw [he, (hi g.val).dist_eq]
  exact hx i

@[instance_reducible] noncomputable def sublevelAction (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (q : ι → G) (A : ℝ) : MulAction (tupleCentralizer q) (displacementSublevel (X := X) q A) where
  smul g x := ⟨g.val • x.val, displacementSublevel_smul hi q A g x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g.val h.val x.val)

lemma sublevelAction_isometry (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (q : ι → G) (A : ℝ) :
    letI := sublevelAction hi q A
    ∀ g : tupleCentralizer q, Isometry (fun x : displacementSublevel (X := X) q A => g • x) := by
  let := sublevelAction hi q A
  intro g
  exact Isometry.of_dist_eq (fun x y => (hi g.val).dist_eq x.val y.val)

lemma sublevelAction_proper (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (hp : ∀ K : Set X, IsCompact K →
      {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}.Finite)
    (q : ι → G) (A : ℝ) :
    letI := sublevelAction hi q A
    ∀ K : Set (displacementSublevel (X := X) q A), IsCompact K →
      {g : tupleCentralizer q | ((fun x => g • x) '' K ∩ K).Nonempty}.Finite := by
  let := sublevelAction hi q A
  intro K hK
  have hF := (hp (Subtype.val '' K) (hK.image continuous_subtype_val)).preimage
    (f := ((↑) : tupleCentralizer q → G))
    (fun _ _ _ _ h => Subtype.val_injective h)
  apply hF.subset
  rintro g ⟨x, ⟨y, hy, rfl⟩, hx⟩
  exact ⟨g.val • y.val, ⟨y.val, ⟨y, hy, rfl⟩, rfl⟩, ⟨g • y, hx, rfl⟩⟩

lemma sublevelAction_cocompact [Finite ι] [ProperSpace X] [Nonempty X]
    (hG : GeometricAction G X) (q : ι → G) (A : ℝ) (hA : 0 ≤ A) :
    letI := sublevelAction hG.2.1 q A
    ∃ L : Set (displacementSublevel (X := X) q A), IsCompact L ∧
      ∀ x : displacementSublevel (X := X) q A,
        ∃ g : tupleCentralizer q, ∃ k ∈ L, g • k = x := by
  classical
  let := sublevelAction hG.2.1 q A
  let o : X := Classical.choice inferInstance
  obtain ⟨K, hK, hcover⟩ := hG.2.2.2
  let F : Set G := {g | ∃ p ∈ K, dist p (g • p) ≤ A}
  have hF : F.Finite := finite_movers_of_compact hG.2.2.1 hK o A hA
  let Q : Set (ι → G) := {v | (∀ i, v i ∈ F) ∧ ∃ g : G, ∀ i, g⁻¹ * q i * g = v i}
  have hQ : Q.Finite := (Set.Finite.pi (fun _ : ι => hF)).subset (by
    intro v hv i _
    exact hv.1 i)
  let : Finite Q := hQ.to_subtype
  let rep : Q → G := fun v => Classical.choose v.property.2
  have hrep (v : Q) (i : ι) : (rep v)⁻¹ * q i * rep v = v.val i :=
    Classical.choose_spec v.property.2 i
  let L₀ : Set X := ⋃ v : Q, (fun p => rep v • p) '' K
  have hL₀ : IsCompact L₀ := isCompact_iUnion (fun v => hK.image (hG.2.1 (rep v)).continuous)
  let L : Set (displacementSublevel (X := X) q A) := Subtype.val ⁻¹' L₀
  refine ⟨L, (displacementSublevel_closed hG.2.1 q A).isClosedEmbedding_subtypeVal.isCompact_preimage hL₀, ?_⟩
  intro x
  obtain ⟨g, p, hp, hg⟩ := hcover x.val
  let v : ι → G := fun i => g⁻¹ * q i * g
  have hv : v ∈ Q := by
    refine ⟨?_, g, fun _ => rfl⟩
    intro i
    refine ⟨p, hp, ?_⟩
    have hd : dist p (v i • p) = dist (g • p) (q i • (g • p)) := by
      rw [← (hG.2.1 g).dist_eq]
      simp [v, mul_smul]
    rw [hd, hg]
    exact x.property i
  let r : G := rep ⟨v, hv⟩
  have hr (i : ι) : r⁻¹ * q i * r = g⁻¹ * q i * g := hrep ⟨v, hv⟩ i
  have hc : g * r⁻¹ ∈ tupleCentralizer q := by
    intro i
    change g * r⁻¹ * q i = q i * (g * r⁻¹)
    calc
      g * r⁻¹ * q i = g * (r⁻¹ * q i * r) * r⁻¹ := by group
      _ = g * (g⁻¹ * q i * g) * r⁻¹ := by rw [hr]
      _ = _ := by group
  let c : tupleCentralizer q := ⟨g * r⁻¹, hc⟩
  refine ⟨c, c⁻¹ • x, ?_, smul_inv_smul c x⟩
  change ((c⁻¹ • x).val) ∈ L₀
  apply Set.mem_iUnion.mpr
  refine ⟨⟨v, hv⟩, p, hp, ?_⟩
  change r • p = (g * r⁻¹)⁻¹ • x.val
  rw [← hg]
  simp only [mul_inv_rev, inv_inv, mul_smul, inv_smul_smul]

/-- The finite-tuple geometric centralizer theorem, with no commutation
hypothesis on the tuple itself and no dimension hypothesis. -/
theorem geometric_tupleCentralizer [Finite ι] [ProperSpace X] [Nonempty X]
    (hG : GeometricAction G X) (q : ι → G) (A : ℝ) (hA : 0 ≤ A) :
    letI := sublevelAction hG.2.1 q A
    GeometricAction (tupleCentralizer q) (displacementSublevel (X := X) q A) := by
  let := sublevelAction hG.2.1 q A
  exact ⟨CAT0_subtype hG.1 (displacementSublevel_convex hG.1 hG.2.1 q A),
    sublevelAction_isometry hG.2.1 q A, sublevelAction_proper hG.2.1 hG.2.2.1 q A,
    sublevelAction_cocompact hG q A hA⟩

lemma sublevelAction_stableLength (hi : ∀ g : G, Isometry (fun x : X => g • x))
    (q : ι → G) (A : ℝ) (x : displacementSublevel (X := X) q A)
    (g : tupleCentralizer q) :
    letI := sublevelAction hi q A
    stableLengthAt x g = stableLengthAt x.val g.val := by
  rfl

lemma exists_sublevel_nonempty [Finite ι] [Nonempty X] (q : ι → G) :
    ∃ A : ℝ, 0 ≤ A ∧ Nonempty (displacementSublevel (X := X) q A) := by
  classical
  let := Fintype.ofFinite ι
  let x : X := Classical.choice inferInstance
  refine ⟨∑ i : ι, dist x (q i • x), Finset.sum_nonneg (fun _ _ => dist_nonneg), ?_⟩
  refine ⟨⟨x, fun i => ?_⟩⟩
  exact Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (dist_nonneg : 0 ≤ dist x (q j • x))) (Finset.mem_univ i)

lemma sublevel_properSpace [ProperSpace X]
    (hi : ∀ g : G, Isometry (fun x : X => g • x)) (q : ι → G) (A : ℝ) :
    ProperSpace (displacementSublevel (X := X) q A) :=
  ProperSpace.of_isClosed (displacementSublevel_closed hi q A)

end CommonCentralizerGeometry
end ArtinCAT0

end OAI
