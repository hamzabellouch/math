import OAI.GroupTheory.ArtinCAT0.Wires

namespace OAI

namespace ArtinCAT0.TriangleMesh

/-- On a collapsed triangular face the two nonconstant sides are paired;
on an uncollapsed face every side is a live terminal. -/
def passIndex (v : Fin 3 → Fin 3) (i : Fin 3) : Fin 3 :=
  if Function.Injective v then i else if v (i+1) ≠ v (i+2) then i+1 else i+2

lemma passIndex_active : ∀ (v : Fin 3 → Fin 3) (i : Fin 3), v i ≠ v (i+1) →
    v (passIndex v i) ≠ v (passIndex v i+1) := by decide

lemma passIndex_involutive : ∀ (v : Fin 3 → Fin 3) (i : Fin 3), v i ≠ v (i+1) →
    passIndex v (passIndex v i) = i := by decide

lemma passIndex_fixed_iff : ∀ (v : Fin 3 → Fin 3) (i : Fin 3), v i ≠ v (i+1) →
    (passIndex v i = i ↔ Function.Injective v) := by decide

lemma passIndex_reverses : ∀ (v : Fin 3 → Fin 3) (i : Fin 3), v i ≠ v (i+1) →
    ¬ Function.Injective v →
    v (passIndex v i) = v (i+1) ∧ v (passIndex v i+1) = v i := by decide

lemma passIndex_cases : ∀ (v : Fin 3 → Fin 3) (i : Fin 3), v i ≠ v (i+1) →
    ¬ Function.Injective v →
    (passIndex v i = i+1 ∧ v (i+2) = v i) ∨
    (passIndex v i = i+2 ∧ v (i+1) = v (i+2)) := by decide

lemma exists_constant_side : ∀ (v : Fin 3 → Fin 3), ¬ Function.Injective v →
    ∃ i, v i = v (i+1) := by decide

lemma passIndex_after_constant : ∀ (v : Fin 3 → Fin 3) (i : Fin 3),
    v i = v (i+1) → v (i+1) ≠ v (i+2) → passIndex v (i+1) = i+2 := by decide

lemma sum_three_rotate (w : Fin 3 → ℝ) (i : Fin 3) :
    ∑ j, w j = w i + w (i+1) + w (i+2) := by
  fin_cases i <;> simp [Fin.sum_univ_three, Fin.add_def] <;> ring

lemma sum_collapsed (v : Fin 3 → Fin 3) (w : Fin 3 → ℝ)
    (hf : ¬ Function.Injective v)
    (hz : ∀ i, v i = v (i+1) → w i = 0)
    (hp : ∀ i, v i ≠ v (i+1) → w (passIndex v i) = -w i) :
    ∑ i, w i = 0 := by
  obtain ⟨i,hi⟩ := exists_constant_side v hf
  have h3 : i+2+1 = i := by omega
  rw [sum_three_rotate w i, hz i hi, zero_add]
  by_cases he : v (i+1) = v (i+2)
  · rw [hz (i+1) (by simpa [add_assoc] using he)]
    have hh : v (i+2) = v (i+2+1) := by rw [h3, ← he, hi]
    rw [hz (i+2) hh]
    ring
  · have hh := hp (i+1) (by simpa [add_assoc] using he)
    rw [passIndex_after_constant v i hi he] at hh
    rw [hh]
    ring

variable {F V : Type*} (M : TriangleMesh F V)

/-- Simplicial labels permit a face to map onto an edge or a vertex. The mate
conditions retain the labelled side, not merely its group endpoints. -/
structure SimplicialLabeling where
  cell : F → TargetTriangle
  corner : F → Fin 3 → Fin 3
  vertex : V → TriangleGroup
  vertex_tail : ∀ d, vertex (M.tail d) = (cell d.1).vertex (corner d.1 d.2)
  mate_active : ∀ d,
    (corner (M.mate d).1 (M.mate d).2 ≠ corner (M.mate d).1 ((M.mate d).2+1)) ↔
    (corner d.1 d.2 ≠ corner d.1 (d.2+1))
  mate_compatibility : ∀ d, corner d.1 d.2 ≠ corner d.1 (d.2+1) →
    (cell (M.mate d).1).direction (corner (M.mate d).1 (M.mate d).2)
      (corner (M.mate d).1 ((M.mate d).2+1)) =
    reverseDirection ((cell d.1).direction (corner d.1 d.2) (corner d.1 (d.2+1)))

namespace SimplicialLabeling
variable {M} (L : M.SimplicialLabeling)

def Active (d : F × Fin 3) : Prop := L.corner d.1 d.2 ≠ L.corner d.1 (d.2+1)
def Full (f : F) : Prop := Function.Injective (L.corner f)
abbrev FullFace := {f : F // L.Full f}
abbrev ActiveDart := {d : F × Fin 3 // L.Active d}

noncomputable def wire : WireSystem L.ActiveDart where
  mate d := ⟨M.mate d.val, (L.mate_active d.val).2 d.property⟩
  mate_inv d := Subtype.ext (M.mate_mate d.val)
  mate_ne d h := M.mate_ne d.val (congrArg Subtype.val h)
  pass d := ⟨(d.val.1,passIndex (L.corner d.val.1) d.val.2),
    passIndex_active _ _ d.property⟩
  pass_inv d := Subtype.ext (congrArg (d.val.1,·) (passIndex_involutive _ _ d.property))

lemma full_active (f : L.FullFace) (i : Fin 3) : L.Active (f.val,i) := by
  apply f.property.ne
  intro he
  have := congrArg Fin.val he
  omega

lemma wire_fixed_iff (d : L.ActiveDart) : L.wire.pass d = d ↔ L.Full d.val.1 := by
  constructor
  · intro h
    exact (passIndex_fixed_iff _ _ d.property).1 (congrArg (fun d => d.val.2) h)
  · intro h
    apply Subtype.ext
    exact Prod.ext rfl ((passIndex_fixed_iff _ _ d.property).2 h)

noncomputable def fullDartEquiv : L.wire.Live ≃ L.FullFace × Fin 3 where
  toFun d := (⟨d.val.val.1,(L.wire_fixed_iff d.val).1 d.property⟩,d.val.val.2)
  invFun d := ⟨⟨(d.1.val,d.2),L.full_active d.1 d.2⟩,
    (L.wire_fixed_iff _).2 d.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Identify the endpoints of every constant side. `Quot` includes the
reflexive, symmetric, and transitive closure automatically. -/
def ZeroEdge (v w : V) : Prop :=
  ∃ d : F × Fin 3, ¬ L.Active d ∧ M.tail d = v ∧ M.tail (rotate d) = w
abbrev CollapsedVertex := Quot L.ZeroEdge

def qvertex (v : V) : L.CollapsedVertex := Quot.mk _ v

lemma qvertex_zero (d : F × Fin 3) (hd : ¬ L.Active d) :
    L.qvertex (M.tail d) = L.qvertex (M.tail (rotate d)) :=
  Quot.sound ⟨d,hd,rfl,rfl⟩

lemma collapsed_zero (p : V → ℝ) (hp : ∀ d, ¬ L.Active d → p (M.tail d) = p (M.tail (rotate d)))
    {v w : V} (h : L.ZeroEdge v w) : p v = p w := by
  obtain ⟨d,hd,rfl,rfl⟩ := h
  exact hp d hd

lemma vertex_zero {v w : V} (h : L.ZeroEdge v w) : L.vertex v = L.vertex w := by
  obtain ⟨d,hd,rfl,rfl⟩ := h
  rw [L.vertex_tail d, L.vertex_tail (rotate d)]
  have hh : L.corner d.1 d.2 = L.corner d.1 (d.2+1) := not_not.mp hd
  exact congrArg (L.cell d.1).vertex hh

def collapsedLabel : L.CollapsedVertex → TriangleGroup := Quot.lift L.vertex (fun _ _ => L.vertex_zero)

lemma pass_tail_head (d : L.ActiveDart) (hd : L.wire.pass d ≠ d) :
    L.qvertex (M.tail (L.wire.pass d).val) = L.qvertex (M.tail (rotate d.val)) ∧
    L.qvertex (M.tail (rotate (L.wire.pass d).val)) = L.qvertex (M.tail d.val) := by
  have hf : ¬ L.Full d.val.1 := fun h => hd ((L.wire_fixed_iff d).2 h)
  rcases passIndex_cases (L.corner d.val.1) d.val.2 d.property hf with ⟨he,hz⟩ | ⟨he,hz⟩
  · change L.qvertex (M.tail (d.val.1,passIndex _ _)) = _ ∧
      L.qvertex (M.tail (d.val.1,passIndex _ _+1)) = _
    rw [he]
    refine ⟨rfl, ?_⟩
    have hh := L.qvertex_zero (d.val.1,d.val.2+2) (by simpa [Active, show d.val.2+2+1 = d.val.2 by omega] using hz)
    simpa only [rotate_apply, show d.val.2+2+1 = d.val.2 by omega,
      show d.val.2+1+1 = d.val.2+2 by omega] using hh
  · change L.qvertex (M.tail (d.val.1,passIndex _ _)) = _ ∧
      L.qvertex (M.tail (d.val.1,passIndex _ _+1)) = _
    rw [he]
    refine ⟨?_, ?_⟩
    · have hh := L.qvertex_zero (d.val.1,d.val.2+1) (by simpa [Active, add_assoc] using hz)
      simpa only [rotate_apply, show d.val.2+1+1 = d.val.2+2 by omega] using hh.symm
    · rw [show d.val.2+2+1 = d.val.2 by omega]

abbrev WireColor := L.CollapsedVertex × L.CollapsedVertex × LinkDirection

def reverseColor (c : L.WireColor) : L.WireColor := (c.2.1,c.1,reverseDirection c.2.2)

lemma reverseColor_involutive : Function.Involutive L.reverseColor := by
  rintro ⟨x,y,z⟩
  simp only [reverseColor, reverseDirection_reverseDirection]

def wireColor (d : L.ActiveDart) : L.WireColor :=
  (L.qvertex (M.tail d.val), L.qvertex (M.tail (rotate d.val)),
    (L.cell d.val.1).direction (L.corner d.val.1 d.val.2) (L.corner d.val.1 (d.val.2+1)))

lemma wireColor_mate (d : L.ActiveDart) :
    L.wireColor (L.wire.mate d) = L.reverseColor (L.wireColor d) := by
  apply Prod.ext
  · exact congrArg L.qvertex (M.tail_mate d.val)
  · apply Prod.ext
    · exact congrArg L.qvertex (M.tail_rotate_mate d.val)
    · exact L.mate_compatibility d.val d.property

lemma wireColor_pass (d : L.ActiveDart) (hd : L.wire.pass d ≠ d) :
    L.wireColor (L.wire.pass d) = L.reverseColor (L.wireColor d) := by
  obtain ⟨ht,hh⟩ := L.pass_tail_head d hd
  apply Prod.ext ht
  apply Prod.ext hh
  change (L.cell d.val.1).direction (L.corner d.val.1 (passIndex (L.corner d.val.1) d.val.2))
    (L.corner d.val.1 (passIndex (L.corner d.val.1) d.val.2+1)) = _
  obtain ⟨he,hf⟩ := passIndex_reverses (L.corner d.val.1) d.val.2 d.property
    (fun h => hd ((L.wire_fixed_iff d).2 h))
  rw [he,hf]
  exact cellDirection_reverse _ _ _ _ d.property

noncomputable def fullOrder (f : L.FullFace) : CornerOrder :=
  Equiv.ofBijective (L.corner f.val) ((Fintype.bijective_iff_injective_and_card _).2 ⟨f.property,rfl⟩)

@[simp] lemma fullOrder_apply (f : L.FullFace) (i : Fin 3) :
    L.fullOrder f i = L.corner f.val i := rfl

abbrev oldDart (d : L.FullFace × Fin 3) : F × Fin 3 := (d.1.val,d.2)

noncomputable def reducedMate (R : L.wire.Resolution) (d : L.FullFace × Fin 3) : L.FullFace × Fin 3 :=
  L.fullDartEquiv (R.mate (L.fullDartEquiv.symm d))

lemma reducedMate_involutive (R : L.wire.Resolution) : Function.Involutive (L.reducedMate R) := by
  intro d
  simp only [reducedMate, Equiv.symm_apply_apply]
  rw [R.mate_inv, Equiv.apply_symm_apply]

noncomputable def reducedMesh (R : L.wire.Resolution)
    (hc : ∀ d, L.wireColor (R.mate d).val = L.reverseColor (L.wireColor d.val)) :
    TriangleMesh L.FullFace L.CollapsedVertex where
  mate := (L.reducedMate_involutive R).toPerm
  mate_involutive := L.reducedMate_involutive R
  mate_ne d h := R.mate_ne (L.fullDartEquiv.symm d)
    (by
      change L.reducedMate R d = d at h
      simpa only [reducedMate, Equiv.symm_apply_apply] using congrArg L.fullDartEquiv.symm h)
  tail d := L.qvertex (M.tail (L.oldDart d))
  tail_mate d := congrArg Prod.fst (hc (L.fullDartEquiv.symm d))

noncomputable def reducedLabeling (R : L.wire.Resolution)
    (hc : ∀ d, L.wireColor (R.mate d).val = L.reverseColor (L.wireColor d.val)) :
    (L.reducedMesh R hc).Labeling where
  cell f := L.cell f.val
  order := L.fullOrder
  vertex := L.collapsedLabel
  vertex_tail d := L.vertex_tail (L.oldDart d)
  mate_compatibility d := congrArg (fun c : L.WireColor => c.2.2) (hc (L.fullDartEquiv.symm d))

noncomputable def expandWeight (v : L.ActiveDart → ℝ) (d : F × Fin 3) : ℝ := by
  classical
  exact if hd : L.Active d then v ⟨d,hd⟩ else 0

lemma expandWeight_active (v : L.ActiveDart → ℝ) (d : L.ActiveDart) :
    L.expandWeight v d.val = v d := by simp [expandWeight, d.property]

lemma expandWeight_zero (v : L.ActiveDart → ℝ) (d : F × Fin 3) (hd : ¬ L.Active d) :
    L.expandWeight v d = 0 := by simp [expandWeight, hd]

lemma expandWeight_mate (v : L.ActiveDart → ℝ)
    (ha : ∀ d, v (L.wire.mate d) = -v d) (d : F × Fin 3) :
    L.expandWeight v (M.mate d) = -L.expandWeight v d := by
  by_cases hd : L.Active d
  · have hm := (L.mate_active d).2 hd
    rw [L.expandWeight_active v ⟨M.mate d,hm⟩, L.expandWeight_active v ⟨d,hd⟩]
    exact ha ⟨d,hd⟩
  · have hm : ¬ L.Active (M.mate d) := fun h => hd ((L.mate_active d).1 h)
    simp [expandWeight, hd, hm]

lemma expandWeight_collapsed (v : L.ActiveDart → ℝ)
    (hp : ∀ d, L.wire.pass d ≠ d → v (L.wire.pass d) = -v d)
    (f : F) (hf : ¬ L.Full f) : ∑ i, L.expandWeight v (f,i) = 0 := by
  apply sum_collapsed (L.corner f) (fun i => L.expandWeight v (f,i)) hf
  · intro i hi
    exact L.expandWeight_zero v (f,i) (not_not.mpr hi)
  · intro i hi
    have ha := passIndex_active (L.corner f) i hi
    have hh := hp ⟨(f,i),hi⟩ (fun h => hf ((L.wire_fixed_iff _).1 h))
    rw [L.expandWeight_active v ⟨(f,passIndex (L.corner f) i),ha⟩,
      L.expandWeight_active v ⟨(f,i),hi⟩]
    exact hh

lemma expandWeight_full (v : L.ActiveDart → ℝ)
    (w : L.FullFace × Fin 3 → ℝ)
    (hv : ∀ d : L.wire.Live, v d.val = w (L.fullDartEquiv d))
    (d : L.FullFace × Fin 3) : L.expandWeight v (L.oldDart d) = w d := by
  change L.expandWeight v (L.fullDartEquiv.symm d).val.val = _
  rw [L.expandWeight_active, hv, Equiv.apply_symm_apply]

lemma reducedMesh_exact (R : L.wire.Resolution)
    (hcolor : ∀ d, L.wireColor (R.mate d).val = L.reverseColor (L.wireColor d.val))
    (he : M.Exact) : (L.reducedMesh R hcolor).Exact := by
  intro w ha hc
  change ∀ d, w (L.reducedMate R d) = -w d at ha
  let w' : L.wire.Live → ℝ := fun d => w (L.fullDartEquiv d)
  have ha' : ∀ d, w' (R.mate d) = -w' d := by
    intro d
    simpa only [reducedMate, Equiv.symm_apply_apply, w'] using ha (L.fullDartEquiv d)
  obtain ⟨v,hv,hm,hp⟩ := R.lift w' ha'
  have hv' : ∀ d : L.wire.Live, v d.val = w (L.fullDartEquiv d) := hv
  have hface (f : F) : ∑ i, L.expandWeight v (f,i) = 0 := by
    by_cases hf : L.Full f
    · have hh (i) := L.expandWeight_full v w hv' (⟨f,hf⟩,i)
      simpa only [hh] using hc ⟨f,hf⟩
    · exact L.expandWeight_collapsed v hp f hf
  obtain ⟨p,hp⟩ := he (L.expandWeight v) (L.expandWeight_mate v hm) hface
  have hpzero (d : F × Fin 3) (hd : ¬ L.Active d) : p (M.tail d) = p (M.tail (rotate d)) := by
    have hh := hp d
    rw [L.expandWeight_zero v d hd] at hh
    linarith
  let p' : L.CollapsedVertex → ℝ := Quot.lift p (fun _ _ => L.collapsed_zero p hpzero)
  refine ⟨p', fun d => ?_⟩
  have hh := hp (L.oldDart d)
  rw [L.expandWeight_full v w hv' d] at hh
  exact hh

noncomputable def signedSum [Fintype F] (w : TargetTriangle → ℤ) : ℤ := by
  classical
  exact ∑ f : L.FullFace, cornerSign (L.fullOrder f) * w (L.cell f.val)

/-- The sphere-counting dependency including every simplicial degeneracy.
No unproved identification of a pinched diagram with a sphere is used. -/
theorem signed_counts_zero [Fintype F] (he : M.Exact) (w : TargetTriangle → ℤ) :
    L.signedSum w = 0 := by
  classical
  obtain ⟨R,hR⟩ := WireSystem.resolve L.reverseColor L.reverseColor_involutive
    L.ActiveDart L.wire L.wireColor L.wireColor_mate L.wireColor_pass
  exact TriangleMesh.signed_counts_zero w L.FullFace L.CollapsedVertex
    (L.reducedMesh R hR) (L.reducedLabeling R hR) (L.reducedMesh_exact R hR he)

end SimplicialLabeling
end ArtinCAT0.TriangleMesh

namespace ArtinCAT0

lemma mirrorPerm_sq (u : Fin 3) : mirrorPerm u ^ 2 = 1 := by
  apply Equiv.ext
  intro d
  exact mirrorReflect_involutive u d

lemma mirrorGenerator_sq (u : Fin 3) :
    mirrorGenerator u ^ 2 = ⟨Multiplicative.ofAdd (2 • mirrorBasis (sideMirror u)),1⟩ := by
  apply SemidirectProduct.ext
  · simp only [pow_two, SemidirectProduct.mul_left, mirrorGenerator,
      mirrorAut_basis, mirrorPerm_apply, mirrorReflect_side]
    change mirrorBasis (sideMirror u) + mirrorBasis (sideMirror u) =
      (2 : ℕ) • mirrorBasis (sideMirror u)
    simp [two_smul]
  · exact mirrorPerm_sq u

lemma mirrorPerm_delta_sq (u : Fin 3) :
    (mirrorPerm u * mirrorPerm (u+1) * mirrorPerm u) ^ 2 = 1 := by
  have he (i : Fin 3) : mirrorPerm i * mirrorPerm i = 1 := mirrorPerm_sq i
  calc
    _ = mirrorPerm u * mirrorPerm (u+1) * (mirrorPerm u * mirrorPerm u) *
      mirrorPerm (u+1) * mirrorPerm u := by simp only [pow_two, mul_assoc]
    _ = 1 := by rw [he]; simp [mul_assoc, he]

lemma mirrorGenerator_delta (u : Fin 3) :
    mirrorGenerator u * mirrorGenerator (u+1) * mirrorGenerator u =
      ⟨Multiplicative.ofAdd (mirrorBasis (sideMirror u) + mirrorBasis (extraMirror u) +
        mirrorBasis (sideMirror (u+1))),
        mirrorPerm u * mirrorPerm (u+1) * mirrorPerm u⟩ := by
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, mirrorGenerator,
      map_mul, MulAut.mul_apply, mirrorAut_basis, mirrorPerm_apply, mirrorReflect_next,
      mirrorReflect_prev, mirrorReflect_extra]
    rfl
  · rfl

lemma mirrorGenerator_center (u : Fin 3) :
    (mirrorGenerator u * mirrorGenerator (u+1)) ^ 3 =
      ⟨Multiplicative.ofAdd (2 • (mirrorBasis (sideMirror u) + mirrorBasis (extraMirror u) +
        mirrorBasis (sideMirror (u+1)))),1⟩ := by
  have hd : (mirrorGenerator u * mirrorGenerator (u+1)) ^ 3 =
      (mirrorGenerator u * mirrorGenerator (u+1) * mirrorGenerator u) ^ 2 := by
    calc
      _ = (mirrorGenerator u * mirrorGenerator (u+1) * mirrorGenerator u) *
        (mirrorGenerator (u+1) * mirrorGenerator u * mirrorGenerator (u+1)) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = _ := by rw [← mirrorGenerator_braid, pow_two]
  rw [hd]
  apply SemidirectProduct.ext
  · rw [pow_two, SemidirectProduct.mul_left, mirrorGenerator_delta]
    change (Multiplicative.ofAdd (mirrorBasis (sideMirror u)) *
      Multiplicative.ofAdd (mirrorBasis (extraMirror u)) *
      Multiplicative.ofAdd (mirrorBasis (sideMirror (u+1)))) *
      mirrorAut (mirrorPerm u * mirrorPerm (u+1) * mirrorPerm u)
        (Multiplicative.ofAdd (mirrorBasis (sideMirror u)) *
        Multiplicative.ofAdd (mirrorBasis (extraMirror u)) *
        Multiplicative.ofAdd (mirrorBasis (sideMirror (u+1)))) = _
    simp only [map_mul, MulAut.mul_apply, mirrorAut_basis, mirrorPerm_apply,
      mirrorReflect_side, mirrorReflect_next, mirrorReflect_prev,
      mirrorReflect_extra, mirrorReflect_extra_next]
    change (mirrorBasis (sideMirror u) + mirrorBasis (extraMirror u) +
      mirrorBasis (sideMirror (u+1))) +
      (mirrorBasis (sideMirror (u+1)) + mirrorBasis (extraMirror u) +
      mirrorBasis (sideMirror u)) =
      (2 : ℕ) • (mirrorBasis (sideMirror u) + mirrorBasis (extraMirror u) +
      mirrorBasis (sideMirror (u+1)))
    simp only [two_smul]
    abel
  · simpa only [pow_two, mirrorGenerator, SemidirectProduct.mul_right]
      using mirrorPerm_delta_sq u

@[simp] lemma mirrorLinear_mul (s t : TriangleGroup) :
    mirrorLinear (s*t) = mirrorLinear s * mirrorLinear t := by
  simp [mirrorLinear]

lemma mirrorVector_inv (t : TriangleGroup) (d : Mirror) :
    mirrorVector t⁻¹ d = -mirrorVector t (mirrorLinear t d) := by
  have h := mirrorVector_mul t t⁻¹ (mirrorLinear t d)
  simp only [mul_inv_cancel, mirrorVector_one, Equiv.symm_apply_apply] at h
  linarith

lemma mirrorVector_bounded (t : TriangleGroup) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d, |mirrorVector t d| ≤ C := by
  let H : Subgroup TriangleGroup :=
    { carrier := {t | ∃ C : ℝ, 0 ≤ C ∧ ∀ d, |mirrorVector t d| ≤ C}
      one_mem' := ⟨0,le_rfl,by intro d; simp⟩
      mul_mem' := by
        rintro a b ⟨A,hA,ha⟩ ⟨B,hB,hb⟩
        refine ⟨A+B,add_nonneg hA hB,fun d => ?_⟩
        rw [mirrorVector_mul]
        exact (abs_add_le _ _).trans (add_le_add (ha _) (hb _))
      inv_mem' := by
        rintro a ⟨A,hA,ha⟩
        exact ⟨A,hA,fun d => by rw [mirrorVector_inv,abs_neg]; exact ha _⟩ }
  have hh : ∀ i : Fin 3, (PresentedGroup.of i : TriangleGroup) ∈ H := by
    intro i
    exact ⟨1,by norm_num, mirrorVector_generator_abs i⟩
  exact PresentedGroup.generated_by triangleRelators H hh t

end ArtinCAT0

namespace ArtinCAT0
section OrbitControl
variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

lemma orbit_uniformly_dense (hG : GeometricAction G X) (y : X) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p : X, ∃ s : G, dist p (s • y) ≤ R := by
  obtain ⟨K,hK,hcover⟩ := hG.2.2.2
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall y
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro p
  obtain ⟨s,k,hk,rfl⟩ := hcover p
  refine ⟨s, ?_⟩
  rw [(hG.2.1 s).dist_eq]
  exact (hR hk).trans (le_max_left _ _)

/-- A local bound on an orbit becomes a coarse linear global bound. The
constant two only avoids a special case for zero length geodesics. -/
lemma orbit_chain_control (hG : GeometricAction G X) (y : X)
    {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hdense : ∀ p : X, ∃ s : G, dist p (s • y) ≤ R)
    (f : G → ℝ)
    (hlocal : ∀ s t : G, dist (s • y) (t • y) ≤ 2*R+1 → |f t-f s| ≤ C)
    (s t : G) : |f t-f s| ≤ 2*C*(1+dist (s • y) (t • y)) := by
  classical
  let L : ℝ := dist (s • y) (t • y)
  have hL : 0 ≤ L := dist_nonneg
  let N : ℕ := ⌈L⌉₊ + 1
  have hN : 0 < N := by omega
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hLN : L ≤ (N : ℝ) := (Nat.le_ceil L).trans (by simp [N])
  have hNL : (N : ℝ) ≤ L+2 := by
    have h := Nat.ceil_lt_add_one hL
    dsimp [N]
    push_cast
    linarith
  obtain ⟨γ,hγ⟩ := hG.1.1 (s • y) (t • y)
  choose a ha using hdense
  let q : ℕ → G := fun i => if i = 0 then s else if i = N then t else a (γ (i/N))
  have hq0 : q 0 = s := by simp [q]
  have hqN : q N = t := by simp [q, Nat.ne_of_gt hN]
  have hq (i : ℕ) : dist (γ (i/N)) (q i • y) ≤ R := by
    by_cases hi : i = 0
    · subst i; simpa [q,hγ.1] using hR
    by_cases hiN : i = N
    · subst i
      simpa [q, Nat.ne_of_gt hN, ne_of_gt hNr, hγ.2.1] using hR
    · simpa [q,hi,hiN] using ha (γ (i/N))
  have hstep (i : ℕ) (hi : i < N) : dist (q i • y) (q (i+1) • y) ≤ 2*R+1 := by
    have hi0 : 0 ≤ (i : ℝ)/(N : ℝ) := div_nonneg (by positivity) hNr.le
    have hi1 : (i : ℝ)/(N : ℝ) ≤ 1 := (div_le_one hNr).mpr (by exact_mod_cast hi.le)
    have hj0 : 0 ≤ ((i+1 : ℕ) : ℝ)/(N : ℝ) := div_nonneg (by positivity) hNr.le
    have hj1 : ((i+1 : ℕ) : ℝ)/(N : ℝ) ≤ 1 := (div_le_one hNr).mpr (by exact_mod_cast hi)
    have hdist : dist (γ (i/N)) (γ ((i+1 : ℕ)/N)) ≤ 1 := by
      rw [hγ.2.2 _ ⟨hi0,hi1⟩ _ ⟨hj0,hj1⟩]
      change |(i : ℝ)/(N : ℝ) - ((i+1 : ℕ) : ℝ)/(N : ℝ)| * L ≤ 1
      rw [show (i : ℝ)/(N : ℝ) - ((i+1 : ℕ) : ℝ)/(N : ℝ) = -(1/(N : ℝ)) by push_cast; ring,
        abs_neg, abs_of_nonneg (by positivity)]
      simpa [div_eq_mul_inv, mul_comm] using (div_le_one hNr).mpr hLN
    have htri := dist_triangle4 (q i • y) (γ (i/N))
      (γ ((i+1 : ℕ)/N)) (q (i+1) • y)
    have hqi := hq i
    rw [dist_comm] at hqi
    linarith [hq (i+1)]
  have hsum : ∀ i ≤ N, |f (q i)-f (q 0)| ≤ (i : ℝ)*C := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have ih' := ih (by omega)
      have hs := hlocal (q i) (q (i+1)) (hstep i (by omega))
      have ht := abs_sub_le (f (q (i+1))) (f (q i)) (f (q 0))
      push_cast
      linarith
  have hlast := hsum N le_rfl
  rw [hqN,hq0] at hlast
  calc
    _ ≤ (N : ℝ)*C := hlast
    _ ≤ (L+2)*C := mul_le_mul_of_nonneg_right hNL hC
    _ ≤ 2*C*(1+L) := by nlinarith

end OrbitControl
end ArtinCAT0

namespace ArtinCAT0
namespace RayIndex

noncomputable section

abbrev Point := ℝ × ℝ

def det (p q : Point) : ℝ := p.1 * q.2 - q.1 * p.2

def upward (p q : Point) : ℤ := if p.2 ≤ 0 ∧ 0 < q.2 ∧ 0 < det p q then 1 else 0

def edge (p q : Point) : ℤ := upward p q - upward q p

def above (p : Point) : ℤ := if 0 < p.2 then 1 else 0

@[simp] lemma edge_self (p : Point) : edge p p = 0 := sub_self _
lemma edge_reverse (p q : Point) : edge q p = -edge p q := by unfold edge; ring

lemma det_pos_of_cross_right {p q : Point} (hp : 0 < p.1) (hq : 0 < q.1)
    (hy : p.2 ≤ 0) (hy' : 0 < q.2) : 0 < det p q := by
  have h₁ := mul_pos hp hy'
  have h₂ := mul_nonpos_of_nonneg_of_nonpos hq.le hy
  dsimp [det]
  linarith

lemma det_neg_of_cross_left {p q : Point} (hp : p.1 < 0) (hq : q.1 < 0)
    (hy : p.2 ≤ 0) (hy' : 0 < q.2) : det p q < 0 := by
  have h₁ := mul_neg_of_neg_of_pos hp hy'
  have h₂ := mul_nonneg_of_nonpos_of_nonpos hq.le hy
  dsimp [det]
  linarith

lemma edge_right {p q : Point} (hp : 0 < p.1) (hq : 0 < q.1) :
    edge p q = above q - above p := by
  by_cases hy : p.2 ≤ 0 <;> by_cases hy' : q.2 ≤ 0
  · simp [edge, upward, above, not_lt.mpr hy, not_lt.mpr hy']
  · have hq' := lt_of_not_ge hy'
    have hdet := det_pos_of_cross_right hp hq hy hq'
    simp [edge, upward, above, hy, hy', not_lt.mpr hy, hq', hdet]
  · have hp' := lt_of_not_ge hy
    have hdet := det_pos_of_cross_right hq hp hy' hp'
    simp [edge, upward, above, hy, hy', not_lt.mpr hy', hp', hdet]
  · simp [edge, upward, above, hy, hy', lt_of_not_ge hy, lt_of_not_ge hy']

lemma edge_left {p q : Point} (hp : p.1 < 0) (hq : q.1 < 0) : edge p q = 0 := by
  have h₁ : ¬ (p.2 ≤ 0 ∧ 0 < q.2 ∧ 0 < det p q) := by
    rintro ⟨hy,hy',hd⟩
    exact (det_neg_of_cross_left hp hq hy hy').not_gt hd
  have h₂ : ¬ (q.2 ≤ 0 ∧ 0 < p.2 ∧ 0 < det q p) := by
    rintro ⟨hy,hy',hd⟩
    exact (det_neg_of_cross_left hq hp hy hy').not_gt hd
  simp [edge, upward, h₁, h₂]

lemma edge_high {p q : Point} (hp : 0 < p.2) (hq : 0 < q.2) : edge p q = 0 := by
  simp [edge, upward, hp.not_ge, hq.not_ge]

lemma edge_low {p q : Point} (hp : p.2 ≤ 0) (hq : q.2 ≤ 0) : edge p q = 0 := by
  simp [edge, upward, hp.not_gt, hq.not_gt]

def face (p : Fin 3 → Point) : ℤ := ∑ i, edge (p i) (p (i+1))

lemma face_eq (p : Fin 3 → Point) :
    face p = edge (p 0) (p 1) + edge (p 1) (p 2) + edge (p 2) (p 0) := by
  rw [face, Fin.sum_univ_three]
  rfl

lemma face_right (p : Fin 3 → Point) (hp : ∀ i, 0 < (p i).1) : face p = 0 := by
  rw [face_eq]
  rw [edge_right (hp 0) (hp 1), edge_right (hp 1) (hp 2), edge_right (hp 2) (hp 0)]
  ring

lemma face_left (p : Fin 3 → Point) (hp : ∀ i, (p i).1 < 0) : face p = 0 := by
  simp [face, edge_left (hp _) (hp _)]

lemma face_high (p : Fin 3 → Point) (hp : ∀ i, 0 < (p i).2) : face p = 0 := by
  simp [face, edge_high (hp _) (hp _)]

lemma face_low (p : Fin 3 → Point) (hp : ∀ i, (p i).2 ≤ 0) : face p = 0 := by
  simp [face, edge_low (hp _) (hp _)]

lemma corner_order_cases : ∀ p : CornerOrder,
    (p 0 = 0 ∧ p 1 = 1 ∧ p 2 = 2) ∨ (p 0 = 1 ∧ p 1 = 2 ∧ p 2 = 0) ∨
    (p 0 = 2 ∧ p 1 = 0 ∧ p 2 = 1) ∨ (p 0 = 0 ∧ p 1 = 2 ∧ p 2 = 1) ∨
    (p 0 = 1 ∧ p 1 = 0 ∧ p 2 = 2) ∨ (p 0 = 2 ∧ p 1 = 1 ∧ p 2 = 0) := by decide

lemma face_permute (p : Fin 3 → Point) (e : CornerOrder) :
    face (p ∘ e) = cornerSign e * face p := by
  rcases corner_order_cases e with h|h|h|h|h|h <;>
    rcases h with ⟨h₀,h₁,h₂⟩ <;>
    simp only [face_eq, Function.comp_apply, cornerSign, h₀,h₁,h₂] <;>
    norm_num [Fin.add_def, Fin.ext_iff] <;> unfold edge <;> ring

lemma face_collapsed (p : Fin 3 → Point) (v : Fin 3 → Fin 3) (hv : ¬ Function.Injective v) :
    face (p ∘ v) = 0 := by
  obtain ⟨i,hi⟩ := TriangleMesh.exists_constant_side v hv
  have hs : face (p ∘ v) =
      edge (p (v i)) (p (v (i+1))) + edge (p (v (i+1))) (p (v (i+2))) +
        edge (p (v (i+2))) (p (v i)) := by
    fin_cases i <;> simp [face_eq, Function.comp_apply, Fin.add_def] <;> ring
  rw [hs, hi]
  unfold edge
  ring

/-- A nonzero local edge-index sum forces the coordinate bounding box to meet
both axes. This avoids a separate topological winding-number API. -/
lemma face_bbox (p : Fin 3 → Point) (hp : face p ≠ 0) :
    (∃ i, (p i).1 ≤ 0) ∧ (∃ i, 0 ≤ (p i).1) ∧
      (∃ i, (p i).2 ≤ 0) ∧ (∃ i, 0 < (p i).2) := by
  constructor
  · by_contra h
    push Not at h
    exact hp (face_right p h)
  constructor
  · by_contra h
    push Not at h
    exact hp (face_left p h)
  constructor
  · by_contra h
    push Not at h
    exact hp (face_high p h)
  · by_contra h
    push Not at h
    exact hp (face_low p h)

lemma face_local {p : Fin 3 → Point} (hp : face p ≠ 0) (x : Point) {ε : ℝ}
    (hx : ∀ i, |(p i).1 - x.1| < ε ∧ |(p i).2 - x.2| < ε) :
    |x.1| < ε ∧ |x.2| < ε := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩,⟨k,hk⟩,⟨l,hl⟩⟩ := face_bbox p hp
  have hix := abs_lt.mp (hx i).1
  have hjx := abs_lt.mp (hx j).1
  have hkx := abs_lt.mp (hx k).2
  have hlx := abs_lt.mp (hx l).2
  constructor <;> apply abs_lt.mpr <;> constructor <;> linarith

section Mesh
variable {F V : Type*} [Fintype F] (M : TriangleMesh F V)

omit [Fintype F] in
lemma edge_mate (p : V → Point) (d : F × Fin 3) :
    edge (p (M.tail (M.mate d))) (p (M.tail (TriangleMesh.rotate (M.mate d)))) =
      -edge (p (M.tail d)) (p (M.tail (TriangleMesh.rotate d))) := by
  rw [M.tail_mate, M.tail_rotate_mate]
  exact edge_reverse _ _

/-- Finite Stokes cancellation on any union of faces; no manifold hypotheses
are needed because the oriented edge matching is explicit. -/
lemma patch_boundary_sum (P : F → Prop) [DecidablePred P] (p : V → Point) :
    (∑ f, if P f then face (fun i => p (M.tail (f,i))) else 0) =
      ∑ d : F × Fin 3, if P d.1 ∧ ¬ P (M.mate d).1 then
        edge (p (M.tail d)) (p (M.tail (TriangleMesh.rotate d))) else 0 := by
  classical
  let w (d : F × Fin 3) := edge (p (M.tail d)) (p (M.tail (TriangleMesh.rotate d)))
  let interior (d : F × Fin 3) := if P d.1 ∧ P (M.mate d).1 then w d else 0
  have ha (d) : interior (M.mate d) = -interior d := by
    dsimp [interior]
    rw [M.mate_mate]
    by_cases hf : P d.1 <;> by_cases hg : P (M.mate d).1 <;> simp only [hf,hg,and_self,ite_true,and_false,and_true,ite_false,neg_zero]
    exact edge_mate M p d
  have hz : ∑ d, interior d = 0 := by
    have he := Equiv.sum_comp M.mate interior
    simp only [ha, Finset.sum_neg_distrib] at he
    omega
  have he : (∑ f, if P f then face (fun i => p (M.tail (f,i))) else 0) =
      ∑ d : F × Fin 3, if P d.1 then w d else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : P f <;> simp [hf,face,w]
  rw [he]
  have hd (d : F × Fin 3) : (if P d.1 then w d else 0) =
      interior d + (if P d.1 ∧ ¬ P (M.mate d).1 then w d else 0) := by
    by_cases hf : P d.1 <;> by_cases hg : P (M.mate d).1 <;> simp [hf,hg,interior]
  simp only [hd, Finset.sum_add_distrib, hz, zero_add]
  rfl

variable (L : M.SimplicialLabeling) (J : TriangleGroup → Point)

def occurrence (f : F) : ℤ := face (fun i => J (L.vertex (M.tail (f,i))))

def target (c : TargetTriangle) : ℤ := face (J ∘ c.vertex)

omit [Fintype F] in
lemma occurrence_full (f : L.FullFace) :
    occurrence M L J f.val = cornerSign (L.fullOrder f) * target J (L.cell f.val) := by
  unfold occurrence target
  conv_lhs => arg 1; intro i; rw [L.vertex_tail]
  exact face_permute (J ∘ (L.cell f.val).vertex) (L.fullOrder f)

omit [Fintype F] in
lemma occurrence_collapsed (f : F) (hf : ¬ L.Full f) : occurrence M L J f = 0 := by
  unfold occurrence
  conv_lhs => arg 1; intro i; rw [L.vertex_tail]
  exact face_collapsed (J ∘ (L.cell f).vertex) (L.corner f) hf

theorem localized_zero (he : M.Exact) (P : F → Prop) [DecidablePred P]
    (hloc : ∀ f g : F, P f → occurrence M L J f ≠ 0 → L.cell f = L.cell g →
      L.Full g → P g) :
    (∑ f, if P f then occurrence M L J f else 0) = 0 := by
  classical
  let S (c : TargetTriangle) := ∃ f, P f ∧ occurrence M L J f ≠ 0 ∧ L.cell f = c
  let w (c : TargetTriangle) := if S c then target J c else 0
  have hfull (f : L.FullFace) :
      (if P f.val then occurrence M L J f.val else 0) =
        cornerSign (L.fullOrder f) * w (L.cell f.val) := by
    by_cases hf : P f.val
    · rw [ite_eq_left hf]
      by_cases hz : occurrence M L J f.val = 0
      · by_cases hs : S (L.cell f.val)
        · simpa only [w, ite_eq_left hs] using occurrence_full M L J f
        · simp [w,hs,hz]
      · have hs : S (L.cell f.val) := ⟨f.val,hf,hz,rfl⟩
        simpa only [w, ite_eq_left hs] using occurrence_full M L J f
    · have hs : ¬ S (L.cell f.val) := by
        rintro ⟨g,hg,hz,hcell⟩
        exact hf (hloc g f.val hg hz hcell f.property)
      simp [hf,w,hs]
  have hzero : (∑ f : {f : F // ¬ L.Full f},
      if P f.val then occurrence M L J f.val else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro f _
    simp [occurrence_collapsed M L J f.val f.property]
  rw [← Fintype.sum_subtype_add_sum_subtype L.Full
    (fun f => if P f then occurrence M L J f else 0), hzero, add_zero]
  simp_rw [hfull]
  exact L.signed_counts_zero he w

end Mesh
end
end RayIndex
end ArtinCAT0

end OAI
