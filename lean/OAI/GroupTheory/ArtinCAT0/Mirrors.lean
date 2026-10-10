import OAI.GroupTheory.ArtinCAT0.Folding

namespace OAI

namespace ArtinCAT0

abbrev Mirror := Fin 3 × ℤ

def sideMirror (u : Fin 3) : Mirror :=
  if u = 0 then (0,0) else if u = 1 then (1,0) else (2,1)

def extraMirror (u : Fin 3) : Mirror :=
  if u = 0 then (2,0) else if u = 1 then (0,1) else (1,1)

/-- Action on x=k, y=k, x+y=k for the three side reflections of the
triangle x≥0, y≥0, x+y≤1 in equilateral coordinates. -/
def mirrorReflect (u : Fin 3) (d : Mirror) : Mirror :=
  if u = 0 then
    if d.1 = 0 then (0,-d.2) else if d.1 = 1 then (2,d.2) else (1,d.2)
  else if u = 1 then
    if d.1 = 0 then (2,d.2) else if d.1 = 1 then (1,-d.2) else (0,d.2)
  else
    if d.1 = 0 then (1,1-d.2) else if d.1 = 1 then (0,1-d.2) else (2,2-d.2)

lemma mirrorReflect_involutive (u : Fin 3) : Function.Involutive (mirrorReflect u) := by
  rintro ⟨k,n⟩
  fin_cases u <;> fin_cases k <;> simp [mirrorReflect]

lemma mirrorReflect_braid (u : Fin 3) (d : Mirror) :
    mirrorReflect u (mirrorReflect (u+1) (mirrorReflect u d)) =
      mirrorReflect (u+1) (mirrorReflect u (mirrorReflect (u+1) d)) := by
  rcases d with ⟨k,n⟩
  fin_cases u <;> fin_cases k <;> simp [mirrorReflect] <;> ring

def mirrorPerm (u : Fin 3) : Equiv.Perm Mirror := (mirrorReflect_involutive u).toPerm

@[simp] lemma mirrorPerm_apply (u : Fin 3) (d : Mirror) : mirrorPerm u d = mirrorReflect u d := rfl
@[simp] lemma mirrorPerm_symm_apply (u : Fin 3) (d : Mirror) :
    (mirrorPerm u).symm d = mirrorReflect u d := rfl

lemma mirrorPerm_braid (u : Fin 3) :
    mirrorPerm u * mirrorPerm (u+1) * mirrorPerm u =
      mirrorPerm (u+1) * mirrorPerm u * mirrorPerm (u+1) := by
  apply Equiv.ext
  intro d
  exact mirrorReflect_braid u d

lemma mirrorReflect_side : ∀ u : Fin 3, mirrorReflect u (sideMirror u) = sideMirror u := by decide
lemma mirrorReflect_next : ∀ u : Fin 3, mirrorReflect u (sideMirror (u+1)) = extraMirror u := by decide
lemma mirrorReflect_prev : ∀ u : Fin 3, mirrorReflect (u+1) (sideMirror u) = extraMirror u := by decide
lemma mirrorReflect_extra : ∀ u : Fin 3, mirrorReflect u (extraMirror u) = sideMirror (u+1) := by decide
lemma mirrorReflect_extra_next : ∀ u : Fin 3, mirrorReflect (u+1) (extraMirror u) = sideMirror u := by decide

noncomputable def mirrorBasis (d : Mirror) : Mirror → ℝ := Pi.single d 1

noncomputable def mirrorAut : Equiv.Perm Mirror →* MulAut (Multiplicative (Mirror → ℝ)) where
  toFun p :=
    { toFun := fun ξ => Multiplicative.ofAdd (fun d => ξ.toAdd (p.symm d))
      invFun := fun ξ => Multiplicative.ofAdd (fun d => ξ.toAdd (p d))
      left_inv ξ := by ext d; simp
      right_inv ξ := by ext d; simp
      map_mul' ξ η := rfl }
  map_one' := by ext ξ d; rfl
  map_mul' p q := by ext ξ d; rfl

@[simp] lemma mirrorAut_apply (p : Equiv.Perm Mirror) (ξ : Mirror → ℝ) (d : Mirror) :
    (mirrorAut p (Multiplicative.ofAdd ξ)).toAdd d = ξ (p.symm d) := rfl

lemma mirrorAut_basis (p : Equiv.Perm Mirror) (d : Mirror) :
    mirrorAut p (Multiplicative.ofAdd (mirrorBasis d)) =
      Multiplicative.ofAdd (mirrorBasis (p d)) := by
  ext e
  simp [mirrorBasis, Pi.single_apply, p.symm_apply_eq]

abbrev MirrorAffine := (Multiplicative (Mirror → ℝ)) ⋊[mirrorAut] (Equiv.Perm Mirror)

noncomputable def mirrorGenerator (u : Fin 3) : MirrorAffine :=
  ⟨Multiplicative.ofAdd (mirrorBasis (sideMirror u)), mirrorPerm u⟩

lemma mirrorGenerator_braid (u : Fin 3) :
    mirrorGenerator u * mirrorGenerator (u+1) * mirrorGenerator u =
      mirrorGenerator (u+1) * mirrorGenerator u * mirrorGenerator (u+1) := by
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, mirrorGenerator,
      map_mul, MulAut.mul_apply, mirrorAut_basis, mirrorPerm_apply,
      mirrorReflect_next, mirrorReflect_prev, mirrorReflect_extra, mirrorReflect_extra_next]
    change (mirrorBasis (sideMirror u) + mirrorBasis (extraMirror u) +
      mirrorBasis (sideMirror (u+1)) : Mirror → ℝ) =
      mirrorBasis (sideMirror (u+1)) + mirrorBasis (extraMirror u) + mirrorBasis (sideMirror u)
    abel
  · exact mirrorPerm_braid u

noncomputable def mirrorRepresentation : TriangleGroup →* MirrorAffine :=
  triangleLift mirrorGenerator mirrorGenerator_braid

@[simp] lemma mirrorRepresentation_gen (u : Fin 3) :
    mirrorRepresentation (triangleGen u) = mirrorGenerator u := triangleLift_gen _ _ _

noncomputable def mirrorVector (t : TriangleGroup) : Mirror → ℝ :=
  (mirrorRepresentation t).left.toAdd

noncomputable def mirrorLinear (t : TriangleGroup) : Equiv.Perm Mirror :=
  (mirrorRepresentation t).right

lemma mirrorVector_mul (s t : TriangleGroup) (d : Mirror) :
    mirrorVector (s*t) d = mirrorVector s d + mirrorVector t ((mirrorLinear s).symm d) := by
  simp [mirrorVector, mirrorLinear, map_mul, mirrorAut]

@[simp] lemma mirrorVector_one (d : Mirror) : mirrorVector 1 d = 0 := by simp [mirrorVector]

lemma mirrorVector_generator_abs (u : Fin 3) (d : Mirror) :
    |mirrorVector (triangleGen u) d| ≤ 1 := by
  simp [mirrorVector, mirrorGenerator, mirrorBasis, Pi.single_apply]
  split_ifs <;> norm_num

end ArtinCAT0

end OAI
