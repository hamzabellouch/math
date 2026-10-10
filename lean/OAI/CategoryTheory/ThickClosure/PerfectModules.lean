import OAI.CategoryTheory.ThickClosure.LaurentCriterion

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.LaurentDg
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [Ring R] {D : ℕ}

abbrev total (M : Module R D) := DirectSum ℤ (fun n => M.X n)
abbrev inc (M : Module R D) (n : ℤ) : M.X n →ₗ[R] total M :=
  DirectSum.lof R ℤ (fun n => M.X n) n

lemma power_cast (i q : ℤ) : (i : ZMod D) = ((i + (D : ℤ)*q : ℤ) : ZMod D) := by simp

def move (M : Module R D) (i j : ℤ) (h : (i : ZMod D) = (j : ZMod D)) :
    M.X i →ₗ[R] total M := (inc M j).comp (M.power i j h).hom.hom

lemma move_congr (M : Module R D) (i j k : ℤ)
    (h : (i : ZMod D) = (j : ZMod D)) (h' : (i : ZMod D) = (k : ZMod D))
    (e : j = k) : move M i j h = move M i k h' := by
  subst k
  rfl

def shiftPower (M : Module R D) (q : ℤ) : total M →ₗ[R] total M :=
  DirectSum.toModule R ℤ (total M) (fun i => move M i (i+(D:ℤ)*q) (power_cast i q))

@[simp] lemma shiftPower_inc (M : Module R D) (q i : ℤ) (x : M.X i) :
    shiftPower M q (inc M i x) = move M i (i+(D:ℤ)*q) (power_cast i q) x :=
  DirectSum.toModule_lof _ _ _

lemma shiftPower_move (M : Module R D) (q i j : ℤ)
    (h : (i : ZMod D) = (j : ZMod D)) (x : M.X i) :
    shiftPower M q (move M i j h x) =
      move M i (j+(D:ℤ)*q) (h.trans (power_cast j q)) x := by
  simp only [move, LinearMap.comp_apply, shiftPower_inc]
  change inc M _ (((M.power i j h).hom ≫
    (M.power j (j+(D:ℤ)*q) (power_cast j q)).hom) x) = _
  rw [M.power_hom_trans]

@[simp] lemma move_self (M : Module R D) (i : ℤ) (x : M.X i) :
    move M i i rfl x = inc M i x := by simp [move]

lemma shiftPower_zero (M : Module R D) : shiftPower M 0 = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro i
  ext x
  simp

lemma shiftPower_add (M : Module R D) (q r : ℤ) :
    shiftPower M (q+r) = (shiftPower M q).comp (shiftPower M r) := by
  apply DirectSum.linearMap_ext
  intro i
  ext x
  simp only [LinearMap.comp_apply, shiftPower_inc, shiftPower_move]
  have h : i+(D:ℤ)*(q+r) = i+(D:ℤ)*r+(D:ℤ)*q := by ring
  simp only [h]

def powerRepresentation (M : Module R D) : Multiplicative ℤ →* AddMonoid.End (total M) where
  toFun q := (shiftPower M q.toAdd).toAddMonoidHom
  map_one' := by change (shiftPower M 0).toAddMonoidHom = AddMonoidHom.id _; rw [shiftPower_zero]; rfl
  map_mul' q r := by
    change (shiftPower M (q.toAdd+r.toAdd)).toAddMonoidHom = _
    rw [shiftPower_add]
    rfl

def laurentRepresentation (M : Module R D) : LaurentPolynomial R →+* AddMonoid.End (total M) :=
  AddMonoidAlgebra.liftNCRingHom (Module.toAddMonoidEnd R (total M))
    (powerRepresentation M) (by
      intro r q
      apply AddMonoidHom.ext
      intro x
      exact ((shiftPower M q.toAdd).map_smul r x).symm)

lemma laurentRepresentation_single (M : Module R D) (q i : ℤ) (r : R) (x : M.X i) :
    laurentRepresentation M (AddMonoidAlgebra.single q r) (inc M i x) =
      inc M (i+(D:ℤ)*q) (r • (M.power i _ (power_cast i q)).hom x) := by
  unfold laurentRepresentation
  erw [AddMonoidAlgebra.liftNCRingHom_single]
  change r • shiftPower M q (inc M i x) = _
  simp [shiftPower_inc, move]

def totalDifferential (M : Module R D) : total M →ₗ[R] total M :=
  DirectSum.toModule R ℤ (total M) (fun i =>
    (inc M (i-1)).comp ((ChainComplex.of M.X M.d M.dd).d i (i-1)).hom)

lemma totalDifferential_inc (M : Module R D) (i : ℤ) (x : M.X i) :
    totalDifferential M (inc M i x) =
      inc M (i-1) ((ChainComplex.of M.X M.d M.dd).d i (i-1) x) :=
  DirectSum.toModule_lof _ _ _

lemma totalDifferential_inc_succ (M : Module R D) (i : ℤ) (x : M.X (i+1)) :
    totalDifferential M (inc M (i+1) x) = inc M i (M.d i x) := by
  rw [totalDifferential_inc]
  erw [show i+1-1=i by omega]
  have hd : (ChainComplex.of M.X M.d M.dd).d (i+1) i = M.d i :=
    ChainComplex.of_d M.X M.d i
  rw [hd]

lemma totalDifferential_sq (M : Module R D) :
    (totalDifferential M).comp (totalDifferential M) = 0 := by
  apply DirectSum.linearMap_ext
  intro i
  ext x : 1
  simp only [LinearMap.comp_apply, totalDifferential_inc]
  change inc M (i-1-1) (((ChainComplex.of M.X M.d M.dd).d i (i-1) ≫
    (ChainComplex.of M.X M.d M.dd).d (i-1) (i-1-1)) x) = 0
  rw [HomologicalComplex.d_comp_d]
  exact map_zero _

lemma totalDifferential_shiftPower (M : Module R D) (q : ℤ) :
    (totalDifferential M).comp (shiftPower M q) =
      (shiftPower M q).comp (totalDifferential M) := by
  apply DirectSum.linearMap_ext
  intro n
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, n = i+1 := ⟨n-1, by omega⟩
  ext x : 1
  simp only [LinearMap.comp_apply, shiftPower_inc, totalDifferential_inc_succ]
  have h : i+1+(D:ℤ)*q = i+(D:ℤ)*q+1 := by omega
  rw [move_congr M (i+1) _ (i+(D:ℤ)*q+1) _ (by simp) h]
  simp only [move, LinearMap.comp_apply, totalDifferential_inc_succ]
  change inc M _ (((M.power (i+1) (i+(D:ℤ)*q+1) _).hom ≫
    M.d (i+(D:ℤ)*q)) x) = _
  rw [M.power_d i (i+(D:ℤ)*q) (power_cast i q)]
  rfl

lemma laurentRepresentation_commute (M : Module R D) (a : LaurentPolynomial R) :
    Commute (laurentRepresentation M a) (totalDifferential M).toAddMonoidHom := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact Commute.zero_left _
  | add a b ha hb => simpa only [map_add] using ha.add_left hb
  | single q r =>
    unfold laurentRepresentation
    erw [AddMonoidAlgebra.liftNCRingHom_single]
    apply Commute.mul_left
    · apply AddMonoidHom.ext
      intro x
      exact ((totalDifferential M).map_smul r x).symm
    · exact congrArg LinearMap.toAddMonoidHom (totalDifferential_shiftPower M q).symm

theorem actual_laurent_action (M : Module R D) (_hD : 0 < D) (_heven : Even D) :
    ∃ (ρ : LaurentPolynomial R →+* AddMonoid.End (total M))
      (δ : AddMonoid.End (total M)),
    (∀ (q i : ℤ) (r : R) (x : M.X i),
      ρ (AddMonoidAlgebra.single q r) (inc M i x) =
        inc M (i + (D : ℤ)*q) (r • (M.power i _ (power_cast i q)).hom x)) ∧
    (∀ (i : ℤ) (x : M.X (i+1)), δ (inc M (i+1) x) = inc M i (M.d i x)) ∧
    δ * δ = 0 ∧ ∀ a, Commute (ρ a) δ := by
  refine ⟨laurentRepresentation M, (totalDifferential M).toAddMonoidHom,
    laurentRepresentation_single M, totalDifferential_inc_succ M, ?_,
    laurentRepresentation_commute M⟩
  exact congrArg LinearMap.toAddMonoidHom (totalDifferential_sq M)

end HahnWilson.LaurentDg

end

end OAI
