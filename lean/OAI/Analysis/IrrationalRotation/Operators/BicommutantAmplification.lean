import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.BicommutantDensity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (ι : Type*) [Fintype ι]

abbrev Amplification := PiLp 2 (fun _ : ι => H)

def amplify (T : H →L[ℂ] H) : Amplification (H := H) ι →L[ℂ] Amplification (H := H) ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem amplify_apply (T : H →L[ℂ] H) (x : Amplification (H := H) ι) (i : ι) :
    amplify ι T x i = T (x i) := rfl

def amplifyHom : (H →L[ℂ] H) →⋆ₐ[ℂ]
    (Amplification (H := H) ι →L[ℂ] Amplification (H := H) ι) where
  toFun := amplify ι
  map_zero' := by ext x i; simp
  map_one' := by ext x i; simp
  map_add' T S := by ext x i; simp
  map_mul' T S := by ext x i; simp
  commutes' c := by ext x i; simp [Algebra.algebraMap_eq_smul_one]
  map_star' T := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro x y
    simp only [PiLp.inner_apply, amplify_apply, ContinuousLinearMap.adjoint_inner_left]

@[simp] theorem amplifyHom_apply (T : H →L[ℂ] H) : amplifyHom (H := H) ι T = amplify ι T := rfl

variable [DecidableEq ι]

def insert (i : ι) : H →L[ℂ] Amplification (H := H) ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem insert_apply (i : ι) (x : H) (j : ι) :
    insert ι i x j = if j = i then x else 0 := by
  simp [insert, ContinuousLinearMap.single_apply]

def entry (B : Amplification (H := H) ι →L[ℂ] Amplification (H := H) ι)
    (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (B.comp (insert ι j))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem entry_apply (B : Amplification (H := H) ι →L[ℂ] Amplification (H := H) ι)
    (i j : ι) (x : H) : entry ι B i j x = B (insert ι j x) i := rfl

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem amplify_insert (T : H →L[ℂ] H) (j : ι) (x : H) :
    amplify ι T (insert ι j x) = insert ι j (T x) := by
  ext i
  by_cases h : i = j <;> simp [h]

omit [CompleteSpace H] in

theorem sum_insert (x : Amplification (H := H) ι) :
    ∑ j, insert ι j (x j) = x := by
  ext i
  simp

omit [CompleteSpace H] in
theorem apply_eq_sum_entry
    (B : Amplification (H := H) ι →L[ℂ] Amplification (H := H) ι)
    (x : Amplification (H := H) ι) (i : ι) :
    B x i = ∑ j, entry ι B i j (x j) := by
  conv_lhs => rw [← sum_insert ι x]
  simp

omit [CompleteSpace H] [Fintype ι] in
theorem entry_commutes {T : H →L[ℂ] H}
    {B : Amplification (H := H) ι →L[ℂ] Amplification (H := H) ι}
    (h : amplify ι T * B = B * amplify ι T) (i j : ι) :
    T * entry ι B i j = entry ι B i j * T := by
  ext x
  have hx := congrArg (fun C => C (insert ι j x) i) h
  simpa only [mul_apply_eq_comp, amplify_apply, amplify_insert, entry_apply] using hx

omit [CompleteSpace H] in
theorem amplify_commutes_of_entries {T : H →L[ℂ] H}
    {B : Amplification (H := H) ι →L[ℂ] Amplification (H := H) ι}
    (h : ∀ i j, T * entry ι B i j = entry ι B i j * T) :
    amplify ι T * B = B * amplify ι T := by
  ext x i
  change T (B x i) = B (amplify ι T x) i
  rw [apply_eq_sum_entry ι B x i, apply_eq_sum_entry ι B (amplify ι T x) i,
    map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun C : H →L[ℂ] H => C (x j)) (h i j)

theorem amplify_mem_bicommutant (A : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) :
    amplify ι T ∈ Set.centralizer (Set.centralizer
      (StarSubalgebra.map (amplifyHom ι) A : Set
        (Amplification (H := H) ι →L[ℂ] Amplification (H := H) ι))) := by
  intro B hB
  symm
  apply amplify_commutes_of_entries
  intro i j
  have hij : entry ι B i j ∈ Set.centralizer (A : Set (H →L[ℂ] H)) := by
    intro a ha
    apply entry_commutes
    apply hB
    exact StarSubalgebra.mem_map.mpr ⟨a, ha, rfl⟩
  exact (hT _ hij).symm

end Invariant233.BicommutantDensity

end

end OAI
