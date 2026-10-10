import OAI.Analysis.CharacterCriterion.MaxTensor

namespace OAI

noncomputable section
open scoped TensorProduct


open scoped InnerProductSpace
namespace KirchbergRordam.GenericRW
namespace FactorIndependence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  ∀ T : H →L[ℂ] H, T ∈ M → T ∈ M.commutant → ∃ z : ℂ, T = z • 1

abbrev SumHilbert (ι : Type*) (H : Type*) := PiLp 2 (fun _ : ι => H)

def diagonal (T : H →L[ℂ] H) : SumHilbert ι H →L[ℂ] SumHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i))

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma diagonal_apply (T : H →L[ℂ] H) (x : SumHilbert ι H) (i : ι) :
    diagonal T x i = T (x i) := rfl

lemma star_diagonal (T : H →L[ℂ] H) : star (diagonal (ι := ι) T) = diagonal (star T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, diagonal_apply]
  congr 1
  funext i
  exact (ContinuousLinearMap.adjoint_inner_left T (y i) (x i)).symm

lemma projection_commutes (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H)
    (hT : ∀ x ∈ K, T x ∈ K) (hTs : ∀ x ∈ K, star T x ∈ K) :
    Commute K.starProjection T := by
  have hp (S : H →L[ℂ] H) (hS : ∀ x ∈ K, S x ∈ K) :
      K.starProjection * S * K.starProjection = S * K.starProjection := by
    ext x
    exact K.starProjection_eq_self_iff.mpr (hS _ (by simp))
  have h₁ := hp T hT
  have h₂ := congrArg star (hp (star T) hTs)
  simp only [star_mul, star_star, (isSelfAdjoint_starProjection K).star_eq] at h₂
  exact h₂.symm.trans (by rwa [mul_assoc] at h₁)

variable [DecidableEq ι]

def injection (i : ι) : H →L[ℂ] SumHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma injection_apply (i j : ι) (x : H) :
    injection i x j = if j = i then x else 0 := by
  simp [injection]

omit [CompleteSpace H] in
lemma sum_injection (x : SumHilbert ι H) : ∑ i, injection i (x i) = x := by
  apply PiLp.ext
  intro j
  simp

omit [CompleteSpace H] [Fintype ι] in
lemma diagonal_injection (T : H →L[ℂ] H) (i : ι) (x : H) :
    diagonal T (injection (ι := ι) i x) = injection i (T x) := by
  ext j
  by_cases hj : j = i <;> simp [hj]

def entry (P : SumHilbert ι H →L[ℂ] SumHilbert ι H) (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (P.comp (injection j))

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma entry_apply (P : SumHilbert ι H →L[ℂ] SumHilbert ι H)
    (i j : ι) (x : H) : entry P i j x = P (injection j x) i := rfl

omit [CompleteSpace H] [Fintype ι] in
lemma entry_commutes (P : SumHilbert ι H →L[ℂ] SumHilbert ι H) (T : H →L[ℂ] H)
    (hc : Commute P (diagonal T)) (i j : ι) : Commute (entry P i j) T := by
  ext x
  have hh := congrArg (fun S : SumHilbert ι H →L[ℂ] SumHilbert ι H => S (injection j x) i) hc.eq
  simpa [mul_apply_eq_comp, diagonal_injection] using hh

omit [CompleteSpace H] in
lemma apply_eq_sum_entries (P : SumHilbert ι H →L[ℂ] SumHilbert ι H)
    (x : SumHilbert ι H) (i : ι) : P x i = ∑ j, entry P i j (x j) := by
  conv_lhs => rw [← sum_injection x]
  simp

omit [CompleteSpace H] in

lemma invariant_closure (K : Submodule ℂ H) (T : H →L[ℂ] H)
    (h : ∀ x ∈ K, T x ∈ K) : ∀ x ∈ K.topologicalClosure, T x ∈ K.topologicalClosure :=
  Set.MapsTo.closure h T.continuous

def column (b : ι → H →L[ℂ] H) (ξ : H) : SumHilbert ι H :=
  WithLp.toLp 2 (fun i => b i ξ)

omit [CompleteSpace H] [Fintype ι] [DecidableEq ι] in
@[simp] lemma column_apply (b : ι → H →L[ℂ] H) (ξ : H) (i : ι) : column b ξ i = b i ξ := rfl

def columnSpace (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H) :
    Submodule ℂ (SumHilbert ι H) :=
  (Submodule.span ℂ {v | ∃ c : H →L[ℂ] H, c ∈ M.commutant ∧
    ∃ ξ : H, v = diagonal c (column b ξ)}).topologicalClosure

omit [DecidableEq ι] in
lemma columnSpace_closed (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H) :
    IsClosed (columnSpace M b : Set (SumHilbert ι H)) :=
  Submodule.isClosed_topologicalClosure _

omit [DecidableEq ι] in
lemma generator_mem (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H)
    (c : H →L[ℂ] H) (hc : c ∈ M.commutant) (ξ : H) :
    diagonal c (column b ξ) ∈ columnSpace M b :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨c, hc, ξ, rfl⟩)

omit [DecidableEq ι] in
lemma column_mem (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H) (ξ : H) :
    column b ξ ∈ columnSpace M b := by
  simpa only [show diagonal (ι := ι) (1 : H →L[ℂ] H) = 1 by ext; rfl,
    one_apply_eq_self] using generator_mem M b 1 (one_mem _) ξ

omit [CompleteSpace H] in
lemma invariant_span_closure (S : Set H) (T : H →L[ℂ] H)
    (h : ∀ x ∈ S, T x ∈ Submodule.span ℂ S) :
    ∀ x ∈ (Submodule.span ℂ S).topologicalClosure,
      T x ∈ (Submodule.span ℂ S).topologicalClosure := by
  apply invariant_closure
  have hh : Submodule.span ℂ S ≤ (Submodule.span ℂ S).comap T.toLinearMap :=
    Submodule.span_le.mpr h
  exact hh

omit [DecidableEq ι] in
lemma commutant_invariant (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H)
    (T : H →L[ℂ] H) (hT : T ∈ M.commutant) :
    ∀ x ∈ columnSpace M b, diagonal T x ∈ columnSpace M b := by
  apply invariant_span_closure
  rintro x ⟨c, hc, ξ, rfl⟩
  apply Submodule.subset_span
  refine ⟨T * c, mul_mem hT hc, ξ, ?_⟩
  rfl

omit [DecidableEq ι] in
lemma algebra_invariant (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H)
    (hb : ∀ i, b i ∈ M.commutant) (T : H →L[ℂ] H) (hT : T ∈ M) :
    ∀ x ∈ columnSpace M b, diagonal T x ∈ columnSpace M b := by
  apply invariant_span_closure
  rintro x ⟨c, hc, ξ, rfl⟩
  apply Submodule.subset_span
  refine ⟨c, hc, T ξ, ?_⟩
  ext i
  have h₁ := congrArg (fun S : H →L[ℂ] H => S (b i ξ))
    (VonNeumannAlgebra.mem_commutant_iff.mp hc T hT)
  have h₂ := congrArg (fun S : H →L[ℂ] H => S ξ)
    (VonNeumannAlgebra.mem_commutant_iff.mp (hb i) T hT)
  change T (c (b i ξ)) = c (b i (T ξ))
  exact h₁.trans (congrArg c h₂)


lemma columnSpace_eq_top (M : VonNeumannAlgebra H) (hM : IsFactor M)
    (b : ι → H →L[ℂ] H) (hb : ∀ i, b i ∈ M.commutant)
    (hli : LinearIndependent ℂ b) : columnSpace M b = ⊤ := by
  let K := columnSpace M b
  let : CompleteSpace K := (columnSpace_closed M b).completeSpace_coe
  let p : SumHilbert ι H →L[ℂ] SumHilbert ι H := 1 - K.starProjection
  have hp (T : H →L[ℂ] H)
      (hT : ∀ x ∈ K, diagonal T x ∈ K)
      (hTs : ∀ x ∈ K, diagonal (star T) x ∈ K) : Commute p (diagonal T) := by
    have hc := projection_commutes K (diagonal T) hT (by rwa [star_diagonal])
    change (1 - K.starProjection) * diagonal T = diagonal T * (1 - K.starProjection)
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc.eq]
  have he (i j : ι) : ∃ z : ℂ, entry p i j = z • 1 := by
    apply hM
    · rw [← M.commutant_commutant]
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro T hT
      exact (entry_commutes p T (hp T (commutant_invariant M b T hT)
        (commutant_invariant M b (star T) (star_mem hT))) i j).eq.symm
    · apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro T hT
      exact (entry_commutes p T (hp T (algebra_invariant M b hb T hT)
        (algebra_invariant M b hb (star T) (star_mem hT))) i j).eq.symm
  choose z hz using he
  have hpcol (ξ : H) : p (column b ξ) = 0 := by
    change column b ξ - K.starProjection (column b ξ) = 0
    rw [K.starProjection_eq_self_iff.mpr (column_mem M b ξ), sub_self]
  have hz0 (i : ι) : ∀ j, z i j = 0 := by
    apply (Fintype.linearIndependent_iff.mp hli) (z i)
    ext ξ
    have hh := congrArg (fun v : SumHilbert ι H => v i) (hpcol ξ)
    rw [apply_eq_sum_entries] at hh
    simpa [hz] using hh
  have hp0 : p = 0 := by
    ext x i
    rw [apply_eq_sum_entries]
    simp [hz, hz0]
  apply top_unique
  intro x _
  apply K.starProjection_eq_self_iff.mp
  have hh := congrArg (fun P : SumHilbert ι H →L[ℂ] SumHilbert ι H => P x) hp0
  change x - K.starProjection x = 0 at hh
  exact (sub_eq_zero.mp hh).symm

def row (a : ι → H →L[ℂ] H) : SumHilbert ι H →L[ℂ] H :=
  ∑ i, (a i).comp (PiLp.proj 2 (fun _ : ι => H) i)

omit [CompleteSpace H] [DecidableEq ι] in
@[simp] lemma row_apply (a : ι → H →L[ℂ] H) (x : SumHilbert ι H) :
    row a x = ∑ i, a i (x i) := by simp [row]

omit [CompleteSpace H] in
lemma row_injection (a : ι → H →L[ℂ] H) (i : ι) (x : H) :
    row a (injection i x) = a i x := by
  simp only [row_apply, injection_apply, apply_ite, map_zero]
  simp

omit [DecidableEq ι] in
theorem relation_coefficients_zero (M : VonNeumannAlgebra H) (hM : IsFactor M)
    (a b : ι → H →L[ℂ] H) (ha : ∀ i, a i ∈ M) (hb : ∀ i, b i ∈ M.commutant)
    (hli : LinearIndependent ℂ b) (hrel : ∑ i, a i * b i = 0) : ∀ i, a i = 0 := by
  classical
  have hK : columnSpace M b ≤ (row a).ker := by
    apply Submodule.topologicalClosure_minimal _ _ (row a).isClosed_ker
    apply Submodule.span_le.mpr
    rintro x ⟨c, hc, ξ, rfl⟩
    change row a (diagonal c (column b ξ)) = 0
    rw [row_apply]
    simp only [diagonal_apply, column_apply]
    calc
      ∑ i, a i (c (b i ξ)) = ∑ i, c (a i (b i ξ)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun S : H →L[ℂ] H => S (b i ξ))
          (VonNeumannAlgebra.mem_commutant_iff.mp hc (a i) (ha i))
      _ = c ((∑ i, a i * b i) ξ) := by simp
      _ = 0 := by rw [hrel]; simp
  rw [columnSpace_eq_top M hM b hb hli] at hK
  intro i
  ext ξ
  have hh := hK (show injection i ξ ∈ (⊤ : Submodule ℂ (SumHilbert ι H)) from trivial)
  change row a (injection i ξ) = 0 at hh
  rwa [row_injection] at hh

end FactorIndependence
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.GroupedFactors
open scoped Pointwise
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


def commutantOf (S : StarSubalgebra ℂ (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))) =
      (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))
    simp only [StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq, Set.union_self]
    exact Set.centralizer_centralizer_centralizer _

def bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) : VonNeumannAlgebra H :=
  (commutantOf S).commutant

lemma mem_commutantOf_iff (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    T ∈ commutantOf S ↔ ∀ a ∈ S, Commute a T := by
  change T ∈ StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) ↔ _
  rw [← SetLike.mem_coe, StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq,
    Set.union_self]
  rfl

lemma subset_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    ∀ a ∈ S, a ∈ bicommutant S := by
  intro a ha
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  exact ((mem_commutantOf_iff S T).mp hT a ha).eq.symm

lemma closures_commute (S T : StarSubalgebra ℂ (H →L[ℂ] H))
    (hc : ∀ a ∈ S, ∀ b ∈ T, Commute a b) :
    ∀ a ∈ bicommutant S, ∀ b ∈ bicommutant T, Commute a b := by
  intro a ha b hb
  apply VonNeumannAlgebra.mem_commutant_iff.mp hb
  apply (mem_commutantOf_iff T a).mpr
  intro t ht
  exact VonNeumannAlgebra.mem_commutant_iff.mp ha t
    ((mem_commutantOf_iff S t).mpr (fun s hs => hc s hs t ht))


theorem isFactor_of_total (S T : StarSubalgebra ℂ (H →L[ℂ] H))
    (hc : ∀ a ∈ S, ∀ b ∈ T, Commute a b)
    (htotal : ∀ U : H →L[ℂ] H,
      (∀ a ∈ S, Commute U a) → (∀ b ∈ T, Commute U b) → ∃ z : ℂ, U = z • 1) :
    FactorIndependence.IsFactor (bicommutant S) := by
  intro U hU hUc
  apply htotal U
  · intro a ha
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hUc a (subset_bicommutant S a ha)).symm
  · intro b hb
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hU b
      ((mem_commutantOf_iff S b).mpr (fun a ha => hc a ha b hb))).symm

end KirchbergRordam.GenericRW.GroupedFactors

namespace KirchbergRordam.GenericRW.MaxTensor
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

open scoped CStarAlgebra


lemma commute_of_legs (π : Algebra A B →⋆ₐ[ℂ] C) (T : C)
    (hL : ∀ a, Commute T (π (includeLeft a)))
    (hR : ∀ b, Commute T (π (includeRight b))) :
    ∀ x, Commute T (π x) := by
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    change IsClosed {x | T * π x = π x * T}
    exact isClosed_eq (continuous_const.mul (map_continuous π))
      ((map_continuous π).mul continuous_const)
  | ih x =>
    suffices ∀ tensor : A ⊗[ℂ] B, Commute T (π (of (rawEquiv tensor))) from this x
    intro tensor
    induction tensor using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using hx.add_right hy
    | tmul a b =>
      change Commute T (π (of (a ⊗ₜ[ℂ] b)))
      rw [of_tmul, map_mul]
      exact (hL a).mul_right (hR b)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


theorem left_factor (π : Algebra A B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1) :
    FactorIndependence.IsFactor
      (GroupedFactors.bicommutant (π.comp (includeLeft (A := A) (B := B))).range) := by
  apply GroupedFactors.isFactor_of_total _ (π.comp (includeRight (A := A) (B := B))).range
  · rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩
    exact (legs_commute x y).map π
  · intro T hL hR
    apply hs T
    exact commute_of_legs π T (fun a => hL _ ⟨a, rfl⟩) (fun b => hR _ ⟨b, rfl⟩)

theorem right_factor (π : Algebra A B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1) :
    FactorIndependence.IsFactor
      (GroupedFactors.bicommutant (π.comp (includeRight (A := A) (B := B))).range) := by
  apply GroupedFactors.isFactor_of_total _ (π.comp (includeLeft (A := A) (B := B))).range
  · rintro b ⟨y, rfl⟩ a ⟨x, rfl⟩
    exact ((legs_commute x y).map π).symm
  · intro T hR hL
    apply hs T
    exact commute_of_legs π T (fun a => hL _ ⟨a, rfl⟩) (fun b => hR _ ⟨b, rfl⟩)

end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.MaxTensor
section
universe u
variable (D : Type u) [CStarAlgebra D]


def leg : (n : ℕ) → Fin (n + 1) → D →⋆ₐ[ℂ] (powerPack D n)
  | 0 => fun _ => StarAlgHom.id ℂ D
  | n + 1 => Fin.cases includeLeft (fun j => includeRight.comp (leg n j))

@[simp] lemma leg_zero (i : Fin 1) (a : D) : leg D 0 i a = a := rfl
@[simp] lemma leg_succ_zero (n : ℕ) : leg D (n+1) 0 = includeLeft := rfl
@[simp] lemma leg_succ_succ (n : ℕ) (i : Fin (n+1)) :
    leg D (n+1) i.succ = (includeRight (A := D)).comp (leg D n i) := rfl

lemma commute_legs (n : ℕ) (i j : Fin (n+1)) (hij : i ≠ j) (a b : D) :
    Commute (leg D n i a) (leg D n j b) := by
  induction n with
  | zero => exact (hij ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)).elim
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact legs_commute a (leg D n j b)
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (legs_commute b (leg D n i a)).symm
      | succ j => exact (ih i j (fun h => hij (congrArg Fin.succ h))).map includeRight

variable {D} {C : Type*} [CStarAlgebra C]

lemma commute_of_power_legs (n : ℕ) (π : (powerPack D n) →⋆ₐ[ℂ] C) (T : C)
    (h : ∀ i a, Commute T (π (leg D n i a))) : ∀ x, Commute T (π x) := by
  induction n with
  | zero => exact fun x => h 0 x
  | succ n ih =>
    apply commute_of_legs π T
    · exact fun a => h 0 a
    · exact ih (π.comp includeRight) (fun i a => h i.succ a)

end

variable {D C : Type*} [CStarAlgebra D] [CStarAlgebra C]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


lemma power_leg_factor (n : ℕ) (φ : (powerPack D n) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ψ : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ a b, Commute (φ a) (ψ b))
    (hs : ∀ T : H →L[ℂ] H, (∀ a, Commute T (φ a)) →
      (∀ b, Commute T (ψ b)) → ∃ z : ℂ, T = z • 1)
    (i : Fin (n+1)) :
    FactorIndependence.IsFactor (GroupedFactors.bicommutant (φ.comp (leg D n i)).range) := by
  intro U hU hUc
  apply hs U
  · apply commute_of_power_legs n φ U
    intro j a
    by_cases hij : i = j
    · subst j
      exact (VonNeumannAlgebra.mem_commutant_iff.mp hUc _
        (GroupedFactors.subset_bicommutant _ _ ⟨a, rfl⟩)).symm
    · apply (VonNeumannAlgebra.mem_commutant_iff.mp hU _ ?_).symm
      apply (GroupedFactors.mem_commutantOf_iff _ _).mpr
      rintro b ⟨d, rfl⟩
      exact (commute_legs D n i j hij d a).map φ
  · intro b
    apply (VonNeumannAlgebra.mem_commutant_iff.mp hU _ ?_).symm
    apply (GroupedFactors.mem_commutantOf_iff _ _).mpr
    rintro a ⟨d, rfl⟩
    exact hc _ _

lemma power_leg_factors_commute (n : ℕ) (φ : (powerPack D n) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (i j : Fin (n+1)) (hij : i ≠ j) :
    ∀ b ∈ GroupedFactors.bicommutant (φ.comp (leg D n j)).range,
      b ∈ (GroupedFactors.bicommutant (φ.comp (leg D n i)).range).commutant := by
  intro b hb
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  exact (GroupedFactors.closures_commute _ _ (by
    rintro x ⟨c, rfl⟩ y ⟨d, rfl⟩
    exact (commute_legs D n i j hij c d).map φ) a ha b hb).eq

end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.ProductIndependence
variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]


lemma selfAdjoint_complex_independent (v : ι → A) (hv : ∀ i, IsSelfAdjoint (v i))
    (hli : LinearIndependent ℝ v) : LinearIndependent ℂ v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hr : ∑ i, (c i).re • v i = 0 := by
    have h := congrArg (fun x : A => (realPart x : A)) hc
    simpa only [map_sum, realPart_smul, (hv _).imaginaryPart, smul_zero, sub_zero,
      AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_smul, (hv _).coe_realPart, map_zero,
      AddSubgroup.coe_zero] using h
  have hi : ∑ i, (c i).im • v i = 0 := by
    have h := congrArg (fun x : A => (imaginaryPart x : A)) hc
    simpa only [map_sum, imaginaryPart_smul, (hv _).imaginaryPart, smul_zero, zero_add,
      AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_smul, (hv _).coe_realPart, map_zero,
      AddSubgroup.coe_zero] using h
  have hr0 := (Fintype.linearIndependent_iff.mp hli) _ hr
  have hi0 := (Fintype.linearIndependent_iff.mp hli) _ hi
  intro i
  exact Complex.ext (hr0 i) (hi0 i)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma pair_independent (M : VonNeumannAlgebra H) (hM : FactorIndependence.IsFactor M)
    (a : ι → H →L[ℂ] H) (b : κ → H →L[ℂ] H)
    (ha : ∀ i, a i ∈ M) (hb : ∀ j, b j ∈ M.commutant)
    (hia : LinearIndependent ℂ a) (hib : LinearIndependent ℂ b) :
    LinearIndependent ℂ (fun p : ι × κ => a p.1 * b p.2) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hrel : ∑ j, (∑ i, c (i,j) • a i) * b j = 0 := by
    rw [← hc, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.sum_mul, smul_mul_assoc]
  have hcoeff := FactorIndependence.relation_coefficients_zero M hM
    (fun j => ∑ i, c (i,j) • a i) b
    (fun j => M.toStarSubalgebra.sum_mem fun i _ => M.toStarSubalgebra.smul_mem (ha i) _)
    hb hib hrel
  intro p
  exact (Fintype.linearIndependent_iff.mp hia _ (hcoeff p.2)) p.1

variable [Nontrivial H]


theorem many_independent (n : ℕ) (κ : Fin n → Type*) [∀ i, Fintype (κ i)]
    (M : Fin n → VonNeumannAlgebra H) (hM : ∀ i, FactorIndependence.IsFactor (M i))
    (hc : ∀ i j, i ≠ j → ∀ b ∈ M j, b ∈ (M i).commutant)
    (a : ∀ i, κ i → H →L[ℂ] H) (ha : ∀ i j, a i j ∈ M i)
    (hia : ∀ i, LinearIndependent ℂ (a i)) :
    LinearIndependent ℂ (fun p : ∀ i, κ i => (List.ofFn (fun i => a i (p i))).prod) := by
  classical
  induction n with
  | zero =>
    apply linearIndependent_unique_iff.mpr
    simp
  | succ n ih =>
    have htail := ih (fun i => κ i.succ) (fun i => M i.succ) (fun i => hM i.succ)
      (fun i j hij => hc i.succ j.succ (fun h => hij (Fin.succ_injective _ h)))
      (fun i => a i.succ) (fun i => ha i.succ) (fun i => hia i.succ)
    have htailmem (p : ∀ i : Fin n, κ i.succ) :
        (List.ofFn (fun i => a i.succ (p i))).prod ∈ (M 0).commutant := by
      apply list_prod_mem
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hc 0 i.succ (Fin.succ_ne_zero i).symm _ (ha _ _)
    have hp := pair_independent (M 0) (hM 0) (a 0)
      (fun p : ∀ i : Fin n, κ i.succ => (List.ofFn (fun i => a i.succ (p i))).prod)
      (ha 0) htailmem (hia 0) htail
    have h := hp.comp (Fin.consEquiv κ).symm (Fin.consEquiv κ).symm.injective
    simpa only [Function.comp_def, Fin.consEquiv_symm_apply, Fin.tail, List.ofFn_succ, List.prod_cons]
      using h

end KirchbergRordam.GenericRW.ProductIndependence

namespace KirchbergRordam.GenericRW.RealProduct
open scoped TensorProduct
open Module
variable {A : Type*} [CStarAlgebra A] {n : ℕ}
variable {V : Fin n → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]

def multiply (f : ∀ i, V i →ₗ[ℝ] A) : (⨂[ℝ] i, V i) →ₗ[ℝ] A :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebraFin ℝ n A).compLinearMap f)

@[simp] lemma multiply_tprod (f : ∀ i, V i →ₗ[ℝ] A) (v : ∀ i, V i) :
    multiply f (⨂ₜ[ℝ] i, v i) = (List.ofFn fun i => f i (v i)).prod := by
  simp [multiply]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

lemma multiply_injective [∀ i, FiniteDimensional ℝ (V i)]
    (f : ∀ i, V i →ₗ[ℝ] (H →L[ℂ] H))
    (hf : ∀ i, Function.Injective (f i)) (hsa : ∀ i v, IsSelfAdjoint (f i v))
    (M : Fin n → VonNeumannAlgebra H) (hM : ∀ i, FactorIndependence.IsFactor (M i))
    (hc : ∀ i j, i ≠ j → ∀ b ∈ M j, b ∈ (M i).commutant)
    (hmem : ∀ i v, f i v ∈ M i) : Function.Injective (multiply f) := by
  classical
  let b (i : Fin n) := Module.finBasis ℝ (V i)
  let B := Basis.piTensorProduct b
  apply LinearMap.injective_of_linearIndependent B.span_eq
  have hi (i : Fin n) : LinearIndependent ℂ (fun j => f i (b i j)) := by
    apply ProductIndependence.selfAdjoint_complex_independent _ (fun j => hsa _ _)
    exact (b i).linearIndependent.map' (f i) (LinearMap.ker_eq_bot.mpr (hf i))
  have hp := ProductIndependence.many_independent n _ M hM hc
    (fun i j => f i (b i j)) (fun i j => hmem i _) hi
  have hpR := hp.restrict_scalars' ℝ
  simpa only [Function.comp_def, B, Basis.piTensorProduct_apply, multiply_tprod] using hpR

lemma selfAdjoint_product (a : Fin n → A) (ha : ∀ i, IsSelfAdjoint (a i))
    (hc : ∀ i j, i ≠ j → Commute (a i) (a j)) :
    IsSelfAdjoint (List.ofFn a).prod := by
  induction n with
  | zero => simp [IsSelfAdjoint]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have ht := ih (fun i => a i.succ) (fun i => ha i.succ)
      (fun i j hij => hc i.succ j.succ (fun h => hij (Fin.succ_injective _ h)))
    have hcomm : Commute (a 0) (List.ofFn (fun i : Fin n => a i.succ)).prod := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hc 0 i.succ (Fin.succ_ne_zero i).symm
    change star (a 0 * _) = _
    rw [star_mul, ht.star_eq, (ha 0).star_eq, hcomm.eq]

omit [Nontrivial H] in
lemma multiply_selfAdjoint
    (f : ∀ i, V i →ₗ[ℝ] (H →L[ℂ] H))
    (hsa : ∀ i v, IsSelfAdjoint (f i v))
    (hc : ∀ i j, i ≠ j → ∀ v w, Commute (f i v) (f j w))
    (x : ⨂[ℝ] i, V i) : IsSelfAdjoint (multiply f x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, multiply_tprod]
    exact (IsSelfAdjoint.all r).smul (selfAdjoint_product _ (fun i => hsa i _)
      (fun i j hij => hc i j hij _ _))
  | add x y hx hy =>
    rw [map_add]
    exact hx.add hy

end KirchbergRordam.GenericRW.RealProduct
end

end OAI
