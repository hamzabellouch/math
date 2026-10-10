import OAI.Analysis.CharacterCriterion.SignObstruction

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace


open scoped TensorProduct InnerProductSpace
open UniformSpace
namespace KirchbergRordam.GenericRW.Spatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev Hilbert (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] := Completion (H ⊗[ℂ] K)

def map (T : H →L[ℂ] H) (S : K →L[ℂ] K) : Hilbert H K →L[ℂ] Hilbert H K :=
  (TensorProduct.mapL T S).completion

@[simp] lemma map_coe (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
    map T S (x : Hilbert H K) = (TensorProduct.mapL T S x : H ⊗[ℂ] K) := by
  simp [map]

@[ext] lemma ext {T S : Hilbert H K →L[ℂ] Hilbert H K}
    (h : ∀ x : H ⊗[ℂ] K, T x = S x) : T = S := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq T.continuous S.continuous
  | ih x => exact h x

lemma map_add_left (T U : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (T + U) S = map T S + map U S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_add_left, ← Completion.coe_add]

lemma map_add_right (T : H →L[ℂ] H) (S U : K →L[ℂ] K) :
    map T (S + U) = map T S + map T U := by
  apply ext
  intro x
  simp [TensorProduct.mapL_add_right, ← Completion.coe_add]

lemma map_smul_left (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (z • T) S = z • map T S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_smul_left, ← Completion.coe_smul]

lemma map_smul_right (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map T (z • S) = z • map T S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_smul_right, ← Completion.coe_smul]

lemma map_mul (T U : H →L[ℂ] H) (S V : K →L[ℂ] K) :
    map (T * U) (S * V) = map T S * map U V := by
  apply ext
  intro x
  simp only [mul_apply_eq_comp, map_coe, TensorProduct.mapL_mul]

@[simp] lemma map_one : map (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  apply ext
  intro x
  simp [show (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H from rfl,
    show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl]

variable [CompleteSpace H] [CompleteSpace K]

lemma map_inner_algebraic (T : H →L[ℂ] H) (S : K →L[ℂ] K)
    (x y : H ⊗[ℂ] K) :
    ⟪TensorProduct.mapL (star T) (star S) x, y⟫_ℂ =
      ⟪x, TensorProduct.mapL T S y⟫_ℂ := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
    | tmul c d =>
      simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

lemma map_inner (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x y : Hilbert H K) :
    ⟪map (star T) (star S) x, y⟫_ℂ = ⟪x, map T S y⟫_ℂ := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y => simpa using map_inner_algebraic T S x y

lemma map_star (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (star T) (star S) = star (map T S) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [map_inner, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]


def left : (H →L[ℂ] H) →⋆ₐ[ℂ] (Hilbert H K →L[ℂ] Hilbert H K) where
  toFun T := map T 1
  map_zero' := by ext x; simp [map]
  map_one' := map_one
  map_add' T U := map_add_left T U 1
  map_mul' T U := by simpa using map_mul T U (1 : K →L[ℂ] K) 1
  commutes' z := by
    change map (z • 1) 1 = z • 1
    rw [map_smul_left, map_one]
  map_star' T := by simpa using map_star T (1 : K →L[ℂ] K)

def right : (K →L[ℂ] K) →⋆ₐ[ℂ] (Hilbert H K →L[ℂ] Hilbert H K) where
  toFun S := map 1 S
  map_zero' := by ext x; simp [map]
  map_one' := map_one
  map_add' T U := map_add_right 1 T U
  map_mul' T U := by simpa using map_mul (1 : H →L[ℂ] H) 1 T U
  commutes' z := by
    change map 1 (z • 1) = z • 1
    rw [map_smul_right, map_one]
  map_star' S := by simpa using map_star (1 : H →L[ℂ] H) S

lemma left_right_commute (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    Commute (left (K := K) T) (right (H := H) S) := by
  change map T 1 * map 1 S = map 1 S * map T 1
  rw [← map_mul, ← map_mul]
  simp

end KirchbergRordam.GenericRW.Spatial

namespace KirchbergRordam.GenericRW
namespace Spatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [Nontrivial H] [Nontrivial K]
instance : Nontrivial (Hilbert H K) :=
  (UniformSpace.Completion.coe_injective (H ⊗[ℂ] K)).nontrivial
end Spatial
namespace MaxTensor
universe u v
variable (A : Type u) (B : Type v) [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]
omit [Nontrivial A] [Nontrivial B] in
lemma nontrivial_of_representations
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial H] [Nontrivial K]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    Nontrivial (Algebra A B) := by
  let φ : A →⋆ₐ[ℂ] (Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) :=
    (Spatial.left (K := K)).comp π
  let ψ : B →⋆ₐ[ℂ] (Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) :=
    (Spatial.right (H := H)).comp ρ
  have hc : ∀ a b, Commute (φ a) (ψ b) := fun a b =>
    Spatial.left_right_commute (π a) (ρ b)
  let χ : Algebra A B →⋆ₐ[ℂ] (Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) :=
    lift (A := A) (B := B)
      (C := Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) φ ψ hc
  exact χ.toRingHom.domain_nontrivial
instance : Nontrivial (Algebra A B) := by
  obtain ⟨π⟩ := exists_irreducible_representation A
  obtain ⟨ρ⟩ := exists_irreducible_representation B
  exact nontrivial_of_representations A B π.representation ρ.representation
instance powerPack_nontrivial (D : Type u) [CStarAlgebra D] [Nontrivial D] (n : ℕ) :
    Nontrivial (powerPack D n) := by
  induction n with
  | zero => exact inferInstanceAs (Nontrivial D)
  | succ n ih =>
    let : Nontrivial (powerPack D n) := ih
    exact inferInstanceAs (Nontrivial (Algebra D (powerPack D n)))
end MaxTensor
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.MaxTensor
universe u
variable {A B C E F : Type u} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [CStarAlgebra E] [CStarAlgebra F]

def map (φ : A →⋆ₐ[ℂ] E) (ψ : B →⋆ₐ[ℂ] F) : Algebra A B →⋆ₐ[ℂ] Algebra E F :=
  lift (includeLeft.comp φ) (includeRight.comp ψ) (fun a b => legs_commute (φ a) (ψ b))
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.TripleTensor
universe u
variable {A B C : Type u} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor

def firstTwo : MaxTensor.Algebra A B →⋆ₐ[ℂ] Algebra A B C :=
  lift first second first_second

lemma firstTwo_third (ab : MaxTensor.Algebra A B) (c : C) :
    Commute (firstTwo ab) (third c) := by
  apply Commute.symm
  apply MaxTensor.commute_of_legs firstTwo (third c) ?_ ?_ ab
  · intro a
    have he := DFunLike.congr_fun (lift_includeLeft (first (A := A) (B := B) (C := C))
      (second (A := A) (B := B) (C := C)) first_second) a
    change firstTwo (includeLeft a) = first a at he
    rw [he]
    exact (first_third a c).symm
  · intro b
    have he := DFunLike.congr_fun (lift_includeRight (first (A := A) (B := B) (C := C))
      (second (A := A) (B := B) (C := C)) first_second) b
    change firstTwo (includeRight b) = second b at he
    rw [he]
    exact (second_third b c).symm


def reassociate : MaxTensor.Algebra (MaxTensor.Algebra A B) C →⋆ₐ[ℂ] Algebra A B C :=
  lift firstTwo third firstTwo_third
end KirchbergRordam.GenericRW.TripleTensor

namespace KirchbergRordam.GenericRW.MaxTensor
universe u
variable (D : Type u) [CStarAlgebra D]


theorem exists_joinPower (n m : ℕ) :
    Nonempty (Algebra (powerPack D n) (powerPack D m) →⋆ₐ[ℂ] (powerPack D (n+m+1))) := by
  induction n with
  | zero =>
    rw [Nat.zero_add]
    exact ⟨StarAlgHom.id ℂ (Algebra D (powerPack D m))⟩
  | succ n ih =>
    obtain ⟨φ⟩ := ih
    let ψ := (map (StarAlgHom.id ℂ D) φ).comp
      (TripleTensor.reassociate (A := D) (B := powerPack D n) (C := powerPack D m))
    have he : n + 1 + m + 1 = (n + m + 1) + 1 := by omega
    rw [he]
    exact ⟨ψ⟩
end KirchbergRordam.GenericRW.MaxTensor

namespace KirchbergRordam.GenericRW.Fullness
section
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]


theorem finite_bridges {a b : A} (ha : IsFull a) (hb : IsFull b) (hba : b * a = 0) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ c : Fin r → A,
      (∀ i j, c i * c j = 0) ∧ TwoSidedIdeal.span (Set.range c) = ⊤ := by
  classical
  have h1 : (1 : A) ∈ TwoSidedIdeal.span (Set.range (fun d : A => a * d * b)) := by
    rw [bridges_span_one ha hb]
    exact TwoSidedIdeal.mem_top A
  obtain ⟨t, ht, hmem⟩ := mem_span_finite h1
  have hne : t.Nonempty := by
    by_contra he
    have hz : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    subst t
    have hh : TwoSidedIdeal.span ((↑(∅ : Finset A)) : Set A) ≤ ⊥ :=
      TwoSidedIdeal.span_le.mpr (by simp)
    exact one_ne_zero ((TwoSidedIdeal.mem_bot _).mp (hh hmem))
  let e := Fintype.equivFin t
  let c : Fin (Fintype.card t) → A := fun i => (e.symm i : A)
  refine ⟨Fintype.card t, ?_, c, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hne))
  · intro i j
    obtain ⟨d, hd⟩ := ht (e.symm i).property
    obtain ⟨f, hf⟩ := ht (e.symm j).property
    change (e.symm i : A) * (e.symm j : A) = 0
    rw [← hd, ← hf]
    calc
      a * d * b * (a * f * b) = a * d * (b * a) * f * b := by noncomm_ring
      _ = 0 := by rw [hba]; simp
  · apply TwoSidedIdeal.eq_top
    apply TwoSidedIdeal.span_mono ?_ hmem
    intro z hz
    exact ⟨e ⟨z, hz⟩, by simp [c]⟩
end

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] [Nontrivial B]
lemma full_map {a : A} (ha : IsFull a) (φ : A →⋆ₐ[ℂ] B) : IsFull (φ a) := by
  apply full_of_survives
  intro π
  exact full_survives ha (π.representation.comp φ)
end KirchbergRordam.GenericRW.Fullness

namespace KirchbergRordam.GenericRW.FullSquareZero
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor Fullness
universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]


lemma orthogonal_of_pair {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (s t : A) (hs : IsSelfAdjoint s) (ht : IsSelfAdjoint t)
    (hp : ∀ π : IrreducibleRepresentation A,
      ¬ Commute (π.representation s) (π.representation t)) :
    ∃ a b : A, IsFull a ∧ IsFull b ∧ b * a = 0 := by
  let z := s * (s * t - t * s) - (s * t - t * s) * s
  have hfull : IsFull z⁺ ∧ IsFull z⁻ := full_parts s t hs ht hp
  exact ⟨z⁺, z⁻, hfull.1, hfull.2, CFC.negPart_mul_posPart z⟩


theorem full_orthogonal_parts (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ n : ℕ, ∃ a b : TripleTensor.Algebra D (powerPack D n) (powerPack D n),
      IsFull a ∧ IsFull b ∧ b * a = 0 := by
  obtain ⟨n, s, t, hs, ht, hp⟩ := NoncommutingPair.exists_pair hD
  refine ⟨n, orthogonal_of_pair s t hs ht ?_⟩
  intro π
  exact hp π.space π.representation π.scalar_commutant

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]


theorem combine_bridges (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ))
    (r : ℕ) (hr : 1 ≤ r) (c : Fin r → A)
    (hcz : ∀ i j, c i * c j = 0) (hcfull : TwoSidedIdeal.span (Set.range c) = ⊤) :
    ∃ n : ℕ, ∃ y : MaxTensor.Algebra A (powerPack D n), y * y = 0 ∧ IsFull y := by
  classical
  obtain ⟨V, hV, hsa, hd⟩ := finite_detecting_space hD
  let := hV
  obtain ⟨n, x, _, hx⟩ := RepresentedLabels.power_labels V hsa hd r hr
  let P := powerPack D n
  let : CStarAlgebra (MaxTensor.Algebra A P) := inferInstance
  let l : A →⋆ₐ[ℂ] MaxTensor.Algebra A P := includeLeft
  let q : P →⋆ₐ[ℂ] MaxTensor.Algebra A P := includeRight
  let y := ∑ i, l (c i) * q (x i)
  refine ⟨n, y, ?_, ?_⟩
  · change (∑ i, l (c i) * q (x i)) * (∑ i, l (c i) * q (x i)) = 0
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [((legs_commute (c i) (x j)).symm).mul_mul_mul_comm]
    rw [← map_mul, hcz, map_zero, zero_mul]
  · apply full_of_survives
    intro π hy
    let α : A →⋆ₐ[ℂ] (π.space →L[ℂ] π.space) := π.representation.comp l
    let β : P →⋆ₐ[ℂ] (π.space →L[ℂ] π.space) := π.representation.comp q
    let M := GroupedFactors.bicommutant α.range
    have hi : LinearIndependent ℂ (fun i => β (x i)) := by
      apply hx π.space A β α
      · intro p a
        exact ((legs_commute a p).map π.representation).symm
      · intro T hq hl
        exact π.scalar_commutant T (commute_of_legs π.representation T hl hq)
    have hrel : ∑ i, α (c i) * β (x i) = 0 := by
      have he : π.representation y = ∑ i, α (c i) * β (x i) := by
        simp only [y, map_sum, map_mul]
        rfl
      rwa [← he]
    have hz := FactorIndependence.relation_coefficients_zero M
      (left_factor π.representation π.scalar_commutant)
      (fun i => α (c i)) (fun i => β (x i))
      (fun i => GroupedFactors.subset_bicommutant _ _ ⟨c i, rfl⟩)
      (fun i => NoncommutingPair.mem_factor_commutant _ _ (by
        rintro z ⟨a, rfl⟩
        exact (legs_commute a (x i)).map π.representation)) hi hrel
    have hk : TwoSidedIdeal.span (Set.range c) ≤ TwoSidedIdeal.ker α.toRingHom := by
      apply TwoSidedIdeal.span_le.mpr
      rintro z ⟨i, rfl⟩
      exact (TwoSidedIdeal.mem_ker _).mpr (hz i)
    have h1 : (1 : A) ∈ TwoSidedIdeal.span (Set.range c) := by
      rw [hcfull]
      exact TwoSidedIdeal.mem_top A
    have hh := (TwoSidedIdeal.mem_ker _).mp (hk h1)
    exact one_ne_zero (by simpa only [map_one] using hh)


theorem exists_full_square_zero (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ n : ℕ, ∃ y : powerPack D n, y * y = 0 ∧ IsFull y := by
  obtain ⟨n, a, b, ha, hb, hba⟩ := full_orthogonal_parts hD
  obtain ⟨r, hr, c, hcz, hcfull⟩ := finite_bridges ha hb hba
  obtain ⟨m, y, hyz, hyfull⟩ := combine_bridges hD r hr c hcz hcfull
  obtain ⟨φ⟩ := exists_joinPower D n n
  let ψ : TripleTensor.Algebra D (powerPack D n) (powerPack D n) →⋆ₐ[ℂ]
      (powerPack D (n+n+1+1)) := MaxTensor.map (StarAlgHom.id ℂ D) φ
  obtain ⟨χ⟩ := exists_joinPower D (n+n+1+1) m
  let θ := χ.comp (MaxTensor.map ψ (StarAlgHom.id ℂ (powerPack D m)))
  refine ⟨n+n+1+1+m+1, θ y, ?_, full_map hyfull θ⟩
  rw [← map_mul, hyz, map_zero]


theorem normalize {A : Type*} [CStarAlgebra A] [Nontrivial A]
    {y : A} (hyz : y * y = 0) (hyfull : IsFull y) :
    ∃ v : A, v * v = 0 ∧ IsFull v ∧ ‖v‖ = 1 := by
  have hy : y ≠ 0 := full_ne_zero hyfull
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  refine ⟨‖y‖⁻¹ • y, ?_, ?_, ?_⟩
  · simp only [smul_mul_assoc, mul_smul_comm, hyz, smul_zero]
  · apply full_of_survives
    intro π he
    have hm : π.representation (‖y‖⁻¹ • y) = ‖y‖⁻¹ • π.representation y :=
      (π.representation.toLinearMap.restrictScalars ℝ).map_smul _ _
    rw [hm] at he
    exact full_survives hyfull π.representation ((smul_eq_zero.mp he).resolve_left (inv_ne_zero hn))
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]

end KirchbergRordam.GenericRW.FullSquareZero
end

end OAI
