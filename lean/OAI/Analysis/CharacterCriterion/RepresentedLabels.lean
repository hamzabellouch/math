import OAI.Analysis.CharacterCriterion.DetectingSpaces

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology


namespace KirchbergRordam.GenericRW.RepresentedLabels
open Module
open scoped TensorProduct
universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]

omit [Nontrivial D] in
lemma rank_two_of_detecting (V : Submodule ℝ D) [FiniteDimensional ℝ V]
    {B : Type*} [CStarAlgebra B] (φ : D →⋆ₐ[ℂ] B)
    (hd : ∃ x ∈ V, ∃ y ∈ V, ¬ Commute (φ x) (φ y)) :
    2 ≤ finrank ℝ ((φ.toLinearMap.restrictScalars ℝ).comp V.subtype).range := by
  let f := (φ.toLinearMap.restrictScalars ℝ).comp V.subtype
  by_contra h
  change ¬ 2 ≤ finrank ℝ f.range at h
  have h1 : finrank ℝ f.range ≤ 1 := by omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h1
  obtain ⟨x, hx, y, hy, hxy⟩ := hd
  obtain ⟨a, ha⟩ := hv (f.rangeRestrict ⟨x, hx⟩)
  obtain ⟨b, hb⟩ := hv (f.rangeRestrict ⟨y, hy⟩)
  have ha' : a • (v : B) = φ x := congrArg Subtype.val ha
  have hb' : b • (v : B) = φ y := congrArg Subtype.val hb
  apply hxy
  rw [← ha', ← hb']
  show (a • (v : B)) * (b • (v : B)) = (b • (v : B)) * (a • (v : B))
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm a b]

lemma multiply_map {n : ℕ} {E F : Fin n → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, AddCommGroup (F i)] [∀ i, Module ℝ (F i)]
    {A : Type*} [CStarAlgebra A]
    (f : ∀ i, F i →ₗ[ℝ] A) (g : ∀ i, E i →ₗ[ℝ] F i) (x : ⨂[ℝ] i, E i) :
    RealProduct.multiply f (PiTensorProduct.map g x) =
      RealProduct.multiply (fun i => (f i).comp (g i)) x := by
  have hh : (RealProduct.multiply f).comp (PiTensorProduct.map g) =
      RealProduct.multiply (fun i => (f i).comp (g i)) := by
    apply PiTensorProduct.ext
    ext v
    simp
  exact DFunLike.congr_fun hh x

lemma labels_map_independent {n r : ℕ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {V : Fin n → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    (q : (⨂[ℝ] i, V i) →ₗ[ℝ] (H →L[ℂ] H))
    (hq : Function.Injective q) (y : Fin r → ⨂[ℝ] i, V i)
    (hy : LinearIndependent ℝ y) : LinearIndependent ℝ (fun i => q (y i)) := by
  exact hy.map' q (LinearMap.ker_eq_bot.mpr hq)

lemma range_multiply_injective {n : ℕ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : Fin n → V →ₗ[ℝ] (H →L[ℂ] H))
    (hsa : ∀ i a, IsSelfAdjoint (f i a))
    (M : Fin n → VonNeumannAlgebra H)
    (hM : ∀ i, FactorIndependence.IsFactor (M i))
    (hc : ∀ i j, i ≠ j → ∀ b ∈ M j, b ∈ (M i).commutant)
    (hmem : ∀ i a, f i a ∈ M i)
 :
    Function.Injective (RealProduct.multiply (fun i => (f i).range.subtype)) := by
  exact RealProduct.multiply_injective (fun i => (f i).range.subtype)
    (fun i => Subtype.val_injective)
    (fun i v => by
      obtain ⟨a, ha⟩ := v.property
      change IsSelfAdjoint (v : H →L[ℂ] H)
      rw [← ha]
      exact hsa i a)
    M hM hc (fun i v => by
      obtain ⟨a, ha⟩ := v.property
      change (v : H →L[ℂ] H) ∈ M i
      rw [← ha]
      exact hmem i a)

lemma independent_multiply_range {n r : ℕ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : Fin n → V →ₗ[ℝ] (H →L[ℂ] H))
    (hsa : ∀ i a, IsSelfAdjoint (f i a))
    (M : Fin n → VonNeumannAlgebra H)
    (hM : ∀ i, FactorIndependence.IsFactor (M i))
    (hc : ∀ i j, i ≠ j → ∀ b ∈ M j, b ∈ (M i).commutant)
    (hmem : ∀ i a, f i a ∈ M i)
    (x : Fin r → (⨂[ℝ] _ : Fin n, V))
    (hli : LinearIndependent ℝ (fun k => PiTensorProduct.map
      (fun i => (f i).rangeRestrict) (x k))) :
    LinearIndependent ℂ (fun k => RealProduct.multiply f (x k)) := by
  have hsinj := range_multiply_injective f hsa M hM hc hmem
  let q : (⨂[ℝ] i : Fin n, (f i).range) →ₗ[ℝ] (H →L[ℂ] H) :=
    RealProduct.multiply (fun i => (f i).range.subtype)
  have hreal := labels_map_independent q hsinj _ hli
  have hreal' : LinearIndependent ℝ (fun k => RealProduct.multiply f (x k)) := by
    have he (i : Fin n) : (f i).range.subtype.comp (f i).rangeRestrict = f i := rfl
    simpa only [q, multiply_map, he] using hreal
  apply ProductIndependence.selfAdjoint_complex_independent _ ?_ hreal'
  intro k
  apply RealProduct.multiply_selfAdjoint
  · exact hsa
  · intro i j hij a b
    exact (VonNeumannAlgebra.mem_commutant_iff.mp (hc i j hij _ (hmem _ _))
      _ (hmem _ _))


theorem factor_labels (V : Submodule ℝ D) [FiniteDimensional ℝ V]
    (hsa : V ≤ selfAdjoint.submodule ℝ D)
    (hd : ∀ (B : Type u) [CStarAlgebra B] [Nontrivial B] (φ : D →⋆ₐ[ℂ] B),
      ∃ x ∈ V, ∃ y ∈ V, ¬ Commute (φ x) (φ y))
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ x : Fin r → (⨂[ℝ] _ : Fin n, V),
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H]
        (φ : Fin n → D →⋆ₐ[ℂ] (H →L[ℂ] H))
        (M : Fin n → VonNeumannAlgebra H),
        (∀ i, FactorIndependence.IsFactor (M i)) →
        (∀ i j, i ≠ j → ∀ b ∈ M j, b ∈ (M i).commutant) →
        (∀ i a, φ i a ∈ M i) →
        LinearIndependent ℂ (fun k => RealProduct.multiply
          (fun i => ((φ i).toLinearMap.restrictScalars ℝ).comp V.subtype) (x k)) := by
  have hV : 2 ≤ finrank ℝ V := by
    have h := rank_two_of_detecting V (StarAlgHom.id ℂ D) (hd D (StarAlgHom.id ℂ D))
    exact h.trans (LinearMap.finrank_range_le _)
  obtain ⟨n, hn, x, hx⟩ := tensor_real_labels V hV r hr
  refine ⟨n, hn, x, ?_⟩
  intro H _ _ _ _ φ M hM hc hmem
  let f (i : Fin n) := ((φ i).toLinearMap.restrictScalars ℝ).comp V.subtype
  let E (i : Fin n) := (f i).range
  let g (i : Fin n) : V →ₗ[ℝ] E i := (f i).rangeRestrict
  have hrank (i : Fin n) : 2 ≤ finrank ℝ (g i).range := by
    rw [show (g i).range = ⊤ from (f i).range_rangeRestrict, finrank_top]
    exact rank_two_of_detecting V _ (hd _ (φ i))
  have hind := hx (fun i => E i) g hrank
  apply independent_multiply_range f (fun i a => (hsa a.property).map (φ i)) M hM hc
    (fun i a => hmem i a) x
  exact hind



lemma multiply_selfAdjoint_general {n : ℕ} {E : Fin n → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    {A : Type*} [CStarAlgebra A]
    (f : ∀ i, E i →ₗ[ℝ] A)
    (hsa : ∀ i v, IsSelfAdjoint (f i v))
    (hc : ∀ i j, i ≠ j → ∀ v w, Commute (f i v) (f j w))
    (x : ⨂[ℝ] i, E i) : IsSelfAdjoint (RealProduct.multiply f x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, RealProduct.multiply_tprod]
    exact (IsSelfAdjoint.all r).smul (RealProduct.selfAdjoint_product _ (fun i => hsa i _)
      (fun i j hij => hc i j hij _ _))
  | add x y hx hy =>
    rw [map_add]
    exact hx.add hy

lemma map_multiply {n : ℕ} {E : Fin n → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (f : ∀ i, E i →ₗ[ℝ] A) (x : ⨂[ℝ] i, E i) :
    φ (RealProduct.multiply f x) = RealProduct.multiply
      (fun i => (φ.toLinearMap.restrictScalars ℝ).comp (f i)) x := by
  have hh : (φ.toLinearMap.restrictScalars ℝ).comp (RealProduct.multiply f) =
      RealProduct.multiply (fun i => (φ.toLinearMap.restrictScalars ℝ).comp (f i)) := by
    apply PiTensorProduct.ext
    ext v
    simp [map_list_prod, Function.comp_def]
  exact DFunLike.congr_fun hh x


theorem power_labels (V : Submodule ℝ D) [FiniteDimensional ℝ V]
    (hsa : V ≤ selfAdjoint.submodule ℝ D)
    (hd : ∀ (B : Type u) [CStarAlgebra B] [Nontrivial B] (φ : D →⋆ₐ[ℂ] B),
      ∃ x ∈ V, ∃ y ∈ V, ¬ Commute (φ x) (φ y))
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ n : ℕ, ∃ x : Fin r → (MaxTensor.powerPack D n),
      (∀ k, IsSelfAdjoint (x k)) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H]
        (B : Type u) [CStarAlgebra B]
        (φ : (MaxTensor.powerPack D n) →⋆ₐ[ℂ] (H →L[ℂ] H))
        (ψ : B →⋆ₐ[ℂ] (H →L[ℂ] H)),
        (∀ a b, Commute (φ a) (ψ b)) →
        (∀ T : H →L[ℂ] H, (∀ a, Commute T (φ a)) →
          (∀ b, Commute T (ψ b)) → ∃ z : ℂ, T = z • 1) →
        LinearIndependent ℂ (fun k => φ (x k)) := by
  obtain ⟨n, hn, v, hv⟩ := factor_labels V hsa hd r hr
  cases n with
  | zero => omega
  | succ n =>
    let f : Fin (n+1) → V →ₗ[ℝ] (MaxTensor.powerPack D n) :=
      fun i => ((MaxTensor.leg D n i).toLinearMap.restrictScalars ℝ).comp V.subtype
    let x : Fin r → (MaxTensor.powerPack D n) := fun k => RealProduct.multiply f (v k)
    refine ⟨n, x, ?_, ?_⟩
    · intro k
      apply multiply_selfAdjoint_general
      · intro i a
        exact (hsa a.property).map (MaxTensor.leg D n i)
      · intro i j hij a b
        exact MaxTensor.commute_legs D n i j hij a b
    · intro H _ _ _ _ B _ φ ψ hc hs
      let ρ (i : Fin (n+1)) := φ.comp (MaxTensor.leg D n i)
      let M (i : Fin (n+1)) := GroupedFactors.bicommutant (ρ i).range
      have hi := hv H ρ M
        (fun i => MaxTensor.power_leg_factor n φ ψ hc hs i)
        (fun i j hij => MaxTensor.power_leg_factors_commute n φ i j hij)
        (fun i a => GroupedFactors.subset_bicommutant _ _ ⟨a, rfl⟩)
      convert hi using 1
      funext k
      exact map_multiply φ f (v k)
end KirchbergRordam.GenericRW.RepresentedLabels


namespace KirchbergRordam.GenericRW.GroupedFactors
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma isFactor_of_three (S T R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hST : ∀ a ∈ S, ∀ b ∈ T, Commute a b)
    (hSR : ∀ a ∈ S, ∀ c ∈ R, Commute a c)
    (hs : ∀ U : H →L[ℂ] H, (∀ a ∈ S, Commute U a) →
      (∀ b ∈ T, Commute U b) → (∀ c ∈ R, Commute U c) → ∃ z : ℂ, U = z • 1) :
    FactorIndependence.IsFactor (bicommutant S) := by
  intro U hU hUc
  apply hs U
  · intro a ha
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hUc a (subset_bicommutant S a ha)).symm
  · intro b hb
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hU b
      ((mem_commutantOf_iff S b).mpr (fun a ha => hST a ha b hb))).symm
  · intro c hc
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hU c
      ((mem_commutantOf_iff S c).mpr (fun a ha => hSR a ha c hc))).symm
end KirchbergRordam.GenericRW.GroupedFactors

namespace KirchbergRordam.GenericRW.TripleTensor
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor
abbrev Algebra (A B C : Type*) [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C] :=
  MaxTensor.Algebra A (MaxTensor.Algebra B C)
def first : A →⋆ₐ[ℂ] Algebra A B C := includeLeft
def second : B →⋆ₐ[ℂ] Algebra A B C := includeRight.comp includeLeft
def third : C →⋆ₐ[ℂ] Algebra A B C := includeRight.comp includeRight
lemma first_second (a : A) (b : B) :
    Commute (first (C := C) a) (second (A := A) b) := legs_commute _ _
lemma first_third (a : A) (c : C) :
    Commute (first (B := B) a) (third (A := A) c) := legs_commute _ _
lemma second_third (b : B) (c : C) :
    Commute (second (A := A) b) (third (A := A) c) := (legs_commute b c).map includeRight

variable {E : Type*} [CStarAlgebra E]
lemma commute_of_legs (π : Algebra A B C →⋆ₐ[ℂ] E) (T : E)
    (h1 : ∀ a, Commute T (π (first a)))
    (h2 : ∀ b, Commute T (π (second b)))
    (h3 : ∀ c, Commute T (π (third c))) : ∀ x, Commute T (π x) := by
  apply MaxTensor.commute_of_legs π T h1
  exact MaxTensor.commute_of_legs (π.comp includeRight) T h2 h3

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma first_factor (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1) :
    FactorIndependence.IsFactor (GroupedFactors.bicommutant (π.comp first).range) :=
  MaxTensor.left_factor π hs
lemma second_factor (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1) :
    FactorIndependence.IsFactor (GroupedFactors.bicommutant (π.comp second).range) := by
  apply GroupedFactors.isFactor_of_three _ (π.comp first).range (π.comp third).range
  · rintro x ⟨b, rfl⟩ y ⟨a, rfl⟩
    exact ((first_second a b).map π).symm
  · rintro x ⟨b, rfl⟩ y ⟨c, rfl⟩
    exact (second_third b c).map π
  · intro T h2 h1 h3
    exact hs T (commute_of_legs π T (fun a => h1 _ ⟨a, rfl⟩)
      (fun b => h2 _ ⟨b, rfl⟩) (fun c => h3 _ ⟨c, rfl⟩))


def complementSecond (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    MaxTensor.Algebra A C →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  MaxTensor.lift (A := A) (B := C) (C := H →L[ℂ] H)
    (π.comp first) (π.comp third) (fun a c => (first_third a c).map π)
lemma complementSecond_commute (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (b : B) (d : MaxTensor.Algebra A C) :
    Commute (π (second b)) (complementSecond π d) := by
  apply MaxTensor.commute_of_legs (complementSecond π) _ ?_ ?_ d
  · intro a
    have he := DFunLike.congr_fun (MaxTensor.lift_includeLeft (π.comp first) (π.comp third)
      (fun a c => (first_third a c).map π)) a
    change complementSecond π (includeLeft a) = π (first a) at he
    rw [he]
    exact ((first_second a b).map π).symm
  · intro c
    have he := DFunLike.congr_fun (MaxTensor.lift_includeRight (π.comp first) (π.comp third)
      (fun a c => (first_third a c).map π)) c
    change complementSecond π (includeRight c) = π (third c) at he
    rw [he]
    exact (second_third b c).map π
lemma complementSecond_total (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1)
    (T : H →L[ℂ] H) (h2 : ∀ b, Commute T (π (second b)))
    (h13 : ∀ d, Commute T (complementSecond π d)) : ∃ z : ℂ, T = z • 1 := by
  apply hs T
  apply commute_of_legs π T ?_ h2 ?_
  · intro a
    have he := DFunLike.congr_fun (MaxTensor.lift_includeLeft (π.comp first) (π.comp third)
      (fun a c => (first_third a c).map π)) a
    change complementSecond π (includeLeft a) = π (first a) at he
    rw [← he]
    exact h13 _
  · intro c
    have he := DFunLike.congr_fun (MaxTensor.lift_includeRight (π.comp first) (π.comp third)
      (fun a c => (first_third a c).map π)) c
    change complementSecond π (includeRight c) = π (third c) at he
    rw [← he]
    exact h13 _

def complementThird (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    MaxTensor.Algebra A B →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  MaxTensor.lift (A := A) (B := B) (C := H →L[ℂ] H)
    (π.comp first) (π.comp second) (fun a b => (first_second a b).map π)
lemma complementThird_commute (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (c : C) (d : MaxTensor.Algebra A B) :
    Commute (π (third c)) (complementThird π d) := by
  apply MaxTensor.commute_of_legs (complementThird π) _ ?_ ?_ d
  · intro a
    have he := DFunLike.congr_fun (MaxTensor.lift_includeLeft (π.comp first) (π.comp second)
      (fun a b => (first_second a b).map π)) a
    change complementThird π (includeLeft a) = π (first a) at he
    rw [he]
    exact ((first_third a c).map π).symm
  · intro b
    have he := DFunLike.congr_fun (MaxTensor.lift_includeRight (π.comp first) (π.comp second)
      (fun a b => (first_second a b).map π)) b
    change complementThird π (includeRight b) = π (second b) at he
    rw [he]
    exact ((second_third b c).map π).symm
lemma complementThird_total (π : Algebra A B C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1)
    (T : H →L[ℂ] H) (h3 : ∀ c, Commute T (π (third c)))
    (h12 : ∀ d, Commute T (complementThird π d)) : ∃ z : ℂ, T = z • 1 := by
  apply hs T
  apply commute_of_legs π T ?_ ?_ h3
  · intro a
    have he := DFunLike.congr_fun (MaxTensor.lift_includeLeft (π.comp first) (π.comp second)
      (fun a b => (first_second a b).map π)) a
    change complementThird π (includeLeft a) = π (first a) at he
    rw [← he]
    exact h12 _
  · intro b
    have he := DFunLike.congr_fun (MaxTensor.lift_includeRight (π.comp first) (π.comp second)
      (fun a b => (first_second a b).map π)) b
    change complementThird π (includeRight b) = π (second b) at he
    rw [← he]
    exact h12 _
end KirchbergRordam.GenericRW.TripleTensor
end

end OAI
