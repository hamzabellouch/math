import OAI.Analysis.CharacterCriterion.RepresentedLabels

namespace OAI

noncomputable section
open scoped TensorProduct
noncomputable section
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
noncomputable section
open Topology


namespace KirchbergRordam.GenericRW
section
variable {A : Type*} [Ring A] {ι κ : Type*} [Fintype ι] [Fintype κ]
lemma sum_commutator (a : ι → A) (b : κ → A) (x : ι → A) (y : κ → A)
    (hxb : ∀ i j, Commute (x i) (b j)) (hya : ∀ i j, Commute (y j) (a i))
    (hxy : ∀ i j, Commute (x i) (y j)) :
    (∑ i, a i * x i) * (∑ j, b j * y j) -
      (∑ j, b j * y j) * (∑ i, a i * x i) =
      ∑ p : ι × κ, (a p.1 * b p.2 - b p.2 * a p.1) * (x p.1 * y p.2) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => b j * y j * (a i * x i)), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [(hxb i j).mul_mul_mul_comm, (hya i j).mul_mul_mul_comm, (hxy i j).eq,
    sub_mul]
end

section
variable {A : Type*} [CStarAlgebra A] {D : Type*} [CStarAlgebra D]
variable {V : Submodule ℝ D} {ι : Type*} [Fintype ι]
lemma commute_of_basis (b : Module.Basis ι ℝ V) (φ : D →⋆ₐ[ℂ] A)
    (h : ∀ i j, Commute (φ (b i)) (φ (b j))) :
    ∀ x ∈ V, ∀ y ∈ V, Commute (φ x) (φ y) := by
  classical
  intro x hx y hy
  let x' : V := ⟨x, hx⟩
  let y' : V := ⟨y, hy⟩
  have he (z : V) : φ z = ∑ i, (b.repr z i) • φ (b i) := by
    let g := (φ.toLinearMap.restrictScalars ℝ).comp V.subtype
    have hz := congrArg g (b.sum_repr z)
    simp only [map_sum, map_smul] at hz
    exact hz.symm
  rw [show φ x = _ from he x', show φ y = _ from he y']
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact ((h i j).smul_left _).smul_right _
end
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.NoncommutingPair
noncomputable section
open scoped BigOperators
universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]

lemma mem_factor_commutant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hc : ∀ a ∈ S, Commute a T) : T ∈ (GroupedFactors.bicommutant S).commutant := by
  rw [GroupedFactors.bicommutant, VonNeumannAlgebra.commutant_commutant]
  exact (GroupedFactors.mem_commutantOf_iff S T).mpr hc

lemma selfAdjoint_sum {ι : Type*} [Fintype ι] {A : Type*} [CStarAlgebra A]
    (f : ι → A) (hf : ∀ i, IsSelfAdjoint (f i)) : IsSelfAdjoint (∑ i, f i) := by
  change star _ = _
  simp only [star_sum, (hf _).star_eq]

lemma selfAdjoint_mul_of_commute {A : Type*} [CStarAlgebra A] {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hc : Commute a b) :
    IsSelfAdjoint (a * b) := (ha.commute_iff hb).mp hc

lemma map_sum_mul {ι : Type*} [Fintype ι] {A B : Type*}
    [CStarAlgebra A] [CStarAlgebra B] (φ : A →⋆ₐ[ℂ] B) (f g : ι → A) :
    φ (∑ i, f i * g i) = ∑ i, φ (f i) * φ (g i) := by
  simp only [map_sum, map_mul]


theorem exists_pair (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ n : ℕ, ∃ s t : TripleTensor.Algebra D (MaxTensor.powerPack D n)
        (MaxTensor.powerPack D n),
      IsSelfAdjoint s ∧ IsSelfAdjoint t ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H]
        (π : TripleTensor.Algebra D (MaxTensor.powerPack D n)
          (MaxTensor.powerPack D n) →⋆ₐ[ℂ] (H →L[ℂ] H)),
        (∀ T : H →L[ℂ] H, (∀ a, Commute T (π a)) → ∃ z : ℂ, T = z • 1) →
        ¬ Commute (π s) (π t) := by
  classical
  obtain ⟨V, hV, hsa, hd⟩ := finite_detecting_space hD
  let := hV
  let r := Module.finrank ℝ V
  let b := Module.finBasis ℝ V
  have hr : 1 ≤ r := by
    have h := RepresentedLabels.rank_two_of_detecting V (StarAlgHom.id ℂ D)
      (hd D (StarAlgHom.id ℂ D))
    have hh := h.trans (LinearMap.finrank_range_le _)
    exact le_trans (by norm_num) hh
  obtain ⟨n, x, hxsa, hx⟩ := RepresentedLabels.power_labels V hsa hd r hr
  let P := MaxTensor.powerPack D n
  let : CStarAlgebra (TripleTensor.Algebra D P P) := inferInstance
  let a : Fin r → TripleTensor.Algebra D P P := fun i => TripleTensor.first (b i : D)
  let l : Fin r → TripleTensor.Algebra D P P := fun i => TripleTensor.second (x i)
  let q : Fin r → TripleTensor.Algebra D P P := fun i => TripleTensor.third (x i)
  let s := ∑ i, a i * l i
  let t := ∑ i, a i * q i
  refine ⟨n, s, t, ?_, ?_, ?_⟩
  · apply selfAdjoint_sum
    intro i
    have ha : IsSelfAdjoint (a i) :=
      (hsa (b i).property).map (TripleTensor.first (B := P) (C := P))
    have hl : IsSelfAdjoint (l i) :=
      (hxsa i).map (TripleTensor.second (A := D) (C := P))
    exact selfAdjoint_mul_of_commute ha hl (TripleTensor.first_second (b i : D) (x i))
  · apply selfAdjoint_sum
    intro i
    have ha : IsSelfAdjoint (a i) :=
      (hsa (b i).property).map (TripleTensor.first (B := P) (C := P))
    have hq : IsSelfAdjoint (q i) :=
      (hxsa i).map (TripleTensor.third (A := D) (B := P))
    exact selfAdjoint_mul_of_commute ha hq (TripleTensor.first_third (b i : D) (x i))
  · intro H _ _ _ _ π hs hc
    let α : D →⋆ₐ[ℂ] (H →L[ℂ] H) := π.comp TripleTensor.first
    let β : P →⋆ₐ[ℂ] (H →L[ℂ] H) := π.comp TripleTensor.second
    let γ : P →⋆ₐ[ℂ] (H →L[ℂ] H) := π.comp TripleTensor.third
    let M := GroupedFactors.bicommutant α.range
    let N := GroupedFactors.bicommutant β.range
    have hiβ := hx H (MaxTensor.Algebra D P) β (TripleTensor.complementSecond π)
      (TripleTensor.complementSecond_commute π) (TripleTensor.complementSecond_total π hs)
    have hiγ := hx H (MaxTensor.Algebra D P) γ (TripleTensor.complementThird π)
      (TripleTensor.complementThird_commute π) (TripleTensor.complementThird_total π hs)
    have hp : LinearIndependent ℂ (fun ij : Fin r × Fin r => β (x ij.1) * γ (x ij.2)) := by
      apply ProductIndependence.pair_independent N (TripleTensor.second_factor π hs)
        _ _ (fun i => GroupedFactors.subset_bicommutant _ _ ⟨x i, rfl⟩) ?_ hiβ hiγ
      intro j
      apply mem_factor_commutant
      rintro z ⟨c, rfl⟩
      exact (TripleTensor.second_third c (x j)).map π
    have hrel : ∑ ij : Fin r × Fin r,
        (α (b ij.1) * α (b ij.2) - α (b ij.2) * α (b ij.1)) *
          (β (x ij.1) * γ (x ij.2)) = 0 := by
      have he := sum_commutator (fun i => α (b i)) (fun i => α (b i))
        (fun i => β (x i)) (fun i => γ (x i))
        (fun i j => ((TripleTensor.first_second (b j : D) (x i)).map π).symm)
        (fun i j => ((TripleTensor.first_third (b i : D) (x j)).map π).symm)
        (fun i j => (TripleTensor.second_third (x i) (x j)).map π)
      rw [← he]
      have hps : π s = ∑ i, α (b i) * β (x i) := map_sum_mul π a l
      have hpt : π t = ∑ i, α (b i) * γ (x i) := map_sum_mul π a q
      rw [← hps, ← hpt]
      exact sub_eq_zero.mpr hc.eq
    have hz := FactorIndependence.relation_coefficients_zero M
      (TripleTensor.first_factor π hs)
      (fun ij : Fin r × Fin r => α (b ij.1) * α (b ij.2) - α (b ij.2) * α (b ij.1))
      (fun ij : Fin r × Fin r => β (x ij.1) * γ (x ij.2))
      (fun ij => M.toStarSubalgebra.sub_mem
        (M.toStarSubalgebra.mul_mem (GroupedFactors.subset_bicommutant _ _ ⟨_, rfl⟩)
          (GroupedFactors.subset_bicommutant _ _ ⟨_, rfl⟩))
        (M.toStarSubalgebra.mul_mem (GroupedFactors.subset_bicommutant _ _ ⟨_, rfl⟩)
          (GroupedFactors.subset_bicommutant _ _ ⟨_, rfl⟩)))
      (fun ij => mem_factor_commutant _ _ (by
        rintro z ⟨d, rfl⟩
        exact ((TripleTensor.first_second d (x ij.1)).map π).mul_right
          ((TripleTensor.first_third d (x ij.2)).map π))) hp hrel
    obtain ⟨v, hv, w, hw, hn⟩ := hd (H →L[ℂ] H) α
    exact hn (commute_of_basis b α (fun i j => sub_eq_zero.mp (hz (i,j))) v hv w hw)
end
end KirchbergRordam.GenericRW.NoncommutingPair
end
end
end

end OAI
