import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteTypeExpandingEmbedding
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionSpectrumFiniteTrace

namespace OAI

/-! # Realizing an expanding eigenvalue after changing the coefficient field -/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup
open Polynomial

theorem charpoly_root_ne_zero
    {K : Type*} [Field K] {n : ℕ} (g : PolynomialMatrixGroup K n)
    {z : K} (hz : z ∈ (entries g).charpoly.roots) : z ≠ 0 := by
  intro he
  subst z
  have hr := (mem_roots (entries g).charpoly_monic.ne_zero).mp hz
  have hc : (entries g).charpoly.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact hr
  apply g.toGL.det_ne_zero
  change (entries g).det = 0
  rw [Matrix.det_eq_sign_charpoly_coeff, hc, mul_zero]

theorem valued_representation_of_nontorsion_eigenvalue
    {K G : Type} [Field K] [CharZero K] [Group G] [Group.FG G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (hι : Function.Injective ι)
    (a : G) (z : K) (hz : z ∈ (entries (ι a)).charpoly.roots)
    (hnt : ∀ m : ℕ, 0 < m → z ^ m ≠ 1) :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : CompleteSpace L)
      (_ : IsAlgClosed L) (ρ : G →* PolynomialMatrixGroup L n), Function.Injective ρ ∧
      ∃ w ∈ (entries (ρ a)).charpoly.roots, 1 < ‖w‖ := by
  classical
  obtain ⟨F₀, hF₀, he₀⟩ := exists_finite_coefficient_field ι
  let F := F₀ ⊔ IntermediateField.adjoin ℚ {z}
  have hF : F.FG := IntermediateField.fg_sup hF₀
    (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton z))
  let : Algebra.EssFiniteType ℚ F := IntermediateField.essFiniteType_iff.mpr hF
  have heF (g : G) (i j : Fin n) : entries (ι g) i j ∈ F :=
    SetLike.le_def.mp (show F₀ ≤ F from le_sup_left) (he₀ g i j)
  let ιF := restrictCoefficientField ι F heF
  have hιF : Function.Injective ιF := restrictCoefficientField_injective ι F heF hι
  let zF : F := ⟨z, SetLike.le_def.mp
    (show IntermediateField.adjoin ℚ {z} ≤ F from le_sup_right)
    (IntermediateField.mem_adjoin_simple_self ℚ z)⟩
  have hmap : (entries (ιF a)).map (algebraMap F K) = entries (ι a) := rfl
  have hzF : zF ∈ (entries (ιF a)).charpoly.roots := by
    apply (mem_roots (entries (ιF a)).charpoly_monic.ne_zero).mpr
    apply (algebraMap F K).injective
    rw [map_zero, ← eval_map_apply, ← Matrix.charpoly_map, hmap]
    exact (mem_roots (entries (ι a)).charpoly_monic.ne_zero).mp hz
  have hnF (m : ℕ) (hm : 0 < m) : zF ^ m ≠ 1 := by
    intro h
    exact hnt m hm (congrArg (fun t : F => (t : K)) h)
  obtain ⟨L, hL, hC, hA, f, hf⟩ := finiteType_nontorsion_expanding_embedding
    zF (charpoly_root_ne_zero (ιF a) hzF) hnF
  let : NontriviallyNormedField L := hL
  let : CompleteSpace L := hC
  let : IsAlgClosed L := hA
  let ρ := (scalarExtension f).comp ιF
  refine ⟨L, hL, hC, hA, ρ, (scalarExtension_injective f).comp hιF, f zF, ?_, hf⟩
  have hm : entries (ρ a) = (entries (ιF a)).map f := rfl
  rw [hm, Matrix.charpoly_map]
  apply (mem_roots ((entries (ιF a)).charpoly_monic.map f).ne_zero).mpr
  change ((entries (ιF a)).charpoly.map f).eval (f zF) = 0
  rw [eval_map_apply]
  have hr := (mem_roots (entries (ιF a)).charpoly_monic.ne_zero).mp hzF
  change (entries (ιF a)).charpoly.eval zF = 0 at hr
  rw [hr, map_zero]

theorem infinite_irreducible_fg_has_expanding_valued_representation
    {K G : Type} [Field K] [CharZero K] [IsAlgClosed K]
    [Group G] [Group.FG G] [Infinite G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (hι : Function.Injective ι)
    [Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (linearAction.toMonoidHom.comp ι))] :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : CompleteSpace L)
      (_ : IsAlgClosed L) (ρ : G →* PolynomialMatrixGroup L n), Function.Injective ρ ∧
      ∃ a : G, ∃ w ∈ (entries (ρ a)).charpoly.roots, 1 < ‖w‖ := by
  obtain ⟨a, z, hz, hn⟩ := infinite_irreducible_fg_has_nontorsion_eigenvalue ι hι
  obtain ⟨L, hL, hC, hA, ρ, hρ, w, hw, hnw⟩ :=
    valued_representation_of_nontorsion_eigenvalue ι hι a z hz hn
  exact ⟨L, hL, hC, hA, ρ, hρ, a, w, hw, hnw⟩

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
