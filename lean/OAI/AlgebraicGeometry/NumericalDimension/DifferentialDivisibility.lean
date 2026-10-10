import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.DifferentialBaseChange

namespace OAI

/-! Differential Divisibility. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits

namespace NumericalDimensionOne

lemma alternating_snc_divisible
    {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι]
    (f : M [⋀^ι]→ₗ[R] N) (S : Finset ι) (a : ι → R)
    (t : R) (x : M) (v : ι → M) :
    ∃ w : N, f (S.piecewise (fun i => a i • x + t • v i) v) =
      t ^ (S.card - 1) • w := by
  classical
  let v' : ι → M := S.piecewise (fun i => t • v i) v
  let P : Submodule R N := LinearMap.range (LinearMap.lsmul R N (t ^ (S.card - 1)))
  have hterm : ∀ s ∈ S.powerset, f (s.piecewise (fun i => a i • x) v') ∈ P := by
    intro s hs
    have hsS : s ⊆ S := Finset.mem_powerset.mp hs
    by_cases htwo : 2 ≤ s.card
    · obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp htwo
      have hz : f (s.piecewise (fun _ => x) v') = 0 :=
        f.map_eq_zero_of_eq _ (by simp [hi, hj]) hij
      have heq : s.piecewise (fun i => a i • x) v' =
          s.piecewise (fun i => a i • (s.piecewise (fun _ => x) v') i)
            (s.piecewise (fun _ => x) v') := by
        ext z
        by_cases hz : z ∈ s <;> simp [hz]
      rw [heq]
      change f.toMultilinearMap _ ∈ P
      rw [f.toMultilinearMap.map_piecewise_smul]
      change (∏ i ∈ s, a i) • f (s.piecewise (fun _ => x) v') ∈ P
      rw [hz, smul_zero]
      exact P.zero_mem
    · let D := S \ s
      have hcard : S.card - 1 ≤ D.card := by
        dsimp [D]
        rw [Finset.card_sdiff_of_subset hsS]
        omega
      let z := s.piecewise (fun i => a i • x) v
      have heq : s.piecewise (fun i => a i • x) v' =
          D.piecewise (fun i => t • z i) z := by
        ext i
        by_cases hi : i ∈ s
        · have hiS := hsS hi
          simp [D, z, v', hi, hiS]
        · by_cases hiS : i ∈ S <;> simp [D, z, v', hi, hiS]
      rw [heq]
      change f.toMultilinearMap _ ∈ P
      rw [f.toMultilinearMap.map_piecewise_smul]
      simp only [Finset.prod_const]
      refine ⟨t ^ (D.card - (S.card - 1)) • f z, ?_⟩
      change t ^ (S.card - 1) • (t ^ (D.card - (S.card - 1)) • f z) = _
      rw [smul_smul, ← pow_add, Nat.add_sub_of_le hcard]
      rfl
  have hsum : (∑ s ∈ S.powerset, f (s.piecewise (fun i => a i • x) v')) ∈ P :=
    Submodule.sum_mem P hterm
  change (∑ s ∈ S.powerset, f.toMultilinearMap (s.piecewise (fun i => a i • x) v')) ∈ P at hsum
  rw [← f.toMultilinearMap.map_piecewise_add] at hsum
  have heq : S.piecewise ((fun i => a i • x) + v') v' =
      S.piecewise (fun i => a i • x + t • v i) v := by
    ext i
    by_cases hi : i ∈ S <;> simp [v', hi]
  rw [heq] at hsum
  obtain ⟨w, hw⟩ := hsum
  exact ⟨w, hw.symm⟩

theorem topDifferentialMap_divisible_of_coordinate_equations
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    {n : ℕ} (b : Module.Basis (Fin n) A Ω[A⁄k])
    (S : Finset (Fin n)) (g : Fin n → A) (t : B) (u : Fin n → B)
    (e : Fin n → ℕ) (he : ∀ i ∈ S, 0 < e i)
    (hg : ∀ i ∈ S, KaehlerDifferential.D k A (g i) = b i)
    (hpull : ∀ i ∈ S, algebraMap A B (g i) = u i * t ^ e i)
    (v : ⋀[A]^n Ω[A⁄k]) :
    ∃ w : ⋀[B]^n Ω[B⁄k],
      topDifferentialMap k A B n v = t ^ ((∑ i ∈ S, e i) - 1) • w := by
  classical
  let L := KaehlerDifferential.map k k A B
  let F := topDifferentialMap k A B n
  let v₀ : Fin n → Ω[B⁄k] := S.piecewise (fun i => KaehlerDifferential.D k B (u i))
    (fun i => L (b i))
  let z : Fin n → Ω[B⁄k] := S.piecewise
    (fun i => ((e i : B) * u i) • KaehlerDifferential.D k B t + t • v₀ i) v₀
  have hd : ∀ i ∈ S, L (b i) = t ^ (e i - 1) • z i := by
    intro i hi
    have hp : t ^ e i = t ^ (e i - 1) * t := by
      rw [← pow_succ, Nat.sub_add_cancel (he i hi)]
    dsimp [L]
    rw [← hg i hi, KaehlerDifferential.map_D, hpull i hi,
      Derivation.leibniz, Derivation.leibniz_pow]
    simp only [z, v₀, Finset.piecewise, ite_eq_left hi, smul_add, smul_smul, hp]
    simp only [← Nat.cast_smul_eq_nsmul B, smul_smul]
    module
  have hb : (fun i => L (b i)) =
      S.piecewise (fun i => t ^ (e i - 1) • z i) z := by
    ext i
    by_cases hi : i ∈ S
    · simpa only [Finset.piecewise, ite_eq_left hi] using hd i hi
    · simp [z, v₀, hi]
  obtain ⟨w, hw⟩ := alternating_snc_divisible (exteriorPower.ιMulti B n) S
    (fun i => (e i : B) * u i) t (KaehlerDifferential.D k B t) v₀
  change exteriorPower.ιMulti B n z = t ^ (S.card - 1) • w at hw
  have hsum : (∑ i ∈ S, e i) = (∑ i ∈ S, (e i - 1)) + S.card := by
    calc
      _ = ∑ i ∈ S, ((e i - 1) + 1) :=
        Finset.sum_congr rfl (fun i hi => (Nat.sub_add_cancel (he i hi)).symm)
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hexp : (∑ i ∈ S, (e i - 1)) + (S.card - 1) = (∑ i ∈ S, e i) - 1 := by
    by_cases hS : S.Nonempty
    · have := Finset.card_pos.mpr hS
      omega
    · have hS' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [hS']
  have hvol : F (exteriorPower.ιMulti A n b) = t ^ ((∑ i ∈ S, e i) - 1) • w := by
    dsimp [F]
    rw [topDifferentialMap_ιMulti]
    change exteriorPower.ιMulti B n (fun i => L (b i)) = _
    rw [hb]
    change (exteriorPower.ιMulti B n).toMultilinearMap _ = _
    rw [MultilinearMap.map_piecewise_smul]
    change (∏ i ∈ S, t ^ (e i - 1)) • exteriorPower.ιMulti B n z = _
    rw [hw, Finset.prod_pow_eq_pow_sum, smul_smul, ← pow_add, hexp]
  obtain ⟨c, hc⟩ := exterior_volume_spans b v
  refine ⟨c • w, ?_⟩
  change F v = _
  rw [hc, map_smul, hvol]
  exact smul_comm c _ w

theorem topDifferentialMap_divisible_of_independent_equations
    {k A B ι : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Fintype ι] {n : ℕ} (b : Module.Basis (Fin n) A Ω[A⁄k])
    (σ : ι ↪ Fin n) (g : ι → A) (t : B) (u : ι → B) (e : ι → ℕ)
    (hg : ∀ i, KaehlerDifferential.D k A (g i) = b (σ i))
    (hpull : ∀ i, algebraMap A B (g i) = u i * t ^ e i)
    (v : ⋀[A]^n Ω[A⁄k]) :
    ∃ w : ⋀[B]^n Ω[B⁄k],
      topDifferentialMap k A B n v = t ^ ((∑ i, e i) - 1) • w := by
  classical
  let I := Finset.univ.filter (fun i => 0 < e i)
  let S := I.image σ
  let g' := Function.extend σ g (fun _ => 0)
  let u' := Function.extend σ u (fun _ => 1)
  let e' := Function.extend σ e (fun _ => 0)
  have he' : ∀ j ∈ S, 0 < e' j := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    simpa only [e', σ.injective.extend_apply] using (Finset.mem_filter.mp hi).2
  have hg' : ∀ j ∈ S, KaehlerDifferential.D k A (g' j) = b j := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    simpa only [g', σ.injective.extend_apply] using hg i
  have hpull' : ∀ j ∈ S, algebraMap A B (g' j) = u' j * t ^ e' j := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    simpa only [g', u', e', σ.injective.extend_apply] using hpull i
  have hsum : (∑ j ∈ S, e' j) = ∑ i, e i := by
    change (∑ j ∈ I.image σ, e' j) = _
    rw [Finset.sum_image (fun i _ j _ h => σ.injective h)]
    simp only [e', σ.injective.extend_apply]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have : ¬0 < e i := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  obtain ⟨w, hw⟩ := topDifferentialMap_divisible_of_coordinate_equations b S g' t u' e'
    he' hg' hpull' v
  exact ⟨w, by simpa only [hsum] using hw⟩

end NumericalDimensionOne

end OAI
