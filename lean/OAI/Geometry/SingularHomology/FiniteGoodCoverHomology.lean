import OAI.Geometry.SingularHomology.FiniteSimplicialHomology

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340.FiniteGoodCover

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

def FiniteHomology (C : ChainComplex (ModuleCat ℝ) ℕ) : Prop :=
  (∀ n, FiniteDimensional ℝ (C.homology n)) ∧
    ∃ N, ∀ n, N ≤ n → IsZero (C.homology n)

lemma finiteDimensional_of_exact (S : ShortComplex (ModuleCat ℝ))
    (hS : S.Exact) [FiniteDimensional ℝ S.X₁] [FiniteDimensional ℝ S.X₃] :
    FiniteDimensional ℝ S.X₂ := by
  have : FiniteDimensional ℝ (LinearMap.ker S.g.hom) := by
    rw [← hS.moduleCat_range_eq_ker]
    infer_instance
  have : FiniteDimensional ℝ (S.X₂ ⧸ LinearMap.ker S.g.hom) :=
    Module.Finite.equiv S.g.hom.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker S.g.hom)

lemma isZero_of_exact (S : ShortComplex (ModuleCat ℝ)) (hS : S.Exact)
    (h₁ : IsZero S.X₁) (h₃ : IsZero S.X₃) : IsZero S.X₂ := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have := ModuleCat.isZero_iff_subsingleton.mp h₁
  have := ModuleCat.isZero_iff_subsingleton.mp h₃
  have hz : ∀ x : S.X₂, x = 0 := by
    intro x
    obtain ⟨y, hy⟩ := S.moduleCat_exact_iff.mp hS x (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, map_zero] at hy
    exact hy.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

lemma finiteHomology_of_iso {C D : ChainComplex (ModuleCat ℝ) ℕ}
    (e : C ≅ D) (hC : FiniteHomology C) : FiniteHomology D := by
  constructor
  · intro n
    have := hC.1 n
    let e' : C.homology n ≃ₗ[ℝ] D.homology n :=
      ((HomologicalComplex.homologyFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) n).mapIso e).toLinearEquiv
    exact Module.Finite.equiv e'
  · obtain ⟨N, hN⟩ := hC.2
    refine ⟨N, fun n hn => ?_⟩
    exact IsZero.of_iso (hN n hn)
      (((HomologicalComplex.homologyFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) n).mapIso e).symm)

lemma finiteHomology_biprod {C D : ChainComplex (ModuleCat ℝ) ℕ}
    (hC : FiniteHomology C) (hD : FiniteHomology D) : FiniteHomology (C ⊞ D) := by
  have e (n : ℕ) : (C ⊞ D).homology n ≅
      ModuleCat.of ℝ (C.homology n × D.homology n) :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) n).mapBiprod C D ≪≫
      ModuleCat.biprodIsoProd _ _
  constructor
  · intro n
    have := hC.1 n
    have := hD.1 n
    exact Module.Finite.equiv (e n).toLinearEquiv.symm
  · obtain ⟨NC, hNC⟩ := hC.2
    obtain ⟨ND, hND⟩ := hD.2
    refine ⟨max NC ND, fun n hn => ?_⟩
    have := ModuleCat.isZero_iff_subsingleton.mp (hNC n ((le_max_left _ _).trans hn))
    have := ModuleCat.isZero_iff_subsingleton.mp (hND n ((le_max_right _ _).trans hn))
    exact IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr inferInstance) (e n)

lemma finiteHomology_of_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat ℝ) ℕ)) (hS : S.ShortExact)
    (h₁ : FiniteHomology S.X₁) (h₂ : FiniteHomology S.X₂) : FiniteHomology S.X₃ := by
  constructor
  · intro n
    cases n with
    | zero =>
      have := h₂.1 0
      have := hS.epi_g
      have : Epi (HomologicalComplex.homologyMap S.g 0) :=
        HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by simp)
      exact Module.Finite.of_surjective (HomologicalComplex.homologyMap S.g 0).hom
        ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    | succ n =>
      have := h₂.1 (n + 1)
      have := h₁.1 n
      exact finiteDimensional_of_exact _ (hS.homology_exact₃ (n + 1) n (by simp))
  · obtain ⟨N₁, hN₁⟩ := h₁.2
    obtain ⟨N₂, hN₂⟩ := h₂.2
    refine ⟨max (N₁ + 1) N₂, fun n hn => ?_⟩
    have hn₁ : N₁ + 1 ≤ n := (le_max_left _ _).trans hn
    have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
    cases n with
    | zero => omega
    | succ n =>
      exact isZero_of_exact _ (hS.homology_exact₃ (n + 1) n (by simp))
        (hN₂ (n + 1) hn₂) (hN₁ n (by omega))

lemma finiteHomology_of_quasiIso {C D : ChainComplex (ModuleCat ℝ) ℕ}
    (f : C ⟶ D) [QuasiIso f] (hC : FiniteHomology C) : FiniteHomology D := by
  have e (n : ℕ) : C.homology n ≅ D.homology n :=
    asIso (HomologicalComplex.homologyMap f n)
  constructor
  · intro n
    have := hC.1 n
    exact Module.Finite.equiv (e n).toLinearEquiv
  · obtain ⟨N, hN⟩ := hC.2
    exact ⟨N, fun n hn => IsZero.of_iso (hN n hn) (e n).symm⟩

lemma finiteHomology_of_finite_simplicial (X : SSet) [X.Finite] :
    FiniteHomology (X.chainComplex (ModuleCat.of ℝ ℝ)) := by
  constructor
  · exact finiteDimensional_real_simplicial_homology X
  · obtain ⟨N, hN⟩ := real_simplicial_homology_finite_support X
    exact ⟨N, fun n hn => ModuleCat.isZero_iff_subsingleton.mpr (hN n hn)⟩

theorem property_sup_of_inf
    {L ι : Type*} [DistribLattice L] [OrderBot L] [OrderTop L]
    (P : L → Prop) (hbot : P ⊥)
    (hunion : ∀ a b, P a → P b → P (a ⊓ b) → P (a ⊔ b))
    (s : Finset ι) (f : ι → L)
    (hinter : ∀ t : Finset ι, t ⊆ s → t.Nonempty → P (t.inf f)) :
    P (s.sup f) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => simpa using hbot
  | @insert a s ha ih =>
    have hsingle : P (f a) := by
      simpa using hinter {a} (by simp) (by simp)
    have hrest : P (s.sup f) :=
      ih f (fun t hts ht => hinter t (hts.trans (Finset.subset_insert _ _)) ht)
    have hmeet : P (s.sup (fun i => f a ⊓ f i)) := by
      apply ih
      intro t hts ht
      have heq : t.inf (fun i => f a ⊓ f i) = (insert a t).inf f := by
        rw [Finset.inf_insert]
        change t.inf ((fun _ => f a) ⊓ f) = _
        rw [Finset.inf_inf, Finset.inf_const ht]
      rw [heq]
      exact hinter (insert a t) (Finset.insert_subset_insert a hts)
        (Finset.insert_nonempty a t)
    rw [← Finset.sup_inf_distrib_left] at hmeet
    rw [Finset.sup_insert]
    exact hunion _ _ hsingle hrest hmeet

end Problem340.FiniteGoodCover

end

end OAI
