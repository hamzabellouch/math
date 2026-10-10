import Mathlib
import OAI.Analysis.HardSphere.FormDomain.Basic
import OAI.Analysis.HardSphere.FormDomain.Energy

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
namespace HardSphere

theorem IsGroundVector.first_variation {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) (hb : bosonic v.1) :
    (∑ p : Direction N, inner ℂ (u.2 p) (v.2 p)) =
      (energy u : ℂ) * inner ℂ u.1 v.1 := by
  apply Variational.ground_pairing (groundFormSubmodule N L a) u
  · exact mem_groundFormSubmodule.mpr ⟨hu.1, hu.2.1⟩
  · exact hu.2.2.1
  · intro w hw hn
    exact hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn
  · exact mem_groundFormSubmodule.mpr ⟨hv, hb⟩

theorem IsGroundVector.rayleigh {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) (hb : bosonic v.1) :
    energy u * ‖v.1‖ ^ 2 ≤ energy v := by
  exact Variational.rayleigh (groundFormSubmodule N L a) u
    (fun w hw hn ↦ hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn) v
    (mem_groundFormSubmodule.mpr ⟨hv, hb⟩)

@[simp] lemma torusDistance_comm (L : Length) (x y : Torus L) :
    torusDistance L x y = torusDistance L y x := by
  simp only [torusDistance, dist_comm]

lemma allowed_iff_ne {N : ℕ} {L : Length} {a : ℝ} {X : Configuration N L} :
    X ∈ allowed N L a ↔ ∀ i j, i ≠ j → a < torusDistance L (X i) (X j) := by
  constructor
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact h i j hlt
    · simpa only [torusDistance_comm] using h j i hgt
  · intro h i j hij
    exact h i j (ne_of_lt hij)

lemma allowed_permute {N : ℕ} {L : Length} {a : ℝ}
    (σ : Equiv.Perm (Fin N)) (X : Configuration N L) :
    permuteConfiguration σ X ∈ allowed N L a ↔ X ∈ allowed N L a := by
  simp only [allowed_iff_ne, permuteConfiguration]
  constructor
  · intro h i j hij
    simpa using h (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij)
  · intro h i j hij
    exact h (σ i) (σ j) (σ.injective.ne hij)

def permuteLift {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    LiftedConfiguration N ≃L[ℝ] LiftedConfiguration N where
  toFun X := fun i ↦ X (σ i)
  invFun X := fun i ↦ X (σ.symm i)
  left_inv X := by funext i; simp
  right_inv X := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_pi fun _ ↦ continuous_apply _
  continuous_invFun := continuous_pi fun _ ↦ continuous_apply _

lemma permuteLift_direction {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : Direction N) :
    permuteLift σ (Pi.single p.1 (Pi.single p.2 1)) =
      Pi.single (σ.symm p.1) (Pi.single p.2 1) := by
  ext i j
  change (Pi.single p.1 (Pi.single p.2 (1 : ℝ)) : LiftedConfiguration N) (σ i) j = _
  by_cases h : i = σ.symm p.1
  · subst i; simp
  · have h' : σ i ≠ p.1 := fun hh ↦ h ((Equiv.eq_symm_apply σ).mpr hh)
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

lemma coordDerivative_permute {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest N L a) (σ : Equiv.Perm (Fin N)) (p : Direction N) :
    coordDerivative N L (f.toFun ∘ permuteConfiguration σ) p =
      coordDerivative N L f.toFun (σ.symm p.1, p.2) ∘ permuteConfiguration σ := by
  funext X
  change (fderiv ℝ ((fun Y ↦ f.toFun (project N L Y)) ∘ permuteLift σ)
    (representative N L X)) (Pi.single p.1 (Pi.single p.2 1)) = _
  rw [fderiv_comp _ (f.smooth.differentiable (by simp)).differentiableAt
    (permuteLift σ).differentiableAt, (permuteLift σ).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    permuteLift_direction]
  rfl

def SmoothTest.permute {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest N L a) (σ : Equiv.Perm (Fin N)) : SmoothTest N L a where
  toFun := f.toFun ∘ permuteConfiguration σ
  smooth := f.smooth.comp (permuteLift σ).contDiff
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := by
    intro X hX
    apply (allowed_permute σ X).mp
    exact f.support_allowed
      (tsupport_comp_subset_preimage (f := permuteConfiguration σ) f.toFun (continuous_pi fun i ↦ continuous_apply (σ i)) hX)
  memLp := f.memLp.comp_measurePreserving (measurePreserving_permute σ)
  partial_memLp := by
    intro p
    rw [coordDerivative_permute]
    exact (f.partial_memLp (σ.symm p.1, p.2)).comp_measurePreserving
      (measurePreserving_permute σ)

section

attribute [local instance] scalarL2_addCommMonoid scalarL2_module

lemma continuous_permutationPullback_jet {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N)) :
    Continuous (fun u : Jet N L ↦ (permutationPullback σ u.1,
      fun direction : Direction N ↦
        permutationPullback σ (u.2 (σ.symm direction.1, direction.2)))) := by
  let pullback : ScalarL2 N L →ₗᵢ[ℂ] ScalarL2 N L :=
    Lp.compMeasurePreservingₗᵢ ℂ (permuteConfiguration σ) (measurePreserving_permute σ)
  exact (pullback.continuous.comp continuous_fst).prodMk
    (continuous_pi fun p ↦ pullback.continuous.comp ((continuous_apply _).comp continuous_snd))

def permutationJet {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N)) :
    Jet N L →L[ℂ] Jet N L where
  toFun u := (permutationPullback σ u.1,
    fun p ↦ permutationPullback σ (u.2 (σ.symm p.1, p.2)))
  map_add' _ _ := by simp [map_add]; rfl
  map_smul' _ _ := by simp [map_smul]; rfl
  cont := continuous_permutationPullback_jet σ

end

lemma SmoothTest.jet_permute {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest N L a) (σ : Equiv.Perm (Fin N)) :
    (f.permute σ).jet = permutationJet σ f.jet := by
  apply Prod.ext
  · apply Lp.ext
    exact (MemLp.coeFn_toLp (f.permute σ).memLp).trans
      ((Lp.coeFn_compMeasurePreserving f.jet.1 (measurePreserving_permute σ)).trans
        ((measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
          (MemLp.coeFn_toLp f.memLp))).symm
  · funext p
    apply Lp.ext
    have h := (measurePreserving_permute (L := L) σ).quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp (f.partial_memLp (σ.symm p.1, p.2)))
    refine (MemLp.coeFn_toLp ((f.permute σ).partial_memLp p)).trans ?_
    change coordDerivative N L (f.toFun ∘ permuteConfiguration σ) p =ᵐ[volume] _
    rw [coordDerivative_permute]
    exact ((Lp.coeFn_compMeasurePreserving _ (measurePreserving_permute σ)).trans h).symm

lemma permutationJet_mem_domain {N : ℕ} {L : Length} {a : ℝ}
    (σ : Equiv.Perm (Fin N)) {u : Jet N L} (hu : u ∈ dirichletDomain N L a) :
    permutationJet σ u ∈ dirichletDomain N L a := by
  apply map_mem_closure (permutationJet σ).continuous hu
  rintro _ ⟨f, rfl⟩
  exact ⟨f.permute σ, f.jet_permute σ⟩

lemma energy_permutationJet {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N))
    (u : Jet N L) : energy (permutationJet σ u) = energy u := by
  change (∑ p : Direction N, ‖Lp.compMeasurePreserving _ (measurePreserving_permute σ)
    (u.2 (σ.symm p.1, p.2))‖ ^ 2) = _
  simp only [Lp.norm_compMeasurePreserving]
  exact Equiv.sum_comp (Equiv.prodCongr σ.symm (Equiv.refl (Fin 3)))
    (fun p ↦ ‖u.2 p‖ ^ 2)

end HardSphere

end

end OAI
