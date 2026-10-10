import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardSpin

namespace OAI

/-! The canonical, norm-preserving embedding of the spin sector in Fock space. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

theorem siteMode_val (m : ℕ) (i : Fin (m + 1)) (σ : Fin 2) :
    (siteMode m i σ : ℕ) = (σ : ℕ) + 2 * (i : ℕ) := rfl

def spinModeOrderEmbedding (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    Fin (m + 1) ↪o Fin ((2 * m + 1) + 1) :=
  OrderEmbedding.ofStrictMono (fun i => siteMode m i (s i)) (by
    intro i j hij
    apply Fin.lt_def.mpr
    rw [siteMode_val, siteMode_val]
    have hi := (s i).isLt
    have hj := (s j).isLt
    have hij' := Fin.lt_def.mp hij
    omega)

def spinOccupationSet (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    Finset (Fin ((2 * m + 1) + 1)) :=
  (Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s)).val

theorem spinOccupationSet_injective (m : ℕ) : Function.Injective (spinOccupationSet m) := by
  intro s t h
  have hS : Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s) =
      Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m t) := Subtype.ext h
  have hE := Set.powersetCard.ofFinEmbEquiv.injective hS
  funext i
  have hi := congrArg (fun f : Fin (m + 1) ↪o Fin ((2 * m + 1) + 1) => f i) hE
  exact ((siteMode_eq_iff m i i (s i) (t i)).mp hi).2

/-- The ordered spin wedge is exactly a canonical occupation-basis
vector, with no arbitrary normalization or phase. -/
theorem spinWedge_eq_fockBasis (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    spinWedge m s = fockBasis (2 * m + 1) (spinOccupationSet m s) := by
  let S := Set.powersetCard.ofFinEmbEquiv (spinModeOrderEmbedding m s)
  change wedgeModes (m + 1) (fun i => siteMode m i (s i)) =
    (Pi.basisFun ℂ (Fin ((2 * m + 1) + 1))).ExteriorAlgebra S.val
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family, S, Equiv.symm_apply_apply]
  unfold wedgeModes
  congr 1
  funext i
  rw [Function.comp_apply, Pi.basisFun_apply]
  rfl

def spinEmbedding (m : ℕ) : SourceSpinVector (m + 1) →ₗ[ℂ] Space (2 * m + 1) where
  toFun u := ∑ s, u s • spinWedge m s
  map_add' u v := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c u := by simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

theorem spinEmbedding_coordinate (m : ℕ) (u : SourceSpinVector (m + 1))
    (s : SourceSpinBasis (m + 1)) :
    (fockBasis (2 * m + 1)).repr (spinEmbedding m u) (spinOccupationSet m s) = u s := by
  simp [spinEmbedding, spinWedge_eq_fockBasis, Module.Basis.repr_self, Finsupp.single_apply,
    (spinOccupationSet_injective m).eq_iff]

theorem spinEmbedding_coordinate_outside (m : ℕ) (u : SourceSpinVector (m + 1))
    (A : Finset (Fin ((2 * m + 1) + 1)))
    (hA : ∀ s, spinOccupationSet m s ≠ A) :
    (fockBasis (2 * m + 1)).repr (spinEmbedding m u) A = 0 := by
  simp [spinEmbedding, spinWedge_eq_fockBasis, Module.Basis.repr_self, hA]

theorem spinEmbedding_injective (m : ℕ) : Function.Injective (spinEmbedding m) := by
  intro u v h
  funext s
  have hs := congrArg
    (fun x => (fockBasis (2 * m + 1)).repr x (spinOccupationSet m s)) h
  simpa only [spinEmbedding_coordinate] using hs

theorem spinEmbedding_swap (m : ℕ) (u : SourceSpinVector (m + 1))
    (i j : Fin (m + 1)) :
    (∑ s, u s • spinWedge m (sourceSpinSwap i j s)) =
      spinEmbedding m (fun s => u (sourceSpinSwap i j s)) := by
  change (∑ s, u s • spinWedge m (sourceSpinSwap i j s)) =
    ∑ s, u (sourceSpinSwap i j s) • spinWedge m s
  have h := (sourceSpinSwap i j).sum_comp
    (fun s => u s • spinWedge m (sourceSpinSwap i j s))
  have hswap (s : SourceSpinBasis (m + 1)) :
      sourceSpinSwap i j (sourceSpinSwap i j s) = s := sourceSpinSwap_involutive i j s
  simp_rw [hswap] at h
  exact h.symm

/-- The actual Fock Heisenberg operator intertwines the source action
on arbitrary, possibly entangled, spin vectors. -/
theorem spinEmbedding_heisenberg (m : ℕ) (u : SourceSpinVector (m + 1))
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    siteHeisenberg (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)
        (spinEmbedding m u) = spinEmbedding m (sourceHeisenbergAction i j u) := by
  change siteHeisenberg (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)
    (∑ s, u s • spinWedge m s) = _
  rw [map_sum]
  simp_rw [map_smul, siteHeisenberg_spinWedge m _ i j hij]
  have hpoint (s : SourceSpinBasis (m + 1)) :
      u s • ((2 : ℂ) • spinWedge m (sourceSpinSwap i j s) - spinWedge m s) =
        (2 : ℂ) • (u s • spinWedge m (sourceSpinSwap i j s)) - u s • spinWedge m s := by
    simp [smul_sub, smul_smul, mul_comm]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, spinEmbedding_swap]
  change (2 : ℂ) • spinEmbedding m (fun s => u (sourceSpinSwap i j s)) - spinEmbedding m u = _
  rw [← map_smul, ← map_sub]
  congr 1

def fockMass {Q : ℕ} (x : Space Q) : ℝ :=
  ∑ A, Complex.normSq ((fockBasis Q).repr x A)

/-- The embedding preserves the entire many-spin squared norm. -/
theorem spinEmbedding_mass (m : ℕ) (u : SourceSpinVector (m + 1)) :
    fockMass (spinEmbedding m u) = sourceSpinMass u := by
  classical
  let S := Finset.univ.image (spinOccupationSet m)
  have hsub : S ⊆ Finset.univ := Finset.subset_univ _
  have hsum : (∑ A ∈ S, Complex.normSq ((fockBasis (2 * m + 1)).repr (spinEmbedding m u) A)) =
      ∑ A, Complex.normSq ((fockBasis (2 * m + 1)).repr (spinEmbedding m u) A) := by
    apply Finset.sum_subset hsub
    intro A _ hAS
    have hA : ∀ s, spinOccupationSet m s ≠ A := by
      intro s hs
      exact hAS (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, hs⟩)
    rw [spinEmbedding_coordinate_outside m u A hA]
    simp
  unfold fockMass
  rw [← hsum]
  unfold S
  rw [Finset.sum_image]
  · simp only [spinEmbedding_coordinate]
    rfl
  · intro s _ t _ hst
    exact spinOccupationSet_injective m hst

end ContinuumCoulomb.HubbardGlobal

end

end OAI
