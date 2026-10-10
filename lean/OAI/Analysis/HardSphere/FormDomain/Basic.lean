import Mathlib
import OAI.Analysis.HardSphere.Model

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere

lemma coordDerivative_add {N : ℕ} {L : Length} {a : ℝ}
    (f g : SmoothTest N L a) (p : Direction N) :
    coordDerivative N L (f.toFun + g.toFun) p =
      coordDerivative N L f.toFun p + coordDerivative N L g.toFun p := by
  funext X
  simp only [coordDerivative, Pi.add_apply]
  rw [fderiv_fun_add (f.smooth.differentiable (by simp)).differentiableAt
    (g.smooth.differentiable (by simp)).differentiableAt]
  rfl

lemma coordDerivative_smul {N : ℕ} {L : Length} {a : ℝ}
    (c : ℂ) (f : SmoothTest N L a) (p : Direction N) :
    coordDerivative N L (c • f.toFun) p = c • coordDerivative N L f.toFun p := by
  funext X
  simp only [coordDerivative, Pi.smul_apply]
  rw [fderiv_fun_const_smul (f.smooth.differentiable (by simp)).differentiableAt c]
  rfl

lemma coordDerivative_zero (N : ℕ) (L : Length) (p : Direction N) :
    coordDerivative N L 0 p = 0 := by
  funext X
  simp [coordDerivative]

def SmoothTest.zero (N : ℕ) (L : Length) (a : ℝ) : SmoothTest N L a where
  toFun := 0
  smooth := contDiff_const
  compact := HasCompactSupport.zero
  support_allowed := by simp
  memLp := MemLp.zero
  partial_memLp := by
    intro p
    rw [coordDerivative_zero]
    exact MemLp.zero

def SmoothTest.add {N : ℕ} {L : Length} {a : ℝ}
    (f g : SmoothTest N L a) : SmoothTest N L a where
  toFun := f.toFun + g.toFun
  smooth := f.smooth.add g.smooth
  compact := f.compact.add g.compact
  support_allowed := (tsupport_add _ _).trans (union_subset f.support_allowed g.support_allowed)
  memLp := f.memLp.add g.memLp
  partial_memLp := by
    intro p
    rw [coordDerivative_add]
    exact (f.partial_memLp p).add (g.partial_memLp p)

def SmoothTest.smul {N : ℕ} {L : Length} {a : ℝ}
    (c : ℂ) (f : SmoothTest N L a) : SmoothTest N L a where
  toFun := c • f.toFun
  smooth := f.smooth.const_smul c
  compact := f.compact.smul_left
  support_allowed := (tsupport_smul_subset_right (fun _ ↦ c) f.toFun).trans f.support_allowed
  memLp := f.memLp.const_smul c
  partial_memLp := by
    intro p
    rw [coordDerivative_smul]
    exact (f.partial_memLp p).const_smul c

@[simp] lemma SmoothTest.jet_zero (N : ℕ) (L : Length) (a : ℝ) :
    (SmoothTest.zero N L a).jet = 0 := by
  apply Prod.ext
  · rfl
  · funext p
    change MemLp.toLp (coordDerivative N L 0 p) ((SmoothTest.zero N L a).partial_memLp p) = 0
    simp only [coordDerivative_zero, MemLp.toLp_zero]

@[simp] lemma SmoothTest.jet_add {N : ℕ} {L : Length} {a : ℝ}
    (f g : SmoothTest N L a) : (f.add g).jet = f.jet + g.jet := by
  apply Prod.ext
  · rfl
  · funext p
    change _ = (f.partial_memLp p).toLp _ + (g.partial_memLp p).toLp _
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr ((f.add g).partial_memLp p)
      ((f.partial_memLp p).add (g.partial_memLp p)) ?_
    exact Filter.Eventually.of_forall (congrFun (coordDerivative_add f g p))

@[simp] lemma SmoothTest.jet_smul {N : ℕ} {L : Length} {a : ℝ}
    (c : ℂ) (f : SmoothTest N L a) : (f.smul c).jet = c • f.jet := by
  apply Prod.ext
  · rfl
  · funext p
    change _ = c • (f.partial_memLp p).toLp _
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr ((f.smul c).partial_memLp p)
      ((f.partial_memLp p).const_smul c) ?_
    exact Filter.Eventually.of_forall (congrFun (coordDerivative_smul c f p))

def smoothGraph (N : ℕ) (L : Length) (a : ℝ) : Submodule ℂ (Jet N L) where
  carrier := Set.range (SmoothTest.jet (N := N) (L := L) (a := a))
  zero_mem' := ⟨SmoothTest.zero N L a, SmoothTest.jet_zero N L a⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.add g, f.jet_add g⟩
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    exact ⟨f.smul c, f.jet_smul c⟩

def dirichletSubmodule (N : ℕ) (L : Length) (a : ℝ) : Submodule ℂ (Jet N L) :=
  (smoothGraph N L a).topologicalClosure

@[simp] lemma mem_dirichletSubmodule {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L} :
    u ∈ dirichletSubmodule N L a ↔ u ∈ dirichletDomain N L a := Iff.rfl

def permuteConfiguration {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N))
    (X : Configuration N L) : Configuration N L := fun i ↦ X (σ i)

lemma measurePreserving_permute {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (permuteConfiguration (L := L) σ) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin N ↦ Torus L) σ.symm
  convert h using 1
  funext X i
  simp [permuteConfiguration, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

section

attribute [local instance] scalarL2_addCommMonoid scalarL2_module

def permutationPullback {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N)) :
    ScalarL2 N L →ₗ[ℂ] ScalarL2 N L :=
  Lp.compMeasurePreservingₗ ℂ _ (measurePreserving_permute σ)

end

lemma bosonic_iff_pullback {N : ℕ} {L : Length} (ψ : ScalarL2 N L) :
    bosonic ψ ↔ ∀ σ, permutationPullback σ ψ = ψ := by
  have hae (σ : Equiv.Perm (Fin N)) :
      (permutationPullback σ ψ : Configuration N L → ℂ) =ᵐ[volume]
        fun X ↦ ψ (permuteConfiguration σ X) :=
    Lp.coeFn_compMeasurePreserving ψ (measurePreserving_permute σ)
  constructor
  · intro h σ
    exact Lp.ext ((hae σ).trans (h σ))
  · intro h σ
    have hh := hae σ
    rw [h σ] at hh
    exact hh.symm

section

attribute [local instance] scalarL2_normedAddCommGroup scalarL2_module

def bosonicSubmodule (N : ℕ) (L : Length) : Submodule ℂ (ScalarL2 N L) :=
  ⨅ σ : Equiv.Perm (Fin N),
    @LinearMap.ker ℂ ℂ (ScalarL2 N L) (ScalarL2 N L)
      Complex.instSemiring Complex.instSemiring
      (scalarL2_normedAddCommGroup N L).toAddCommMonoid
      (scalarL2_normedAddCommGroup N L).toAddCommMonoid
      (scalarL2_module N L) (scalarL2_module N L) (RingHom.id ℂ)
      (@HSub.hSub _ _ _
        (@instHSub _ (@LinearMap.instSub ℂ ℂ (ScalarL2 N L) (ScalarL2 N L)
          Complex.instSemiring Complex.instSemiring
          (scalarL2_normedAddCommGroup N L).toAddCommMonoid
          (scalarL2_normedAddCommGroup N L).toAddCommGroup
          (scalarL2_module N L) (scalarL2_module N L) (RingHom.id ℂ)))
        (permutationPullback σ)
        (@LinearMap.id ℂ (ScalarL2 N L) Complex.instSemiring
          (scalarL2_normedAddCommGroup N L).toAddCommMonoid (scalarL2_module N L)))

@[simp] lemma mem_bosonicSubmodule {N : ℕ} {L : Length} {ψ : ScalarL2 N L} :
    ψ ∈ bosonicSubmodule N L ↔ bosonic ψ := by
  simp only [bosonicSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact (bosonic_iff_pullback ψ).symm

end

def groundFormSubmodule (N : ℕ) (L : Length) (a : ℝ) : Submodule ℂ (Jet N L) :=
  dirichletSubmodule N L a ⊓
    (bosonicSubmodule N L).comap (LinearMap.fst ℂ (ScalarL2 N L) (Direction N → ScalarL2 N L))

@[simp] lemma mem_groundFormSubmodule {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L} :
    u ∈ groundFormSubmodule N L a ↔ u ∈ dirichletDomain N L a ∧ bosonic u.1 := by
  simp [groundFormSubmodule]

end HardSphere

end

end OAI
