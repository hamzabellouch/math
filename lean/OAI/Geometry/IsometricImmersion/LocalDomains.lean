import OAI.Geometry.IsometricImmersion.Metric
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

namespace OAI

noncomputable section
open Set Filter Function TopologicalSpace
open scoped ContDiff Topology Manifold Matrix

namespace SmoothLocal.Geometry

section Extension
variable {E : Type*}

def openDomainExtend (U : Opens Coord) (F : U → E) (outside : E) : Coord → E :=
  Function.extend Subtype.val F (fun _ => outside)

@[simp] theorem openDomainExtend_apply (U : Opens Coord) (F : U → E)
    (outside : E) (p : U) : openDomainExtend U F outside p = F p :=
  Subtype.val_injective.extend_apply F (fun _ => outside) p

theorem openDomainExtend_restrict (U : Opens Coord) (F : U → E)
    (outside : E) : (fun p : U => openDomainExtend U F outside p) = F := by
  funext p
  exact openDomainExtend_apply U F outside p

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contMDiff_restrict_iff (U : Opens Coord) (F : Coord → E)
    (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, E) n (fun p : U => F p) ↔
      ContDiffOn ℝ n F (U : Set Coord) := by
  constructor
  · intro h p hp
    have hs := contMDiffAt_subtype_iff.mp (h ⟨p, hp⟩)
    exact hs.contDiffAt.contDiffWithinAt
  · intro h p
    apply contMDiffAt_subtype_iff.mpr
    exact ((h p p.property).contDiffAt (U.isOpen.mem_nhds p.property)).contMDiffAt

theorem openDomainExtend_contDiffOn (U : Opens Coord) (F : U → E)
    (outside : E) {n : ℕ∞ω}
    (hF : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, E) n F) :
    ContDiffOn ℝ n (openDomainExtend U F outside) (U : Set Coord) := by
  apply (contMDiff_restrict_iff U _ n).mp
  rw [openDomainExtend_restrict]
  exact hF

theorem mfderiv_restrict_eq_fderiv (U : Opens Coord) (F : Coord → E)
    (p : U) (hF : ContDiffAt ℝ ∞ F (p : Coord)) :
    mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, E) (fun q : U => F q) p =
      fderiv ℝ F (p : Coord) := by
  have hs : ContMDiffAt 𝓘(ℝ, Coord) 𝓘(ℝ, E) ∞
      (fun q : U => F q) p :=
    contMDiffAt_subtype_iff.mpr hF.contMDiffAt
  have hd := hs.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hc : (fun y : Coord => ((chartAt Coord p).symm y : Coord))
      =ᶠ[𝓝 (p : Coord)] (fun y : Coord => y) := by
    exact (U.chartAt_subtype_val_symm_eventuallyEq (H := Coord) (x := p)).symm
  have he : writtenInExtChartAt 𝓘(ℝ, Coord) 𝓘(ℝ, E) p
      (fun q : U => F q) =ᶠ[𝓝 (p : Coord)] F := by
    exact hc.fun_comp F
  rw [hd.mfderiv]
  change fderivWithin ℝ
    (writtenInExtChartAt 𝓘(ℝ, Coord) 𝓘(ℝ, E) p (fun q : U => F q))
    (range 𝓘(ℝ, Coord)) (p : Coord) = _
  rw [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  exact he.fderiv_eq

theorem fderiv_openDomainExtend_eq_mfderiv (U : Opens Coord) (F : U → E)
    (outside : E) (hF : ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, E) ∞ F) (p : U) :
    fderiv ℝ (openDomainExtend U F outside) (p : Coord) =
      mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, E) F p := by
  have hd := ((openDomainExtend_contDiffOn U F outside hF) p p.property).contDiffAt
    (U.isOpen.mem_nhds p.property)
  have he := mfderiv_restrict_eq_fderiv U (openDomainExtend U F outside) p hd
  rw [openDomainExtend_restrict] at he
  exact he.symm

end Extension

def LocalIsometric (g : MetricField) (U : Opens Coord) (F : U → Ambient) : Prop :=
  ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ F ∧
    ∀ p : U, ∀ v w : Coord,
      (inner ℝ : Ambient → Ambient → ℝ) (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p v)
        (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p w) =
          v ⬝ᵥ (g p *ᵥ w)

theorem localIsometric_restrict_iff (g : MetricField) (U : Opens Coord)
    (F : Coord → Ambient) :
    LocalIsometric g U (fun p : U => F p) ↔ IsometricOn g F (U : Set Coord) := by
  constructor
  · rintro ⟨hF, he⟩
    have hc := (contMDiff_restrict_iff U F ∞).mp hF
    refine ⟨hc, ?_⟩
    intro p hp v w
    have hd := mfderiv_restrict_eq_fderiv U F ⟨p, hp⟩
      ((hc p hp).contDiffAt (U.isOpen.mem_nhds hp))
    have hinner := he ⟨p, hp⟩ v w
    rw [hd] at hinner
    exact hinner
  · rintro ⟨hF, he⟩
    refine ⟨(contMDiff_restrict_iff U F ∞).mpr hF, ?_⟩
    intro p v w
    rw [mfderiv_restrict_eq_fderiv U F p
      ((hF p p.property).contDiffAt (U.isOpen.mem_nhds p.property))]
    exact he p p.property v w

theorem localIsometric_extend_iff (g : MetricField) (U : Opens Coord)
    (F : U → Ambient) (outside : Ambient) :
    LocalIsometric g U F ↔ IsometricOn g (openDomainExtend U F outside) U := by
  rw [← localIsometric_restrict_iff, openDomainExtend_restrict]

theorem localIsometric_injective_differential {g : MetricField} {U : Opens Coord}
    {F : U → Ambient} (hg : SmoothPositiveOn g U) (hF : LocalIsometric g U F)
    (p : U) : Function.Injective (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p) := by
  rw [← fderiv_openDomainExtend_eq_mfderiv U F 0 hF.1 p]
  exact isometricOn_injective_differential hg
    ((localIsometric_extend_iff g U F 0).mp hF) p.property

def LocalSmoothPositive (U : Opens Coord)
    (g : U → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ i j, ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) ∞ (fun p => g p i j)) ∧
    ∀ p, (g p).PosDef

theorem localSmoothPositive_restrict_iff (U : Opens Coord) (g : MetricField) :
    LocalSmoothPositive U (fun p => g p) ↔ SmoothPositiveOn g U := by
  constructor
  · rintro ⟨hs, hp⟩
    exact ⟨fun i j => (contMDiff_restrict_iff U (fun p => g p i j) ∞).mp (hs i j),
      fun p h => hp ⟨p, h⟩⟩
  · rintro ⟨hs, hp⟩
    exact ⟨fun i j => (contMDiff_restrict_iff U (fun p => g p i j) ∞).mpr (hs i j),
      fun p => hp p p.property⟩

theorem localSmoothPositive_extend_iff (U : Opens Coord)
    (g : U → Matrix (Fin 2) (Fin 2) ℝ) (outside : Matrix (Fin 2) (Fin 2) ℝ) :
    LocalSmoothPositive U g ↔ SmoothPositiveOn
      (Function.extend Subtype.val g (fun _ => outside)) U := by
  rw [← localSmoothPositive_restrict_iff]
  have he : (fun p : U => Function.extend Subtype.val g (fun _ => outside) p) = g := by
    funext p
    exact Subtype.val_injective.extend_apply g (fun _ => outside) p
  rw [he]

end SmoothLocal.Geometry

end

end OAI
