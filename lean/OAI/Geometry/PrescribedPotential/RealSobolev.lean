import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.ComplexKernel
import OAI.Geometry.PrescribedPotential.GlobalStrongEmbedding
import OAI.Geometry.PrescribedPotential.MatrixHilbertCoordinates

namespace OAI

/-! Real Sobolev. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace ClosedCore
variable {V W H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
lemma maps_closure_range (e : V → H) (q : W → G) (L : H → G) (hL : Continuous L)
    (he : ∀ f, ∃ h, L (e f) = q h) :
    ∀ u ∈ closure (range e), L u ∈ closure (range q) := by
  apply closure_minimal _ (isClosed_closure.preimage hL)
  rintro _ ⟨f, rfl⟩
  obtain ⟨h, hh⟩ := he f
  exact subset_closure ⟨h, hh.symm⟩
end ClosedCore

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

def realSmoothSpace (A : ComplexAtlas d X) : Submodule ℝ (Smooth A) where
  carrier := {f | ∀ x, (f x).im = 0}
  zero_mem' := by intro x; rfl
  add_mem' := by intro f h hf hh x; simp [hf x, hh x]
  smul_mem' := by intro c f hf x; simp [hf x]

abbrev RealSmooth (A : ComplexAtlas d X) := ↥(realSmoothSpace A)

namespace RealSmooth

def ofReal (f : SmoothRealFunction A) : RealSmooth A :=
  ⟨Smooth.ofReal f, fun _ => Complex.ofReal_im _⟩

def source (f : RealSmooth A) : SmoothRealFunction A := f.val.part Complex.reCLM

lemma ofReal_source (f : RealSmooth A) : Smooth.ofReal f.source = f.val := by
  apply Smooth.ext
  intro x
  exact Complex.ext rfl (f.property x).symm

def const (r : ℝ) : RealSmooth A := ⟨Smooth.const r, fun _ => Complex.ofReal_im _⟩

lemma complexL_real (g : KaehlerMetric A) (f : RealSmooth A) :
    complexL g f.val ∈ realSmoothSpace A := by
  intro x
  rw [complexL_im]
  have hi : f.val.part Complex.imCLM = SmoothRealFunction.constant 0 := by
    cases h : f.val.part Complex.imCLM with
    | mk v hv =>
      have he : v = fun _ => 0 := by
        funext x
        have hh := congrArg (fun u : SmoothRealFunction A => u.value x) h
        exact hh.symm.trans (f.property x)
      subst v
      rfl
  rw [hi]
  obtain ⟨i, hi⟩ := A.covers x
  change g.laplacianValue (SmoothRealFunction.constant 0) x = 0
  rw [g.laplacianValue_local _ i hi, g.linearizedMongeAmpere_constant]
  rfl

def laplace (g : KaehlerMetric A) : RealSmooth A →ₗ[ℝ] RealSmooth A :=
  ((complexL g).comp (realSmoothSpace A).subtype).codRestrict (realSmoothSpace A)
    (fun f => complexL_real g f)

end RealSmooth

variable [T2Space X] [CompactSpace X] {ι : Type*} [Fintype ι]
namespace Localizers
variable (D : Localizers A ι)

def realCoreMap (s : ℝ) : RealSmooth A →ₗ[ℝ] D.Sobolev s :=
  (D.embed s).comp (realSmoothSpace A).subtype

def realCompletion (s : ℝ) : Submodule ℝ (D.Sobolev s) :=
  (D.realCoreMap s).range.topologicalClosure

abbrev RealSobolev (s : ℝ) := ↥(D.realCompletion s)

instance realSobolev_complete (s : ℝ) : CompleteSpace (D.RealSobolev s) :=
  inferInstanceAs (CompleteSpace (D.realCoreMap s).range.topologicalClosure)

def realEmbed (s : ℝ) : RealSmooth A →ₗ[ℝ] D.RealSobolev s :=
  (D.realCoreMap s).codRestrict (D.realCompletion s)
    (fun f => (D.realCoreMap s).range.le_topologicalClosure (LinearMap.mem_range_self _ f))

@[simp] lemma realEmbed_val (s : ℝ) (f : RealSmooth A) :
    (D.realEmbed s f).val = D.embed s f.val := rfl

lemma realEmbed_dense (s : ℝ) : DenseRange (D.realEmbed s) := by
  rw [DenseRange, Subtype.dense_iff]
  change closure ((D.realCoreMap s).range : Set (D.Sobolev s)) ⊆ _
  apply closure_mono
  rintro _ ⟨f, rfl⟩
  exact ⟨D.realEmbed s f, ⟨f, rfl⟩, rfl⟩

lemma maps_realCompletion {s t : ℝ} (L : D.Sobolev s →L[ℝ] D.Sobolev t)
    (hL : ∀ f : RealSmooth A, ∃ h : RealSmooth A, L (D.embed s f.val) = D.embed t h.val) :
    ∀ u ∈ D.realCompletion s, L u ∈ D.realCompletion t := by
  exact ClosedCore.maps_closure_range (D.realCoreMap s) (D.realCoreMap t) L L.continuous hL

lemma real_strong {s : ℝ} (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s)
    (u : D.RealSobolev s) (x : X) : (D.strong s u.val x).im = 0 := by
  have hc : IsClosed {v : D.Sobolev s | (D.strong s v x).im = 0} :=
    isClosed_eq (Complex.continuous_im.comp ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
      (D.strong s).continuous)) continuous_const
  apply closure_minimal (s := ((D.realCoreMap s).range : Set (D.Sobolev s))) _ hc u.property
  rintro _ ⟨f, rfl⟩
  change (D.strong s (D.embed s f.val) x).im = 0
  rw [D.strong_embed s hs]
  exact f.property x

end Localizers
end GlobalElliptic

end
end

end OAI
