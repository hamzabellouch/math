import Mathlib
import OAI.Geometry.NearbyLagrangian.LiouvilleDifferentials

namespace OAI

/-! Smooth cotangent lifts of diffeomorphisms and their symplecticity. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Bundle Set ContinuousLinearMap
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
local instance : ChartedSpace (E × (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=M)) :=
  inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=M)))
local instance : ChartedSpace (F × (F →L[ℝ] ℝ)) (Cotangent (E:=F) (M:=N)) :=
  inferInstanceAs (ChartedSpace (ModelProd F (F →L[ℝ] ℝ)) (Cotangent (E:=F) (M:=N)))

def cotangentLiftMap (e : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (z : Cotangent (E:=E) (M:=M)) : Cotangent (E:=F) (M:=N) :=
  ⟨e z.proj, z.snd.comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e.symm (e z.proj))⟩

lemma contMDiffAt_cotangentLiftMap (e : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (z : Cotangent (E:=E) (M:=M)) :
    ContMDiffAt (cotangentModel (E:=E)) (cotangentModel (E:=F)) ∞
      (cotangentLiftMap e) z := by
  have hp : ContMDiffAt (cotangentModel (E:=E)) 𝓘(ℝ,E) ∞
      (fun y : Cotangent (E:=E) (M:=M) => y.proj) z := contMDiff_projection.contMDiffAt
  have he := e.contMDiffAt.comp z hp
  have hpc := (contMDiffAt_hom_bundle (IB:=𝓘(ℝ,E)) (IM:=cotangentModel (E:=E)) (n:=∞) (x₀:=z)
    (fun y : Cotangent (E:=E) (M:=M) => y)).mp contMDiffAt_id
  have hf : ContMDiffAt ((cotangentModel (E:=E)).prod 𝓘(ℝ,F)) 𝓘(ℝ,E) ∞
      (Function.uncurry (fun _ : Cotangent (E:=E) (M:=M) => e.symm)) (z,e z.proj) :=
    e.symm.contMDiffAt.comp _ contMDiffAt_snd
  have hd := hf.mfderiv (fun _ : Cotangent (E:=E) (M:=M) => e.symm)
    (fun y => e y.proj) he (by simp)
  rw [contMDiffAt_hom_bundle]
  refine ⟨he, ?_⟩
  apply (hpc.2.clm_comp hd).congr_of_eventuallyEq
  have hnear : ∀ᶠ y : Cotangent (E:=E) (M:=M) in 𝓝 z,
      y.proj ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) z.proj).baseSet :=
    hp.continuousAt.eventually ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) z.proj).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ,E)) z.proj))
  filter_upwards [hnear] with y hy
  simp only [cotangentLiftMap, inTangentCoordinates, inCoordinates, Diffeomorph.symm_apply_apply]
  change (Bundle.Trivial.trivialization N ℝ).continuousLinearMapAt ℝ (e y.proj) ∘L
    ((y.snd : E →L[ℝ] ℝ) ∘L (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e.symm (e y.proj) : F →L[ℝ] E)) ∘L
      (trivializationAt F (TangentSpace 𝓘(ℝ,F)) (e z.proj)).symmL ℝ (e y.proj) =
    ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ y.proj ∘L
      ((y.snd : E →L[ℝ] ℝ) ∘L (trivializationAt E (TangentSpace 𝓘(ℝ,E)) z.proj).symmL ℝ y.proj)) ∘L
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) z.proj).continuousLinearMapAt ℝ (e.symm (e y.proj)) ∘L
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e.symm (e y.proj) : F →L[ℝ] E) ∘L
          (trivializationAt F (TangentSpace 𝓘(ℝ,F)) (e z.proj)).symmL ℝ (e y.proj))
  have hid : ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) z.proj).continuousLinearMapAt
      ℝ (e.symm (e y.proj)) : E →L[ℝ] E) =
      (trivializationAt E (TangentSpace 𝓘(ℝ,E)) z.proj).continuousLinearMapAt ℝ y.proj :=
    by rw [e.symm_apply_apply]
  rw [hid]
  simp only [Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp]
  ext v
  simp only [ContinuousLinearMap.comp_apply]
  exact congrArg (y.snd : E →L[ℝ] ℝ)
    (Trivialization.symmL_continuousLinearMapAt _ hy _).symm

lemma contMDiff_cotangentLiftMap (e : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞) :
    ContMDiff (cotangentModel (E:=E)) (cotangentModel (E:=F)) ∞ (cotangentLiftMap e) :=
  fun z => contMDiffAt_cotangentLiftMap e z

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma mfderiv_diffeomorph_inverse_comp (e : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞) (x : M) :
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e.symm (e x)).comp (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e x) =
      ContinuousLinearMap.id ℝ E := by
  have h := mfderiv_comp x (e.symm.contMDiffAt.mdifferentiableAt (by simp))
    (e.contMDiffAt.mdifferentiableAt (by simp))
  have heq : (e.symm ∘ e) = id := funext e.symm_apply_apply
  rw [heq, mfderiv_id] at h
  exact h.symm

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma cotangentLiftMap_inverse (e : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (z : Cotangent (E:=E) (M:=M)) : cotangentLiftMap e.symm (cotangentLiftMap e z) = z := by
  apply Bundle.TotalSpace.ext (e.symm_apply_apply z.proj)
  apply heq_of_eq
  change ((z.snd : E →L[ℝ] ℝ).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e.symm (e z.proj))).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e (e.symm (e z.proj))) = z.snd
  have he : (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e (e.symm (e z.proj)) : E →L[ℝ] F) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e z.proj :=
    by rw [e.symm_apply_apply]
  erw [he, ContinuousLinearMap.comp_assoc,
    mfderiv_diffeomorph_inverse_comp e z.proj]
  exact ContinuousLinearMap.comp_id _

def cotangentLift (e : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞) :
    Diffeomorph (cotangentModel (E:=E)) (cotangentModel (E:=F))
      (Cotangent (E:=E) (M:=M)) (Cotangent (E:=F) (M:=N)) ∞ where
  toFun := cotangentLiftMap e
  invFun := cotangentLiftMap e.symm
  left_inv := cotangentLiftMap_inverse e
  right_inv := cotangentLiftMap_inverse e.symm
  contMDiff_toFun := contMDiff_cotangentLiftMap e
  contMDiff_invFun := contMDiff_cotangentLiftMap e.symm

theorem cotangentLift_liouville (e : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (z : Cotangent (E:=E) (M:=M))
    (v : TangentSpace (cotangentModel (E:=E)) z) :
    liouville (cotangentLift e z)
      (mfderiv (cotangentModel (E:=E)) (cotangentModel (E:=F)) (cotangentLift e) z v) =
      liouville z v := by
  have hl : MDifferentiableAt (cotangentModel (E:=E)) (cotangentModel (E:=F))
      (cotangentLiftMap e) z := (contMDiffAt_cotangentLiftMap e z).mdifferentiableAt (by simp)
  have hc := mfderiv_comp z
    ((contMDiff_projection (E:=F) (M:=N)).mdifferentiableAt (by simp)) hl
  have hec := mfderiv_comp z (e.contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiff_projection (E:=E) (M:=M)).mdifferentiableAt (by simp))
  change z.snd ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e.symm (e z.proj))
    ((mfderiv (cotangentModel (E:=F)) 𝓘(ℝ,F) projection (cotangentLiftMap e z))
      (mfderiv (cotangentModel (E:=E)) (cotangentModel (E:=F)) (cotangentLiftMap e) z v))) =
    z.snd (mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E) projection z v)
  have hc' : (mfderiv (cotangentModel (E:=F)) 𝓘(ℝ,F) projection (cotangentLiftMap e z)).comp
      (mfderiv (cotangentModel (E:=E)) (cotangentModel (E:=F)) (cotangentLiftMap e) z) =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e z.proj).comp
      (mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E) projection z) := by
    exact hc.symm.trans hec
  have hc'' := congrArg (fun A : (E × (E →L[ℝ] ℝ)) →L[ℝ] F => A v) hc'
  have hi := congrArg (fun A : E →L[ℝ] E => A
    (mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E) projection z v))
      (mfderiv_diffeomorph_inverse_comp e z.proj)
  exact congrArg z.snd ((congrArg
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e.symm (e z.proj) : F →L[ℝ] E) hc'').trans hi)

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem cotangentLift_symplectic (e : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (z : Cotangent (E:=E) (M:=M))
    (u v : TangentSpace (cotangentModel (E:=E)) z) :
    symplecticForm (cotangentLift e z)
      (mfderiv (cotangentModel (E:=E)) (cotangentModel (E:=F)) (cotangentLift e) z u)
      (mfderiv (cotangentModel (E:=E)) (cotangentModel (E:=F)) (cotangentLift e) z v) =
      symplecticForm z u v :=
  symplectic_of_liouville (cotangentLift e).contMDiff (cotangentLift_liouville e) z u v

end NearbyLagrangian.CotangentGeometry

end

end OAI
