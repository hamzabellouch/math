import OAI.Dynamics.EntropyCounterexample.RealizedConstruction
import OAI.Dynamics.EntropyCounterexample.StandardSaturation
import OAI.Dynamics.EntropyCounterexample.ReadoutLocalExtension
import OAI.Dynamics.EntropyCounterexample.SphereMainUpdateTransport

namespace OAI

noncomputable section

open scoped Topology ContDiff

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem periodicReadout_hasLocalC1Extension (i : Fin 3) :
    HasLocalC1Extension modelEmbedding (fun x : RawManifold => periodicReadout i x.1) := by
  have h := (standardReader_hasLocalC1Extension_manifold i 3).precomp_ambient
    (eY := modelEmbedding) modelHomeomorph id contDiff_id (fun _ => rfl)
  convert h using 1
  funext x
  change periodicReadout i x.1 = standardReader i (ClockModel.clockHomeomorph x.1)
  change periodicReadout i x.1 = standardReader i (clockHomeomorph x.1)
  simp only [standardReader, Homeomorph.symm_apply_apply, periodicReadout]

theorem concrete_saturation_hasLocalC1Extension (L : ℝ) (hL : 2 < L) (i : Fin 3) :
    HasLocalC1Extension modelEmbedding
      (fun x : RawManifold => (concreteData L hL).saturation (x.2.2 i)) := by
  have hs : HasLocalC1Extension (fun x : StandardSphere2 => x.1)
      (standardSphereSaturation (3 * L) (by linarith)) := by
    intro x
    obtain ⟨U, hU, hxU, A, hA, heq⟩ :=
      standardSphereSaturation_local_ambient (3 * L) (by linarith) x
    exact ⟨U, hU, hxU, A, hA.of_le (by simp), heq⟩
  have h := (hs.sphere_coordinate (q := 3) i.succ).precomp_ambient
    (eY := modelEmbedding) modelHomeomorph id contDiff_id (fun _ => rfl)
  convert h using 1
  funext x
  rw [Function.comp_apply, modelHomeomorph_register,
    standardSphereSaturation_eq_transport, Homeomorph.symm_apply_apply]
  rfl

theorem concrete_readout_hasLocalC1Extension (L : ℝ) (hL : 2 < L) :
    HasLocalC1Extension modelEmbedding
      (fun x : RawManifold => readout (concreteData L hL) x.1 x.2.2) := by
  have hb := HasLocalC1Extension.pi (fun i => periodicReadout_hasLocalC1Extension i)
  have hs := HasLocalC1Extension.pi (fun i => concrete_saturation_hasLocalC1Extension L hL i)
  have hp : ContDiff ℝ 1 (fun p : (Fin 3 → ℝ) × (Fin 3 → ℂ) =>
      (20 : ℂ) * ∑ i : Fin 3, (p.1 i : ℂ) * p.2 i) := by
    apply contDiff_const.mul
    apply ContDiff.sum
    intro i hi
    exact (Complex.ofRealCLM.contDiff.comp
      ((contDiff_apply ℝ ℝ i).comp contDiff_fst)).mul
      ((contDiff_apply ℝ ℂ i).comp contDiff_snd)
  exact (hb.prodMk hs).comp_contDiff hp

theorem mainUpdate_hasLocalC1Extension :
    HasLocalC1Extension (fun p : ℂ × StandardSphere2 => (p.1, p.2.1))
      (fun p => (SphereMainUpdate.update p.1 p.2).1) := by
  intro p
  obtain ⟨U, hU, hA⟩ :=
    (SphereMainUpdate.contDiffAt_ambient 1 p.1 p.2).contDiffOn le_rfl (by simp)
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp hU
  exact ⟨V, hV, hpV, fun q => SphereMainUpdate.ambient q.1 q.2,
    hA.mono hVU, fun _ _ => rfl⟩

theorem concrete_main_hasLocalC1Extension (L : ℝ) (hL : 2 < L) :
    HasLocalC1Extension modelEmbedding
      (fun x : RawManifold => (complexSphereHomeomorph ((concreteMap L hL x).2.1)).1) := by
  have hm : HasLocalC1Extension modelEmbedding
      (fun x : RawManifold => (complexSphereHomeomorph x.2.1).1) :=
    .of_contDiffOn isOpen_univ (fun _ => Set.mem_univ _)
      (fun p : CounterexampleAmbient 3 => p.2 0)
      (((contDiff_apply ℝ SphereAmbient (0 : Fin 4)).comp contDiff_snd).contDiffOn)
      (fun _ => rfl)
  have h := mainUpdate_hasLocalC1Extension.comp
    (f := fun x : RawManifold =>
      (readout (concreteData L hL) x.1 x.2.2, complexSphereHomeomorph x.2.1))
    ((concrete_readout_hasLocalC1Extension L hL).prodMk hm)
  convert h using 1
  funext x
  exact congrArg Subtype.val
    (SphereMainUpdate.update_complexSphereHomeomorph
      (readout (concreteData L hL) x.1 x.2.2) x.2.1).symm

theorem realizedMap_main_hasLocalC1Extension (L : ℝ) (hL : 2 < L) :
    HasLocalC1Extension (standardEmbedding 3)
      (fun x : CounterexampleManifold 3 => ((realizedMap L hL x).2 0).1) := by
  have h := (concrete_main_hasLocalC1Extension L hL).precomp_ambient
    (eY := standardEmbedding 3) modelHomeomorph.symm id contDiff_id
    (fun y => by simp [modelEmbedding])
  convert h using 1
  funext x
  rfl

end Problem340.Construction

end

end OAI
