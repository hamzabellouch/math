import Mathlib
import OAI.Analysis.HardSphere.Conditioning.BathPhase
import OAI.Analysis.HardSphere.Rescaling.PhysicalUnitary

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Rescaling
attribute [local instance] Classical.propDecidable

lemma coord_pull {N : ℕ} {L J : Length} {a : ℝ} (f : SmoothTest N J a) (c : ℝ)
    (p : Direction N) (X : Configuration N L) :
    coordDerivative N L (fun X ↦ c • f.toFun (config N L J X)) p X=
      (J.val/L.val) • (c • coordDerivative N J f.toFun p (config N L J X)) := by
  let T : LiftedConfiguration N →L[ℝ] LiftedConfiguration N :=
    (J.val/L.val) • ContinuousLinearMap.id ℝ _
  let F := fun Y : LiftedConfiguration N ↦ f.toFun (project N J Y)
  have he : (fun Y : LiftedConfiguration N ↦ c • f.toFun (config N L J (project N L Y)))=
      fun Y ↦ c • F (T Y) := by
    funext Y
    rw [config_project]
    rfl
  have hd := ((((f.smooth.differentiable (by simp)) (T (representative N L X))).hasFDerivAt).comp
    (representative N L X) T.hasFDerivAt).const_smul c
  change HasFDerivAt (fun Y ↦ c • F (T Y)) _ _ at hd
  unfold coordDerivative
  rw [he,hd.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,T,
    ContinuousLinearMap.id_apply,map_smul,←config_representative,smul_smul]
  rw [mul_comm c (J.val/L.val)]

lemma pulled_memLp {N : ℕ} {L J : Length} {f : Configuration N J → ℂ}
    (hf : MemLp f 2 volume) (c : ℝ) :
    MemLp (fun X ↦ c • f (config N L J X)) 2 volume :=
  ((hf.smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving (config_preserving N L J)).const_smul c

def smoothPull {N : ℕ} {L J : Length} {a : ℝ} (f : SmoothTest N J a) :
    SmoothTest N L ((L.val/J.val)*a) where
  toFun X := amplitude N L J • f.toFun (config N L J X)
  smooth := by
    have he : (fun Y : LiftedConfiguration N ↦ amplitude N L J • f.toFun (config N L J (project N L Y)))=
        fun Y ↦ amplitude N L J • f.toFun (project N J ((J.val/L.val) • Y)) := by
      funext Y; rw [config_project]
    rw [he]
    exact (f.smooth.comp (contDiff_id.const_smul (J.val/L.val))).const_smul _
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := by
    intro X hX
    have hs := (tsupport_smul_subset_right (fun _ ↦ amplitude N L J) (f.toFun ∘ config N L J)) hX
    have hc := f.support_allowed ((tsupport_comp_subset_preimage f.toFun (config_continuous N L J)) hs)
    apply (config_allowed N L J ((L.val/J.val)*a) X).mp
    have he : J.val/L.val*((L.val/J.val)*a)=a := by field_simp [L.property.ne',J.property.ne']
    rwa [he]
  memLp := pulled_memLp f.memLp _
  partial_memLp := by
    intro p
    have he : coordDerivative N L (fun X ↦ amplitude N L J • f.toFun (config N L J X)) p=
      fun X ↦ (J.val/L.val) • (amplitude N L J • coordDerivative N J f.toFun p (config N L J X)) :=
        funext (coord_pull f _ p)
    rw [he]
    exact (pulled_memLp (f.partial_memLp p) (amplitude N L J)).const_smul (J.val/L.val)

lemma smoothPull_jet {N : ℕ} {L J : Length} {a : ℝ} (f : SmoothTest N J a) :
    (smoothPull (L:=L) f).jet=jet N L J f.jet := by
  apply Prod.ext
  · apply Lp.ext
    have hf := (config_preserving N L J).quasiMeasurePreserving.tendsto_ae.eventually
      (Measure.ae_smul_measure (MemLp.coeFn_toLp f.memLp) (ENNReal.ofReal (jacobian N L J)))
    filter_upwards [MemLp.coeFn_toLp (smoothPull (L:=L) f).memLp,hf,pull_ae N L J f.jet.1] with X hX hF hP
    change ((smoothPull (L:=L) f).memLp.toLp _) X=(pull N L J f.jet.1) X
    rw [hX,hP]
    change amplitude N L J • f.toFun (config N L J X) = amplitude N L J • (f.memLp.toLp _) (config N L J X)
    rw [hF]
  · funext p
    apply Lp.ext
    have hf := (config_preserving N L J).quasiMeasurePreserving.tendsto_ae.eventually
      (Measure.ae_smul_measure (MemLp.coeFn_toLp (f.partial_memLp p)) (ENNReal.ofReal (jacobian N L J)))
    have hp := pull_ae N L J (f.jet.2 p)
    have hc := Lp.coeFn_smul (J.val/L.val) (pull N L J (f.jet.2 p))
    filter_upwards [MemLp.coeFn_toLp ((smoothPull (L:=L) f).partial_memLp p),hf,hp,hc] with X hX hF hP hC
    change (((smoothPull (L:=L) f).partial_memLp p).toLp _) X=((J.val/L.val) • pull N L J (f.jet.2 p)) X
    rw [hX,hC]
    change coordDerivative N L (smoothPull (L:=L) f).toFun p X=(J.val/L.val) • (pull N L J (f.jet.2 p)) X
    rw [hP]
    change _=(J.val/L.val) • (amplitude N L J • ((f.partial_memLp p).toLp _) (config N L J X))
    rw [hF]
    exact coord_pull f _ p X

lemma jet_domain {N : ℕ} {L J : Length} {a : ℝ} {u : Jet N J}
    (hu : u∈dirichletDomain N J a) : jet N L J u∈dirichletDomain N L ((L.val/J.val)*a) := by
  apply map_mem_closure (jet N L J).continuous hu
  rintro v ⟨f,rfl⟩
  exact ⟨smoothPull f,smoothPull_jet f⟩

theorem jet_ground {N : ℕ} {L J : Length} {a : ℝ} {u : Jet N J}
    (hu : IsGroundVector N J a u) : IsGroundVector N L ((L.val/J.val)*a) (jet N L J u) := by
  have hLp := L.property
  have hJp := J.property
  refine ⟨jet_domain hu.1,pull_bosonic hu.2.1,?_,?_⟩
  · change ‖unitary N L J u.1‖=1
    exact ((unitary N L J).norm_map u.1).trans hu.2.2.1
  · intro v hv hb hn
    have hd := jet_domain (L:=J) hv
    have he : (J.val/L.val)*((L.val/J.val)*a)=a := by field_simp
    rw [he] at hd
    have h := hu.2.2.2 (jet N J L v) hd (pull_bosonic hb) (by rw [jet_fst,pull_norm,hn])
    rw [jet_energy] at h ⊢
    have ht := mul_le_mul_of_nonneg_left h (sq_nonneg (J.val/L.val))
    have hid : (J.val/L.val)^2*((L.val/J.val)^2*energy v)=energy v := by field_simp
    exact ht.trans_eq hid

end HardSphere.Rescaling
end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Rescaling
attribute [local instance] Classical.propDecidable

def torusHomeo (L J : Length) : Torus L ≃ₜ Torus J :=
  Homeomorph.piCongrRight fun _ ↦ AddCircle.homeomorphAddCircle L.val J.val L.property.ne' J.property.ne'
lemma torus_preserving (L J : Length) : MeasurePreserving (torus L J) volume
    (ENNReal.ofReal (L.val^3/J.val^3) • volume) := by
  have hLp := L.property
  have hJp := J.property
  let : Measure.IsAddHaarMeasure (ENNReal.ofReal (L.val^3/J.val^3) • (volume : Measure (Torus J))) :=
    Measure.IsAddHaarMeasure.smul _ (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top
  apply AddMonoidHom.measurePreserving (μ:=(volume : Measure (Torus L)))
    (ν:= ENNReal.ofReal (L.val^3/J.val^3) • (volume : Measure (Torus J)))
    (f:=(torus L J).toAddMonoidHom) (torusHomeo L J).continuous (torus L J).surjective
  rw [BathSlice.volume_torus,Measure.smul_apply,smul_eq_mul,BathSlice.volume_torus,
    ←ENNReal.ofReal_mul (by positivity : 0≤L.val^3/J.val^3)]
  congr 1
  field_simp

lemma config_cons {n : ℕ} (L J : Length) (x : Torus L) (Y : Configuration n L) :
    config (n+1) L J (Fin.cons x Y)=Fin.cons (torus L J x) (config n L J Y) := by
  funext i
  refine Fin.cases ?_ (fun i ↦ ?_) i <;> rfl

lemma pull_occupation_succ {n : ℕ} {L J : Length} (f : ScalarL2 (n+1) J) :
    occupation (Nat.zero_lt_succ n) (pull (n+1) L J f)=occupation (Nat.zero_lt_succ n) f := by
  have hLp := L.property
  have hJp := J.property
  let z := L.val^3/J.val^3
  have hz : 0<z := by dsimp only [z]; positivity
  have ha := (cons_preserving (n:=n) L).quasiMeasurePreserving.tendsto_ae.eventually (pull_ae (n+1) L J f)
  have ha' := Measure.ae_ae_of_ae_prod ha
  have hs : (fun Y : Configuration n L ↦ ∫x : Torus L,(pull (n+1) L J f) (Fin.cons x Y))=ᵐ[volume]
      fun Y ↦ amplitude (n+1) L J • (z • ∫x : Torus J,f (Fin.cons x (config n L J Y))) := by
    filter_upwards [ha'] with Y hY
    calc
      _ = ∫x : Torus L,amplitude (n+1) L J • f (Fin.cons (torus L J x) (config n L J Y)) := by
        apply integral_congr_ae
        filter_upwards [hY] with x hx
        simpa only [config_cons] using hx
      _ = amplitude (n+1) L J • (z • ∫x : Torus J,f (Fin.cons x (config n L J Y))) := by
        rw [integral_smul,(torus_preserving L J).integral_comp (torusHomeo L J).measurableEmbedding
          (fun x ↦ f (Fin.cons x (config n L J Y))),integral_smul_measure,
          ENNReal.toReal_ofReal hz.le]
  change (L.val^3)⁻¹ * (∫Y : Configuration n L,‖∫x : Torus L,(pull (n+1) L J f) (Fin.cons x Y)‖^2)=
    (J.val^3)⁻¹ * (∫Y : Configuration n J,‖∫x : Torus J,f (Fin.cons x Y)‖^2)
  have hsi := integral_congr_ae (hs.fun_comp fun x ↦ ‖x‖^2)
  simp only [Function.comp_def] at hsi
  rw [hsi]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
  rw [(config_preserving n L J).integral_comp (config_embedding n L J)
    (fun Y ↦ ‖∫x : Torus J,f (Fin.cons x Y)‖^2),integral_smul_measure,
    ENNReal.toReal_ofReal (jacobian_pos n L J).le,smul_eq_mul,amplitude_sq]
  have hprod (b : ℝ) : (z^(n+1))⁻¹*(z^2*(z^n*b))=z*b := by
    rw [pow_succ]
    field_simp [hz.ne']
  change (L.val^3)⁻¹*((z^(n+1))⁻¹*(z^2*(z^n*_)))=(J.val^3)⁻¹*_
  rw [hprod]
  dsimp only [z]
  field_simp [hLp.ne',hJp.ne']

lemma pull_occupation {N : ℕ} (hN : 0<N) {L J : Length} (f : ScalarL2 N J) :
    occupation hN (pull N L J f)=occupation hN f := by
  cases N with
  | zero => omega
  | succ n => exact pull_occupation_succ f

end HardSphere.Rescaling
end
end

end OAI
