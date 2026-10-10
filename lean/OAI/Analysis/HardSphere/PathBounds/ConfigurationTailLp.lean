import Mathlib
import OAI.Analysis.HardSphere.Geometry.SmoothMultiplier

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma configurationTail_preserving (n : ℕ) (L : Length) :
    MeasurePreserving (Fin.tail : Configuration (n+1) L → Configuration n L)
      volume ((volume (Set.univ : Set (Torus L))) • (volume : Measure (Configuration n L))) := by
  have h : MeasurePreserving (Prod.snd : Torus L × Configuration n L → Configuration n L)
      volume ((volume (Set.univ : Set (Torus L))) • (volume : Measure (Configuration n L))) :=
    ⟨measurable_snd,Measure.map_snd_prod⟩
  simpa only [Function.comp_def,MeasurableEquiv.piFinSuccAbove_apply,Fin.zero_succAbove,Fin.insertNthEquiv_zero,Fin.consEquiv_symm_apply] using
    h.comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0)

lemma configurationTail_quasiPreserving (n : ℕ) (L : Length) :
    Measure.QuasiMeasurePreserving (Fin.tail : Configuration (n+1) L → Configuration n L)
      volume volume := by
  refine ⟨(configurationTail_preserving n L).measurable,?_⟩
  rw [(configurationTail_preserving n L).map_eq]
  exact Measure.smul_absolutelyContinuous

lemma memLp_configurationTail {n : ℕ} {L : Length} {f : Configuration n L → ℂ}
    (hf : MemLp f 2 volume) : MemLp (fun X : Configuration (n+1) L ↦ f (Fin.tail X)) 2 volume :=
  (hf.smul_measure (measure_ne_top _ _)).comp_measurePreserving (configurationTail_preserving n L)

def configurationTailLp {n : ℕ} {L : Length} (u : ScalarL2 n L) : ScalarL2 (n+1) L :=
  (memLp_configurationTail (Lp.memLp u)).toLp _

lemma coe_configurationTailLp {n : ℕ} {L : Length} (u : ScalarL2 n L) :
    configurationTailLp u =ᵐ[volume] fun X ↦ u (Fin.tail X) := MemLp.coeFn_toLp _

def configurationTailLinear (n : ℕ) (L : Length) : ScalarL2 n L →ₗ[ℂ] ScalarL2 (n+1) L where
  toFun := configurationTailLp
  map_add' u v := by
    apply Lp.ext
    filter_upwards [coe_configurationTailLp (u+v),coe_configurationTailLp u,coe_configurationTailLp v,
      (configurationTail_quasiPreserving n L).ae_eq_comp (Lp.coeFn_add u v),
      Lp.coeFn_add (configurationTailLp u) (configurationTailLp v)] with X h1 h2 h3 h4 h5
    simp only [Function.comp_def,Pi.add_apply] at h4
    rw [h1,h4,h5,Pi.add_apply,h2,h3]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [coe_configurationTailLp (c • u),coe_configurationTailLp u,
      (configurationTail_quasiPreserving n L).ae_eq_comp (Lp.coeFn_smul c u),
      Lp.coeFn_smul c (configurationTailLp u)] with X h1 h2 h3 h4
    simp only [Function.comp_def,Pi.smul_apply] at h3
    simp only [h1,h3,h4,Pi.smul_apply,h2,RingHom.id_apply]

lemma norm_configurationTailLp {n : ℕ} {L : Length} (u : ScalarL2 n L) :
    ‖configurationTailLp u‖ = (volume (Set.univ : Set (Torus L)) ^ (1 / (2:ℝ))).toReal * ‖u‖ := by
  rw [configurationTailLp,Lp.norm_toLp]
  have he := eLpNorm_comp_measurePreserving (p:= (2:ℝ≥0∞))
    ((Lp.stronglyMeasurable u).aestronglyMeasurable
      (μ := volume univ • (volume : Measure (Configuration n L)))) (configurationTail_preserving n L)
  simp only [Function.comp_def] at he
  rw [he]
  have hv : volume (Set.univ : Set (Torus L))≠0 := Measure.measure_univ_ne_zero.mpr (NeZero.ne volume)
  rw [eLpNorm_smul_measure_of_ne_zero hv,smul_eq_mul,ENNReal.toReal_mul,Lp.norm_def]
  congr 2
  norm_num

def configurationTailCLM (n : ℕ) (L : Length) : ScalarL2 n L →L[ℂ] ScalarL2 (n+1) L :=
  (configurationTailLinear n L).mkContinuous
    (volume (Set.univ : Set (Torus L)) ^ (1 / (2:ℝ))).toReal
    (fun u ↦ (norm_configurationTailLp u).le)

lemma coe_configurationTailCLM {n : ℕ} {L : Length} (u : ScalarL2 n L) :
    configurationTailCLM n L u =ᵐ[volume] fun X ↦ u (Fin.tail X) := coe_configurationTailLp u

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

def tailLift (n : ℕ) : LiftedConfiguration (n+1) →L[ℝ] LiftedConfiguration n :=
  .pi fun i ↦ .proj i.succ

lemma tailLift_direction_zero (n : ℕ) (j : Fin 3) :
    tailLift n (Pi.single 0 (Pi.single j 1))=0 := by
  ext i k
  simp [tailLift]

lemma tailLift_direction_succ (n : ℕ) (i : Fin n) (j : Fin 3) :
    tailLift n (Pi.single i.succ (Pi.single j 1))=Pi.single i (Pi.single j 1) := by
  ext k q
  by_cases h : k=i
  · subst k; simp [tailLift]
  · simp [tailLift,Pi.single_eq_of_ne h,Pi.single_eq_of_ne (fun h' ↦ h (Fin.succ_injective _ h'))]

lemma smooth_tail {n : ℕ} {L : Length} {f : Configuration n L → ℂ}
    (hf : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun X : LiftedConfiguration n ↦ f (project n L X))) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun X : LiftedConfiguration (n+1) ↦ f (Fin.tail (project (n+1) L X))) :=
  hf.comp (tailLift n).contDiff

lemma coordDerivative_tail_zero {n : ℕ} {L : Length} {f : Configuration n L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration n ↦ f (project n L X))) (j : Fin 3) :
    coordDerivative (n+1) L (fun X ↦ f (Fin.tail X)) (0,j)=0 := by
  funext X
  have h := (hf (tailLift n (representative (n+1) L X))).hasFDerivAt.comp
    (representative (n+1) L X) (tailLift n).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration n ↦ f (project n L Y)) ∘ tailLift n)
    (representative (n+1) L X)) (Pi.single 0 (Pi.single j 1))=0
  rw [h.fderiv,ContinuousLinearMap.comp_apply,tailLift_direction_zero,map_zero]

lemma coordDerivative_tail_succ {n : ℕ} {L : Length} {f : Configuration n L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration n ↦ f (project n L X)))
    (i : Fin n) (j : Fin 3) :
    coordDerivative (n+1) L (fun X ↦ f (Fin.tail X)) (i.succ,j)=
      fun X ↦ coordDerivative n L f (i,j) (Fin.tail X) := by
  funext X
  have h := (hf (tailLift n (representative (n+1) L X))).hasFDerivAt.comp
    (representative (n+1) L X) (tailLift n).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration n ↦ f (project n L Y)) ∘ tailLift n)
    (representative (n+1) L X)) (Pi.single i.succ (Pi.single j 1))=_
  rw [h.fderiv,ContinuousLinearMap.comp_apply,tailLift_direction_succ]
  rfl

lemma allowed_of_tail {n : ℕ} {L : Length} {a : ℝ} {X : Configuration (n+1) L}
    (htail : Fin.tail X∈allowed n L a)
    (hhead : ∀ i : Fin n, a<torusDistance L (X 0) (X i.succ)) :
    X∈allowed (n+1) L a := by
  intro i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · intro j hij
    exact Fin.cases (fun h ↦ (lt_irrefl _ h).elim) (fun k _ ↦ hhead k) j hij
  · intro j hij
    exact Fin.cases (fun h ↦ (Fin.not_lt_zero _ h).elim)
      (fun l h ↦ htail k l (Fin.succ_lt_succ_iff.mp h)) j hij

def InsertionClearance {n : ℕ} {L : Length} (a : ℝ) (f : SmoothMultiplier (n+1) L) : Prop :=
  tsupport f.toFun ⊆ {X | ∀ i : Fin n, a<torusDistance L (X 0) (X i.succ)}

def SmoothTest.insert {n : ℕ} {L : Length} {a : ℝ} (g : SmoothTest n L a)
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f) : SmoothTest (n+1) L a where
  toFun := fun X ↦ f.toFun X * g.toFun (Fin.tail X)
  smooth := f.smooth.mul (smooth_tail g.smooth)
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := by
    intro X hX
    have hf : X∈tsupport f.toFun := tsupport_mul_subset_left hX
    have hg : X∈tsupport (fun X : Configuration (n+1) L ↦ g.toFun (Fin.tail X)) :=
      tsupport_mul_subset_right hX
    have htail : Fin.tail X∈tsupport g.toFun := by
      exact (tsupport_comp_subset_preimage g.toFun
        (f := (Fin.tail : Configuration (n+1) L → Configuration n L))
        (continuous_pi fun i ↦ continuous_apply i.succ)) hg
    exact allowed_of_tail (g.support_allowed htail) (hc hf)
  memLp := f.memLp_top.mul (memLp_configurationTail g.memLp)
  partial_memLp := by
    rintro ⟨i,j⟩
    rw [show (fun X ↦ f.toFun X*g.toFun (Fin.tail X))=f.toFun*(fun X ↦ g.toFun (Fin.tail X)) from rfl,
      coordDerivative_mul (f.smooth.differentiable (by simp)) ((smooth_tail g.smooth).differentiable (by simp))]
    apply MemLp.add
    · refine Fin.cases ?_ (fun k ↦ ?_) i
      · rw [coordDerivative_tail_zero (g.smooth.differentiable (by simp))]
        simp
      · rw [coordDerivative_tail_succ (g.smooth.differentiable (by simp))]
        exact f.memLp_top.mul (memLp_configurationTail (g.partial_memLp (k,j)))
    · exact (memLp_configurationTail g.memLp).mul (f.partial_memLp_top (i,j))

def insertionParentDerivative (n : ℕ) (L : Length) (p : Direction (n+1)) :
    Jet n L →L[ℂ] ScalarL2 n L :=
  Fin.cases 0 (fun i ↦ (ContinuousLinearMap.proj (i,p.2)).comp (.snd ℂ _ _)) p.1

def SmoothMultiplier.insertionScalar {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L) :
    ScalarL2 n L →L[ℂ] ScalarL2 (n+1) L :=
  f.onScalar.comp (configurationTailCLM n L)

def SmoothMultiplier.insertionJet {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L) :
    Jet n L →L[ℂ] Jet (n+1) L :=
  (f.insertionScalar.comp (.fst ℂ _ _)).prod (.pi fun p ↦
    f.insertionScalar.comp (insertionParentDerivative n L p) +
    ((L2Multiplier.clm _ (f.partial_memLp_top p)).comp (configurationTailCLM n L)).comp (.fst ℂ _ _))

lemma coe_insertionScalar {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L) (u : ScalarL2 n L) :
    f.insertionScalar u =ᵐ[volume] fun X ↦ f.toFun X*u (Fin.tail X) := by
  filter_upwards [coe_configurationTailCLM u,L2Multiplier.coe_clm f.toFun f.memLp_top (configurationTailCLM n L u)]
    with X h1 h2
  exact h2.trans (by rw [h1])

lemma coe_insertionParentDerivative {n : ℕ} {L : Length} (u : Jet n L) (p : Direction (n+1)) :
    insertionParentDerivative n L p u = Fin.cases 0 (fun i ↦ u.2 (i,p.2)) p.1 := by
  rcases p with ⟨p,j⟩
  cases p using Fin.cases <;> rfl

lemma coe_insertionJet_zero {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (u : Jet n L) (j : Fin 3) :
    (f.insertionJet u).2 (0,j) =ᵐ[volume]
      fun X ↦ coordDerivative (n+1) L f.toFun (0,j) X*u.1 (Fin.tail X) := by
  change (f.insertionScalar 0+L2Multiplier.clm _ (f.partial_memLp_top (0,j))
    (configurationTailCLM n L u.1)) =ᵐ[volume] _
  rw [map_zero,zero_add]
  filter_upwards [coe_configurationTailCLM u.1,
    L2Multiplier.coe_clm _ (f.partial_memLp_top (0,j)) (configurationTailCLM n L u.1)] with X h1 h2
  exact h2.trans (by rw [h1])

lemma coe_insertionJet_succ {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (u : Jet n L) (i : Fin n) (j : Fin 3) :
    (f.insertionJet u).2 (i.succ,j) =ᵐ[volume]
      fun X ↦ f.toFun X*u.2 (i,j) (Fin.tail X)+
        coordDerivative (n+1) L f.toFun (i.succ,j) X*u.1 (Fin.tail X) := by
  change (f.insertionScalar (u.2 (i,j))+L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j))
    (configurationTailCLM n L u.1)) =ᵐ[volume] _
  filter_upwards [coe_insertionScalar f (u.2 (i,j)),coe_configurationTailCLM u.1,
    L2Multiplier.coe_clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1),
    Lp.coeFn_add (f.insertionScalar (u.2 (i,j)))
      (L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1))]
      with X h1 h2 h3 h4
  rw [h4,Pi.add_apply,h1,h3,h2]

lemma SmoothTest.jet_insert {n : ℕ} {L : Length} {a : ℝ} (g : SmoothTest n L a)
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f) :
    (g.insert f hc).jet=f.insertionJet g.jet := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (g.insert f hc).memLp,
      (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp g.memLp),
      coe_insertionScalar f g.jet.1] with X h1 h2 h3
    dsimp only [Function.comp_def] at h2
    change ((g.insert f hc).jet.1) X=(f.insertionScalar g.jet.1) X
    rw [h3]
    dsimp only [SmoothTest.jet]
    rw [h1,h2]
    rfl
  · funext p
    rcases p with ⟨i,j⟩
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp ((g.insert f hc).partial_memLp (0,j)),
        (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp g.memLp),
        coe_insertionJet_zero f g.jet j] with X h1 h2 h3
      dsimp only [Function.comp_def] at h2
      rw [h3]
      dsimp only [SmoothTest.jet]
      rw [h1]
      change coordDerivative (n+1) L (f.toFun*(fun X ↦ g.toFun (Fin.tail X))) (0,j) X=_
      rw [coordDerivative_mul (f.smooth.differentiable (by simp))
        ((smooth_tail g.smooth).differentiable (by simp)),
        coordDerivative_tail_zero (g.smooth.differentiable (by simp))]
      simp only [Pi.add_apply,Pi.mul_apply,Pi.zero_apply,mul_zero,zero_add,h2]
      ring
    · apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp ((g.insert f hc).partial_memLp (k.succ,j)),
        (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp g.memLp),
        (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp (g.partial_memLp (k,j))),
        coe_insertionJet_succ f g.jet k j] with X h1 h2 h3 h4
      dsimp only [Function.comp_def] at h2 h3
      rw [h4]
      dsimp only [SmoothTest.jet]
      rw [h1]
      change coordDerivative (n+1) L (f.toFun*(fun X ↦ g.toFun (Fin.tail X))) (k.succ,j) X=_
      rw [coordDerivative_mul (f.smooth.differentiable (by simp))
        ((smooth_tail g.smooth).differentiable (by simp)),
        coordDerivative_tail_succ (g.smooth.differentiable (by simp))]
      simp only [Pi.add_apply,Pi.mul_apply,h2,h3]
      ring

lemma SmoothMultiplier.insertionJet_mem_domain {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    {u : Jet n L} (hu : u∈dirichletDomain n L a) :
    f.insertionJet u∈dirichletDomain (n+1) L a := by
  apply map_mem_closure f.insertionJet.continuous hu
  rintro _ ⟨g,rfl⟩
  exact ⟨g.insert f hc,g.jet_insert f hc⟩

end
end HardSphere

end
end
end
end
end
end

end OAI
