import OAI.Probability.GaussianReplacement.ConditionalLaw

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def appendEquiv (E : Type*) [MeasurableSpace E] (m r : ℕ) :
    ((Fin m→E)×(Fin r→E)) ≃ᵐ (Fin (m+r)→E) where
  toFun z := Fin.append z.1 z.2
  invFun z := ((fun i => z (Fin.castAdd r i)),fun i => z (Fin.natAdd m i))
  left_inv z := by ext i <;> simp
  right_inv z := by ext i; induction i using Fin.addCases <;> simp
  measurable_toFun := measurable_append m r
  measurable_invFun := by
    change Measurable (fun z : Fin (m+r) → E =>
      ((fun i => z (Fin.castAdd r i)),fun i => z (Fin.natAdd m i)))
    fun_prop

lemma appendEquiv_map {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (m r : ℕ) :
    ((Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi (fun _ : Fin r => μ))).map
      (appendEquiv E m r) = Measure.pi (fun _ : Fin (m+r) => μ) := map_append_pi μ m r

abbrev Observations (k d : ℕ) := Fin k → (Vector d×ℝ)

def pairObservation {d k : ℕ} (z : Rows k d×(Fin k→ℝ)) : Observations k d :=
  fun j => (z.1 j,z.2 j)

def observationEquiv (k d : ℕ) : (Rows k d×(Fin k→ℝ)) ≃ᵐ Observations k d :=
  (MeasurableEquiv.arrowProdEquivProdArrow (Vector d) ℝ (Fin k)).symm

lemma observationEquiv_apply {k d : ℕ} (z : Rows k d×(Fin k→ℝ)) :
    observationEquiv k d z = pairObservation z := rfl

def gaussianObservation (d : ℕ) : Measure (Vector d×ℝ) :=
  (stdGaussian (Vector d)).prod (gaussianReal 0 1)

instance gaussianObservation_probability (d : ℕ) : IsProbabilityMeasure (gaussianObservation d) := by
  unfold gaussianObservation; infer_instance

def gaussianObservations (k d : ℕ) : Measure (Observations k d) :=
  Measure.pi (fun _ => gaussianObservation d)

instance gaussianObservations_probability (k d : ℕ) : IsProbabilityMeasure (gaussianObservations k d) := by
  unfold gaussianObservations Observations; infer_instance

lemma gaussianObservations_eq (k d : ℕ) :
    ((gaussianRows k d).prod (gaussianLabels k)).map (observationEquiv k d) =
      gaussianObservations k d := by
  exact (measurePreserving_arrowProdEquivProdArrow (Vector d) ℝ (Fin k)
    (fun _ => stdGaussian (Vector d)) (fun _ => gaussianReal 0 1)).symm.map_eq

def ownObservations {k d : ℕ} (G : Rows k d) (s : Sphere d) : Observations k d :=
  pairObservation (G,label G (s:Vector d))

lemma measurable_ownObservations {k d : ℕ} :
    Measurable (fun z : Rows k d×Sphere d => ownObservations z.1 z.2) := by
  unfold ownObservations pairObservation label
  fun_prop

lemma ownObservations_append {i r d : ℕ} (X : Rows i d) (A : Rows r d) (s : Sphere d) :
    ownObservations (Fin.append X A) s = Fin.append (ownObservations X s) (ownObservations A s) := by
  funext j
  induction j using Fin.addCases <;> simp [ownObservations,pairObservation,label]

lemma gaussianObservations_append (i r d : ℕ) :
    ((gaussianObservations i d).prod (gaussianObservations r d)).map
      (appendEquiv (Vector d×ℝ) i r) = gaussianObservations (i+r) d :=
  appendEquiv_map (gaussianObservation d) i r

lemma conditionalReferenceKL_map_context {C D A : Type*} [MeasurableSpace C]
    [MeasurableSpace D] [MeasurableSpace A]
    (P : Measure (C×A)) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (f : C → D) (g : D → C) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    conditionalReferenceKL (P.map (Prod.map f id)) ν = conditionalReferenceKL P ν := by
  have hfst : (P.map (Prod.map f id)).fst = P.fst.map f := by
    rw [Measure.fst,Measure.map_map measurable_fst (hf.prodMap measurable_id),Measure.fst,
      Measure.map_map hf measurable_fst]
    rfl
  unfold conditionalReferenceKL
  rw [hfst,show (P.fst.map f).prod ν = (P.fst.prod ν).map (Prod.map f id) by
    rw [←Measure.map_prod_map _ _ hf measurable_id,Measure.map_id]]
  exact klDiv_map_leftInverse _ _ _ (Prod.map g id) (hf.prodMap measurable_id)
    (hg.prodMap measurable_id) (fun z => Prod.ext (hgf z.1) rfl)

lemma conditionalReferenceKL_context_equiv {C D A : Type*} [MeasurableSpace C]
    [MeasurableSpace D] [MeasurableSpace A]
    (P : Measure (C×A)) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (e : C ≃ᵐ D) :
    conditionalReferenceKL (P.map (Prod.map e id)) ν = conditionalReferenceKL P ν :=
  conditionalReferenceKL_map_context P ν e e.symm e.measurable e.symm.measurable e.left_inv


def observationReferenceKL {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : ℝ≥0∞ :=
  klDiv (observedMessage P) (((gaussianRows k d).prod (gaussianLabels k)).prod P.fst.snd)

lemma observationReferenceKL_decomposition {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows k d)) :
    observationReferenceKL P =
      klDiv (projectionJoint ν (gaussianRows k d)) ((gaussianRows k d).prod (gaussianLabels k)) +
      mutualInformation (observedMessage P) := by
  unfold observationReferenceKL
  rw [←observedMessage_snd P,mutualInformation_reference,
    observedMessage_fst_of_independence P ν (gaussianRows k d) hInd]

lemma observationReferenceKL_chain_exposed {d k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W] [Nonempty (Sphere d)]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows k d)) :
    observationReferenceKL P + exposedInformation P =
      klDiv (projectionJoint ν (gaussianRows k d)) ((gaussianRows k d).prod (gaussianLabels k)) +
      mutualInformation P.fst + rowInformation P (gaussianRows k d) := by
  rw [observationReferenceKL_decomposition P ν hInd,add_assoc,
    ←exposedInformation_chain,mutualInformation_rows_chain P ν (gaussianRows k d) hInd,add_assoc]



def snocEquiv (E : Type*) [MeasurableSpace E] (r : ℕ) :
    ((Fin r→E)×E) ≃ᵐ (Fin (r+1)→E) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r+1) => E) (Fin.last r)).symm

lemma snocEquiv_apply {E : Type*} [MeasurableSpace E] {r : ℕ} (z : (Fin r→E)×E) :
    snocEquiv E r z = Fin.snoc z.1 z.2 := by
  ext j
  induction j using Fin.lastCases <;> simp [snocEquiv,Fin.snoc,MeasurableEquiv.prodComm]

lemma snocEquiv_map {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (r : ℕ) :
    ((Measure.pi (fun _ : Fin r => μ)).prod μ).map (snocEquiv E r) =
      Measure.pi (fun _ : Fin (r+1) => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (r+1) => μ) (Fin.last r)).symm.map_eq
  change Measure.map ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r+1) => E) (Fin.last r)).symm ∘ Prod.swap) _ = _
  rw [←Measure.map_map (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (r+1) => E) (Fin.last r)).symm.measurable measurable_swap,Measure.prod_swap]
  exact h

lemma conditionalReferenceKL_outcome_equiv {C A B : Type*} [MeasurableSpace C]
    [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure (C×A)) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (e : A ≃ᵐ B) :
    conditionalReferenceKL (P.map (Prod.map id e)) (ν.map e) = conditionalReferenceKL P ν := by
  have hf : (P.map (Prod.map id e)).fst = P.fst := by
    rw [Measure.fst,Measure.map_map measurable_fst (measurable_id.prodMap e.measurable)]
    rfl
  unfold conditionalReferenceKL
  rw [hf,show P.fst.prod (ν.map e) = (P.fst.prod ν).map (Prod.map id e) by
    rw [←Measure.map_prod_map _ _ measurable_id e.measurable,Measure.map_id]]
  exact klDiv_map_leftInverse _ _ _ (Prod.map id e.symm) (measurable_id.prodMap e.measurable)
    (measurable_id.prodMap e.symm.measurable) (fun z => Prod.ext rfl (e.left_inv z.2))

def arrayResidualObservation {d r : ℕ} {C : Type*} (z : (C×Sphere d)×Rows r d) :
    (C×Observations r d)×Sphere d := ((z.1.1,ownObservations z.2 z.1.2),z.1.2)

lemma measurable_arrayResidualObservation {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (arrayResidualObservation (d:=d) (r:=r) (C:=C)) := by
  unfold arrayResidualObservation
  exact (measurable_fst.fst.prodMk (measurable_ownObservations.comp
    (measurable_snd.prodMk measurable_fst.snd))).prodMk measurable_fst.snd

def arrayResidualLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) : Measure ((C×Observations r d)×Sphere d) :=
  (Γ.prod (gaussianRows r d)).map arrayResidualObservation

instance arrayResidualLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    IsProbabilityMeasure (arrayResidualLaw Γ r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_arrayResidualObservation.aemeasurable).mpr inferInstance

def freshArrayLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) : Measure (C×Observations r d) := (arrayResidualLaw Γ r).fst

instance freshArrayLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    IsProbabilityMeasure (freshArrayLaw Γ r) := by unfold freshArrayLaw; infer_instance

def freshReference {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) : ℝ≥0∞ :=
  conditionalReferenceKL (freshArrayLaw Γ r) (gaussianObservations r d)

def freshSlope {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) : ℝ≥0∞ :=
  conditionalReferenceKL (scalarObservationLaw (arrayResidualLaw Γ r)) (gaussianReal 0 1)

lemma freshArrayLaw_eq {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) :
    freshArrayLaw Γ r = (Γ.prod (gaussianRows r d)).map
      (fun z => (z.1.1,ownObservations z.2 z.1.2)) := by
  rw [freshArrayLaw,arrayResidualLaw,Measure.fst,Measure.map_map measurable_fst measurable_arrayResidualObservation]
  rfl

lemma freshArrayLaw_fst {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    (freshArrayLaw Γ r).fst = Γ.fst := by
  have hm : Measurable (fun z : (C×Sphere d)×Rows r d => (z.1.1,ownObservations z.2 z.1.2)) :=
    measurable_fst.fst.prodMk (measurable_ownObservations.comp (measurable_snd.prodMk measurable_fst.snd))
  rw [freshArrayLaw_eq,Measure.fst,Measure.map_map measurable_fst hm]
  change (Γ.prod (gaussianRows r d)).map (Prod.fst ∘ Prod.fst) = _
  rw [←Measure.map_map measurable_fst measurable_fst]
  change (Γ.prod (gaussianRows r d)).fst.fst = Γ.fst
  rw [Measure.fst_prod]

lemma arrayResidualLaw_eq {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) (r : ℕ) :
    arrayResidualLaw Γ r = (residualLaw Γ r).map
      (Prod.map (Prod.map id (observationEquiv r d)) id) := by
  rw [residualLaw,Measure.map_map
    ((measurable_id.prodMap (observationEquiv r d).measurable).prodMap measurable_id)
    measurable_residualObservation]
  rfl

lemma scalarObservationLaw_context {d : ℕ} {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (Γ : Measure (C×Sphere d)) [SFinite Γ] (f : C → D) (hf : Measurable f) :
    scalarObservationLaw (Γ.map (Prod.map f id)) = (scalarObservationLaw Γ).map
      (Prod.map (Prod.map f id) id) := by
  rw [scalarObservationLaw,show (Γ.map (Prod.map f id)).prod (stdGaussian (Vector d)) =
      (Γ.prod (stdGaussian (Vector d))).map (Prod.map (Prod.map f id) id) by
    rw [←Measure.map_prod_map _ _ (hf.prodMap measurable_id) measurable_id,Measure.map_id],
    Measure.map_map measurable_scalarObservation ((hf.prodMap measurable_id).prodMap measurable_id),
    scalarObservationLaw,Measure.map_map ((hf.prodMap measurable_id).prodMap measurable_id)
      measurable_scalarObservation]
  rfl

lemma freshSlope_eq {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    freshSlope Γ r = conditionalReferenceKL (scalarObservationLaw (residualLaw Γ r)) (gaussianReal 0 1) := by
  rw [freshSlope,arrayResidualLaw_eq,scalarObservationLaw_context _ _
    (measurable_id.prodMap (observationEquiv r d).measurable)]
  exact conditionalReferenceKL_context_equiv _ _
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl C) (observationEquiv r d)).prodCongr
      (MeasurableEquiv.refl (Vector d)))

lemma ownObservations_snoc {d r : ℕ} (G : Rows r d) (x : Vector d) (s : Sphere d) :
    ownObservations (Fin.snoc G x) s = Fin.snoc (ownObservations G s) (x,⟪(s:Vector d),x⟫) := by
  funext j
  induction j using Fin.lastCases <;> simp [ownObservations,pairObservation,label]

lemma prod_append_gaussian_map {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [SigmaFinite μ] (d r s : ℕ) :
    (((μ.prod (gaussianRows r d)).prod (gaussianRows s d)).map
      (fun z => (z.1.1,Fin.append z.1.2 z.2))) = μ.prod (gaussianRows (r+s) d) := by
  have h := map_append_pi (stdGaussian (Vector d)) r s
  change ((gaussianRows r d).prod (gaussianRows s d)).map (fun z => Fin.append z.1 z.2) = gaussianRows (r+s) d at h
  have hp := Measure.map_prod_map μ ((gaussianRows r d).prod (gaussianRows s d)) measurable_id (measurable_append r s)
  simp only [Measure.map_id] at hp
  rw [←h,hp,
    ←Measure.prodAssoc_prod,Measure.map_map (measurable_id.prodMap (measurable_append r s))
      MeasurableEquiv.prodAssoc.measurable]
  rfl

lemma arrayResidualLaw_append {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r s : ℕ) :
    arrayResidualLaw Γ (r+s) = (arrayResidualLaw (arrayResidualLaw Γ r) s).map
      (fun z => ((z.1.1.1,Fin.append z.1.1.2 z.1.2),z.2)) := by
  have hm : Measurable (fun z : ((C×Observations r d)×Observations s d)×Sphere d =>
      ((z.1.1.1,Fin.append z.1.1.2 z.1.2),z.2)) :=
    (measurable_fst.fst.fst.prodMk ((measurable_append r s).comp
      (measurable_fst.fst.snd.prodMk measurable_fst.snd))).prodMk measurable_snd
  have hm0 : Measurable (fun z : ((C×Sphere d)×Rows r d)×Rows s d => (z.1.1,Fin.append z.1.2 z.2)) :=
    measurable_fst.fst.prodMk ((measurable_append r s).comp (measurable_fst.snd.prodMk measurable_snd))
  rw [arrayResidualLaw,←prod_append_gaussian_map Γ d r s,
    Measure.map_map measurable_arrayResidualObservation hm0]
  rw [arrayResidualLaw,Measure.map_map hm measurable_arrayResidualObservation,arrayResidualLaw,
    show ((Γ.prod (gaussianRows r d)).map arrayResidualObservation).prod (gaussianRows s d) =
      (((Γ.prod (gaussianRows r d)).prod (gaussianRows s d))).map
        (Prod.map arrayResidualObservation id) by
      rw [←Measure.map_prod_map _ _ measurable_arrayResidualObservation measurable_id,Measure.map_id],
    Measure.map_map (hm.comp measurable_arrayResidualObservation)
      (measurable_arrayResidualObservation.prodMap measurable_id)]
  congr 1
  funext z
  simp only [Function.comp_apply,Prod.map,arrayResidualObservation,ownObservations_append,id_eq]

lemma freshArrayLaw_append {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r s : ℕ) :
    freshArrayLaw Γ (r+s) = (freshArrayLaw (arrayResidualLaw Γ r) s).map
      (fun z => (z.1.1,Fin.append z.1.2 z.2)) := by
  have hm : Measurable (fun z : ((C×Observations r d)×Observations s d)×Sphere d =>
      ((z.1.1.1,Fin.append z.1.1.2 z.1.2),z.2)) :=
    (measurable_fst.fst.fst.prodMk ((measurable_append r s).comp
      (measurable_fst.fst.snd.prodMk measurable_fst.snd))).prodMk measurable_snd
  have hm' : Measurable (fun z : (C×Observations r d)×Observations s d =>
      (z.1.1,Fin.append z.1.2 z.2)) :=
    measurable_fst.fst.prodMk ((measurable_append r s).comp (measurable_fst.snd.prodMk measurable_snd))
  rw [freshArrayLaw,arrayResidualLaw_append,Measure.fst,Measure.map_map measurable_fst hm,
    freshArrayLaw,Measure.fst,Measure.map_map hm' measurable_fst]
  rfl

lemma freshReference_append {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r s : ℕ) :
    freshReference Γ (r+s) = freshReference Γ r + freshReference (arrayResidualLaw Γ r) s := by
  let P := freshArrayLaw (arrayResidualLaw Γ r) s
  let Q := P.map MeasurableEquiv.prodAssoc
  let : IsProbabilityMeasure Q := inferInstance
  have hQ : Q.map (Prod.map id (appendEquiv (Vector d×ℝ) r s)) = freshArrayLaw Γ (r+s) := by
    dsimp only [Q]
    rw [Measure.map_map (measurable_id.prodMap (appendEquiv _ _ _).measurable)
      MeasurableEquiv.prodAssoc.measurable,freshArrayLaw_append]
    rfl
  have hQf : Q.map (Prod.map id Prod.fst) = freshArrayLaw Γ r := by
    dsimp only [Q]
    rw [Measure.map_map (measurable_id.prodMap measurable_fst) MeasurableEquiv.prodAssoc.measurable]
    change P.fst = freshArrayLaw Γ r
    exact freshArrayLaw_fst _ _
  have hQa : Q.map MeasurableEquiv.prodAssoc.symm = P := MeasurableEquiv.map_symm_map _
  have h := conditionalReferenceKL_outcome_equiv Q
    ((gaussianObservations r d).prod (gaussianObservations s d)) (appendEquiv (Vector d×ℝ) r s)
  rw [hQ,gaussianObservations_append,conditionalReferenceKL_chain Q,hQf,hQa] at h
  exact h



def singleResidualObservation {d : ℕ} {C : Type*} (z : (C×Sphere d)×Vector d) :
    (C×(Vector d×ℝ))×Sphere d := ((z.1.1,(z.2,⟪(z.1.2:Vector d),z.2⟫)),z.1.2)

lemma measurable_singleResidualObservation {d : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (singleResidualObservation (d:=d) (C:=C)) := by
  unfold singleResidualObservation; fun_prop

def singleSignalLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) : Measure ((C×(Vector d×ℝ))×Sphere d) :=
  P.map singleResidualObservation

instance singleSignalLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (singleSignalLaw P) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_singleResidualObservation.aemeasurable).mpr inferInstance

def singleObservationLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) : Measure (C×(Vector d×ℝ)) := (singleSignalLaw P).fst

instance singleObservationLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (singleObservationLaw P) := by unfold singleObservationLaw; infer_instance

def singleReference {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) : ℝ≥0∞ :=
  conditionalReferenceKL (singleObservationLaw P) (gaussianObservation d)

lemma singleObservationLaw_eq {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) :
    singleObservationLaw P = P.map (fun z => (z.1.1,(z.2,⟪(z.1.2:Vector d),z.2⟫))) := by
  rw [singleObservationLaw,singleSignalLaw,Measure.fst,Measure.map_map measurable_fst measurable_singleResidualObservation]
  rfl

lemma singleObservationLaw_fst {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) : (singleObservationLaw P).fst = P.fst.fst := by
  have hm : Measurable (fun z : (C×Sphere d)×Vector d => (z.1.1,(z.2,⟪(z.1.2:Vector d),z.2⟫))) := by fun_prop
  rw [singleObservationLaw_eq,Measure.fst,Measure.map_map measurable_fst hm,
    Measure.fst,Measure.fst,Measure.map_map measurable_fst measurable_fst]
  rfl

lemma singleObservationLaw_scalar {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) :
    singleObservationLaw (Γ.prod (stdGaussian (Vector d))) =
      (scalarObservationLaw Γ).map MeasurableEquiv.prodAssoc := by
  rw [singleObservationLaw_eq,scalarObservationLaw,
    Measure.map_map MeasurableEquiv.prodAssoc.measurable measurable_scalarObservation]
  rfl

lemma singleReference_fresh {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    singleReference (Γ.prod (stdGaussian (Vector d))) =
      conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) := by
  let P := singleObservationLaw (Γ.prod (stdGaussian (Vector d)))
  have hfst : P.map (Prod.map id Prod.fst) = Γ.fst.prod (stdGaussian (Vector d)) := by
    dsimp only [P]
    rw [singleObservationLaw_eq,Measure.map_map (measurable_id.prodMap measurable_fst) (by fun_prop)]
    change (Γ.prod (stdGaussian (Vector d))).map (Prod.map Prod.fst id) = _
    rw [←Measure.map_prod_map Γ _ measurable_fst measurable_id,Measure.map_id]
    rfl
  have ha : P.map MeasurableEquiv.prodAssoc.symm = scalarObservationLaw Γ := by
    dsimp only [P]
    rw [singleObservationLaw_scalar,MeasurableEquiv.map_symm_map]
  change conditionalReferenceKL P ((stdGaussian (Vector d)).prod (gaussianReal 0 1)) = _
  rw [conditionalReferenceKL_chain,hfst,ha,conditionalReferenceKL,Measure.fst_prod,klDiv_self,zero_add]

lemma gaussianRows_one (d : ℕ) :
    (gaussianRows 1 d).map (MeasurableEquiv.funUnique (Fin 1) (Vector d)) = stdGaussian (Vector d) :=
  (measurePreserving_funUnique (stdGaussian (Vector d)) (Fin 1)).map_eq

lemma gaussianObservations_one (d : ℕ) :
    (gaussianObservations 1 d).map (MeasurableEquiv.funUnique (Fin 1) (Vector d×ℝ)) = gaussianObservation d :=
  (measurePreserving_funUnique (gaussianObservation d) (Fin 1)).map_eq

lemma singleSignalLaw_fresh {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    singleSignalLaw (Γ.prod (stdGaussian (Vector d))) = (arrayResidualLaw Γ 1).map
      (Prod.map (Prod.map id (MeasurableEquiv.funUnique (Fin 1) (Vector d×ℝ))) id) := by
  have hprod : Γ.prod (stdGaussian (Vector d)) = (Γ.prod (gaussianRows 1 d)).map
      (Prod.map id (MeasurableEquiv.funUnique (Fin 1) (Vector d))) := by
    rw [←Measure.map_prod_map Γ _ measurable_id (MeasurableEquiv.funUnique _ _).measurable,
      Measure.map_id,gaussianRows_one]
  rw [singleSignalLaw,hprod,Measure.map_map measurable_singleResidualObservation
    (measurable_id.prodMap (MeasurableEquiv.funUnique _ _).measurable),arrayResidualLaw,
    Measure.map_map ((measurable_id.prodMap (MeasurableEquiv.funUnique _ _).measurable).prodMap measurable_id)
      measurable_arrayResidualObservation]
  rfl

lemma freshReference_one {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    freshReference Γ 1 = conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) := by
  have he : singleObservationLaw (Γ.prod (stdGaussian (Vector d))) = (freshArrayLaw Γ 1).map
      (Prod.map id (MeasurableEquiv.funUnique (Fin 1) (Vector d×ℝ))) := by
    rw [singleObservationLaw,singleSignalLaw_fresh,Measure.fst,
      Measure.map_map measurable_fst ((measurable_id.prodMap (MeasurableEquiv.funUnique _ _).measurable).prodMap measurable_id),
      freshArrayLaw,Measure.fst,Measure.map_map (measurable_id.prodMap (MeasurableEquiv.funUnique _ _).measurable) measurable_fst]
    rfl
  have h := conditionalReferenceKL_outcome_equiv (freshArrayLaw Γ 1) (gaussianObservations 1 d)
    (MeasurableEquiv.funUnique (Fin 1) (Vector d×ℝ))
  rw [←he,gaussianObservations_one] at h
  exact h.symm.trans (singleReference_fresh Γ)

lemma freshReference_succ {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    freshReference Γ (r+1) = freshReference Γ r + freshSlope Γ r := by
  rw [freshReference_append,freshReference_one]
  rfl

lemma arrayResidualLaw_context {d : ℕ} {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (Γ : Measure (C×Sphere d)) [SFinite Γ] (r : ℕ) (f : C → D) (hf : Measurable f) :
    arrayResidualLaw (Γ.map (Prod.map f id)) r = (arrayResidualLaw Γ r).map
      (Prod.map (Prod.map f id) id) := by
  rw [arrayResidualLaw,show (Γ.map (Prod.map f id)).prod (gaussianRows r d) =
      (Γ.prod (gaussianRows r d)).map (Prod.map (Prod.map f id) id) by
    rw [←Measure.map_prod_map _ _ (hf.prodMap measurable_id) measurable_id,Measure.map_id],
    Measure.map_map measurable_arrayResidualObservation ((hf.prodMap measurable_id).prodMap measurable_id),
    arrayResidualLaw,Measure.map_map ((hf.prodMap measurable_id).prodMap measurable_id)
      measurable_arrayResidualObservation]
  rfl

lemma freshReference_context {d : ℕ} {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) (e : C ≃ᵐ D) :
    freshReference (Γ.map (Prod.map e id)) r = freshReference Γ r := by
  have hf : freshArrayLaw (Γ.map (Prod.map e id)) r =
      (freshArrayLaw Γ r).map (Prod.map e id) := by
    rw [freshArrayLaw,arrayResidualLaw_context _ _ _ e.measurable,Measure.fst,
      Measure.map_map measurable_fst ((e.measurable.prodMap measurable_id).prodMap measurable_id),
      freshArrayLaw,Measure.fst,Measure.map_map (e.measurable.prodMap measurable_id) measurable_fst]
    rfl
  rw [freshReference,hf]
  exact conditionalReferenceKL_context_equiv _ _ e

lemma freshSlope_context {d : ℕ} {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) (e : C ≃ᵐ D) :
    freshSlope (Γ.map (Prod.map e id)) r = freshSlope Γ r := by
  rw [freshSlope,arrayResidualLaw_context _ _ _ e.measurable,scalarObservationLaw_context _ _
    (e.measurable.prodMap measurable_id)]
  exact conditionalReferenceKL_context_equiv _ _
    ((e.prodCongr (MeasurableEquiv.refl (Observations r d))).prodCongr (MeasurableEquiv.refl (Vector d)))

lemma arrayResidualLaw_keep {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    (arrayResidualLaw Γ r).map (fun z => (z.1.1,z.2)) = Γ := by
  rw [arrayResidualLaw,Measure.map_map (measurable_fst.fst.prodMk measurable_snd)
    measurable_arrayResidualObservation]
  change (Γ.prod (gaussianRows r d)).fst = Γ
  exact Measure.fst_prod

lemma arrayResidualLaw_drop_last {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    (arrayResidualLaw Γ (r+1)).map
      (Prod.map (fun z => (z.1,fun j : Fin r => z.2 (Fin.castAdd 1 j))) id) = arrayResidualLaw Γ r := by
  have hm : Measurable (fun z : ((C×Observations r d)×Observations 1 d)×Sphere d =>
      ((z.1.1.1,Fin.append z.1.1.2 z.1.2),z.2)) := by
    apply Measurable.prodMk _ measurable_snd
    exact measurable_fst.fst.fst.prodMk ((measurable_append r 1).comp
      (measurable_fst.fst.snd.prodMk measurable_fst.snd))
  have hf : Measurable (fun z : C×Observations (r+1) d =>
      (z.1,fun j : Fin r => z.2 (Fin.castAdd 1 j))) := by fun_prop
  rw [arrayResidualLaw_append,Measure.map_map (hf.prodMap measurable_id) hm]
  have he : (Prod.map (fun z : C×Observations (r+1) d =>
      (z.1,fun j : Fin r => z.2 (Fin.castAdd 1 j))) id) ∘
      (fun z : ((C×Observations r d)×Observations 1 d)×Sphere d =>
        ((z.1.1.1,Fin.append z.1.1.2 z.1.2),z.2)) = (fun z => (z.1.1,z.2)) := by
    funext z
    simp [Prod.map]
  rw [he,arrayResidualLaw_keep]

lemma conditionalReferenceKL_map_context_le {C D A : Type*} [MeasurableSpace C]
    [MeasurableSpace D] [MeasurableSpace A]
    (P : Measure (C×A)) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (f : C → D) (hf : Measurable f) :
    conditionalReferenceKL (P.map (Prod.map f id)) ν ≤ conditionalReferenceKL P ν := by
  have hfst : (P.map (Prod.map f id)).fst = P.fst.map f := by
    rw [Measure.fst,Measure.map_map measurable_fst (hf.prodMap measurable_id),Measure.fst,
      Measure.map_map hf measurable_fst]
    rfl
  unfold conditionalReferenceKL
  rw [hfst,show (P.fst.map f).prod ν = (P.fst.prod ν).map (Prod.map f id) by
    rw [←Measure.map_prod_map _ _ hf measurable_id,Measure.map_id]]
  exact klDiv_map_le _ _ (hf.prodMap measurable_id)

lemma freshSlope_monotone {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] : Monotone (freshSlope Γ) := by
  apply monotone_nat_of_le_succ
  intro r
  let f : C×Observations (r+1) d → C×Observations r d :=
    fun z => (z.1,fun j : Fin r => z.2 (Fin.castAdd 1 j))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : arrayResidualLaw Γ r = (arrayResidualLaw Γ (r+1)).map (Prod.map f id) :=
    (arrayResidualLaw_drop_last Γ r).symm
  rw [freshSlope,he,scalarObservationLaw_context _ _ hf]
  exact conditionalReferenceKL_map_context_le _ _ (Prod.map f id) (hf.prodMap measurable_id)

lemma freshReference_monotone {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] : Monotone (freshReference Γ) := by
  apply monotone_nat_of_le_succ
  intro r
  rw [freshReference_succ]
  exact le_add_right le_rfl

lemma freshSlope_mul_le {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r h : ℕ) :
    (h:ℝ≥0∞)*freshSlope Γ r ≤ freshReference Γ (r+h) := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,Nat.add_succ,freshReference_succ]
      exact add_le_add ih (freshSlope_monotone Γ (by omega))

lemma freshSlope_average {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r h : ℕ) (hh : 1 ≤ h)
    (hfin : freshReference Γ (r+h) ≠ ∞) :
    freshSlope Γ r ≠ ∞ ∧ (freshSlope Γ r).toReal ≤ (freshReference Γ (r+h)).toReal / h := by
  have hle : freshSlope Γ r ≤ freshReference Γ (r+h) := by
    apply le_trans _ (freshReference_monotone Γ (show r+1 ≤ r+h by omega))
    rw [freshReference_succ]
    exact le_add_left le_rfl
  have hTf := ne_top_of_le_ne_top hfin hle
  refine ⟨hTf,?_⟩
  have hb := ENNReal.toReal_mono hfin (freshSlope_mul_le Γ r h)
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hb
  apply (le_div_iff₀ (show (0:ℝ)<h by exact_mod_cast (show 0<h by omega))).mpr
  nlinarith

lemma scalarReference_context {d : ℕ} {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (e : C ≃ᵐ D) :
    conditionalReferenceKL (scalarObservationLaw (Γ.map (Prod.map e id))) (gaussianReal 0 1) =
      conditionalReferenceKL (scalarObservationLaw Γ) (gaussianReal 0 1) := by
  rw [scalarObservationLaw_context _ _ e.measurable]
  exact conditionalReferenceKL_context_equiv _ _ (e.prodCongr (MeasurableEquiv.refl (Vector d)))

lemma freshSlope_succ {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    freshSlope Γ (r+1) = conditionalReferenceKL
      (scalarObservationLaw (singleSignalLaw ((arrayResidualLaw Γ r).prod (stdGaussian (Vector d)))))
      (gaussianReal 0 1) := by
  let e : ((C×Observations r d)×Observations 1 d) ≃ᵐ C×Observations (r+1) d :=
    MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl C).prodCongr (appendEquiv (Vector d×ℝ) r 1))
  have he : arrayResidualLaw Γ (r+1) = (arrayResidualLaw (arrayResidualLaw Γ r) 1).map (Prod.map e id) :=
    arrayResidualLaw_append Γ r 1
  rw [freshSlope,he,scalarReference_context,singleSignalLaw_fresh]
  exact (scalarReference_context _ ((MeasurableEquiv.refl (C×Observations r d)).prodCongr
    (MeasurableEquiv.funUnique (Fin 1) (Vector d×ℝ)))).symm



end CurrentProjection

end

end OAI
