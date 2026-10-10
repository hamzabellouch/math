import OAI.Probability.GaussianReplacement.Observation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def exchangeMiddle (C A B D : Type*) [MeasurableSpace C] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace D] :
    ((C×(A×B))×D) ≃ᵐ ((C×(A×D))×B) where
  toFun z := ((z.1.1,(z.1.2.1,z.2)),z.1.2.2)
  invFun z := ((z.1.1,(z.1.2.1,z.2)),z.1.2.2)
  left_inv z := by rcases z with ⟨⟨c,a,b⟩,d⟩; rfl
  right_inv z := by rcases z with ⟨⟨c,a,d⟩,b⟩; rfl
  measurable_toFun := (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd)).prodMk measurable_fst.snd.snd
  measurable_invFun := (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd)).prodMk measurable_fst.snd.snd

lemma cauchyObservationLaw_single {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    cauchyObservationLaw Γ =
      (scalarObservationLaw (singleSignalLaw (Γ.prod (stdGaussian (Vector d))))).map
        (Prod.map (exchangeMiddle C (Vector d) ℝ (Vector d)) id) := by
  rw [scalarObservationLaw,singleSignalLaw,
    show ((Γ.prod (stdGaussian (Vector d))).map singleResidualObservation).prod
        (stdGaussian (Vector d)) =
        ((Γ.prod (stdGaussian (Vector d))).prod (stdGaussian (Vector d))).map
          (Prod.map singleResidualObservation id) by
      rw [←Measure.map_prod_map _ _ measurable_singleResidualObservation measurable_id,Measure.map_id],
    Measure.map_map measurable_scalarObservation (measurable_singleResidualObservation.prodMap measurable_id),
    Measure.map_map ((exchangeMiddle C (Vector d) ℝ (Vector d)).measurable.prodMap measurable_id)
      (measurable_scalarObservation.comp (measurable_singleResidualObservation.prodMap measurable_id))]
  rw [cauchyObservationLaw,show gaussianVectorPair d = (stdGaussian (Vector d)).prod (stdGaussian (Vector d)) from rfl,
    ←Measure.prodAssoc_prod,Measure.map_map measurable_cauchyObservation MeasurableEquiv.prodAssoc.measurable]
  rfl

lemma cauchyReference_single {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] :
    conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1) =
      conditionalReferenceKL
        (scalarObservationLaw (singleSignalLaw (Γ.prod (stdGaussian (Vector d))))) (gaussianReal 0 1) := by
  rw [cauchyObservationLaw_single,conditionalReferenceKL_context_equiv]

lemma cauchyReference_context {d : ℕ} {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (e : C ≃ᵐ D) :
    conditionalReferenceKL (cauchyObservationLaw (Γ.map (Prod.map e id))) (gaussianReal 0 1) =
      conditionalReferenceKL (cauchyObservationLaw Γ) (gaussianReal 0 1) := by
  have he : cauchyObservationLaw (Γ.map (Prod.map e id)) =
      (cauchyObservationLaw Γ).map (Prod.map
        ((e.prodCongr (MeasurableEquiv.refl (Vector d×Vector d))).prodCongr (MeasurableEquiv.refl ℝ)) id) := by
    rw [cauchyObservationLaw,show (Γ.map (Prod.map e id)).prod (gaussianVectorPair d) =
      (Γ.prod (gaussianVectorPair d)).map (Prod.map (Prod.map e id) id) by
        rw [←Measure.map_prod_map _ _ (e.measurable.prodMap measurable_id) measurable_id,Measure.map_id],
      Measure.map_map measurable_cauchyObservation ((e.measurable.prodMap measurable_id).prodMap measurable_id),
      cauchyObservationLaw,Measure.map_map (by fun_prop) measurable_cauchyObservation]
    rfl
  rw [he,conditionalReferenceKL_context_equiv]

lemma freshSlope_next_residual {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [IsProbabilityMeasure Γ] (r : ℕ) :
    freshSlope Γ (r+1) =
      conditionalReferenceKL (cauchyObservationLaw (residualLaw Γ r)) (gaussianReal 0 1) := by
  rw [freshSlope_succ,←cauchyReference_single,arrayResidualLaw_eq]
  exact cauchyReference_context _ ((MeasurableEquiv.refl C).prodCongr (observationEquiv r d))

def liftActualObservation {d r : ℕ} {C : Type*} (w : ((C×Sphere d)×Vector d)×Rows r d) :
    (((C×Observations r d)×Sphere d)×Vector d) :=
  (((w.1.1.1,ownObservations w.2 w.1.1.2),w.1.1.2),w.1.2)

lemma measurable_liftActualObservation {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (liftActualObservation (d:=d) (r:=r) (C:=C)) := by
  unfold liftActualObservation
  exact ((measurable_fst.fst.fst.prodMk (measurable_ownObservations.comp
    (measurable_snd.prodMk measurable_fst.fst.snd))).prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd

def liftActualLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) (r : ℕ) : Measure (((C×Observations r d)×Sphere d)×Vector d) :=
  (P.prod (gaussianRows r d)).map liftActualObservation

instance liftActualLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    IsProbabilityMeasure (liftActualLaw P r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_liftActualObservation.aemeasurable).mpr inferInstance

lemma liftActualLaw_fst {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    (liftActualLaw P r).fst = arrayResidualLaw P.fst r := by
  rw [liftActualLaw,Measure.fst,Measure.map_map measurable_fst measurable_liftActualObservation,
    arrayResidualLaw,show P.fst.prod (gaussianRows r d) =
      (P.prod (gaussianRows r d)).map (Prod.map Prod.fst id) by
        rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]; rfl,
    Measure.map_map measurable_arrayResidualObservation (measurable_fst.prodMap measurable_id)]
  rfl

def actualFreshArrayLaw {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) (r : ℕ) :
    Measure (C×((Vector d×ℝ)×Observations r d)) :=
  (P.prod (gaussianRows r d)).map (fun w =>
    (w.1.1.1,((w.1.2,⟪(w.1.1.2:Vector d),w.1.2⟫),ownObservations w.2 w.1.1.2)))

lemma measurable_actualFreshArray {d r : ℕ} {C : Type*} [MeasurableSpace C] :
    Measurable (fun w : ((C×Sphere d)×Vector d)×Rows r d =>
      (w.1.1.1,((w.1.2,⟪(w.1.1.2:Vector d),w.1.2⟫),ownObservations w.2 w.1.1.2))) := by
  apply Measurable.prodMk measurable_fst.fst.fst
  exact (measurable_fst.snd.prodMk (by fun_prop)).prodMk
    (measurable_ownObservations.comp (measurable_snd.prodMk measurable_fst.fst.snd))

instance actualFreshArrayLaw_probability {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    IsProbabilityMeasure (actualFreshArrayLaw P r) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_actualFreshArray.aemeasurable).mpr inferInstance

lemma actualFreshArrayLaw_first {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    (actualFreshArrayLaw P r).map (Prod.map id Prod.fst) = singleObservationLaw P := by
  rw [actualFreshArrayLaw,Measure.map_map (measurable_id.prodMap measurable_fst) measurable_actualFreshArray]
  have h : (Prod.map id Prod.fst) ∘ (fun w : ((C×Sphere d)×Vector d)×Rows r d =>
      (w.1.1.1,((w.1.2,⟪(w.1.1.2:Vector d),w.1.2⟫),ownObservations w.2 w.1.1.2))) =
      (fun z : (C×Sphere d)×Vector d => (z.1.1,(z.2,⟪(z.1.2:Vector d),z.2⟫))) ∘ Prod.fst := rfl
  rw [h,←Measure.map_map (by fun_prop) measurable_fst]
  change (P.prod (gaussianRows r d)).fst.map _ = _
  rw [Measure.fst_prod,singleObservationLaw_eq]

attribute [fun_prop] measurable_ownObservations

lemma actualFreshArrayLaw_second {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    (actualFreshArrayLaw P r).map MeasurableEquiv.prodAssoc.symm = freshArrayLaw (singleSignalLaw P) r := by
  rw [actualFreshArrayLaw,Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable measurable_actualFreshArray,
    freshArrayLaw_eq,singleSignalLaw,show (P.map singleResidualObservation).prod (gaussianRows r d) =
      (P.prod (gaussianRows r d)).map (Prod.map singleResidualObservation id) by
        rw [←Measure.map_prod_map _ _ measurable_singleResidualObservation measurable_id,Measure.map_id],
    Measure.map_map (by fun_prop)
      (measurable_singleResidualObservation.prodMap measurable_id)]
  rfl

lemma actualFreshArrayLaw_swapped_first {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    ((actualFreshArrayLaw P r).map (Prod.map id Prod.swap)).map (Prod.map id Prod.fst) =
      freshArrayLaw P.fst r := by
  rw [actualFreshArrayLaw,Measure.map_map (measurable_id.prodMap measurable_swap) measurable_actualFreshArray,
    Measure.map_map (measurable_id.prodMap measurable_fst)
      ((measurable_id.prodMap measurable_swap).comp measurable_actualFreshArray),
    freshArrayLaw_eq,show P.fst.prod (gaussianRows r d) =
      (P.prod (gaussianRows r d)).map (Prod.map Prod.fst id) by
        rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]; rfl,
    Measure.map_map (by fun_prop)
      (measurable_fst.prodMap measurable_id)]
  rfl

lemma actualFreshArrayLaw_swapped_second {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    ((actualFreshArrayLaw P r).map (Prod.map id Prod.swap)).map MeasurableEquiv.prodAssoc.symm =
      singleObservationLaw (liftActualLaw P r) := by
  rw [actualFreshArrayLaw,Measure.map_map (measurable_id.prodMap measurable_swap) measurable_actualFreshArray,
    Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      ((measurable_id.prodMap measurable_swap).comp measurable_actualFreshArray),
    singleObservationLaw_eq,liftActualLaw,
    Measure.map_map (by fun_prop) measurable_liftActualObservation]
  rfl

lemma actual_fresh_diamond {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    singleReference P + freshReference (singleSignalLaw P) r =
      freshReference P.fst r + singleReference (liftActualLaw P r) := by
  let : IsProbabilityMeasure ((actualFreshArrayLaw P r).map (Prod.map id Prod.swap)) :=
    inferInstance
  have he := conditionalReferenceKL_outcome_equiv (actualFreshArrayLaw P r)
    ((gaussianObservation d).prod (gaussianObservations r d)) MeasurableEquiv.prodComm
  change conditionalReferenceKL ((actualFreshArrayLaw P r).map (Prod.map id Prod.swap))
    (((gaussianObservation d).prod (gaussianObservations r d)).map Prod.swap) = _ at he
  rw [Measure.prod_swap] at he
  rw [conditionalReferenceKL_chain,actualFreshArrayLaw_swapped_first,actualFreshArrayLaw_swapped_second,
    conditionalReferenceKL_chain,actualFreshArrayLaw_first,actualFreshArrayLaw_second] at he
  exact he.symm


lemma residualLabelLaw_to_single {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) (r : ℕ) :
    (residualLabelLaw P r).map
      (MeasurableEquiv.prodAssoc.trans
        (((MeasurableEquiv.refl C).prodCongr (observationEquiv r d)).prodCongr
          (MeasurableEquiv.refl (Vector d×ℝ)))) =
      singleObservationLaw (liftActualLaw P r) := by
  rw [residualLabelLaw,Measure.map_map (MeasurableEquiv.measurable _) measurable_residualLabelObservation,
    singleObservationLaw_eq,liftActualLaw,Measure.map_map (by fun_prop) measurable_liftActualObservation]
  rfl

lemma scalarObservationLaw_fst_direct {d : ℕ} {C : Type*} [MeasurableSpace C]
    (Γ : Measure (C×Sphere d)) [SFinite Γ] :
    (scalarObservationLaw Γ).fst = Γ.fst.prod (stdGaussian (Vector d)) := by
  rw [scalarObservationLaw,Measure.fst,Measure.map_map measurable_fst measurable_scalarObservation]
  change (Γ.prod (stdGaussian (Vector d))).map (Prod.map Prod.fst id) = _
  rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
  rfl

lemma singleReference_lift_eq {d : ℕ} {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P] (r : ℕ) :
    singleReference (liftActualLaw P r) = klDiv (residualLabelLaw P r)
      ((scalarObservationLaw (residualLaw P.fst r)).fst.prod (gaussianReal 0 1)) := by
  let e := (MeasurableEquiv.refl C).prodCongr (observationEquiv r d)
  let e' := MeasurableEquiv.prodAssoc.trans (e.prodCongr (MeasurableEquiv.refl (Vector d×ℝ)))
  have hbase : ((residualLaw P.fst r).fst).map e = freshArrayLaw P.fst r := by
    rw [freshArrayLaw,arrayResidualLaw_eq]
    simp only [Measure.fst]
    rw [Measure.map_map e.measurable measurable_fst,
      Measure.map_map measurable_fst ((measurable_id.prodMap (observationEquiv r d).measurable).prodMap measurable_id)]
    rfl
  have hfst : (singleObservationLaw (liftActualLaw P r)).fst = freshArrayLaw P.fst r := by
    rw [singleObservationLaw_fst,liftActualLaw_fst]; rfl
  have href : ((scalarObservationLaw (residualLaw P.fst r)).fst.prod (gaussianReal 0 1)).map e' =
      (freshArrayLaw P.fst r).prod (gaussianObservation d) := by
    rw [scalarObservationLaw_fst_direct]
    change (((residualLaw P.fst r).fst.prod (stdGaussian (Vector d))).prod (gaussianReal 0 1)).map
      (e.prodCongr (MeasurableEquiv.refl (Vector d×ℝ)) ∘ MeasurableEquiv.prodAssoc) = _
    rw [←Measure.map_map (e.prodCongr (MeasurableEquiv.refl (Vector d×ℝ))).measurable
      MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod]
    change (((residualLaw P.fst r).fst).prod (gaussianObservation d)).map (Prod.map e id) = _
    rw [←Measure.map_prod_map _ _ e.measurable measurable_id,Measure.map_id,hbase]
  rw [singleReference,conditionalReferenceKL,hfst,
    ←residualLabelLaw_to_single P r,←href]
  exact klDiv_map_equiv _ _ e'

lemma actual_fresh_row_bound {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 1 ≤ q) (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (hfresh : freshSlope P.fst r ≠ ∞) (hnext : freshSlope P.fst (r+1) ≠ ∞)
    (hlabel : (residualLabelLaw P r).snd = gaussianReal 0 1) :
    singleReference (liftActualLaw P r) ≠ ∞ ∧
    (singleReference (liftActualLaw P r)).toReal ≤
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal +
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q + hybridRowConstant +
      (freshSlope P.fst (r+1)).toReal := by
  rw [singleReference_lift_eq,freshSlope_next_residual] at ⊢
  rw [freshSlope_eq] at hfresh
  rw [freshSlope_next_residual] at hnext
  exact residual_reference_bound P hKL hr hd hq hqr hmargin hfresh hnext hlabel




def initialArray {E : Type*} {i m : ℕ} (hi : i ≤ m) (X : Fin m → E) : Fin i → E :=
  fun j => X (Fin.castLE hi j)

lemma measurable_initialArray {E : Type*} [MeasurableSpace E] {i m : ℕ} (hi : i ≤ m) :
    Measurable (initialArray (E:=E) hi) := by
  unfold initialArray; fun_prop

lemma initialArray_pi {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {i m : ℕ} (hi : i ≤ m) :
    (Measure.pi (fun _ : Fin m => μ)).map (initialArray hi) = Measure.pi (fun _ : Fin i => μ) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [←map_append_pi μ i r,Measure.map_map (measurable_initialArray hi) (measurable_append i r)]
  have he : (initialArray hi) ∘ (fun z : (Fin i→E)×(Fin r→E) => Fin.append z.1 z.2) = Prod.fst := by
    funext z j
    change Fin.append z.1 z.2 (Fin.castLE hi j) = z.1 j
    have hj : Fin.castLE hi j = Fin.castAdd r j := rfl
    rw [hj,Fin.append_left]
  rw [he]
  exact Measure.fst_prod

def prefixLaw {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i ≤ m) :
    Measure ((Sphere d×W)×Rows i d) := P.map (Prod.map id (initialArray hi))

instance prefixLaw_probability {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i ≤ m) :
    IsProbabilityMeasure (prefixLaw P i hi) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_id.prodMap (measurable_initialArray hi)).aemeasurable).mpr inferInstance

lemma prefixLaw_fst {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i ≤ m) : (prefixLaw P i hi).fst = P.fst := by
  rw [prefixLaw,Measure.fst,Measure.map_map measurable_fst (measurable_id.prodMap (measurable_initialArray hi))]
  rfl

lemma prefixLaw_self {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) : prefixLaw P m le_rfl = P := by
  change P.map id = P
  rw [Measure.map_id]

lemma prefixLaw_independence {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) (i : ℕ) (hi : i ≤ m) :
    ((prefixLaw P i hi).map swapLast).fst = ν.prod (gaussianRows i d) := by
  have he := congrArg (fun μ : Measure (Sphere d×Rows m d) => μ.map (Prod.map id (initialArray hi))) hInd
  rw [←Measure.map_prod_map _ _ measurable_id (measurable_initialArray hi),Measure.map_id] at he
  change _ = ν.prod ((Measure.pi (fun _ : Fin m => stdGaussian (Vector d))).map (initialArray hi)) at he
  rw [initialArray_pi] at he
  rw [prefixLaw,Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map (measurable_fst.comp swapLast.measurable) (measurable_id.prodMap (measurable_initialArray hi))]
  rw [Measure.fst,Measure.map_map (measurable_id.prodMap (measurable_initialArray hi)) measurable_fst,
    Measure.map_map ((measurable_id.prodMap (measurable_initialArray hi)).comp measurable_fst) swapLast.measurable] at he
  exact he

def observationSignalMap {d k : ℕ} {W : Type*} (z : (Sphere d×W)×Rows k d) :
    (W×Observations k d)×Sphere d := ((z.1.2,ownObservations z.2 z.1.1),z.1.1)

lemma measurable_observationSignalMap {d k : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (observationSignalMap (d:=d) (k:=k) (W:=W)) := by
  unfold observationSignalMap
  exact (measurable_fst.snd.prodMk (measurable_ownObservations.comp
    (measurable_snd.prodMk measurable_fst.fst))).prodMk measurable_fst.fst

def observationSignalLaw {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : Measure ((W×Observations k d)×Sphere d) :=
  P.map observationSignalMap

instance observationSignalLaw_probability {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (observationSignalLaw P) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_observationSignalMap.aemeasurable).mpr inferInstance

lemma observationSignalLaw_context {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : (observationSignalLaw P).fst.fst = P.fst.snd := by
  simp only [observationSignalLaw,Measure.fst,Measure.snd]
  rw [Measure.map_map measurable_fst measurable_observationSignalMap,
    Measure.map_map measurable_fst (measurable_fst.comp measurable_observationSignalMap),
    Measure.map_map measurable_snd measurable_fst]
  rfl

def nextActualRowLaw {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    Measure (((W×Observations i d)×Sphere d)×Vector d) :=
  P.map (fun z => (((z.1.2,ownObservations (initialArray (Nat.le_of_lt hi) z.2) z.1.1),z.1.1),z.2 ⟨i,hi⟩))

lemma measurable_nextActualRow {d m i : ℕ} {W : Type*} [MeasurableSpace W] (hi : i < m) :
    Measurable (fun z : (Sphere d×W)×Rows m d =>
      (((z.1.2,ownObservations (initialArray (Nat.le_of_lt hi) z.2) z.1.1),z.1.1),z.2 ⟨i,hi⟩)) := by
  exact ((measurable_fst.snd.prodMk (measurable_ownObservations.comp
    (((measurable_initialArray _).comp measurable_snd).prodMk measurable_fst.fst))).prodMk
      measurable_fst.fst).prodMk ((measurable_pi_apply _).comp measurable_snd)

instance nextActualRowLaw_probability {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) :
    IsProbabilityMeasure (nextActualRowLaw P i hi) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_nextActualRow hi).aemeasurable).mpr inferInstance

lemma nextActualRowLaw_fst {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    (nextActualRowLaw P i hi).fst = observationSignalLaw (prefixLaw P i (Nat.le_of_lt hi)) := by
  rw [nextActualRowLaw,Measure.fst,Measure.map_map measurable_fst (measurable_nextActualRow hi),
    observationSignalLaw,prefixLaw,Measure.map_map measurable_observationSignalMap
      (measurable_id.prodMap (measurable_initialArray _))]
  rfl

lemma initialArray_snoc {E : Type*} {i m : ℕ} (hi : i < m) (X : Fin m → E) :
    initialArray (Nat.succ_le_of_lt hi) X = Fin.snoc (initialArray (Nat.le_of_lt hi) X) (X ⟨i,hi⟩) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; rfl
  | cast j => simp only [Fin.snoc_castSucc]; rfl

lemma snoc_ownObservations {d i : ℕ} (X : Rows i d) (x : Vector d) (s : Sphere d) :
    ownObservations (Fin.snoc X x) s = Fin.snoc (ownObservations X s) (x,⟪(s:Vector d),x⟫) := by
  funext j
  induction j using Fin.lastCases <;> simp [ownObservations,pairObservation,label]

lemma nextActualRowLaw_single {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    (singleSignalLaw (nextActualRowLaw P i hi)).map
      (Prod.map (MeasurableEquiv.prodAssoc.trans
        ((MeasurableEquiv.refl W).prodCongr (snocEquiv (Vector d×ℝ) i))) id) =
      observationSignalLaw (prefixLaw P (i+1) (Nat.succ_le_of_lt hi)) := by
  rw [singleSignalLaw,nextActualRowLaw,
    Measure.map_map measurable_singleResidualObservation (measurable_nextActualRow hi),
    Measure.map_map ((MeasurableEquiv.measurable _).prodMap measurable_id)
      (measurable_singleResidualObservation.comp (measurable_nextActualRow hi)),
    observationSignalLaw,prefixLaw,Measure.map_map measurable_observationSignalMap
      (measurable_id.prodMap (measurable_initialArray _))]
  congr 1
  funext z
  change ((z.1.2,snocEquiv (Vector d×ℝ) i
    (ownObservations (initialArray (Nat.le_of_lt hi) z.2) z.1.1,
      (z.2 ⟨i,hi⟩,⟪(z.1.1:Vector d),z.2 ⟨i,hi⟩⟫))),z.1.1) =
    ((z.1.2,ownObservations (initialArray (Nat.succ_le_of_lt hi) z.2) z.1.1),z.1.1)
  rw [snocEquiv_apply,initialArray_snoc,snoc_ownObservations]



def rawNextRowLaw {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    Measure (((Sphere d×W)×Rows i d)×Vector d) :=
  P.map (fun z => ((z.1,initialArray (Nat.le_of_lt hi) z.2),z.2 ⟨i,hi⟩))

lemma measurable_rawNextRow {d m i : ℕ} {W : Type*} [MeasurableSpace W] (hi : i < m) :
    Measurable (fun z : (Sphere d×W)×Rows m d => ((z.1,initialArray (Nat.le_of_lt hi) z.2),z.2 ⟨i,hi⟩)) := by
  exact (measurable_fst.prodMk ((measurable_initialArray _).comp measurable_snd)).prodMk
    ((measurable_pi_apply _).comp measurable_snd)

instance rawNextRowLaw_probability {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) :
    IsProbabilityMeasure (rawNextRowLaw P i hi) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_rawNextRow hi).aemeasurable).mpr inferInstance

lemma rawNextRowLaw_fst {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    (rawNextRowLaw P i hi).fst = prefixLaw P i (Nat.le_of_lt hi) := by
  rw [rawNextRowLaw,Measure.fst,Measure.map_map measurable_fst (measurable_rawNextRow hi)]
  rfl

lemma nextActualRowLaw_raw {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) (i : ℕ) (hi : i < m) :
    nextActualRowLaw P i hi = (rawNextRowLaw P i hi).map (Prod.map observationSignalMap id) := by
  rw [rawNextRowLaw,Measure.map_map (measurable_observationSignalMap.prodMap measurable_id) (measurable_rawNextRow hi)]
  rfl

lemma rowCharge_eq_raw {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) :
    klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d))) =
      conditionalReferenceKL (rawNextRowLaw P i hi) (stdGaussian (Vector d)) := by
  change conditionalReferenceKL (nextActualRowLaw P i hi) _ = _
  rw [nextActualRowLaw_raw]
  apply conditionalReferenceKL_map_context _ _ _
    (fun z : (W×Observations i d)×Sphere d => ((z.2,z.1.1),fun j => (z.1.2 j).1))
      measurable_observationSignalMap (by fun_prop)
  intro z
  rfl

lemma prefix_rowInformation_step {d m : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (i : ℕ) (hi : i < m) :
    rowInformation (prefixLaw P (i+1) (Nat.succ_le_of_lt hi)) (gaussianRows (i+1) d) =
      rowInformation (prefixLaw P i (Nat.le_of_lt hi)) (gaussianRows i d) +
      klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d))) := by
  let Q := (rawNextRowLaw P i hi).map MeasurableEquiv.prodAssoc
  let : IsProbabilityMeasure Q := inferInstance
  have hfirst : Q.map (Prod.map id Prod.fst) = prefixLaw P i (Nat.le_of_lt hi) := by
    dsimp only [Q]
    rw [Measure.map_map (measurable_id.prodMap measurable_fst) MeasurableEquiv.prodAssoc.measurable]
    exact rawNextRowLaw_fst P i hi
  have htotal : Q.map (Prod.map id (snocEquiv (Vector d) i)) = prefixLaw P (i+1) (Nat.succ_le_of_lt hi) := by
    dsimp only [Q]
    rw [rawNextRowLaw,Measure.map_map MeasurableEquiv.prodAssoc.measurable (measurable_rawNextRow hi),
      Measure.map_map (measurable_id.prodMap (snocEquiv (Vector d) i).measurable)
        (MeasurableEquiv.prodAssoc.measurable.comp (measurable_rawNextRow hi)),prefixLaw]
    congr 1
    funext z
    change (z.1,snocEquiv (Vector d) i (initialArray (Nat.le_of_lt hi) z.2,z.2 ⟨i,hi⟩)) =
      (z.1,initialArray (Nat.succ_le_of_lt hi) z.2)
    rw [snocEquiv_apply,initialArray_snoc]
  have he := conditionalReferenceKL_outcome_equiv Q
    ((gaussianRows i d).prod (stdGaussian (Vector d))) (snocEquiv (Vector d) i)
  rw [show (((gaussianRows i d).prod (stdGaussian (Vector d))).map (snocEquiv (Vector d) i)) =
      gaussianRows (i+1) d from snocEquiv_map (stdGaussian (Vector d)) i,htotal,
    conditionalReferenceKL_chain,hfirst] at he
  dsimp only [Q] at he
  rw [MeasurableEquiv.map_symm_map,←rowCharge_eq_raw P i hi] at he
  exact he



end CurrentProjection

end

end OAI
