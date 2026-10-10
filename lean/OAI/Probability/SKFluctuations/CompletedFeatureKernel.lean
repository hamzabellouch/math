import Mathlib
import OAI.Probability.SKFluctuations.PhysicalIncrementMoment
import OAI.Probability.SKFluctuations.RootedIncrements

namespace OAI

/-! Completed Feature Kernel. -/

noncomputable section


namespace SKFluctuations
open Hierarchy MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal

 theorem sum_square_edges (n : ℕ) (z : Fin n → ℝ) :
    (∑ i, z i)^2 = (∑ i, (z i)^2)+2*∑ e : Edge n, z e.val.1*z e.val.2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc, Cavity.sum_edges]
    simp only [Cavity.oldEdge,Cavity.rowEdge]
    rw [add_sq,ih]
    rw [← Finset.sum_mul]
    ring

 theorem completedCovariance (n : ℕ) (hn : 0<n) (σ τ : Spin n) (b h : ℝ) :
    (∑ i : FeatureIndex n, Sum.elim (fun _ => h) (fun _ => b) i*
      featureCoefficient n σ i*featureCoefficient n τ i) =
      (n:ℝ)*h*orderedOverlap n σ τ+(n:ℝ)*b/2*(orderedOverlap n σ τ)^2 := by
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hs : (Real.sqrt (n:ℝ))^2=(n:ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  let z : Fin n → ℝ := fun i => spinValue (σ i)*spinValue (τ i)
  have hz (i : Fin n) : (z i)^2=1 := by
    dsimp [z]
    rw [mul_pow]
    simp only [pow_two,spinValue_sq,mul_one]
  have he := sum_square_edges n z
  simp only [hz,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at he
  have hedge (e : Edge n) :
      b*(1/Real.sqrt (n:ℝ)*spinValue (σ e.val.1)*spinValue (σ e.val.2))*
        (1/Real.sqrt (n:ℝ)*spinValue (τ e.val.1)*spinValue (τ e.val.2)) =
        b/(n:ℝ)*(z e.val.1*z e.val.2) := by
    calc
      _ = b/(Real.sqrt (n:ℝ))^2*(z e.val.1*z e.val.2) := by dsimp [z]; ring
      _ = _ := by rw [hs]
  rw [Fintype.sum_sum_type,Fintype.sum_option]
  simp only [featureCoefficient,Sum.elim_inl,Sum.elim_inr,liftedCoefficients,hedge]
  have hnone : b*(1/Real.sqrt 2)*(1/Real.sqrt 2)=b/2 := by
    calc
      _ = b/(Real.sqrt 2)^2 := by ring
      _ = _ := by rw [hs2]
  rw [hnone]
  have hfield : (∑ i, h*spinValue (σ i)*spinValue (τ i))=h*∑ i, z i := by
    simp only [z,Finset.mul_sum,mul_assoc]
  rw [hfield,← Finset.mul_sum]
  change _ = (n:ℝ)*h*((∑ i, z i)/(n:ℝ))+(n:ℝ)*b/2*((∑ i, z i)/(n:ℝ))^2
  field_simp
  nlinarith only [congrArg (fun t : ℝ => b*t) he]

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι]

abbrev HamiltonianStep (S : Type*) [Fintype S] := ℝ × ProbabilityMeasure (S → ℝ)

def hamiltonianHierarchy (w : S → ℝ) : List (HamiltonianStep S) → (S → ℝ) → ℝ
  | [] => spinLogPartition w (fun σ => ContinuousLinearMap.proj σ)
  | (m,ν)::L => shiftedContinuation ν m (hamiltonianHierarchy w L)

def hamiltonianHierarchyMean (w : S → ℝ) (A : S → ℝ) :
    List (HamiltonianStep S) → (S → ℝ) → ℝ
  | [] => fun x => ∑ σ, spinWeight w (fun σ => ContinuousLinearMap.proj σ) x σ*A σ
  | (m,ν)::L => shiftedMean ν m (hamiltonianHierarchy w L) (hamiltonianHierarchyMean w A L)

omit [Nonempty S] in
 theorem hamiltonianHierarchy_measurable [Nonempty S]
    (w : S → ℝ) (L : List (HamiltonianStep S)) :
    Measurable (hamiltonianHierarchy w L) := by
  induction L with
  | nil =>
    change Measurable (fun x : S → ℝ => Real.log (∑ σ, w σ*Real.exp (x σ)))
    fun_prop
  | cons s L ih =>
    obtain ⟨m,ν⟩ := s
    change Measurable (fun x => Real.log (∫ z, Real.exp (m*hamiltonianHierarchy w L (x+z)) ∂ν)/m)
    have hh : Measurable (fun p : (S → ℝ) × (S → ℝ) => Real.exp (m*hamiltonianHierarchy w L (p.1+p.2))) :=
      (measurable_const.mul (ih.comp (measurable_fst.add measurable_snd))).exp
    exact hh.stronglyMeasurable.integral_prod_right'.measurable.log.div_const m

 theorem hamiltonianHierarchyMean_measurable (w : S → ℝ) (A : S → ℝ)
    (L : List (HamiltonianStep S)) : Measurable (hamiltonianHierarchyMean w A L) := by
  induction L with
  | nil =>
    change Measurable (fun x : S → ℝ => ∑ σ, (w σ*Real.exp (x σ)/(∑ τ, w τ*Real.exp (x τ)))*A σ)
    fun_prop
  | cons s L ih =>
    obtain ⟨m,ν⟩ := s
    change Measurable (fun x =>
      (∫ z, hamiltonianHierarchyMean w A L (x+z)*Real.exp (m*hamiltonianHierarchy w L (x+z)) ∂ν)/
      (∫ z, Real.exp (m*hamiltonianHierarchy w L (x+z)) ∂ν))
    have hF : Measurable (fun p : (S → ℝ) × (S → ℝ) => Real.exp (m*hamiltonianHierarchy w L (p.1+p.2))) :=
      (measurable_const.mul ((hamiltonianHierarchy_measurable w L).comp (measurable_fst.add measurable_snd))).exp
    exact ((ih.comp (measurable_fst.add measurable_snd)).mul hF).stronglyMeasurable.integral_prod_right'.measurable.div hF.stronglyMeasurable.integral_prod_right'.measurable

 def featureLaw (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0) : ProbabilityMeasure (S → ℝ) :=
  ⟨(Measure.pi fun i => gaussianReal 0 (q i)).map (featureVector φ),
    (Measure.isProbabilityMeasure_map_iff (featureVector φ).measurable.aemeasurable).2 inferInstance⟩

 def featureSteps (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : List (GaussianStep ι)) : List (HamiltonianStep S) :=
  L.map (fun s => (s.1,featureLaw φ s.2))

omit [Nonempty S] in
 theorem featureLaw_integral [Nonempty S] (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0)
    (f : (S → ℝ) → ℝ) (hf : Measurable f) :
    ∫ y, f y ∂(featureLaw φ q) = ∫ x, f (featureVector φ x) ∂(Measure.pi fun i => gaussianReal 0 (q i)) := by
  exact integral_map (featureVector φ).measurable.aemeasurable hf.aestronglyMeasurable

 theorem gaussianHierarchy_featureLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : List (GaussianStep ι)) (x : ι → ℝ) :
    gaussianHierarchy w φ L x = hamiltonianHierarchy w (featureSteps φ L) (featureVector φ x) := by
  induction L generalizing x with
  | nil => rfl
  | cons s L ih =>
    obtain ⟨m,q⟩ := s
    simp only [gaussianHierarchy,featureSteps,List.map_cons,hamiltonianHierarchy,shiftedContinuation]
    simp_rw [ih]
    congr 2
    have hF : Measurable (fun z : S → ℝ => Real.exp (m*hamiltonianHierarchy w (featureSteps φ L) (featureVector φ x+z))) :=
      (((hamiltonianHierarchy_measurable w (featureSteps φ L)).comp
        (measurable_const.add measurable_id)).const_mul m).exp
    simpa only [map_add,featureSteps] using (featureLaw_integral φ q _ hF).symm

 theorem gaussianHierarchyMean_featureLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (L : List (GaussianStep ι)) (x : ι → ℝ) :
    gaussianHierarchyMean w φ A L x = hamiltonianHierarchyMean w A (featureSteps φ L) (featureVector φ x) := by
  induction L generalizing x with
  | nil => rfl
  | cons s L ih =>
    obtain ⟨m,q⟩ := s
    simp only [gaussianHierarchyMean,featureSteps,List.map_cons,hamiltonianHierarchyMean,shiftedMean,tiltedMean]
    simp_rw [ih,gaussianHierarchy_featureLaw]
    have hF : Measurable (fun z : S → ℝ => Real.exp (m*hamiltonianHierarchy w (featureSteps φ L) (featureVector φ x+z))) :=
      (((hamiltonianHierarchy_measurable w (featureSteps φ L)).comp
        (measurable_const.add measurable_id)).const_mul m).exp
    have hA : Measurable (fun z : S → ℝ => hamiltonianHierarchyMean w A (featureSteps φ L) (featureVector φ x+z)) :=
      (hamiltonianHierarchyMean_measurable w A (featureSteps φ L)).comp
        (measurable_const.add measurable_id)
    have hnum := (featureLaw_integral φ q _ (hA.mul hF)).symm
    have hden := (featureLaw_integral φ q _ hF).symm
    simpa only [map_add,featureSteps,Pi.mul_apply] using congrArg₂ (fun a b : ℝ => a/b) hnum hden

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι]

 theorem hamiltonianHierarchyMean_jointMeasurable (w : S → ℝ) (L : List (HamiltonianStep S)) :
    Measurable (fun p : (S → ℝ) × (S → ℝ) => hamiltonianHierarchyMean w p.1 L p.2) := by
  induction L with
  | nil =>
    change Measurable (fun p : (S → ℝ) × (S → ℝ) =>
      ∑ σ, (w σ*Real.exp (p.2 σ)/(∑ τ, w τ*Real.exp (p.2 τ)))*p.1 σ)
    fun_prop
  | cons s L ih =>
    obtain ⟨m,ν⟩ := s
    change Measurable (fun p : (S → ℝ) × (S → ℝ) =>
      (∫ z, hamiltonianHierarchyMean w p.1 L (p.2+z)*Real.exp (m*hamiltonianHierarchy w L (p.2+z)) ∂ν)/
      (∫ z, Real.exp (m*hamiltonianHierarchy w L (p.2+z)) ∂ν))
    have hF : Measurable (fun p : ((S → ℝ) × (S → ℝ)) × (S → ℝ) =>
        Real.exp (m*hamiltonianHierarchy w L (p.1.2+p.2))) :=
      (((hamiltonianHierarchy_measurable w L).comp (measurable_fst.snd.add measurable_snd)).const_mul m).exp
    have hA : Measurable (fun p : ((S → ℝ) × (S → ℝ)) × (S → ℝ) =>
        hamiltonianHierarchyMean w p.1.1 L (p.1.2+p.2)) :=
      ih.comp (measurable_fst.fst.prodMk (measurable_fst.snd.add measurable_snd))
    exact (hA.mul hF).stronglyMeasurable.integral_prod_right'.measurable.div
      hF.stronglyMeasurable.integral_prod_right'.measurable

 def hamiltonianPrefixTest (w : S → ℝ) (post : List (HamiltonianStep S))
    (A : (S → ℝ) → ℝ) : List (HamiltonianStep S) → (S → ℝ) → ℝ
  | [] => A
  | (m,ν)::L => shiftedMean ν m (hamiltonianHierarchy w (L++post)) (hamiltonianPrefixTest w post A L)

 theorem hamiltonianPrefixTest_measurable (w : S → ℝ) (post pre : List (HamiltonianStep S))
    (A : (S → ℝ) → ℝ) (hA : Measurable A) : Measurable (hamiltonianPrefixTest w post A pre) := by
  induction pre with
  | nil => exact hA
  | cons s L ih =>
    obtain ⟨m,ν⟩ := s
    change Measurable (fun x =>
      (∫ z, hamiltonianPrefixTest w post A L (x+z)*Real.exp (m*hamiltonianHierarchy w (L++post) (x+z)) ∂ν)/
      (∫ z, Real.exp (m*hamiltonianHierarchy w (L++post) (x+z)) ∂ν))
    have hF : Measurable (fun p : (S → ℝ) × (S → ℝ) =>
        Real.exp (m*hamiltonianHierarchy w (L++post) (p.1+p.2))) :=
      (((hamiltonianHierarchy_measurable w _).comp (measurable_fst.add measurable_snd)).const_mul m).exp
    exact ((ih.comp (measurable_fst.add measurable_snd)).mul hF).stronglyMeasurable.integral_prod_right'.measurable.div
      hF.stronglyMeasurable.integral_prod_right'.measurable

 theorem prefixTest_featureLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (post pre : List (GaussianStep ι)) (A : (S → ℝ) → ℝ) (hA : Measurable A) (x : ι → ℝ) :
    prefixTest pre (gaussianHierarchy w φ post) (fun y => A (featureVector φ y)) x =
      hamiltonianPrefixTest w (featureSteps φ post) A (featureSteps φ pre) (featureVector φ x) := by
  induction pre generalizing x with
  | nil => rfl
  | cons s L ih =>
    obtain ⟨m,q⟩ := s
    simp only [prefixTest,prefixContinuation_hierarchy,featureSteps,List.map_cons,hamiltonianPrefixTest,
      shiftedMean,tiltedMean]
    simp_rw [ih,gaussianHierarchy_featureLaw]
    have hF : Measurable (fun z : S → ℝ => Real.exp (m*hamiltonianHierarchy w
        (featureSteps φ (L++post)) (featureVector φ x+z))) :=
      (((hamiltonianHierarchy_measurable w _).comp (measurable_const.add measurable_id)).const_mul m).exp
    have hD : Measurable (fun z : S → ℝ => hamiltonianPrefixTest w (featureSteps φ post) A
        (featureSteps φ L) (featureVector φ x+z)) :=
      (hamiltonianPrefixTest_measurable w _ _ A hA).comp (measurable_const.add measurable_id)
    have hn := (featureLaw_integral φ q _ (hD.mul hF)).symm
    have hd := (featureLaw_integral φ q _ hF).symm
    simpa only [map_add,featureSteps,List.map_append,Pi.mul_apply] using congrArg₂ (fun a b : ℝ => a/b) hn hd

 def hamiltonianPairTest (w : S → ℝ) (L : List (HamiltonianStep S)) (P : S → S → ℝ)
    (x : S → ℝ) : ℝ := hamiltonianHierarchyMean w (fun σ => hamiltonianHierarchyMean w (P σ) L x) L x

 theorem hamiltonianPairTest_measurable (w : S → ℝ) (L : List (HamiltonianStep S)) (P : S → S → ℝ) :
    Measurable (hamiltonianPairTest w L P) := by
  exact (hamiltonianHierarchyMean_jointMeasurable w L).comp
    ((Measurable.of_eval (fun σ => hamiltonianHierarchyMean_measurable w (P σ) L)).prodMk measurable_id)

 theorem stepPairMean_featureLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre post : List (GaussianStep ι)) (P : S → S → ℝ) (x : ι → ℝ) :
    stepPairMean w φ pre post P x = hamiltonianPrefixTest w (featureSteps φ post)
      (hamiltonianPairTest w (featureSteps φ post) P) (featureSteps φ pre) (featureVector φ x) := by
  have ht : (fun y => gaussianHierarchyMean w φ
      (fun σ => gaussianHierarchyMean w φ (P σ) post y) post y) =
      fun y => hamiltonianPairTest w (featureSteps φ post) P (featureVector φ y) := by
    funext y
    simp only [gaussianHierarchyMean_featureLaw,hamiltonianPairTest]
  unfold stepPairMean
  rw [ht]
  exact prefixTest_featureLaw w φ post pre _ (hamiltonianPairTest_measurable w _ P) x

 theorem stepPairDisorder_featureLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ι → ℝ≥0) (pre post : List (GaussianStep ι)) (P : S → S → ℝ) (x : ι → ℝ) :
    stepPairDisorder w φ q pre post P x =
      ∫ z, hamiltonianPrefixTest w (featureSteps φ post) (hamiltonianPairTest w (featureSteps φ post) P)
        (featureSteps φ pre) (featureVector φ x+z) ∂(featureLaw φ q) := by
  unfold stepPairDisorder zeroContinuation
  simp_rw [stepPairMean_featureLaw,map_add]
  exact (featureLaw_integral φ q _ ((hamiltonianPrefixTest_measurable w _ _ _
    (hamiltonianPairTest_measurable w _ P)).comp (measurable_const.add measurable_id))).symm

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι κ : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Fintype κ]

 theorem stepPairDisorder_eq_of_featureLaws (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : S → (κ → ℝ) →L[ℝ] ℝ)
    (q : ι → ℝ≥0) (r : κ → ℝ≥0) (pre post : List (GaussianStep ι))
    (pre' post' : List (GaussianStep κ)) (P : S → S → ℝ)
    (hroot : featureLaw φ q=featureLaw ψ r)
    (hpre : featureSteps φ pre=featureSteps ψ pre') (hpost : featureSteps φ post=featureSteps ψ post') :
    stepPairDisorder w φ q pre post P 0=stepPairDisorder w ψ r pre' post' P 0 := by
  rw [stepPairDisorder_featureLaw,stepPairDisorder_featureLaw,hroot,hpre,hpost]
  simp only [map_zero]

 def splitHamiltonianSteps (u : ℝ) : List (HamiltonianStep S) → List (HamiltonianStep S) × List (HamiltonianStep S)
  | [] => ([],[])
  | s::L => if s.1≤u then (s::(splitHamiltonianSteps u L).1,(splitHamiltonianSteps u L).2) else ([],s::L)

omit [Nonempty S] in
 theorem featureSteps_split [Nonempty S]
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (u : ℝ) (L : List (GaussianStep ι)) :
    (featureSteps φ (splitClockSteps u L).1,featureSteps φ (splitClockSteps u L).2)=
      splitHamiltonianSteps u (featureSteps φ L) := by
  induction L with
  | nil => rfl
  | cons s L ih =>
    simp only [splitClockSteps,featureSteps,List.map_cons,splitHamiltonianSteps]
    split_ifs with hs
    · have h₁ := congrArg Prod.fst ih
      have h₂ := congrArg Prod.snd ih
      simp only [featureSteps] at h₁ h₂
      rw [List.map_cons,h₁,h₂]
    · rfl

 theorem stepPairMoment_eq_of_featureLaws [Nonempty ι] [Nonempty κ] {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : S → (κ → ℝ) →L[ℝ] ℝ)
    (q : ι → ℝ≥0) (r : κ → ℝ≥0) (L : List (GaussianStep ι)) (M : List (GaussianStep κ))
    (hL : OrderedSteps 0 L) (hM : OrderedSteps 0 M) (P : S → S → ℝ)
    (hroot : featureLaw φ q=featureLaw ψ r) (hsteps : featureSteps φ L=featureSteps ψ M) (u : ℝ) :
    stepPairMoment w φ q L hL.mem_pos P u=stepPairMoment w ψ r M hM.mem_pos P u := by
  rw [stepPairMoment_eq_split hw φ q L hL,stepPairMoment_eq_split hw ψ r M hM]
  have he := (featureSteps_split φ u L).trans ((congrArg (splitHamiltonianSteps u) hsteps).trans
    (featureSteps_split ψ u M).symm)
  exact stepPairDisorder_eq_of_featureLaws w φ ψ q r _ _ _ _ P hroot
    (congrArg Prod.fst he) (congrArg Prod.snd he)

omit [Nonempty S] in
 theorem sampleFeatureSteps_eq [Nonempty S]
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : S → (κ → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (r : ℝ → κ → ℝ≥0)
    (he : ∀ a b, featureLaw φ (fun i => q b i-q a i)=featureLaw ψ (fun i => r b i-r a i))
    (a : ℝ) (as : List PositiveMass) :
    featureSteps φ (sampleClockSteps q a as)=featureSteps ψ (sampleClockSteps r a as) := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
    change (b.val,featureLaw φ (fun i => q b.val i-q a i))::featureSteps φ (sampleClockSteps q b.val bs)=_
    rw [he,ih]
    rfl

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι κ : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Fintype κ]
variable [Nonempty ι] [Nonempty κ]

omit [Nonempty ι] [Nonempty κ] in
 theorem retainedPairSample_eq_of_featureLaws [Nonempty ι] [Nonempty κ] (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : S → (κ → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (r : ℝ → κ → ℝ≥0)
    (hroot : featureLaw φ (q 0)=featureLaw ψ (r 0))
    (he : ∀ a b, featureLaw φ (fun i => q b i-q a i)=featureLaw ψ (fun i => r b i-r a i))
    (u : PositiveMass) (as : List PositiveMass) (P : S → S → ℝ) :
    retainedPairSample w φ q u as P 0=retainedPairSample w ψ r u as P 0 := by
  exact stepPairDisorder_eq_of_featureLaws w φ ψ _ _ _ _ _ _ P hroot
    (sampleFeatureSteps_eq φ ψ q r he _ _) (sampleFeatureSteps_eq φ ψ q r he _ _)

 theorem pathPairMoment_eq_of_featureLaws {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : S → (κ → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (r : ℝ → κ → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (hroot : featureLaw φ (q 0)=featureLaw ψ (r 0))
    (he : ∀ a b, featureLaw φ (fun i => q b i-q a i)=featureLaw ψ (fun i => r b i-r a i))
    (P : S → S → ℝ) {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    pathPairMoment w φ q P u=pathPairMoment w ψ r P u := by
  simp only [pathPairMoment,dite_eq_left hu.1]
  apply tendsto_nhds_unique (retainedPairSample_tendsto_all hw φ q hq ⟨u,hu.1⟩ hu.2 P 0)
  simpa only [retainedPairSample_eq_of_featureLaws w φ ψ q r hroot he] using
    retainedPairSample_tendsto_all hw ψ r hr ⟨u,hu.1⟩ hu.2 P 0

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open Hierarchy MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 def completedPathClock (n : ℕ) (b h : ℝ → ℝ≥0) (u : ℝ) : FeatureIndex n → ℝ≥0 :=
  Sum.elim (fun _ => h u) (fun _ => b u)

 theorem completedPathClock_monotone (n : ℕ) {b h : ℝ → ℝ≥0}
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) :
    ∀ i, MonotoneOn (fun u => completedPathClock n b h u i) (Icc (0:ℝ) 1) := by
  intro i; cases i with
  | inl i => exact hh
  | inr i => exact hb

 theorem ordered_completed_featureLaw (n : ℕ) (hn : 0<n) (b h : ℝ≥0) :
    featureLaw (orderedFeature n) (Sum.elim (fun _ => h) (fun _ => b))=
      featureLaw (finiteFeature n) (Sum.elim (fun _ => h) (fun _ => b)) := by
  classical
  apply Subtype.ext
  apply featureVector_law_eq
  intro σ τ
  simp only [orderedFeature_single]
  have hc (ρ : Spin n) (i : FeatureIndex n) : finiteFeature n ρ (Pi.single i 1)=featureCoefficient n ρ i := by
    simp [finiteFeature_apply,Pi.single_apply]
  simp only [hc]
  convert (orderedCovariance n hn σ τ (b:ℝ) (h:ℝ)).trans
    (completedCovariance n hn σ τ (b:ℝ) (h:ℝ)).symm using 1 <;>
    apply Finset.sum_congr rfl <;> intro i hi <;> cases i <;> rfl

 theorem ordered_completed_incrementLaw (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0) (u v : ℝ) :
    featureLaw (orderedFeature n) (fun i => orderedPathClock n b h v i-orderedPathClock n b h u i)=
      featureLaw (finiteFeature n) (fun i => completedPathClock n b h v i-completedPathClock n b h u i) := by
  have ho : (fun i => orderedPathClock n b h v i-orderedPathClock n b h u i)=
      Sum.elim (fun _ => h v-h u) (fun _ => b v-b u) := by funext i; cases i <;> rfl
  have he : (fun i => completedPathClock n b h v i-completedPathClock n b h u i)=
      Sum.elim (fun _ => h v-h u) (fun _ => b v-b u) := by funext i; cases i <;> rfl
  rw [ho,he]
  exact ordered_completed_featureLaw n hn _ _

 theorem orderedPathPair_eq_completed (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (P : Spin n → Spin n → ℝ) {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    orderedPathPair n b h P u=
      pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b h) P u := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact pathPairMoment_eq_of_featureLaws (uniformWeight_pos n) _ _ _ _
    (orderedPathClock_monotone n hb hh) (completedPathClock_monotone n hb hh)
    (ordered_completed_featureLaw n hn (b 0) (h 0)) (ordered_completed_incrementLaw n hn b h) P hu

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalFieldDuration_take_coordinate {ι : Type} (i : ι) (q₀ : ι → ℝ)
    (steps : List (GaussianStep ι)) (j : ℕ) :
    physicalFieldDuration (fun st => st.2 i) (steps.take j)=stepClockValues q₀ steps j i-q₀ i := by
  induction steps generalizing q₀ j with
  | nil => cases j <;> simp [physicalFieldDuration,stepClockValues]
  | cons st steps ih =>
    cases j with
    | zero => simp [physicalFieldDuration,stepClockValues]
    | succ j =>
      simp only [List.take_succ_cons,physicalFieldDuration,List.map_cons,List.sum_cons,NNReal.coe_add]
      change _+physicalFieldDuration (fun st => st.2 i) (steps.take j)=_
      rw [ih (fun i => q₀ i+st.2 i)]
      simp only [stepClockValues]
      ring

 theorem splitClockSteps_take {ι : Type} [Fintype ι] [Nonempty ι] (u : ℝ) (steps : List (GaussianStep ι)) :
    steps.take (splitClockSteps u steps).1.length=(splitClockSteps u steps).1 := by
  calc _ = ((splitClockSteps u steps).1++(splitClockSteps u steps).2).take
        (splitClockSteps u steps).1.length := congrArg (fun L : List (GaussianStep ι) => L.take (splitClockSteps u steps).1.length)
          (splitClockSteps_append u steps).symm
       _ = _ := List.take_left ..

 theorem physicalFieldDuration_split {ι : Type} [Fintype ι] [Nonempty ι] (i : ι) (q₀ : ι → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (u : ℝ) :
    physicalFieldDuration (fun st => st.2 i) (steps.take (splitClockSteps u steps).1.length)=
      stepClockFunction q₀ steps u i-q₀ i := by
  rw [splitClockSteps_take,stepClockFunction_split q₀ u steps ha]
  simpa only [List.take_length] using physicalFieldDuration_take_coordinate i q₀
    (splitClockSteps u steps).1 (splitClockSteps u steps).1.length

 theorem sampledFieldDuration (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : ℝ) :
    let q := completedPathClock n b h
    let steps := sampleClockSteps q 0 as
    physicalFieldDuration (fun st => st.2 (Sum.inl ⟨0,hn⟩))
      (steps.take (splitClockSteps u steps).1.length)=
      partitionSample (fun u => (h u:ℝ)) 0 as u-(h 0:ℝ) := by
  dsimp only
  rw [physicalFieldDuration_split (Sum.inl ⟨0,hn⟩)
    (fun i => (completedPathClock n b h 0 i:ℝ)) _ (sampleClockSteps_ordered _ _ ha)]
  rw [sampleClockSteps_function _ (completedPathClock_monotone n hb hh) as ha]
  rfl

 theorem sampledFieldClock_aligned (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (a : ℝ) :
    ∀ st ∈ sampleClockSteps (completedPathClock n b h) a as, ∀ i : Fin n,
      st.2 (Sum.inl i)=st.2 (Sum.inl ⟨0,hn⟩) := by
  induction as generalizing a with
  | nil => simp [sampleClockSteps]
  | cons c cs ih =>
    intro st hst i
    rcases List.mem_cons.mp hst with rfl | hst
    · rfl
    · exact ih c.val st hst i

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem pathMassDifferences_eq_cutMass {ι : Type} (steps : List (GaussianStep ι))
    (a : ℝ) (j : Fin (steps.length+1)) :
    pathMassDifferences steps a j=physicalCutMass a steps (j.val+1)-physicalCutMass a steps j.val := by
  induction steps generalizing a with
  | nil =>
    have hj : j=0 := by
      apply Fin.ext
      change j.val=0
      have hh := j.isLt
      simp only [List.length_nil,zero_add] at hh
      omega
    subst j
    rfl
  | cons st steps ih =>
    rcases st with ⟨m,q⟩
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [pathMassDifferences,Fin.cons_zero,Fin.val_zero,physicalCutMass]
    · simpa only [pathMassDifferences,Fin.cons_succ,Fin.val_succ,physicalCutMass] using ih m k

 theorem physicalCutMass_sampleClockSteps {ι : Type} (q : ℝ → ι → ℝ≥0)
    (a : ℝ) (as : List PositiveMass) (j : ℕ) (hj : j ≤ as.length) :
    physicalCutMass a (sampleClockSteps q a as) j=partitionPoint a as j := by
  induction as generalizing a j with
  | nil =>
    have hj' : j=0 := by simpa using hj
    subst j
    rfl
  | cons b bs ih => cases j with
    | zero => rfl
    | succ j => exact ih b.val j (by simpa using hj)

 theorem sampledFieldDuration_index (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (j : ℕ) (hj : j ≤ as.length) :
    let q := completedPathClock n b h
    let steps := sampleClockSteps q 0 as
    physicalFieldDuration (fun st => st.2 (Sum.inl ⟨0,hn⟩)) (steps.take j)=
      (h (physicalCutMass 0 steps j):ℝ)-(h 0:ℝ) := by
  dsimp only
  rw [physicalFieldDuration_take_coordinate (Sum.inl ⟨0,hn⟩)
    (fun i => (completedPathClock n b h 0 i:ℝ))]
  rw [sampleClockSteps_values _ (completedPathClock_monotone n hb hh) as ha,
    partitionValues_point,physicalCutMass_sampleClockSteps _ _ _ j hj]
  rfl

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 def cutPredecessor : (cs : List (ℝ × ℕ)) → ℕ → Fin cs.length → ℕ
  | [], _, i => Fin.elim0 i
  | c::cs, j, i => Fin.cases j (cutPredecessor cs c.2) i

 def cutIncrement {E : Type*} [Sub E] (cs : List (ℝ × ℕ)) (X : ℕ → E)
    (j : ℕ) (i : Fin cs.length) : E := X (cs.get i).2-X (cutPredecessor cs j i)

 theorem cutIncrement_zero {E : Type*} [Sub E] (c : ℝ × ℕ) (cs : List (ℝ × ℕ))
    (X : ℕ → E) (j : ℕ) : cutIncrement (c::cs) X j 0 = X c.2-X j := rfl

 theorem cutIncrement_succ {E : Type*} [Sub E] (c : ℝ × ℕ) (cs : List (ℝ × ℕ))
    (X : ℕ → E) (j : ℕ) (i : Fin cs.length) :
    cutIncrement (c::cs) X j i.succ = cutIncrement cs X c.2 i := rfl

 theorem weightedPathIncrements_eq_sum (cs : List (ℝ × ℕ)) (X : ℕ → ℝ) (j : ℕ) :
    weightedPathIncrements cs X j = ∑ i : Fin cs.length, (cs.get i).1*(cutIncrement cs X j i)^2 := by
  induction cs generalizing j with
  | nil => simp [weightedPathIncrements]
  | cons c cs ih =>
    simp only [weightedPathIncrements, List.length_cons, Fin.sum_univ_succ,
      cutIncrement_zero,cutIncrement_succ]
    exact congrArg (fun t => c.1*(X c.2-X j)^2+t) (ih c.2)

 theorem sum_cutIncrement {E : Type*} [AddCommGroup E] (cs : List (ℝ × ℕ))
    (X : ℕ → E) (j : ℕ) :
    (∑ i : Fin cs.length, cutIncrement cs X j i) = X (lastLayerCut cs j)-X j := by
  induction cs generalizing j with
  | nil => simp [lastLayerCut]
  | cons c cs ih =>
    simp only [List.length_cons,Fin.sum_univ_succ,cutIncrement_zero,cutIncrement_succ,ih,lastLayerCut]
    abel

 theorem dot_cutIncrement {d : Type*} [Fintype d] (cs : List (ℝ × ℕ))
    (X : ℕ → d → ℝ) (V : d → ℝ) (j : ℕ) (i : Fin cs.length) :
    cutIncrement cs (fun k => ∑ l, V l*X k l) j i = ∑ l, V l*cutIncrement cs X j i l := by
  simp only [cutIncrement,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

end SKFluctuations.Hierarchy

end

end OAI
