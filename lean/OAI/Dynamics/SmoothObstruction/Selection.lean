import OAI.Dynamics.SmoothObstruction.TubeProjection

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.CanonicalRelation
open Set MeasureTheory Filter Topology

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y]

/-- A Borel relation with exactly one output at every input has a genuine
measurable solution map. Its definition does not depend on any auxiliary
frame certificate used to obtain existence and uniqueness. -/
theorem measurable_solution (R : Set (X × Y)) (hR : MeasurableSet R)
    (hex : ∀ x,∃! y,(x,y)∈R) :
    ∃ f : X → Y,Measurable f ∧ (∀ x,(x,f x)∈R) ∧
      ∀ x y,(x,y)∈R → y=f x := by
  classical
  let f : X → Y := fun x => (hex x).choose
  have hf (x : X) : (x,f x)∈R := (hex x).choose_spec.1
  have hu (x : X) (y : Y) (hy : (x,y)∈R) : y=f x :=
    (hex x).choose_spec.2 y hy
  let : StandardBorelSpace R := hR.standardBorel
  let π : R → X := fun z => z.val.1
  have hπ : Measurable π := measurable_fst.comp measurable_subtype_coe
  have hsurj : Function.Surjective π := fun x => ⟨⟨(x,f x),hf x⟩,rfl⟩
  have he : f ∘ π=(fun z : R => z.val.2) := by
    funext z
    exact (hu z.val.1 z.val.2 z.property).symm
  have hm : Measurable (f ∘ π) := by
    rw [he]
    exact measurable_snd.comp measurable_subtype_coe
  exact ⟨f,(Measurable.measurable_comp_iff_of_surjective hπ hsurj).mp hm,hf,hu⟩

/-- The retained set has its original Borel subspace, not a conditioned
probability space. The measurable total extension is only for convenient
pushforward notation; it is equal to the canonical solution on the carrier. -/
theorem retained_solution [Nonempty Y] (G : Set X) (hG : MeasurableSet G)
    (R : X → Y → Prop) (hR : MeasurableSet {z : X×Y | z.1∈G ∧ R z.1 z.2})
    (hex : ∀ x∈G,∃! y,R x y) :
    ∃ f : X → Y,Measurable f ∧ (∀ x∈G,R x (f x)) ∧
      ∀ x∈G,∀ y,R x y → y=f x := by
  classical
  let : StandardBorelSpace G := hG.standardBorel
  let R' : Set (G×Y) := {z | R z.1.val z.2}
  have hR' : MeasurableSet R' := by
    have hm : Measurable (fun z : G×Y => (z.1.val,z.2)) :=
      (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
    have he : R'= (fun z : G×Y => (z.1.val,z.2)) ⁻¹' {z : X×Y | z.1∈G ∧ R z.1 z.2} := by
      ext z
      simp only [R',mem_ofPred_eq,Set.mem_preimage]
      exact ⟨fun h => ⟨z.1.property,h⟩,fun h => h.2⟩
    rw [he]
    exact hR.preimage hm
  obtain ⟨f,hf,hfr,hfu⟩ := measurable_solution R' hR' (fun x => hex x x.property)
  obtain ⟨F,hF,hFf⟩ := (MeasurableEmbedding.subtype_coe hG).exists_measurable_extend hf
    (fun _ => inferInstance)
  have he (x : G) : F x=f x := congrFun hFf x
  refine ⟨F,hF,?_,?_⟩
  · intro x hx
    rw [he ⟨x,hx⟩]
    exact hfr ⟨x,hx⟩
  · intro x hx y hy
    rw [he ⟨x,hx⟩]
    exact hfu ⟨x,hx⟩ y hy

end SmoothObstruction.CanonicalRelation

namespace SmoothObstruction.CanonicalRelation
open Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Local analytic branches agree with the canonical Borel solution merely
by satisfying its boundary relation inside the uniqueness tube. The frame
witnesses and chart codes need not be continuous functions of the inputs. -/
theorem local_derivative (G : Set E) (x : E) (hx : x∈G)
    (R : E → F → Prop) (f g : E → F) (L : E →L[ℝ] F)
    (hu : ∀ u∈G,∀ v,R u v → v=f u)
    (hg : HasFDerivAt g L x) (hrel : ∀ᶠ u in 𝓝[G] x,R u (g u)) :
    HasFDerivWithinAt f L G x := by
  have he : g =ᶠ[𝓝[G] x] f := by
    filter_upwards [hrel,self_mem_nhdsWithin] with u huR huG
    exact hu u huG (g u) huR
  exact hg.hasFDerivWithinAt.congr_of_eventuallyEq he.symm (he.eq_of_nhdsWithin hx).symm
end SmoothObstruction.CanonicalRelation

namespace SmoothObstruction.SelectedTube
open Set MeasureTheory
variable {X C E : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The literal fixed-atlas coordinate tube, with chart sources checked.
Only the base point chooses the chart; the second point need not be good. -/
def tube (q : X → C) (U : C → Set X) (φ : C → X → E)
    (f : ℕ → X → X) (n : ℕ) (δ : ℝ) (x z : X) : Prop :=
  ∀ t : Fin (n+1),f t z∈U (q (f t x)) ∧
    ‖φ (q (f t x)) (f t z)-φ (q (f t x)) (f t x)‖≤δ

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
lemma measurable_evaluate (φ : C → X → E) (hφ : ∀ c,Measurable (φ c)) :
    Measurable (fun p : C×X => φ p.1 p.2) :=
  measurable_from_prod_countable_right hφ

lemma measurable_tube (q : X → C) (hq : Measurable q)
    (U : C → Set X) (hU : ∀ c,MeasurableSet (U c))
    (φ : C → X → E) (hφ : ∀ c,Measurable (φ c))
    (f : ℕ → X → X) (hf : ∀ t,Measurable (f t)) (n : ℕ) (δ : ℝ) :
    MeasurableSet {p : X×X | tube q U φ f n δ p.1 p.2} := by
  have hu : MeasurableSet {p : C×X | p.2∈U p.1} := by
    have he : {p : C×X | p.2∈U p.1}=⋃ c,({c} ×ˢ U c) := by
      ext p
      simp only [mem_ofPred_eq,mem_iUnion,mem_prod,mem_singleton_iff]
      exact ⟨fun h => ⟨p.1,rfl,h⟩,fun ⟨c,hc,h⟩ => hc ▸ h⟩
    rw [he]
    exact MeasurableSet.iUnion (fun c => (measurableSet_singleton c).prod (hU c))
  simp only [tube,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro t
  have hx : Measurable (fun p : X×X => f t p.1) := (hf t).comp measurable_fst
  have hz : Measurable (fun p : X×X => f t p.2) := (hf t).comp measurable_snd
  have hc := hq.comp hx
  exact (hu.preimage (hc.prodMk hz)).inter
    (measurableSet_le (((measurable_evaluate φ hφ).comp (hc.prodMk hz)).sub
      ((measurable_evaluate φ hφ).comp (hc.prodMk hx))).norm measurable_const)
end SmoothObstruction.SelectedTube

namespace SmoothObstruction.MeasurableSwitch
open Set MeasureTheory
variable {X C E : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Fixed-bin future/past observations and the two old coordinate tubes.
All auxiliary frames have disappeared from this boundary relation. -/
def relation (F P : X → X → E) (TF TB : X → X → Prop) (u : X×X) (z : X) : Prop :=
  F u.1 z=F u.1 u.1 ∧ P u.2 z=P u.2 u.2 ∧ TF u.1 z ∧ TB u.2 z

lemma measurable_relation (F P : X → X → E)
    (hF : Measurable (Function.uncurry F)) (hP : Measurable (Function.uncurry P))
    (TF TB : X → X → Prop) (hTF : MeasurableSet {p : X×X | TF p.1 p.2})
    (hTB : MeasurableSet {p : X×X | TB p.1 p.2}) :
    MeasurableSet {p : (X×X)×X | relation F P TF TB p.1 p.2} := by
  have h₁ : Measurable (fun p : (X×X)×X => (p.1.1,p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have h₂ : Measurable (fun p : (X×X)×X => (p.1.2,p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hx : Measurable (fun p : (X×X)×X => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hy : Measurable (fun p : (X×X)×X => p.1.2) :=
    measurable_snd.comp measurable_fst
  exact (measurableSet_eq_fun (hF.comp h₁) (hF.comp (hx.prodMk hx))).inter
    ((measurableSet_eq_fun (hP.comp h₂) (hP.comp (hy.prodMk hy))).inter
      ((hTF.preimage h₁).inter (hTB.preimage h₂)))

/-- The original retained carrier gives one globally measurable pair map.
There is no measurable moving-frame selection and no conditioning of a law.
Existence and uniqueness are supplied by the actual finite-tube solve. -/
theorem canonical_pair [StandardBorelSpace X] [Nonempty X]
    (G : Set (X×X)) (hG : MeasurableSet G)
    (F P : X → X → E) (hF : Measurable (Function.uncurry F))
    (hP : Measurable (Function.uncurry P))
    (TF TB : X → X → Prop) (hTF : MeasurableSet {p : X×X | TF p.1 p.2})
    (hTB : MeasurableSet {p : X×X | TB p.1 p.2})
    (hex : ∀ u∈G,∃! z,relation F P TF TB u z)
    (hex' : ∀ u∈G,∃! w,relation F P TF TB u.swap w) :
    ∃ Φ : X×X → X×X,Measurable Φ ∧
      (∀ u∈G,relation F P TF TB u (Φ u).1 ∧ relation F P TF TB u.swap (Φ u).2) ∧
      (∀ u∈G,∀ z,relation F P TF TB u z → z=(Φ u).1) ∧
      (∀ u∈G,∀ w,relation F P TF TB u.swap w → w=(Φ u).2) := by
  have hR := measurable_relation F P hF hP TF TB hTF hTB
  have hRG : MeasurableSet {p : (X×X)×X | p.1∈G ∧ relation F P TF TB p.1 p.2} :=
    (hG.preimage measurable_fst).inter hR
  have hRG' : MeasurableSet {p : (X×X)×X | p.1∈G ∧ relation F P TF TB p.1.swap p.2} :=
    (hG.preimage measurable_fst).inter (hR.preimage
      ((measurable_swap.comp measurable_fst).prodMk measurable_snd))
  obtain ⟨z,hz,hzr,hzu⟩ := CanonicalRelation.retained_solution G hG
    (relation F P TF TB) hRG hex
  obtain ⟨w,hw,hwr,hwu⟩ := CanonicalRelation.retained_solution G hG
    (fun u => relation F P TF TB u.swap) hRG' hex'
  exact ⟨fun u => (z u,w u),hz.prodMk hw,fun u hu => ⟨hzr u hu,hwr u hu⟩,hzu,hwu⟩
end SmoothObstruction.MeasurableSwitch

namespace SmoothObstruction.EndpointObservation
open Set MeasureTheory
variable {X C B E : Type*} [MeasurableSpace X]
  [Fintype C] [Fintype B] [MeasurableSpace C] [MeasurableSingletonClass C]
  [MeasurableSpace B] [MeasurableSingletonClass B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The source endpoint observation in the ambient coordinate space. Its
finite index consists ONLY of the starting coarse bin and endpoint coarse
bin; an internal frame witness is not part of this index. -/
def observation (c : X → C) (b : X → B) (f : X → X)
    (φ : B → X → E) (P : C → B → E →L[ℝ] E) (x z : X) : E :=
  P (c x) (b (f x)) (φ (b (f x)) (f z))

lemma measurable_observation (c : X → C) (hc : Measurable c)
    (b : X → B) (hb : Measurable b) (f : X → X) (hf : Measurable f)
    (φ : B → X → E) (hφ : ∀ j,Measurable (φ j)) (P : C → B → E →L[ℝ] E) :
    Measurable (Function.uncurry (observation c b f φ P)) := by
  have hh : Measurable (fun u : (C×B)×X => P u.1.1 u.1.2 (φ u.1.2 (f u.2))) := by
    apply measurable_from_prod_countable_right
    intro ij
    exact (P ij.1 ij.2).continuous.measurable.comp ((hφ ij.2).comp hf)
  exact hh.comp (((hc.comp measurable_fst).prodMk
    (hb.comp (hf.comp measurable_fst))).prodMk measurable_snd)

omit [MeasurableSpace X] [Fintype C] [Fintype B]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [MeasurableSpace B] [MeasurableSingletonClass B] [MeasurableSpace E] [BorelSpace E]

/-- Positive bin margins turn the ambient observations into the actual fixed
smooth endpoint maps on a neighborhood; there is no differentiability claim
for the discontinuously selected observation itself. -/
lemma observation_fixed (c : X → C) (b : X → B) (f : X → X)
    (φ : B → X → E) (P : C → B → E →L[ℝ] E)
    (x y z : X) (hc : c x=c y) (hb : b (f x)=b (f y)) :
    observation c b f φ P x z=observation c b f φ P y z := by
  simp only [observation,hc,hb]

lemma observation_eq_iff (c : X → C) (b : X → B) (f : X → X)
    (φ : B → X → E) (P : C → B → E →L[ℝ] E) (x y z : X) :
    observation c b f φ P x z=observation c b f φ P x y ↔
      P (c x) (b (f x)) (φ (b (f x)) (f z)-φ (b (f x)) (f y))=0 := by
  simp only [observation,map_sub,sub_eq_zero]
end SmoothObstruction.EndpointObservation

namespace SmoothObstruction.ManifoldCoordinates
open Set MeasureTheory
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]

/-- A chart has no prescribed behaviour outside its source. This Borel
extension, used only to state global relations, agrees with it on the source. -/
noncomputable def borelChart (a : M) : M → EuclideanSpace ℝ (Fin d) := by
  classical
  exact (chartAt H a).source.piecewise (extChartAt I a) (fun _ => 0)

lemma borelChart_eq (a z : M) (hz : z∈(chartAt H a).source) :
    borelChart I a z=(extChartAt I a) z := by
  classical
  exact Set.piecewise_eq_of_mem _ _ _ hz

variable [MeasurableSpace M] [BorelSpace M]

lemma measurable_borelChart (a : M) : Measurable (borelChart I a) := by
  classical
  apply ContinuousOn.measurable_piecewise _ continuousOn_const (chartAt H a).open_source.measurableSet
  simpa only [extChartAt_source] using continuousOn_extChartAt (I:=I) a

variable {ι C : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι) (n : ℕ)

lemma measurable_originalTube (hc : Measurable c)
    (hsource : ∀ z,z∈(chartAt H (a (c z))).source) (δ : ℝ) :
    MeasurableSet {p : M×M | originalTube I S a c (n:=n) δ p.1 p.2} := by
  have he : {p : M×M | originalTube I S a c (n:=n) δ p.1 p.2}=
      {p | SelectedTube.tube c (fun j => (chartAt H (a j)).source)
        (fun j => borelChart I (a j)) (fun t => S^[t]) n δ p.1 p.2} := by
    ext p
    constructor <;> intro hp t <;> obtain ⟨hs,ht⟩ := hp t
    · exact ⟨hs,by simpa only [borelChart_eq I _ _ hs,
        borelChart_eq I _ _ (hsource _)] using ht⟩
    · exact ⟨hs,by simpa only [borelChart_eq I _ _ hs,
        borelChart_eq I _ _ (hsource _)] using ht⟩
  rw [he]
  exact SelectedTube.measurable_tube c hc (fun j => (chartAt H (a j)).source)
    (fun j => (chartAt H (a j)).open_source.measurableSet)
    (fun j => borelChart I (a j)) (fun j => measurable_borelChart I (a j))
    (fun t => S^[t]) (fun t => S.continuous.measurable.iterate t) n δ

noncomputable def originalObservation (P : M → C)
    (W : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x z : M) :=
  (W (P x,P (S^[n] x))).starProjection
    (borelChart I (a (c (S^[n] x))) (S^[n] z))

lemma measurable_originalObservation (hc : Measurable c) (P : M → C) (hP : Measurable P)
    (W : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    Measurable (Function.uncurry (originalObservation I S a c n P W)) := by
  exact EndpointObservation.measurable_observation P hP (fun x => (P x,c x))
    (hP.prodMk hc) (S^[n]) (S.continuous.measurable.iterate n)
    (fun j : C×ι => borelChart I (a j.2)) (fun j => measurable_borelChart I (a j.2))
    (fun q j => (W (q,j.1)).starProjection)

omit [MeasurableSpace M] [BorelSpace M]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

lemma originalObservation_eq_iff (P : M → C)
    (W : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x z : M)
    (hx : S^[n] x∈(chartAt H (a (c (S^[n] x)))).source)
    (hz : S^[n] z∈(chartAt H (a (c (S^[n] x)))).source) :
    originalObservation I S a c n P W x z=originalObservation I S a c n P W x x ↔
      originalEndpoint I S a c (n:=n) (W (P x,P (S^[n] x))) x z := by
  simp only [originalObservation,originalEndpoint,borelChart_eq I _ _ hx,borelChart_eq I _ _ hz]

lemma originalTube_mono {δ ε : ℝ} {x z : M} (h : δ≤ε)
    (hx : originalTube I S a c (n:=n) δ x z) :
    originalTube I S a c (n:=n) ε x z := fun t => ⟨(hx t).1,(hx t).2.trans h⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
open FiniteGreen ShortBin

/-- A measurable, witness-independent ORIGINAL pair switch. Its Borel relation
uses zero-extended charts, but all asserted equations and tube estimates are in
the original atlas. The retained set has not been normalized or repartitioned. -/
theorem canonical_original_switch (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r₀ C₀ : ℝ,0<r₀ ∧ 1≤C₀ ∧
      ∀ (C J : Type*) [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
        [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
        (c : M → ι) (P : M → C) (L : M → J) (G R : Set M)
        (n : ℕ) (B R₀ ε g α r δ : ℝ) (γ : C → ℝ)
        (A : ∀ x:G,BilateralGauge I S a c n B R₀ x)
        (T : G → Finset (Fin d)) (ref : G → G)
        (Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
        Measurable c → Measurable P → Measurable L → MeasurableSet R → R⊆G →
        (∀ v,v∈K (c v)) →
        (∀ x y,L x=L y → P x=P y) →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈R,I.IsInteriorPoint x) →
        (∀ x:G,P (ref x)=P x) →
        (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x y:G,P x=P y → ref x=ref y) →
        (∀ x:G,
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))ᶜ).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)ᶜ).starProjection‖≤ε ∧
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)).starProjection‖≤ε) →
        (∀ x:G,
          Module.finrank ℝ ((A x).forwardSpace I S a c n (T x))=
            Module.finrank ℝ (Wf (P x,P (S^[n] x))) ∧
          Module.finrank ℝ ((A x).backwardSpace I S a c n (T x)ᶜ)=
            Module.finrank ℝ (Wb (P x,P (S.symm^[n] x))) ∧
          ‖((A x).forwardSpace I S a c n (T x)).starProjection-
            (Wf (P x,P (S^[n] x))).starProjection‖≤1/2 ∧
          ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2) →
        0≤ε → ε≤1/2 → Real.exp (2*B)*(2*ε)≤1/2 →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (2*Real.exp (2*B))*(2*(2*Real.exp (2*B)^2*Real.exp (-2*g*n)))≤1/2 →
        (∀ x:G,|γ (P x)|+|g|≤α) → 0≤r → 0<δ → δ≤r₀ →
        (∀ x∈R,∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) δ⊆interior (range I)) →
        (∀ x∈R,∀ y∈R,L x=L y →
          ‖(extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x‖≤C₀*r) →
        bvpInverseBound B α n*C₀*δ≤1/4 → bvpInverseBound B α n*C₀*r≤δ/4 →
        ∃ Φ : M×M → M×M,Measurable Φ ∧
          (∀ x y:G,x.val∈R → y.val∈R → L x=L y →
            let z := (Φ (x.val,y.val)).1
            let w := (Φ (x.val,y.val)).2
            originalTube I S a c (n:=n) (δ/2) x z ∧
            originalTube I S.symm a c (n:=n) (δ/2) y z ∧
            originalTube I S a c (n:=n) (δ/2) y w ∧
            originalTube I S.symm a c (n:=n) (δ/2) x w ∧
            originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z ∧
            originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z ∧
            originalEndpoint I S a c (n:=n) (Wf (P y,P (S^[n] y))) y w ∧
            originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x w ∧
            originalTube I S a c (n:=n) (2*C₀*bvpInverseBound B α n*r) x z ∧
            originalTube I S.symm a c (n:=n) (2*C₀*bvpInverseBound B α n*r) y z ∧
            originalTube I S a c (n:=n) (2*C₀*bvpInverseBound B α n*r) y w ∧
            originalTube I S.symm a c (n:=n) (2*C₀*bvpInverseBound B α n*r) x w ∧
            ‖(extChartAt I (a (c x))) z-(extChartAt I (a (c x))) x-
              (((A (ref x)).forward I S a c).splitting (T (ref x))ᶜ).slow 0
                ((extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x)‖≤
                4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C₀*r)+
                  bvpInverseBound B α n*C₀*(2*C₀*bvpInverseBound B α n*r)^2) ∧
          ∀ x∈R,∀ z,
            originalTube I S a c (n:=n) δ x z → originalTube I S.symm a c (n:=n) δ x z →
            originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
            originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x z → z=x := by
  obtain ⟨r₀,C₀,hr₀,hC₀,hjoin⟩ := original_gauged_join I hclosed S a K hK hKU
  refine ⟨r₀,C₀,hr₀,hC₀,?_⟩
  intro C J _ _ _ _ _ _ c P L G R n B R₀ ε g α r δ γ A T ref Wf Wb
    hc hP hL hR hRG hcover hLP hPc hint href hcard hrefeq hstart hend hε hεhalf
    hsmall hslow hfast hgap hα hr hδ hδr hsafe hnear hcontract hdata
  let F := originalObservation I S a c n P Wf
  let V := originalObservation I S.symm a c n P Wb
  let TF := originalTube I S a c (n:=n) δ
  let TB := originalTube I S.symm a c (n:=n) δ
  let Gpair : Set (M×M) := {u | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
  have hGpair : MeasurableSet Gpair :=
    (hR.preimage measurable_fst).inter ((hR.preimage measurable_snd).inter
      (measurableSet_eq_fun (hL.comp measurable_fst) (hL.comp measurable_snd)))
  have hsrc (x : M) : x∈(chartAt H (a (c x))).source := hKU _ (hcover x)
  have hspec (x y : G) (hx : x.val∈R) (hy : y.val∈R) (hxy : L x=L y) := by
    have hp := hLP x y hxy
    have hcst :
        ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
          ((A y).forwardSpace I S a c 0 (T y)).starProjection‖≤ε := by
      rw [hrefeq x y hp]
      exact (hstart y).2
    exact hjoin c n B R₀ ε (γ (P x)) g α r δ (ref x) x y
      (A (ref x)) (A x) (A y) (T (ref x)) (T x) (T y)
      (Wf (P x,P (S^[n] x))) (Wb (P y,P (S.symm^[n] y))) hcover (hPc x y hp)
      (hint x hx) (hint y hy) (hend x).1 (hend y).2.1 (hend x).2.2.1 (hend y).2.2.2
      hε hεhalf (hcard _ _ (href x)) (hcard _ _ ((href x).trans hp)) (hstart x).1 hcst hsmall
      (hslow x) (hfast x) (by simpa only [hp] using hslow y) (by simpa only [hp] using hfast y)
      hgap (hα x) hr hδ hδr (fun t => (hsafe x hx t).1) (fun t => (hsafe y hy t).2)
      (hnear x hx y hy hxy) hcontract hdata
  have hrel (x y : M) (z : M) :
      MeasurableSwitch.relation F V TF TB (x,y) z ↔
        originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z ∧
        originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z ∧
        TF x z ∧ TB y z := by
    constructor
    · rintro ⟨hf,hb,htf,htb⟩
      exact ⟨(originalObservation_eq_iff I S a c n P Wf x z (hsrc _) (htf ⟨n,by omega⟩).1).mp hf,
        (originalObservation_eq_iff I S.symm a c n P Wb y z (hsrc _) (htb ⟨n,by omega⟩).1).mp hb,htf,htb⟩
    · rintro ⟨hf,hb,htf,htb⟩
      exact ⟨(originalObservation_eq_iff I S a c n P Wf x z (hsrc _) (htf ⟨n,by omega⟩).1).mpr hf,
        (originalObservation_eq_iff I S.symm a c n P Wb y z (hsrc _) (htb ⟨n,by omega⟩).1).mpr hb,htf,htb⟩
  have hex (u : M×M) (hu : u∈Gpair) : ∃! z,MeasurableSwitch.relation F V TF TB u z := by
    let x : G := ⟨u.1,hRG hu.1⟩
    let y : G := ⟨u.2,hRG hu.2.1⟩
    obtain ⟨z,hzf,hzb,hze,hze',hsharp,hsharp',hideal,hunique⟩ := hspec x y hu.1 hu.2.1 hu.2.2
    refine ⟨z,(hrel _ _ _).mpr ⟨hze,hze',?_,?_⟩,?_⟩
    · exact originalTube_mono I S a c n (by linarith) hzf
    · exact originalTube_mono I S.symm a c n (by linarith) hzb
    · intro z' hz'
      obtain ⟨hf,hb,htf,htb⟩ := (hrel _ _ _).mp hz'
      exact hunique z' htf htb hf hb
  have hswap (u : M×M) (hu : u∈Gpair) : u.swap∈Gpair := ⟨hu.2.1,hu.1,hu.2.2.symm⟩
  obtain ⟨Φ,hΦ,hΦr,hΦu,hΦu'⟩ := MeasurableSwitch.canonical_pair Gpair hGpair F V
    (measurable_originalObservation I S a c n hc P hP Wf)
    (measurable_originalObservation I S.symm a c n hc P hP Wb) TF TB
    (measurable_originalTube I S a c n hc hsrc δ)
    (measurable_originalTube I S.symm a c n hc hsrc δ) hex (fun u hu => hex u.swap (hswap u hu))
  refine ⟨Φ,hΦ,?_,?_⟩
  · intro x y hx hy hxy
    obtain ⟨z,hzf,hzb,hze,hze',hsf,hsb,hideal,hunique⟩ := hspec x y hx hy hxy
    obtain ⟨w,hwf,hwb,hwe,hwe',htf,htb,_,_⟩ := hspec y x hy hx hxy.symm
    have hz : z=(Φ (x.val,y.val)).1 := hΦu _ ⟨hx,hy,hxy⟩ _ ((hrel _ _ _).mpr
      ⟨hze,hze',originalTube_mono I S a c n (by linarith) hzf,
        originalTube_mono I S.symm a c n (by linarith) hzb⟩)
    have hw : w=(Φ (x.val,y.val)).2 := hΦu' _ ⟨hx,hy,hxy⟩ _ ((hrel _ _ _).mpr
      ⟨hwe,hwe',originalTube_mono I S a c n (by linarith) hwf,
        originalTube_mono I S.symm a c n (by linarith) hwb⟩)
    dsimp only
    rw [←hz,←hw]
    exact ⟨hzf,hzb,hwf,hwb,hze,hze',hwe,hwe',hsf,hsb,htf,htb,hideal⟩
  · intro x hx z htf htb hef heb
    obtain ⟨w,_,_,_,_,_,_,_,hunique⟩ := hspec (⟨x,hRG hx⟩ : G) ⟨x,hRG hx⟩ hx hx rfl
    have hselfF : originalTube I S a c (n:=n) δ x x := by
      intro t
      exact ⟨hsrc _,by simpa only [sub_self,norm_zero] using hδ.le⟩
    have hselfB : originalTube I S.symm a c (n:=n) δ x x := by
      intro t
      exact ⟨hsrc _,by simpa only [sub_self,norm_zero] using hδ.le⟩
    exact (hunique z htf htb hef heb).trans (hunique x hselfF hselfB rfl rfl).symm
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
open FiniteGreen ShortBin

/-- A measurable, witness-independent ORIGINAL pair switch. Its Borel relation
uses zero-extended charts, but all asserted equations and tube estimates are in
the original atlas. The retained set has not been normalized or repartitioned. -/
theorem canonical_original_switch_unique (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r₀ C₀ : ℝ,0<r₀ ∧ 1≤C₀ ∧
      ∀ (C J : Type*) [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
        [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
        (c : M → ι) (P : M → C) (L : M → J) (G R : Set M)
        (n : ℕ) (B R₀ ε g α r δ : ℝ) (γ : C → ℝ)
        (A : ∀ x:G,BilateralGauge I S a c n B R₀ x)
        (T : G → Finset (Fin d)) (ref : G → G)
        (Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
        Measurable c → Measurable P → Measurable L → MeasurableSet R → R⊆G →
        (∀ v,v∈K (c v)) →
        (∀ x y,L x=L y → P x=P y) →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈R,I.IsInteriorPoint x) →
        (∀ x:G,P (ref x)=P x) →
        (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x y:G,P x=P y → ref x=ref y) →
        (∀ x:G,
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))ᶜ).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)ᶜ).starProjection‖≤ε ∧
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)).starProjection‖≤ε) →
        (∀ x:G,
          Module.finrank ℝ ((A x).forwardSpace I S a c n (T x))=
            Module.finrank ℝ (Wf (P x,P (S^[n] x))) ∧
          Module.finrank ℝ ((A x).backwardSpace I S a c n (T x)ᶜ)=
            Module.finrank ℝ (Wb (P x,P (S.symm^[n] x))) ∧
          ‖((A x).forwardSpace I S a c n (T x)).starProjection-
            (Wf (P x,P (S^[n] x))).starProjection‖≤1/2 ∧
          ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2) →
        0≤ε → ε≤1/2 → Real.exp (2*B)*(2*ε)≤1/2 →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (2*Real.exp (2*B))*(2*(2*Real.exp (2*B)^2*Real.exp (-2*g*n)))≤1/2 →
        (∀ x:G,|γ (P x)|+|g|≤α) → 0≤r → 0<δ → δ≤r₀ →
        (∀ x∈R,∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) δ⊆interior (range I)) →
        (∀ x∈R,∀ y∈R,L x=L y →
          ‖(extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x‖≤C₀*r) →
        bvpInverseBound B α n*C₀*δ≤1/4 → bvpInverseBound B α n*C₀*r≤δ/4 →
        ∃ Φ : M×M → M×M,Measurable Φ ∧
          (∀ x y:G,x.val∈R → y.val∈R → L x=L y →
            let z := (Φ (x.val,y.val)).1
            let w := (Φ (x.val,y.val)).2
            originalTube I S a c (n:=n) (δ/2) x z ∧
            originalTube I S.symm a c (n:=n) (δ/2) y z ∧
            originalTube I S a c (n:=n) (δ/2) y w ∧
            originalTube I S.symm a c (n:=n) (δ/2) x w ∧
            originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z ∧
            originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z ∧
            originalEndpoint I S a c (n:=n) (Wf (P y,P (S^[n] y))) y w ∧
            originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x w ∧
            originalTube I S a c (n:=n) (2*C₀*bvpInverseBound B α n*r) x z ∧
            originalTube I S.symm a c (n:=n) (2*C₀*bvpInverseBound B α n*r) y z ∧
            originalTube I S a c (n:=n) (2*C₀*bvpInverseBound B α n*r) y w ∧
            originalTube I S.symm a c (n:=n) (2*C₀*bvpInverseBound B α n*r) x w ∧
            ‖(extChartAt I (a (c x))) z-(extChartAt I (a (c x))) x-
              (((A (ref x)).forward I S a c).splitting (T (ref x))ᶜ).slow 0
                ((extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x)‖≤
                4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C₀*r)+
                  bvpInverseBound B α n*C₀*(2*C₀*bvpInverseBound B α n*r)^2) ∧
          (∀ x∈R,∀ z,
            originalTube I S a c (n:=n) δ x z → originalTube I S.symm a c (n:=n) δ x z →
            originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
            originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x z → z=x) ∧
          ∀ x∈R,∀ y∈R,L x=L y → ∀ z,
            originalTube I S a c (n:=n) δ x z → originalTube I S.symm a c (n:=n) δ y z →
            originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
            originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z →
              z=(Φ (x,y)).1 := by
  obtain ⟨r₀,C₀,hr₀,hC₀,hjoin⟩ := original_gauged_join I hclosed S a K hK hKU
  refine ⟨r₀,C₀,hr₀,hC₀,?_⟩
  intro C J _ _ _ _ _ _ c P L G R n B R₀ ε g α r δ γ A T ref Wf Wb
    hc hP hL hR hRG hcover hLP hPc hint href hcard hrefeq hstart hend hε hεhalf
    hsmall hslow hfast hgap hα hr hδ hδr hsafe hnear hcontract hdata
  let F := originalObservation I S a c n P Wf
  let V := originalObservation I S.symm a c n P Wb
  let TF := originalTube I S a c (n:=n) δ
  let TB := originalTube I S.symm a c (n:=n) δ
  let Gpair : Set (M×M) := {u | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
  have hGpair : MeasurableSet Gpair :=
    (hR.preimage measurable_fst).inter ((hR.preimage measurable_snd).inter
      (measurableSet_eq_fun (hL.comp measurable_fst) (hL.comp measurable_snd)))
  have hsrc (x : M) : x∈(chartAt H (a (c x))).source := hKU _ (hcover x)
  have hspec (x y : G) (hx : x.val∈R) (hy : y.val∈R) (hxy : L x=L y) := by
    have hp := hLP x y hxy
    have hcst :
        ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
          ((A y).forwardSpace I S a c 0 (T y)).starProjection‖≤ε := by
      rw [hrefeq x y hp]
      exact (hstart y).2
    exact hjoin c n B R₀ ε (γ (P x)) g α r δ (ref x) x y
      (A (ref x)) (A x) (A y) (T (ref x)) (T x) (T y)
      (Wf (P x,P (S^[n] x))) (Wb (P y,P (S.symm^[n] y))) hcover (hPc x y hp)
      (hint x hx) (hint y hy) (hend x).1 (hend y).2.1 (hend x).2.2.1 (hend y).2.2.2
      hε hεhalf (hcard _ _ (href x)) (hcard _ _ ((href x).trans hp)) (hstart x).1 hcst hsmall
      (hslow x) (hfast x) (by simpa only [hp] using hslow y) (by simpa only [hp] using hfast y)
      hgap (hα x) hr hδ hδr (fun t => (hsafe x hx t).1) (fun t => (hsafe y hy t).2)
      (hnear x hx y hy hxy) hcontract hdata
  have hrel (x y : M) (z : M) :
      MeasurableSwitch.relation F V TF TB (x,y) z ↔
        originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z ∧
        originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z ∧
        TF x z ∧ TB y z := by
    constructor
    · rintro ⟨hf,hb,htf,htb⟩
      exact ⟨(originalObservation_eq_iff I S a c n P Wf x z (hsrc _) (htf ⟨n,by omega⟩).1).mp hf,
        (originalObservation_eq_iff I S.symm a c n P Wb y z (hsrc _) (htb ⟨n,by omega⟩).1).mp hb,htf,htb⟩
    · rintro ⟨hf,hb,htf,htb⟩
      exact ⟨(originalObservation_eq_iff I S a c n P Wf x z (hsrc _) (htf ⟨n,by omega⟩).1).mpr hf,
        (originalObservation_eq_iff I S.symm a c n P Wb y z (hsrc _) (htb ⟨n,by omega⟩).1).mpr hb,htf,htb⟩
  have hex (u : M×M) (hu : u∈Gpair) : ∃! z,MeasurableSwitch.relation F V TF TB u z := by
    let x : G := ⟨u.1,hRG hu.1⟩
    let y : G := ⟨u.2,hRG hu.2.1⟩
    obtain ⟨z,hzf,hzb,hze,hze',hsharp,hsharp',hideal,hunique⟩ := hspec x y hu.1 hu.2.1 hu.2.2
    refine ⟨z,(hrel _ _ _).mpr ⟨hze,hze',?_,?_⟩,?_⟩
    · exact originalTube_mono I S a c n (by linarith) hzf
    · exact originalTube_mono I S.symm a c n (by linarith) hzb
    · intro z' hz'
      obtain ⟨hf,hb,htf,htb⟩ := (hrel _ _ _).mp hz'
      exact hunique z' htf htb hf hb
  have hswap (u : M×M) (hu : u∈Gpair) : u.swap∈Gpair := ⟨hu.2.1,hu.1,hu.2.2.symm⟩
  obtain ⟨Φ,hΦ,hΦr,hΦu,hΦu'⟩ := MeasurableSwitch.canonical_pair Gpair hGpair F V
    (measurable_originalObservation I S a c n hc P hP Wf)
    (measurable_originalObservation I S.symm a c n hc P hP Wb) TF TB
    (measurable_originalTube I S a c n hc hsrc δ)
    (measurable_originalTube I S.symm a c n hc hsrc δ) hex (fun u hu => hex u.swap (hswap u hu))
  refine ⟨Φ,hΦ,?_,?_,?_⟩
  · intro x y hx hy hxy
    obtain ⟨z,hzf,hzb,hze,hze',hsf,hsb,hideal,hunique⟩ := hspec x y hx hy hxy
    obtain ⟨w,hwf,hwb,hwe,hwe',htf,htb,_,_⟩ := hspec y x hy hx hxy.symm
    have hz : z=(Φ (x.val,y.val)).1 := hΦu _ ⟨hx,hy,hxy⟩ _ ((hrel _ _ _).mpr
      ⟨hze,hze',originalTube_mono I S a c n (by linarith) hzf,
        originalTube_mono I S.symm a c n (by linarith) hzb⟩)
    have hw : w=(Φ (x.val,y.val)).2 := hΦu' _ ⟨hx,hy,hxy⟩ _ ((hrel _ _ _).mpr
      ⟨hwe,hwe',originalTube_mono I S a c n (by linarith) hwf,
        originalTube_mono I S.symm a c n (by linarith) hwb⟩)
    dsimp only
    rw [←hz,←hw]
    exact ⟨hzf,hzb,hwf,hwb,hze,hze',hwe,hwe',hsf,hsb,htf,htb,hideal⟩
  · intro x hx z htf htb hef heb
    obtain ⟨w,_,_,_,_,_,_,_,hunique⟩ := hspec (⟨x,hRG hx⟩ : G) ⟨x,hRG hx⟩ hx hx rfl
    have hselfF : originalTube I S a c (n:=n) δ x x := by
      intro t
      exact ⟨hsrc _,by simpa only [sub_self,norm_zero] using hδ.le⟩
    have hselfB : originalTube I S.symm a c (n:=n) δ x x := by
      intro t
      exact ⟨hsrc _,by simpa only [sub_self,norm_zero] using hδ.le⟩
    exact (hunique z htf htb hef heb).trans (hunique x hselfF hselfB rfl rfl).symm
  · intro x hx y hy hxy z htf htb hef heb
    exact hΦu _ ⟨hx,hy,hxy⟩ z ((hrel x y z).mpr ⟨hef,heb,htf,htb⟩)
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
open FiniteGreen ShortBin

/-- A measurable, witness-independent ORIGINAL pair switch. Its Borel relation
uses zero-extended charts, but all asserted equations and tube estimates are in
the original atlas. The retained set has not been normalized or repartitioned. -/
theorem canonical_original_switch_complete (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r₀ C₀ : ℝ,0<r₀ ∧ 1≤C₀ ∧
      ∀ (C J : Type*) [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
        [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
        (c : M → ι) (P : M → C) (L : M → J) (G R : Set M)
        (n : ℕ) (B R₀ ε g α r δ : ℝ) (γ : C → ℝ)
        (A : ∀ x:G,BilateralGauge I S a c n B R₀ x)
        (T : G → Finset (Fin d)) (ref : G → G)
        (Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
        Measurable c → Measurable P → Measurable L → MeasurableSet R → R⊆G →
        (∀ v,v∈K (c v)) →
        (∀ x y,L x=L y → P x=P y) →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈R,I.IsInteriorPoint x) →
        (∀ x:G,P (ref x)=P x) →
        (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x y:G,P x=P y → ref x=ref y) →
        (∀ x:G,
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))ᶜ).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)ᶜ).starProjection‖≤ε ∧
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)).starProjection‖≤ε) →
        (∀ x:G,
          Module.finrank ℝ ((A x).forwardSpace I S a c n (T x))=
            Module.finrank ℝ (Wf (P x,P (S^[n] x))) ∧
          Module.finrank ℝ ((A x).backwardSpace I S a c n (T x)ᶜ)=
            Module.finrank ℝ (Wb (P x,P (S.symm^[n] x))) ∧
          ‖((A x).forwardSpace I S a c n (T x)).starProjection-
            (Wf (P x,P (S^[n] x))).starProjection‖≤1/2 ∧
          ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2) →
        0≤ε → ε≤1/2 → Real.exp (2*B)*(2*ε)≤1/2 →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (2*Real.exp (2*B))*(2*(2*Real.exp (2*B)^2*Real.exp (-2*g*n)))≤1/2 →
        (∀ x:G,|γ (P x)|+|g|≤α) → 0≤r → 0<δ → δ≤r₀ →
        (∀ x∈R,∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) δ⊆interior (range I)) →
        (∀ x∈R,∀ y∈R,L x=L y →
          ‖(extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x‖≤C₀*r) →
        bvpInverseBound B α n*C₀*δ≤1/4 → bvpInverseBound B α n*C₀*r≤δ/4 →
        ∃ Φ : M×M → M×M,Measurable Φ ∧
          (∀ x y:G,x.val∈R → y.val∈R → L x=L y →
            let z := (Φ (x.val,y.val)).1
            let w := (Φ (x.val,y.val)).2
            originalTube I S a c (n:=n) (δ/2) x z ∧
            originalTube I S.symm a c (n:=n) (δ/2) y z ∧
            originalTube I S a c (n:=n) (δ/2) y w ∧
            originalTube I S.symm a c (n:=n) (δ/2) x w ∧
            originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z ∧
            originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z ∧
            originalEndpoint I S a c (n:=n) (Wf (P y,P (S^[n] y))) y w ∧
            originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x w ∧
            originalTube I S a c (n:=n) (2*C₀*bvpInverseBound B α n*r) x z ∧
            originalTube I S.symm a c (n:=n) (2*C₀*bvpInverseBound B α n*r) y z ∧
            originalTube I S a c (n:=n) (2*C₀*bvpInverseBound B α n*r) y w ∧
            originalTube I S.symm a c (n:=n) (2*C₀*bvpInverseBound B α n*r) x w ∧
            ‖(extChartAt I (a (c x))) z-(extChartAt I (a (c x))) x-
              (((A (ref x)).forward I S a c).splitting (T (ref x))ᶜ).slow 0
                ((extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x)‖≤
                4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C₀*r)+
                  bvpInverseBound B α n*C₀*(2*C₀*bvpInverseBound B α n*r)^2 ∧
            ‖(extChartAt I (a (c y))) w-(extChartAt I (a (c y))) y-
              (((A (ref y)).forward I S a c).splitting (T (ref y))ᶜ).slow 0
                ((extChartAt I (a (c x))) x-(extChartAt I (a (c y))) y)‖≤
                4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C₀*r)+
                  bvpInverseBound B α n*C₀*(2*C₀*bvpInverseBound B α n*r)^2) ∧
          (∀ x∈R,∀ z,
            originalTube I S a c (n:=n) δ x z → originalTube I S.symm a c (n:=n) δ x z →
            originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
            originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x z → z=x) ∧
          ∀ x∈R,∀ y∈R,L x=L y → ∀ z,
            originalTube I S a c (n:=n) δ x z → originalTube I S.symm a c (n:=n) δ y z →
            originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
            originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z →
              z=(Φ (x,y)).1 := by
  obtain ⟨r₀,C₀,hr₀,hC₀,hjoin⟩ := original_gauged_join I hclosed S a K hK hKU
  refine ⟨r₀,C₀,hr₀,hC₀,?_⟩
  intro C J _ _ _ _ _ _ c P L G R n B R₀ ε g α r δ γ A T ref Wf Wb
    hc hP hL hR hRG hcover hLP hPc hint href hcard hrefeq hstart hend hε hεhalf
    hsmall hslow hfast hgap hα hr hδ hδr hsafe hnear hcontract hdata
  let F := originalObservation I S a c n P Wf
  let V := originalObservation I S.symm a c n P Wb
  let TF := originalTube I S a c (n:=n) δ
  let TB := originalTube I S.symm a c (n:=n) δ
  let Gpair : Set (M×M) := {u | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
  have hGpair : MeasurableSet Gpair :=
    (hR.preimage measurable_fst).inter ((hR.preimage measurable_snd).inter
      (measurableSet_eq_fun (hL.comp measurable_fst) (hL.comp measurable_snd)))
  have hsrc (x : M) : x∈(chartAt H (a (c x))).source := hKU _ (hcover x)
  have hspec (x y : G) (hx : x.val∈R) (hy : y.val∈R) (hxy : L x=L y) := by
    have hp := hLP x y hxy
    have hcst :
        ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
          ((A y).forwardSpace I S a c 0 (T y)).starProjection‖≤ε := by
      rw [hrefeq x y hp]
      exact (hstart y).2
    exact hjoin c n B R₀ ε (γ (P x)) g α r δ (ref x) x y
      (A (ref x)) (A x) (A y) (T (ref x)) (T x) (T y)
      (Wf (P x,P (S^[n] x))) (Wb (P y,P (S.symm^[n] y))) hcover (hPc x y hp)
      (hint x hx) (hint y hy) (hend x).1 (hend y).2.1 (hend x).2.2.1 (hend y).2.2.2
      hε hεhalf (hcard _ _ (href x)) (hcard _ _ ((href x).trans hp)) (hstart x).1 hcst hsmall
      (hslow x) (hfast x) (by simpa only [hp] using hslow y) (by simpa only [hp] using hfast y)
      hgap (hα x) hr hδ hδr (fun t => (hsafe x hx t).1) (fun t => (hsafe y hy t).2)
      (hnear x hx y hy hxy) hcontract hdata
  have hrel (x y : M) (z : M) :
      MeasurableSwitch.relation F V TF TB (x,y) z ↔
        originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z ∧
        originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z ∧
        TF x z ∧ TB y z := by
    constructor
    · rintro ⟨hf,hb,htf,htb⟩
      exact ⟨(originalObservation_eq_iff I S a c n P Wf x z (hsrc _) (htf ⟨n,by omega⟩).1).mp hf,
        (originalObservation_eq_iff I S.symm a c n P Wb y z (hsrc _) (htb ⟨n,by omega⟩).1).mp hb,htf,htb⟩
    · rintro ⟨hf,hb,htf,htb⟩
      exact ⟨(originalObservation_eq_iff I S a c n P Wf x z (hsrc _) (htf ⟨n,by omega⟩).1).mpr hf,
        (originalObservation_eq_iff I S.symm a c n P Wb y z (hsrc _) (htb ⟨n,by omega⟩).1).mpr hb,htf,htb⟩
  have hex (u : M×M) (hu : u∈Gpair) : ∃! z,MeasurableSwitch.relation F V TF TB u z := by
    let x : G := ⟨u.1,hRG hu.1⟩
    let y : G := ⟨u.2,hRG hu.2.1⟩
    obtain ⟨z,hzf,hzb,hze,hze',hsharp,hsharp',hideal,hunique⟩ := hspec x y hu.1 hu.2.1 hu.2.2
    refine ⟨z,(hrel _ _ _).mpr ⟨hze,hze',?_,?_⟩,?_⟩
    · exact originalTube_mono I S a c n (by linarith) hzf
    · exact originalTube_mono I S.symm a c n (by linarith) hzb
    · intro z' hz'
      obtain ⟨hf,hb,htf,htb⟩ := (hrel _ _ _).mp hz'
      exact hunique z' htf htb hf hb
  have hswap (u : M×M) (hu : u∈Gpair) : u.swap∈Gpair := ⟨hu.2.1,hu.1,hu.2.2.symm⟩
  obtain ⟨Φ,hΦ,hΦr,hΦu,hΦu'⟩ := MeasurableSwitch.canonical_pair Gpair hGpair F V
    (measurable_originalObservation I S a c n hc P hP Wf)
    (measurable_originalObservation I S.symm a c n hc P hP Wb) TF TB
    (measurable_originalTube I S a c n hc hsrc δ)
    (measurable_originalTube I S.symm a c n hc hsrc δ) hex (fun u hu => hex u.swap (hswap u hu))
  refine ⟨Φ,hΦ,?_,?_,?_⟩
  · intro x y hx hy hxy
    obtain ⟨z,hzf,hzb,hze,hze',hsf,hsb,hideal,hunique⟩ := hspec x y hx hy hxy
    obtain ⟨w,hwf,hwb,hwe,hwe',htf,htb,hideal',_⟩ := hspec y x hy hx hxy.symm
    have hz : z=(Φ (x.val,y.val)).1 := hΦu _ ⟨hx,hy,hxy⟩ _ ((hrel _ _ _).mpr
      ⟨hze,hze',originalTube_mono I S a c n (by linarith) hzf,
        originalTube_mono I S.symm a c n (by linarith) hzb⟩)
    have hw : w=(Φ (x.val,y.val)).2 := hΦu' _ ⟨hx,hy,hxy⟩ _ ((hrel _ _ _).mpr
      ⟨hwe,hwe',originalTube_mono I S a c n (by linarith) hwf,
        originalTube_mono I S.symm a c n (by linarith) hwb⟩)
    dsimp only
    rw [←hz,←hw]
    exact ⟨hzf,hzb,hwf,hwb,hze,hze',hwe,hwe',hsf,hsb,htf,htb,hideal,hideal'⟩
  · intro x hx z htf htb hef heb
    obtain ⟨w,_,_,_,_,_,_,_,hunique⟩ := hspec (⟨x,hRG hx⟩ : G) ⟨x,hRG hx⟩ hx hx rfl
    have hselfF : originalTube I S a c (n:=n) δ x x := by
      intro t
      exact ⟨hsrc _,by simpa only [sub_self,norm_zero] using hδ.le⟩
    have hselfB : originalTube I S.symm a c (n:=n) δ x x := by
      intro t
      exact ⟨hsrc _,by simpa only [sub_self,norm_zero] using hδ.le⟩
    exact (hunique z htf htb hef heb).trans (hunique x hselfF hselfB rfl rfl).symm
  · intro x hx y hy hxy z htf htb hef heb
    exact hΦu _ ⟨hx,hy,hxy⟩ z ((hrel x y z).mpr ⟨hef,heb,htf,htb⟩)
end SmoothObstruction.ManifoldCoordinates

end

end OAI
