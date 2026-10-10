import OAI.Dynamics.SmoothObstruction.ManifoldMatching

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.FiniteBins
open Set
variable {X C : Type*} (P : X → C) (G : Set X)
/-- Only bins meeting the original good set require a reference. -/
def Active := {c : C // ∃ x∈G,P x=c}
def Fiber (c : Active P G) := {x : G // P x=c.val}

noncomputable def reference (c : Active P G) : Fiber P G c := by
  classical
  apply Classical.choice
  obtain ⟨x,hx,hP⟩ := c.property
  exact ⟨⟨⟨x,hx⟩,hP⟩⟩

instance [Finite C] : Finite (Active P G) :=
  inferInstanceAs (Finite {category : C // ∃ point∈G,P point=category})
end SmoothObstruction.FiniteBins

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι C : Type*} [Fintype ι]

/-- The original genuine finite-window estimates produce all starting-bin
thresholds simultaneously. Only finite bin reference choices survive: no
measurable choice of frame, exponent, or orbit chart code is used. -/
theorem finite_starting_references (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ rF CF rB CB D : ℝ,0<rF ∧ 1≤CF ∧ 0<rB ∧ 1≤CB ∧ 1≤D ∧
      ∀ (c : M → ι) (P : M → C) (G : Set M)
        (n N : ℕ) (B R h g : ℝ) (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint x) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        CF^N*h≤rF → CB^N*h≤rB → 0<g →
        Real.exp (-2*g*N+4*(B+Real.log D))≤1/2 →
        (let δ := ((N:ℝ)*CF*CF^(2*N)+N*CB*CB^(2*N))*h
         δ<Real.exp (-2*(B+Real.log D))/2 ∧
         Real.exp (-2*g*N+4*(B+Real.log D))+
           δ*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))≤1/2) →
        ∃ j : Active P G → Fin (d+1),∀ Q : Active P G,
          let x₀ : G := (reference P G Q).val
          let γ := (1+8*((j Q).val:ℝ))*g
          let ε := Real.exp (-2*g*N+4*(B+Real.log D))+
            (((N:ℝ)*CF*CF^(2*N)+N*CB*CB^(2*N))*h)*
              Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))
          ∀ x:G,P x=Q.val →
            (∀ k,(A x).lam k<γ-g ∨ γ+g<(A x).lam k) ∧
            (Finset.univ.filter (fun k => γ<(A x).lam k)).card=
              (Finset.univ.filter (fun k => γ<(A x₀).lam k)).card ∧
            ‖(((A x).forward I S a c).space (Finset.univ.filter (fun k => (A x).lam k≤γ))).starProjection-
              (((A x₀).forward I S a c).space (Finset.univ.filter (fun k => (A x₀).lam k≤γ))).starProjection‖≤3*ε ∧
            ‖(((A x).forward I S a c).space (Finset.univ.filter (fun k => γ<(A x).lam k))).starProjection-
              (((A x₀).forward I S a c).space (Finset.univ.filter (fun k => γ<(A x₀).lam k))).starProjection‖≤3*ε := by
  classical
  obtain ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,hh⟩ :=
    uniform_genuine_bin_splitting I hclosed S a K hK hKU
  refine ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,?_⟩
  intro c P G n N B R h g A hc hN hco hint hdiam hsF hsB hg hdec hsmall
  have hex (Q : Active P G) := hh c (Fiber P G Q) (fun x => x.val.val)
    (reference P G Q) n N B R h g (fun x => A x.val) hc hN
    (fun x => hco _ _ (x.property.trans (reference P G Q).property.symm))
    (fun x => hint _ x.val.property)
    (fun x => hdiam _ _ (x.property.trans (reference P G Q).property.symm))
    hsF hsB hg hdec hsmall.1 hsmall.2
  choose j hj using hex
  refine ⟨j,?_⟩
  intro Q x₀ γ ε x hx
  have hgx := (hj Q).1 (⟨x,hx⟩ : Fiber P G Q)
  exact ⟨hgx.1,hgx.2,(hj Q).2.1 ⟨x,hx⟩,(hj Q).2.2 ⟨x,hx⟩⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι C : Type*} [Fintype ι]

/-- The endpoint reference is indexed only by starting and endpoint coarse
bins. The common starting rank and threshold are retained unchanged. Inactive
endpoint keys are not part of the construction or the partition count. -/
theorem finite_endpoint_references (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C₁ D : ℝ,0<r ∧ 1≤C₁ ∧ 1≤D ∧
      ∀ (c : M → ι) (P : M → C) (G : Set M) (n N : ℕ) (B R h g : ℝ)
        (γ : C → ℝ) (T : G → Finset (Fin d))
        (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint (S^[n] x)) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        C₁^N*h≤r → 0≤h →
        (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (∀ q : C,let ε := Real.exp ((γ q-g)*N+2*(B+Real.log D))*
          (Real.exp ((-γ q-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)
          ε≤1/2) →
        let EKey := fun x => (P x,P (S^[n] x))
        ∃ W : Active EKey G → Submodule ℝ (EuclideanSpace ℝ (Fin d)),
          ∀ Q : Active EKey G,∀ x:G,EKey x=Q.val →
            Module.finrank ℝ (W Q)=(T x).card ∧
            ‖((A x).forwardSpace I S a c n (T x)).starProjection-(W Q).starProjection‖≤
              3*(Real.exp ((γ (P x)-g)*N+2*(B+Real.log D))*
                (Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)) := by
  classical
  obtain ⟨r,C₁,D,hr,hC,hD,hh⟩ := uniform_original_endpoint_fast_comparison I hclosed S a K hK hKU
  refine ⟨r,C₁,D,hr,hC,hD,?_⟩
  intro c P G n N B R h g γ T A hc hN hco hint hdiam ht hn hdim hslow hfast hsmall EKey
  let ref (Q : Active EKey G) : G := (reference EKey G Q).val
  let W (Q : Active EKey G) := (A (ref Q)).forwardSpace I S a c n (T (ref Q))
  refine ⟨W,?_⟩
  intro Q x hx
  have hp (y : Fiber EKey G Q) : EKey y.val=EKey (ref Q) :=
    y.property.trans (reference EKey G Q).property.symm
  have hq (y : Fiber EKey G Q) : P y.val=P (ref Q) := congrArg Prod.fst (hp y)
  have hend (y : Fiber EKey G Q) : P (S^[n] y.val.val)=P (S^[n] (ref Q).val) :=
    congrArg Prod.snd (hp y)
  have he : P x=P (ref Q) := hq ⟨x,hx⟩
  constructor
  · exact (EuclideanSplitting.finrank_groupSpace ((A (ref Q)).UF n)
      ((A (ref Q)).VF n) ((A (ref Q)).invF n).1 ((A (ref Q)).invF n).2
      (T (ref Q))).trans (hdim _ _ he.symm)
  · have hb := hh c (Fiber EKey G Q) (fun y => y.val.val) (reference EKey G Q)
      n N B R h (γ (P (ref Q))) g (fun y => T y.val) (fun y => A y.val)
      hc hN (fun y => hco _ _ (hend y)) (fun y => hint _ y.val.property)
      (fun y => hdiam _ _ (hend y)) ht hn (fun y => hdim _ _ (hq y).symm)
      (fun y j hj => by simpa only [←hq y] using hslow y.val j hj)
      (fun y j hj => by simpa only [←hq y] using hfast y.val j hj)
      (hsmall (P (ref Q))) (⟨x,hx⟩ : Fiber EKey G Q)
    simpa only [W,ref,he] using hb
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    {n : ℕ} {B R : ℝ} {x : M}

/-- Time reversal keeps the original gauge and negates its rates; it is not
an independently selected certificate. -/
noncomputable def BilateralGauge.reverse (A : BilateralGauge I S a c n B R x) :
    BilateralGauge I S.symm a c n B R x where
  lam := fun j => -A.lam j
  rate_bound j := by simpa only [abs_neg] using A.rate_bound j
  UF := A.UB
  VF := A.VB
  UB := A.UF
  VB := A.VF
  invF := A.invB
  invB := A.invF
  centerU := A.centerU.symm
  centerV := A.centerV.symm
  normF := A.normB
  normB := A.normF
  stepF := A.stepB
  stepB t ht := by
    have he : S.symm.symm = S := by ext x; rfl
    simpa only [he,neg_neg] using A.stepF t ht

@[simp] lemma BilateralGauge.reverse_forwardSpace (A : BilateralGauge I S a c n B R x)
    (t : ℕ) (T : Finset (Fin d)) :
    (A.reverse I S a c).forwardSpace I S.symm a c t T=A.backwardSpace I S a c t T := rfl

/-- The two true middle subspaces agree exactly. -/
lemma BilateralGauge.backwardSpace_zero (A : BilateralGauge I S a c n B R x)
    (T : Finset (Fin d)) :
    A.backwardSpace I S a c 0 T=A.forwardSpace I S a c 0 T := by
  simp only [BilateralGauge.backwardSpace,BilateralGauge.forwardSpace,A.centerU,A.centerV]
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.FiniteBins
open Set
variable {X C Z : Type*} (P : X → C) (G : Set X)
def key (x : G) : Active P G := ⟨P x,⟨x,x.property,rfl⟩⟩
noncomputable def extend (f : Active P G → Z) (z₀ : Z) (c : C) : Z := by
  classical
  exact if h : ∃ x∈G,P x=c then f ⟨c,h⟩ else z₀
@[simp] lemma extend_active (f : Active P G → Z) (z₀ : Z) (c : Active P G) :
    extend P G f z₀ c.val=f c := by
  classical
  simp only [extend,dite_eq_left c.property]
  congr 1
@[simp] lemma extend_key (f : Active P G → Z) (z₀ : Z) (x : G) :
    extend P G f z₀ (P x)=f (key P G x) := extend_active P G f z₀ (key P G x)
end SmoothObstruction.FiniteBins

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι C : Type*} [Fintype ι]

/-- All future and past reference projectors are selected from the same
original good inputs. Their labels are exactly (starting bin, endpoint bin).
Time reversal is the original bilateral gauge, so its endpoint rank is the
complementary original rank, not a new threshold or a separately chosen frame. -/
theorem bilateral_endpoint_references (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ rF CF DF rB CB DB : ℝ,0<rF ∧ 1≤CF ∧ 1≤DF ∧ 0<rB ∧ 1≤CB ∧ 1≤DB ∧
      ∀ (c : M → ι) (P : M → C) (G : Set M) (n N : ℕ) (B R h g : ℝ)
        (γ : C → ℝ) (T : G → Finset (Fin d))
        (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint (S^[n] x) ∧ I.IsInteriorPoint (S.symm^[n] x)) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        CF^N*h≤rF → CB^N*h≤rB → 0≤h →
        (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (∀ q : C,Real.exp ((γ q-g)*N+2*(B+Real.log DF))*
          (Real.exp ((-γ q-g)*N+2*(B+Real.log DF))+N*CF*CF^(2*N)*h)≤1/2) →
        (∀ q : C,Real.exp ((-γ q-g)*N+2*(B+Real.log DB))*
          (Real.exp ((γ q-g)*N+2*(B+Real.log DB))+N*CB*CB^(2*N)*h)≤1/2) →
        ∃ Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d)),∀ x:G,
          Module.finrank ℝ (Wf (P x,P (S^[n] x)))=(T x).card ∧
          Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-(T x).card ∧
          ‖((A x).forwardSpace I S a c n (T x)).starProjection-
            (Wf (P x,P (S^[n] x))).starProjection‖≤
              3*(Real.exp ((γ (P x)-g)*N+2*(B+Real.log DF))*
                (Real.exp ((-γ (P x)-g)*N+2*(B+Real.log DF))+N*CF*CF^(2*N)*h)) ∧
          ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n] x))).starProjection‖≤
              3*(Real.exp ((-γ (P x)-g)*N+2*(B+Real.log DB))*
                (Real.exp ((γ (P x)-g)*N+2*(B+Real.log DB))+N*CB*CB^(2*N)*h)) := by
  classical
  obtain ⟨rF,CF,DF,hrF,hCF,hDF,hF⟩ := finite_endpoint_references (C:=C) I hclosed S a K hK hKU
  obtain ⟨rB,CB,DB,hrB,hCB,hDB,hB⟩ := finite_endpoint_references (C:=C) I hclosed S.symm a K hK hKU
  refine ⟨rF,CF,DF,rB,CB,DB,hrF,hCF,hDF,hrB,hCB,hDB,?_⟩
  intro c P G n N B R h g γ T A hc hN hco hint hdiam htF htB hh hcard hslow hfast hsmallF hsmallB
  obtain ⟨WF,hWF⟩ := hF c P G n N B R h g γ T A hc hN hco
    (fun x hx => (hint x hx).1) hdiam htF hh hcard hslow hfast hsmallF
  have hcardB (x y : G) (hxy : P x=P y) : (T x)ᶜ.card=(T y)ᶜ.card := by
    simp only [Finset.card_compl,Fintype.card_fin,hcard x y hxy]
  have hsB (x : G) (j : Fin d) (hj : j∈((T x)ᶜ)ᶜ) :
      -((A x).lam j)≤(-γ (P x))-g := by
    simp only [compl_compl] at hj
    linarith [hfast x j hj]
  have hfB (x : G) (j : Fin d) (hj : j∈(T x)ᶜ) :
      (-γ (P x))+g≤-((A x).lam j) := by linarith [hslow x j hj]
  obtain ⟨WB,hWB⟩ := hB c P G n N B R h g (fun q => -γ q) (fun x => (T x)ᶜ)
    (fun x => (A x).reverse I S a c) hc hN hco (fun x hx => (hint x hx).2)
    hdiam htB hh hcardB hsB hfB (by simpa only [neg_neg] using hsmallB)
  let PF (x : M) := (P x,P (S^[n] x))
  let PB (x : M) := (P x,P (S.symm^[n] x))
  refine ⟨extend PF G WF ⊥,extend PB G WB ⊥,?_⟩
  intro x
  have hFx := hWF (key PF G x) x rfl
  have hBx := hWB (key PB G x) x rfl
  have eF := extend_key PF G WF (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) x
  have eB := extend_key PB G WB (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) x
  dsimp only [PF,PB] at eF eB hFx hBx ⊢
  rw [eF,eB]
  refine ⟨hFx.1,?_,hFx.2,?_⟩
  · simpa only [Finset.card_compl,Fintype.card_fin] using hBx.1
  · simpa only [BilateralGauge.reverse_forwardSpace,neg_neg] using hBx.2
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι C : Type*} [Fintype ι]

noncomputable def fastSet (v : Fin d → ℝ) (γ : ℝ) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun j => γ<v j)
noncomputable def slowSet (v : Fin d → ℝ) (γ : ℝ) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun j => v j≤γ)
lemma slowSet_eq_compl (v : Fin d → ℝ) (γ : ℝ) : slowSet v γ=(fastSet v γ)ᶜ := by
  classical
  ext j
  simp only [fastSet,slowSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl,not_lt]

/-- Simultaneous starting and two endpoint references derived from the ORIGINAL
bilateral good gauges. All choices are finite bin choices: the pointwise frames
and rate lists are never made into a measurable refinement. -/
theorem finite_references (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r₁ C₁ r₂ C₂ D r₃ C₃ D₃ r₄ C₄ D₄ : ℝ,
      0<r₁ ∧ 1≤C₁ ∧ 0<r₂ ∧ 1≤C₂ ∧ 1≤D ∧
      0<r₃ ∧ 1≤C₃ ∧ 1≤D₃ ∧ 0<r₄ ∧ 1≤C₄ ∧ 1≤D₄ ∧
      ∀ (c : M → ι) (P : M → C) (G : Set M) (n N : ℕ) (B R h g : ℝ)
        (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint x) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        C₁^N*h≤r₁ → C₂^N*h≤r₂ → C₃^N*h≤r₃ → C₄^N*h≤r₄ → 0≤h → 0<g →
        Real.exp (-2*g*N+4*(B+Real.log D))≤1/2 →
        (let δ := ((N:ℝ)*C₁*C₁^(2*N)+N*C₂*C₂^(2*N))*h
         δ<Real.exp (-2*(B+Real.log D))/2 ∧
         Real.exp (-2*g*N+4*(B+Real.log D))+
           δ*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))≤1/2) →
        (∀ j : Fin (d+1),let γ := (1+8*(j.val:ℝ))*g
          Real.exp ((γ-g)*N+2*(B+Real.log D₃))*
            (Real.exp ((-γ-g)*N+2*(B+Real.log D₃))+N*C₃*C₃^(2*N)*h)≤1/2) →
        (∀ j : Fin (d+1),let γ := (1+8*(j.val:ℝ))*g
          Real.exp ((-γ-g)*N+2*(B+Real.log D₄))*
            (Real.exp ((γ-g)*N+2*(B+Real.log D₄))+N*C₄*C₄^(2*N)*h)≤1/2) →
        ∃ j : C → Fin (d+1),
          let γ (q : C) := (1+8*((j q).val:ℝ))*g
          let T (x : G) := fastSet (A x).lam (γ (P x))
          let ε := Real.exp (-2*g*N+4*(B+Real.log D))+
            (((N:ℝ)*C₁*C₁^(2*N)+N*C₂*C₂^(2*N))*h)*
              Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))
          ∃ Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d)),
            (∀ x:G,∀ i∈(T x)ᶜ,(A x).lam i≤γ (P x)-g) ∧
            (∀ x:G,∀ i∈T x,γ (P x)+g≤(A x).lam i) ∧
            (∀ x y:G,P x=P y → (T x).card=(T y).card) ∧
            (∀ x:G,let y : G := (reference P G (key P G x)).val
              ‖(((A x).forward I S a c).space (T x)ᶜ).starProjection-
                (((A y).forward I S a c).space (T y)ᶜ).starProjection‖≤3*ε ∧
              ‖(((A x).forward I S a c).space (T x)).starProjection-
                (((A y).forward I S a c).space (T y)).starProjection‖≤3*ε) ∧
            ∀ x:G,
              Module.finrank ℝ (Wf (P x,P (S^[n] x)))=(T x).card ∧
              Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-(T x).card ∧
              ‖((A x).forwardSpace I S a c n (T x)).starProjection-
                (Wf (P x,P (S^[n] x))).starProjection‖≤
                  3*(Real.exp ((γ (P x)-g)*N+2*(B+Real.log D₃))*
                    (Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D₃))+N*C₃*C₃^(2*N)*h)) ∧
              ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
                (Wb (P x,P (S.symm^[n] x))).starProjection‖≤
                  3*(Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D₄))*
                    (Real.exp ((γ (P x)-g)*N+2*(B+Real.log D₄))+N*C₄*C₄^(2*N)*h)) := by
  classical
  obtain ⟨r₁,C₁,r₂,C₂,D,hr₁,hC₁,hr₂,hC₂,hD,hs⟩ :=
    finite_starting_references (C:=C) I hclosed S a K hK hKU
  obtain ⟨r₃,C₃,D₃,r₄,C₄,D₄,hr₃,hC₃,hD₃,hr₄,hC₄,hD₄,he⟩ :=
    bilateral_endpoint_references (C:=C) I hclosed S a K hK hKU
  refine ⟨r₁,C₁,r₂,C₂,D,r₃,C₃,D₃,r₄,C₄,D₄,
    hr₁,hC₁,hr₂,hC₂,hD,hr₃,hC₃,hD₃,hr₄,hC₄,hD₄,?_⟩
  intro c P G n N B R h g A hc hN hco hint hdiam ht₁ ht₂ ht₃ ht₄ hh hg hd hsml hfml hbml
  obtain ⟨j₀,hj₀⟩ := hs c P G n N B R h g A hc hN hco hint hdiam ht₁ ht₂ hg hd hsml
  let j := FiniteBins.extend P G j₀ (0 : Fin (d+1))
  let γ (q : C) := (1+8*((j q).val:ℝ))*g
  let T (x : G) := fastSet (A x).lam (γ (P x))
  have hj (x : G) : j (P x)=j₀ (key P G x) := extend_key P G j₀ _ x
  have hgap (x : G) (i : Fin d) : (A x).lam i<γ (P x)-g ∨ γ (P x)+g<(A x).lam i := by
    have hh := (hj₀ (key P G x) x rfl).1 i
    simpa only [γ,hj] using hh
  have hsc (x : G) (i : Fin d) (hi : i∈(T x)ᶜ) : (A x).lam i≤γ (P x)-g := by
    have hl : (A x).lam i≤γ (P x) := by simpa only [T,fastSet,Finset.mem_compl,Finset.mem_filter,
      Finset.mem_univ,true_and,not_lt] using hi
    rcases hgap x i with hi | hi
    · exact hi.le
    · linarith
  have hfc (x : G) (i : Fin d) (hi : i∈T x) : γ (P x)+g≤(A x).lam i := by
    have hl : γ (P x)<(A x).lam i := by simpa only [T,fastSet,Finset.mem_filter,
      Finset.mem_univ,true_and] using hi
    rcases hgap x i with hi | hi
    · linarith
    · exact hi.le
  have hcard (x y : G) (hxy : P x=P y) : (T x).card=(T y).card := by
    have hx := (hj₀ (key P G x) x rfl).2.1
    have hy := (hj₀ (key P G x) y hxy.symm).2.1
    dsimp only [T,fastSet,γ]
    rw [←hxy,hj x]
    exact hx.trans hy.symm
  have hi (F : Diffeomorph I I M M ∞) (x : M) (hx : I.IsInteriorPoint x) (t : ℕ) :
      I.IsInteriorPoint (F^[t] x) := by
    induction t with
    | zero => exact hx
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ((F.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp ih
  obtain ⟨Wf,Wb,hW⟩ := he c P G n N B R h g γ T A hc hN hco
    (fun x hx => ⟨hi S x (hint x hx) n,hi S.symm x (hint x hx) n⟩)
    hdiam ht₃ ht₄ hh hcard hsc hfc (fun q => hfml (j q)) (fun q => hbml (j q))
  refine ⟨j,Wf,Wb,hsc,hfc,hcard,?_,hW⟩
  intro x y
  have hy : P y=P x := (reference P G (key P G x)).property
  have hxs := (hj₀ (key P G x) x rfl).2.2
  dsimp only [T]
  rw [←slowSet_eq_compl,←slowSet_eq_compl]
  simpa only [γ,hy,hj x,slowSet,fastSet] using hxs
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
theorem finite_starting_references_uniform (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ rF CF rB CB D : ℝ,0<rF ∧ 1≤CF ∧ 0<rB ∧ 1≤CB ∧ 1≤D ∧
      ∀ (C : Type*) (c : M → ι) (P : M → C) (G : Set M)
        (n N : ℕ) (B R h g : ℝ) (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint x) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        CF^N*h≤rF → CB^N*h≤rB → 0<g →
        Real.exp (-2*g*N+4*(B+Real.log D))≤1/2 →
        (let δ := ((N:ℝ)*CF*CF^(2*N)+N*CB*CB^(2*N))*h
         δ<Real.exp (-2*(B+Real.log D))/2 ∧
         Real.exp (-2*g*N+4*(B+Real.log D))+
           δ*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))≤1/2) →
        ∃ j : Active P G → Fin (d+1),∀ Q : Active P G,
          let x₀ : G := (reference P G Q).val
          let γ := (1+8*((j Q).val:ℝ))*g
          let ε := Real.exp (-2*g*N+4*(B+Real.log D))+
            (((N:ℝ)*CF*CF^(2*N)+N*CB*CB^(2*N))*h)*
              Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))
          ∀ x:G,P x=Q.val →
            (∀ k,(A x).lam k<γ-g ∨ γ+g<(A x).lam k) ∧
            (Finset.univ.filter (fun k => γ<(A x).lam k)).card=
              (Finset.univ.filter (fun k => γ<(A x₀).lam k)).card ∧
            ‖(((A x).forward I S a c).space (Finset.univ.filter (fun k => (A x).lam k≤γ))).starProjection-
              (((A x₀).forward I S a c).space (Finset.univ.filter (fun k => (A x₀).lam k≤γ))).starProjection‖≤3*ε ∧
            ‖(((A x).forward I S a c).space (Finset.univ.filter (fun k => γ<(A x).lam k))).starProjection-
              (((A x₀).forward I S a c).space (Finset.univ.filter (fun k => γ<(A x₀).lam k))).starProjection‖≤3*ε := by
  classical
  obtain ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,hh⟩ :=
    uniform_genuine_bin_splitting I hclosed S a K hK hKU
  refine ⟨rF,CF,rB,CB,D,hrF,hCF,hrB,hCB,hD,?_⟩
  intro C c P G n N B R h g A hc hN hco hint hdiam hsF hsB hg hdec hsmall
  have hex (Q : Active P G) := hh c (Fiber P G Q) (fun x => x.val.val)
    (reference P G Q) n N B R h g (fun x => A x.val) hc hN
    (fun x => hco _ _ (x.property.trans (reference P G Q).property.symm))
    (fun x => hint _ x.val.property)
    (fun x => hdiam _ _ (x.property.trans (reference P G Q).property.symm))
    hsF hsB hg hdec hsmall.1 hsmall.2
  choose j hj using hex
  refine ⟨j,?_⟩
  intro Q x₀ γ ε x hx
  have hgx := (hj Q).1 (⟨x,hx⟩ : Fiber P G Q)
  exact ⟨hgx.1,hgx.2,(hj Q).2.1 ⟨x,hx⟩,(hj Q).2.2 ⟨x,hx⟩⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
theorem finite_endpoint_references_uniform (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C₁ D : ℝ,0<r ∧ 1≤C₁ ∧ 1≤D ∧
      ∀ (C : Type*) (c : M → ι) (P : M → C) (G : Set M) (n N : ℕ) (B R h g : ℝ)
        (γ : C → ℝ) (T : G → Finset (Fin d))
        (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint (S^[n] x)) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        C₁^N*h≤r → 0≤h →
        (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (∀ q : C,let ε := Real.exp ((γ q-g)*N+2*(B+Real.log D))*
          (Real.exp ((-γ q-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)
          ε≤1/2) →
        let EKey := fun x => (P x,P (S^[n] x))
        ∃ W : Active EKey G → Submodule ℝ (EuclideanSpace ℝ (Fin d)),
          ∀ Q : Active EKey G,∀ x:G,EKey x=Q.val →
            Module.finrank ℝ (W Q)=(T x).card ∧
            ‖((A x).forwardSpace I S a c n (T x)).starProjection-(W Q).starProjection‖≤
              3*(Real.exp ((γ (P x)-g)*N+2*(B+Real.log D))*
                (Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D))+N*C₁*C₁^(2*N)*h)) := by
  classical
  obtain ⟨r,C₁,D,hr,hC,hD,hh⟩ := uniform_original_endpoint_fast_comparison I hclosed S a K hK hKU
  refine ⟨r,C₁,D,hr,hC,hD,?_⟩
  intro C c P G n N B R h g γ T A hc hN hco hint hdiam ht hn hdim hslow hfast hsmall EKey
  let ref (Q : Active EKey G) : G := (reference EKey G Q).val
  let W (Q : Active EKey G) := (A (ref Q)).forwardSpace I S a c n (T (ref Q))
  refine ⟨W,?_⟩
  intro Q x hx
  have hp (y : Fiber EKey G Q) : EKey y.val=EKey (ref Q) :=
    y.property.trans (reference EKey G Q).property.symm
  have hq (y : Fiber EKey G Q) : P y.val=P (ref Q) := congrArg Prod.fst (hp y)
  have hend (y : Fiber EKey G Q) : P (S^[n] y.val.val)=P (S^[n] (ref Q).val) :=
    congrArg Prod.snd (hp y)
  have he : P x=P (ref Q) := hq ⟨x,hx⟩
  constructor
  · exact (EuclideanSplitting.finrank_groupSpace ((A (ref Q)).UF n)
      ((A (ref Q)).VF n) ((A (ref Q)).invF n).1 ((A (ref Q)).invF n).2
      (T (ref Q))).trans (hdim _ _ he.symm)
  · have hb := hh c (Fiber EKey G Q) (fun y => y.val.val) (reference EKey G Q)
      n N B R h (γ (P (ref Q))) g (fun y => T y.val) (fun y => A y.val)
      hc hN (fun y => hco _ _ (hend y)) (fun y => hint _ y.val.property)
      (fun y => hdiam _ _ (hend y)) ht hn (fun y => hdim _ _ (hq y).symm)
      (fun y j hj => by simpa only [←hq y] using hslow y.val j hj)
      (fun y j hj => by simpa only [←hq y] using hfast y.val j hj)
      (hsmall (P (ref Q))) (⟨x,hx⟩ : Fiber EKey G Q)
    simpa only [W,ref,he] using hb
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
theorem bilateral_endpoint_references_uniform (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ rF CF DF rB CB DB : ℝ,0<rF ∧ 1≤CF ∧ 1≤DF ∧ 0<rB ∧ 1≤CB ∧ 1≤DB ∧
      ∀ (C : Type*) (c : M → ι) (P : M → C) (G : Set M) (n N : ℕ) (B R h g : ℝ)
        (γ : C → ℝ) (T : G → Finset (Fin d))
        (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint (S^[n] x) ∧ I.IsInteriorPoint (S.symm^[n] x)) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        CF^N*h≤rF → CB^N*h≤rB → 0≤h →
        (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (∀ q : C,Real.exp ((γ q-g)*N+2*(B+Real.log DF))*
          (Real.exp ((-γ q-g)*N+2*(B+Real.log DF))+N*CF*CF^(2*N)*h)≤1/2) →
        (∀ q : C,Real.exp ((-γ q-g)*N+2*(B+Real.log DB))*
          (Real.exp ((γ q-g)*N+2*(B+Real.log DB))+N*CB*CB^(2*N)*h)≤1/2) →
        ∃ Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d)),∀ x:G,
          Module.finrank ℝ (Wf (P x,P (S^[n] x)))=(T x).card ∧
          Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-(T x).card ∧
          ‖((A x).forwardSpace I S a c n (T x)).starProjection-
            (Wf (P x,P (S^[n] x))).starProjection‖≤
              3*(Real.exp ((γ (P x)-g)*N+2*(B+Real.log DF))*
                (Real.exp ((-γ (P x)-g)*N+2*(B+Real.log DF))+N*CF*CF^(2*N)*h)) ∧
          ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n] x))).starProjection‖≤
              3*(Real.exp ((-γ (P x)-g)*N+2*(B+Real.log DB))*
                (Real.exp ((γ (P x)-g)*N+2*(B+Real.log DB))+N*CB*CB^(2*N)*h)) := by
  classical
  obtain ⟨rF,CF,DF,hrF,hCF,hDF,hF⟩ := finite_endpoint_references_uniform I hclosed S a K hK hKU
  obtain ⟨rB,CB,DB,hrB,hCB,hDB,hB⟩ := finite_endpoint_references_uniform I hclosed S.symm a K hK hKU
  refine ⟨rF,CF,DF,rB,CB,DB,hrF,hCF,hDF,hrB,hCB,hDB,?_⟩
  intro C c P G n N B R h g γ T A hc hN hco hint hdiam htF htB hh hcard hslow hfast hsmallF hsmallB
  obtain ⟨WF,hWF⟩ := hF C c P G n N B R h g γ T A hc hN hco
    (fun x hx => (hint x hx).1) hdiam htF hh hcard hslow hfast hsmallF
  have hcardB (x y : G) (hxy : P x=P y) : (T x)ᶜ.card=(T y)ᶜ.card := by
    simp only [Finset.card_compl,Fintype.card_fin,hcard x y hxy]
  have hsB (x : G) (j : Fin d) (hj : j∈((T x)ᶜ)ᶜ) :
      -((A x).lam j)≤(-γ (P x))-g := by
    simp only [compl_compl] at hj
    linarith [hfast x j hj]
  have hfB (x : G) (j : Fin d) (hj : j∈(T x)ᶜ) :
      (-γ (P x))+g≤-((A x).lam j) := by linarith [hslow x j hj]
  obtain ⟨WB,hWB⟩ := hB C c P G n N B R h g (fun q => -γ q) (fun x => (T x)ᶜ)
    (fun x => (A x).reverse I S a c) hc hN hco (fun x hx => (hint x hx).2)
    hdiam htB hh hcardB hsB hfB (by simpa only [neg_neg] using hsmallB)
  let PF (x : M) := (P x,P (S^[n] x))
  let PB (x : M) := (P x,P (S.symm^[n] x))
  refine ⟨extend PF G WF ⊥,extend PB G WB ⊥,?_⟩
  intro x
  have hFx := hWF (key PF G x) x rfl
  have hBx := hWB (key PB G x) x rfl
  have eF := extend_key PF G WF (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) x
  have eB := extend_key PB G WB (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) x
  dsimp only [PF,PB] at eF eB hFx hBx ⊢
  rw [eF,eB]
  refine ⟨hFx.1,?_,hFx.2,?_⟩
  · simpa only [Finset.card_compl,Fintype.card_fin] using hBx.1
  · simpa only [BilateralGauge.reverse_forwardSpace,neg_neg] using hBx.2
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
theorem finite_references_uniform (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r₁ C₁ r₂ C₂ D r₃ C₃ D₃ r₄ C₄ D₄ : ℝ,
      0<r₁ ∧ 1≤C₁ ∧ 0<r₂ ∧ 1≤C₂ ∧ 1≤D ∧
      0<r₃ ∧ 1≤C₃ ∧ 1≤D₃ ∧ 0<r₄ ∧ 1≤C₄ ∧ 1≤D₄ ∧
      ∀ (C : Type*) (c : M → ι) (P : M → C) (G : Set M) (n N : ℕ) (B R h g : ℝ)
        (A : ∀ x:G,BilateralGauge I S a c n B R x),
        (∀ y,y∈K (c y)) → N≤n →
        (∀ x y,P x=P y → c x=c y) →
        (∀ x∈G,I.IsInteriorPoint x) →
        (∀ x y,P x=P y → ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h) →
        C₁^N*h≤r₁ → C₂^N*h≤r₂ → C₃^N*h≤r₃ → C₄^N*h≤r₄ → 0≤h → 0<g →
        Real.exp (-2*g*N+4*(B+Real.log D))≤1/2 →
        (let δ := ((N:ℝ)*C₁*C₁^(2*N)+N*C₂*C₂^(2*N))*h
         δ<Real.exp (-2*(B+Real.log D))/2 ∧
         Real.exp (-2*g*N+4*(B+Real.log D))+
           δ*Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))≤1/2) →
        (∀ j : Fin (d+1),let γ := (1+8*(j.val:ℝ))*g
          Real.exp ((γ-g)*N+2*(B+Real.log D₃))*
            (Real.exp ((-γ-g)*N+2*(B+Real.log D₃))+N*C₃*C₃^(2*N)*h)≤1/2) →
        (∀ j : Fin (d+1),let γ := (1+8*(j.val:ℝ))*g
          Real.exp ((-γ-g)*N+2*(B+Real.log D₄))*
            (Real.exp ((γ-g)*N+2*(B+Real.log D₄))+N*C₄*C₄^(2*N)*h)≤1/2) →
        ∃ j : C → Fin (d+1),
          let γ (q : C) := (1+8*((j q).val:ℝ))*g
          let T (x : G) := fastSet (A x).lam (γ (P x))
          let ε := Real.exp (-2*g*N+4*(B+Real.log D))+
            (((N:ℝ)*C₁*C₁^(2*N)+N*C₂*C₂^(2*N))*h)*
              Real.exp ((1+8*(d:ℝ))*g*N+2*(B+Real.log D))
          ∃ Wf Wb : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d)),
            (∀ x:G,∀ i∈(T x)ᶜ,(A x).lam i≤γ (P x)-g) ∧
            (∀ x:G,∀ i∈T x,γ (P x)+g≤(A x).lam i) ∧
            (∀ x y:G,P x=P y → (T x).card=(T y).card) ∧
            (∀ x:G,let y : G := (reference P G (key P G x)).val
              ‖(((A x).forward I S a c).space (T x)ᶜ).starProjection-
                (((A y).forward I S a c).space (T y)ᶜ).starProjection‖≤3*ε ∧
              ‖(((A x).forward I S a c).space (T x)).starProjection-
                (((A y).forward I S a c).space (T y)).starProjection‖≤3*ε) ∧
            ∀ x:G,
              Module.finrank ℝ (Wf (P x,P (S^[n] x)))=(T x).card ∧
              Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-(T x).card ∧
              ‖((A x).forwardSpace I S a c n (T x)).starProjection-
                (Wf (P x,P (S^[n] x))).starProjection‖≤
                  3*(Real.exp ((γ (P x)-g)*N+2*(B+Real.log D₃))*
                    (Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D₃))+N*C₃*C₃^(2*N)*h)) ∧
              ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
                (Wb (P x,P (S.symm^[n] x))).starProjection‖≤
                  3*(Real.exp ((-γ (P x)-g)*N+2*(B+Real.log D₄))*
                    (Real.exp ((γ (P x)-g)*N+2*(B+Real.log D₄))+N*C₄*C₄^(2*N)*h)) := by
  classical
  obtain ⟨r₁,C₁,r₂,C₂,D,hr₁,hC₁,hr₂,hC₂,hD,hs⟩ :=
    finite_starting_references_uniform I hclosed S a K hK hKU
  obtain ⟨r₃,C₃,D₃,r₄,C₄,D₄,hr₃,hC₃,hD₃,hr₄,hC₄,hD₄,he⟩ :=
    bilateral_endpoint_references_uniform I hclosed S a K hK hKU
  refine ⟨r₁,C₁,r₂,C₂,D,r₃,C₃,D₃,r₄,C₄,D₄,
    hr₁,hC₁,hr₂,hC₂,hD,hr₃,hC₃,hD₃,hr₄,hC₄,hD₄,?_⟩
  intro C c P G n N B R h g A hc hN hco hint hdiam ht₁ ht₂ ht₃ ht₄ hh hg hd hsml hfml hbml
  obtain ⟨j₀,hj₀⟩ := hs C c P G n N B R h g A hc hN hco hint hdiam ht₁ ht₂ hg hd hsml
  let j := FiniteBins.extend P G j₀ (0 : Fin (d+1))
  let γ (q : C) := (1+8*((j q).val:ℝ))*g
  let T (x : G) := fastSet (A x).lam (γ (P x))
  have hj (x : G) : j (P x)=j₀ (key P G x) := extend_key P G j₀ _ x
  have hgap (x : G) (i : Fin d) : (A x).lam i<γ (P x)-g ∨ γ (P x)+g<(A x).lam i := by
    have hh := (hj₀ (key P G x) x rfl).1 i
    simpa only [γ,hj] using hh
  have hsc (x : G) (i : Fin d) (hi : i∈(T x)ᶜ) : (A x).lam i≤γ (P x)-g := by
    have hl : (A x).lam i≤γ (P x) := by simpa only [T,fastSet,Finset.mem_compl,Finset.mem_filter,
      Finset.mem_univ,true_and,not_lt] using hi
    rcases hgap x i with hi | hi
    · exact hi.le
    · linarith
  have hfc (x : G) (i : Fin d) (hi : i∈T x) : γ (P x)+g≤(A x).lam i := by
    have hl : γ (P x)<(A x).lam i := by simpa only [T,fastSet,Finset.mem_filter,
      Finset.mem_univ,true_and] using hi
    rcases hgap x i with hi | hi
    · linarith
    · exact hi.le
  have hcard (x y : G) (hxy : P x=P y) : (T x).card=(T y).card := by
    have hx := (hj₀ (key P G x) x rfl).2.1
    have hy := (hj₀ (key P G x) y hxy.symm).2.1
    dsimp only [T,fastSet,γ]
    rw [←hxy,hj x]
    exact hx.trans hy.symm
  have hi (F : Diffeomorph I I M M ∞) (x : M) (hx : I.IsInteriorPoint x) (t : ℕ) :
      I.IsInteriorPoint (F^[t] x) := by
    induction t with
    | zero => exact hx
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ((F.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp ih
  obtain ⟨Wf,Wb,hW⟩ := he C c P G n N B R h g γ T A hc hN hco
    (fun x hx => ⟨hi S x (hint x hx) n,hi S.symm x (hint x hx) n⟩)
    hdiam ht₃ ht₄ hh hcard hsc hfc (fun q => hfml (j q)) (fun q => hbml (j q))
  refine ⟨j,Wf,Wb,hsc,hfc,hcard,?_,hW⟩
  intro x y
  have hy : P y=P x := (reference P G (key P G x)).property
  have hxs := (hj₀ (key P G x) x rfl).2.2
  dsimp only [T]
  rw [←slowSet_eq_compl,←slowSet_eq_compl]
  simpa only [γ,hy,hj x,slowSet,fastSet] using hxs
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- All the one-step tube/Taylor hypotheses used by the boundary-value
solver follow from actual one-step smoothness on the finite compact atlas.
The only variable-domain input is the literal avoidance of the boundary. -/
theorem actual_tube_data (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0<r ∧ 1≤C ∧ ∀ (i j : ι) (x : M) (δ : ℝ),
      x∈K i → S x∈K j → 0≤δ → δ≤r →
      closedBall ((extChartAt I (a i)) x) δ⊆interior (range I) →
      closedBall ((extChartAt I (a i)) x) δ⊆(extChartAt I (a i)).target ∧
      closedBall ((extChartAt I (a i)) x) δ⊆domainU I S (a i) (a j) ∧
      ∀ y∈closedBall ((extChartAt I (a i)) x) δ,
        ContDiffAt ℝ ∞ (localMap I S (a i) (a j)) y ∧
        ‖fderiv ℝ (localMap I S (a i) (a j)) y‖≤C ∧
        ‖fderiv ℝ (localMap I S (a i) (a j)) y-
          fderiv ℝ (localMap I S (a i) (a j)) ((extChartAt I (a i)) x)‖≤
            C*‖y-(extChartAt I (a i)) x‖ := by
  obtain ⟨r,C,hr,hC,hh⟩ := actual_uniform_c2 I hclosed S a K hK hKU
  refine ⟨r,C,hr,hC,fun i j x δ hx hSx hδ hδr hsafe => ?_⟩
  have hball := closedBall_subset_closedBall hδr (x:=(extChartAt I (a i)) x)
  have hdat := hh i j x hx hSx
  have hdom := hball.trans hdat.1
  refine ⟨?_,hdom,fun y hy => ?_⟩
  · intro y hy
    rw [extChartAt,OpenPartialHomeomorph.extend_target]
    exact ⟨(hdom hy).1,interior_subset (hsafe hy)⟩
  · have hyd := hdat.2 y (hball hy) (hsafe hy)
    refine ⟨hyd.1,hyd.2.1,?_⟩
    apply (convex_closedBall ((extChartAt I (a i)) x) δ).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
    · intro z hz
      exact ((hdat.2 z (hball hz) (hsafe hz)).1.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
    · intro z hz
      exact (hdat.2 z (hball hz) (hsafe hz)).2.2
    · exact mem_closedBall_self hδ
    · exact hy
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    {n : ℕ} {B R : ℝ} {x : M}
open FiniteGreen ShortBin

lemma BilateralGauge.forward_space (A : BilateralGauge I S a c n B R x)
    (T : Finset (Fin d)) :
    (A.forward I S a c).space T=A.forwardSpace I S a c 0 T := by
  simp only [Gauge.space,BilateralGauge.forward,BilateralGauge.forwardSpace,
    Gauge.ofFinite,Nat.zero_min]

lemma BilateralGauge.backward_space (A : BilateralGauge I S a c n B R x)
    (T : Finset (Fin d)) :
    (A.backward I S a c).space T=A.forwardSpace I S a c 0 T := by
  simp only [Gauge.space,BilateralGauge.backward,BilateralGauge.forwardSpace,
    Gauge.ofFinite,Nat.zero_min,A.centerU,A.centerV]

lemma BilateralGauge.forward_fast (A : BilateralGauge I S a c n B R x)
    (T : Finset (Fin d)) :
    (((A.forward I S a c).splitting T).fast n).range=
      A.forwardSpace I S a c n Tᶜ := by
  rw [Gauge.splitting,EuclideanSplitting.splitting_fast_range]
  simp only [BilateralGauge.forward,BilateralGauge.forwardSpace,Gauge.ofFinite,Nat.min_self]

lemma BilateralGauge.backward_fast (A : BilateralGauge I S a c n B R x)
    (T : Finset (Fin d)) :
    (((A.backward I S a c).splitting T).fast n).range=
      A.backwardSpace I S a c n Tᶜ := by
  rw [Gauge.splitting,EuclideanSplitting.splitting_fast_range]
  simp only [BilateralGauge.backward,BilateralGauge.backwardSpace,Gauge.ofFinite,Nat.min_self]

/-- An old tube tests the candidate in the original input's selected charts.
The candidate is not required to belong to the good set. -/
def originalTube (δ : ℝ) (x z : M) : Prop :=
  ∀ t : Fin (n+1),S^[t.val] z∈(chartAt H (a (c (S^[t.val] x)))).source ∧
    ‖(extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] z)-
      (extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)‖≤δ

/-- Fixed endpoint projection, still based on the old input's endpoint chart. -/
def originalEndpoint (V : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x z : M) : Prop :=
  V.starProjection ((extChartAt I (a (c (S^[n] x)))) (S^[n] z))=
    V.starProjection ((extChartAt I (a (c (S^[n] x)))) (S^[n] x))
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
open FiniteGreen ShortBin

private lemma projection_diff_iff (V : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d)) :
    V.orthogonalProjectionOnto (u-v)=0 ↔ V.starProjection u=V.starProjection v := by
  constructor
  · intro h
    have hh := congrArg Subtype.val h
    change V.starProjection (u-v)=0 at hh
    simpa only [map_sub,sub_eq_zero] using hh
  · intro h
    apply Subtype.ext
    change V.starProjection (u-v)=0
    simpa only [map_sub,sub_eq_zero] using h

/-- An actual two-sided joining. The uniform geometry is chosen BEFORE the
window, good gauges, cells, thresholds, or endpoint ranks. Every tube and Taylor
hypothesis is derived here from the source finite atlas; the only tube-domain
condition retained is the literal avoidance of the manifold boundary. -/
theorem original_gauged_join (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r₀ C : ℝ,0<r₀ ∧ 1≤C ∧
      ∀ (c : M → ι) (n : ℕ) (B R ε γ g α r δ : ℝ) (q x y : M)
        (A₀ : BilateralGauge I S a c n B R q)
        (Ax : BilateralGauge I S a c n B R x)
        (Ay : BilateralGauge I S a c n B R y)
        (T₀ Tx Ty : Finset (Fin d))
        (V W : Submodule ℝ (EuclideanSpace ℝ (Fin d))),
        (∀ v,v∈K (c v)) → c x=c y → I.IsInteriorPoint x → I.IsInteriorPoint y →
        Module.finrank ℝ (Ax.forwardSpace I S a c n Tx)=Module.finrank ℝ V →
        Module.finrank ℝ (Ay.backwardSpace I S a c n Tyᶜ)=Module.finrank ℝ W →
        ‖(Ax.forwardSpace I S a c n Tx).starProjection-V.starProjection‖≤1/2 →
        ‖(Ay.backwardSpace I S a c n Tyᶜ).starProjection-W.starProjection‖≤1/2 →
        0≤ε → ε≤1/2 → T₀.card=Tx.card → T₀.card=Ty.card →
        ‖(A₀.forwardSpace I S a c 0 T₀ᶜ).starProjection-
          (Ax.forwardSpace I S a c 0 Txᶜ).starProjection‖≤ε →
        ‖(A₀.forwardSpace I S a c 0 T₀).starProjection-
          (Ay.forwardSpace I S a c 0 Ty).starProjection‖≤ε →
        Real.exp (2*B)*(2*ε)≤1/2 →
        (∀ j∈Txᶜ,Ax.lam j≤γ-g) → (∀ j∈Tx,γ+g≤Ax.lam j) →
        (∀ j∈Tyᶜ,Ay.lam j≤γ-g) → (∀ j∈Ty,γ+g≤Ay.lam j) →
        (2*Real.exp (2*B))*(2*(2*Real.exp (2*B)^2*Real.exp (-2*g*n)))≤1/2 →
        |γ|+|g|≤α → 0≤r → 0<δ → δ≤r₀ →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆
          interior (range I)) →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) δ⊆
          interior (range I)) →
        ‖(extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x‖≤C*r →
        bvpInverseBound B α n*C*δ≤1/4 → bvpInverseBound B α n*C*r≤δ/4 →
        ∃ z : M,
          originalTube I S a c (n:=n) (δ/2) x z ∧
          originalTube I S.symm a c (n:=n) (δ/2) y z ∧
          originalEndpoint I S a c (n:=n) V x z ∧
          originalEndpoint I S.symm a c (n:=n) W y z ∧
          originalTube I S a c (n:=n) (2*C*bvpInverseBound B α n*r) x z ∧
          originalTube I S.symm a c (n:=n) (2*C*bvpInverseBound B α n*r) y z ∧
          ‖(extChartAt I (a (c x))) z-(extChartAt I (a (c x))) x-
            ((A₀.forward I S a c).splitting T₀ᶜ).slow 0
              ((extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x)‖≤
            4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C*r)+
              bvpInverseBound B α n*C*(2*C*bvpInverseBound B α n*r)^2 ∧
          ∀ z' : M,originalTube I S a c (n:=n) δ x z' →
            originalTube I S.symm a c (n:=n) δ y z' →
            originalEndpoint I S a c (n:=n) V x z' →
            originalEndpoint I S.symm a c (n:=n) W y z' → z'=z := by
  obtain ⟨rF,CF,hrF,hCF,hF⟩ := actual_tube_data I hclosed S a K hK hKU
  obtain ⟨rB,CB,hrB,hCB,hB⟩ := actual_tube_data I hclosed S.symm a K hK hKU
  let C := max CF CB
  have hFC : CF≤C := le_max_left _ _
  have hBC : CB≤C := le_max_right _ _
  have hC : 1≤C := hCF.trans hFC
  refine ⟨min rF rB,C,lt_min hrF hrB,hC,?_⟩
  intro c n B R ε γ g α r δ q x y A₀ Ax Ay T₀ Tx Ty V W hc hxy hix hiy
    hdV hdW hcV hcW hε hεhalf hdS hdT hcS hcT hsmall hsx hfx hsy hfy hgap hα hr hδ hδr
    hsafeF hsafeB hnear hcontract hdata
  let af : Fin (n+1) → M := fun t => a (c (S^[t.val] x))
  let ab : Fin (n+1) → M := fun t => a (c (S.symm^[t.val] y))
  have hgeomF (t : Fin (n+1)) := hF (c (S^[t.val] x)) (c (S (S^[t.val] x)))
    (S^[t.val] x) δ (hc _) (hc _) hδ.le (hδr.trans (min_le_left _ _)) (hsafeF t)
  have hgeomB (t : Fin (n+1)) := hB (c (S.symm^[t.val] y)) (c (S.symm (S.symm^[t.val] y)))
    (S.symm^[t.val] y) δ (hc _) (hc _) hδ.le (hδr.trans (min_le_right _ _)) (hsafeB t)
  have hstepF (t : Fin n) : (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S (af t.castSucc) (af t.succ) (S^[t.val] x))*(Ax.forward I S a c).U t=
        (Ax.forward I S a c).U (t+1)*EuclideanSplitting.rate (Ax.forward I S a c).lam 1 := by
    simpa only [af,Fin.val_castSucc,Fin.val_succ,BilateralGauge.forward,Gauge.ofFinite,
      Nat.min_eq_left t.isLt.le,Nat.min_eq_left (Nat.succ_le_of_lt t.isLt)] using Ax.stepF t t.isLt
  have hstepB (t : Fin n) : (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S.symm (ab t.castSucc) (ab t.succ) (S.symm^[t.val] y))*(Ay.backward I S a c).U t=
        (Ay.backward I S a c).U (t+1)*EuclideanSplitting.rate (Ay.backward I S a c).lam 1 := by
    simpa only [ab,Fin.val_castSucc,Fin.val_succ,BilateralGauge.backward,Gauge.ofFinite,
      Nat.min_eq_left t.isLt.le,Nat.min_eq_left (Nat.succ_le_of_lt t.isLt)] using Ay.stepB t t.isLt
  have hdV' : Module.finrank ℝ (((Ax.forward I S a c).splitting Txᶜ).fast n).range=
      Module.finrank ℝ V := by
    have he := Ax.forward_fast I S a c Txᶜ
    simp only [compl_compl] at he
    exact (congrArg (fun Z : Submodule ℝ (EuclideanSpace ℝ (Fin d)) => Module.finrank ℝ Z) he).trans hdV
  have hcV' : ‖(((Ax.forward I S a c).splitting Txᶜ).fast n).range.starProjection-
      V.starProjection‖≤1/2 := by simpa only [Ax.forward_fast,compl_compl] using hcV
  have hdW' : Module.finrank ℝ (((Ay.backward I S a c).splitting Ty).fast n).range=
      Module.finrank ℝ W := by
    exact (congrArg (fun Z : Submodule ℝ (EuclideanSpace ℝ (Fin d)) => Module.finrank ℝ Z)
      (Ay.backward_fast I S a c Ty)).trans hdW
  have hcW' : ‖(((Ay.backward I S a c).splitting Ty).fast n).range.starProjection-
      W.starProjection‖≤1/2 := by simpa only [Ay.backward_fast] using hcW
  have hjoin := gauged_join_ideal I S af ab x y
    (by simp only [af,ab,Fin.val_zero,Function.iterate_zero_apply,hxy])
    (fun t => hKU _ (hc _)) (fun t => hKU _ (hc _)) hix hiy
    (A₀.forward I S a c) (Ax.forward I S a c) (Ay.backward I S a c) T₀ᶜ Txᶜ Ty V W
    hdV' hdW' hcV' hcW' hε hεhalf
    (by simp only [Finset.card_compl,hdS]) (by simpa only [compl_compl] using hdT)
    (by simpa only [BilateralGauge.forward_space] using hcS)
    (by simpa only [BilateralGauge.forward_space,BilateralGauge.backward_space,compl_compl] using hcT)
    hsmall hsx (by simpa only [compl_compl,BilateralGauge.forward,Gauge.ofFinite] using hfx)
    (by intro j hj; change -Ay.lam j≤ -γ-g; linarith [hfy j hj])
    (by intro j hj; change -γ+g≤ -Ay.lam j; linarith [hsy j hj])
    hgap hα hstepF hstepB (show 0≤C by linarith) hr hδ
    (by intro t z hz; simpa only [af,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using ((hgeomF t.castSucc).2.2 z hz).1.differentiableAt (by simp))
    (by intro t z hz; simpa only [ab,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using ((hgeomB t.castSucc).2.2 z hz).1.differentiableAt (by simp))
    (by intro t z hz
        simpa only [af,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using
          (((hgeomF t.castSucc).2.2 z hz).2.2).trans (mul_le_mul_of_nonneg_right hFC (norm_nonneg _)))
    (by intro t z hz
        simpa only [ab,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using
          (((hgeomB t.castSucc).2.2 z hz).2.2).trans (mul_le_mul_of_nonneg_right hBC (norm_nonneg _)))
    (fun t => (hgeomF t).1) (fun t => (hgeomB t).1)
    (by intro t; simpa only [af,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using (hgeomF t.castSucc).2.1)
    (by intro t; simpa only [ab,Fin.val_castSucc,Fin.val_succ,Function.iterate_succ_apply'] using (hgeomB t.castSucc).2.1)
    (by simpa only [af,ab,Fin.val_zero,Function.iterate_zero_apply] using hnear) hcontract hdata
  obtain ⟨z,hzF,hzB,hzV,hzW,hsharpF,hsharpB,hideal,hunique⟩ := hjoin
  have hV (z' : M) :
      (((Ax.forward I S a c).splitting Txᶜ).terminalProjection n V hdV' hcV').P
        ((extChartAt I (af (Fin.last n))) (S^[n] z')-
          (extChartAt I (af (Fin.last n))) (S^[n] x))=0 ↔
      originalEndpoint I S a c (n:=n) V x z' := by
    exact projection_diff_iff V _ _
  have hW (z' : M) :
      (((Ay.backward I S a c).splitting Ty).terminalProjection n W hdW' hcW').P
        ((extChartAt I (ab (Fin.last n))) (S.symm^[n] z')-
          (extChartAt I (ab (Fin.last n))) (S.symm^[n] y))=0 ↔
      originalEndpoint I S.symm a c (n:=n) W y z' := by
    exact projection_diff_iff W _ _
  refine ⟨z,hzF,hzB,(hV z).mp hzV,(hW z).mp hzW,?_,?_,hideal,?_⟩
  · exact fun t => ⟨(hzF t).1,hsharpF t⟩
  · exact fun t => ⟨(hzB t).1,hsharpB t⟩
  · intro z' hzF' hzB' hzV' hzW'
    exact hunique z' hzF' hzB' ((hV z').mpr hzV') ((hW z').mpr hzW')
end SmoothObstruction.ManifoldCoordinates

end

end OAI
