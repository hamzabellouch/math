import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays05
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates
open ConstructedWordPlan.GlobalWordPlan
open AllLevelFactorization AllLevelFactorization.Factorization MeasureTheory
open ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
open Filter
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a) {ι : Fin D.targets→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : Fin D.targets→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j)
variable (Γ : ∀ t i,Subgroup (G t i)) (coord : ∀ e,Fin (q (D.owner e)))

 

def modelEval (t : Fin D.targets) (i : ι t) (u : Fin (q t)→ℤ) :
    C(Target D G n q c hsk A w hA Γ t,(G t i)⧸Γ t i) :=
  NonnormalCoset.map _ _
    {toFun:=fun f=>(f i).val (fun j=>(u j:ℝ)),map_one':=rfl,map_mul':=fun _ _=>rfl}
    ((PolynomialArrays.evaluate_continuous (c t i) (hsk t i) (A t i) (w t i) (hA t i) _).comp (continuous_apply i))
    (fun _ hf=>hf i u)

 

def modelRead {r : ℕ}
    (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (f : ∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ) :
    (t : Fin D.targets)→ℚ→Target D G n q c hsk A w hA Γ t × Slots D→Fin r→ℝ :=
  fun t a y col=>f t (formula t a y.2 col)
    (modelEval D G n q c hsk A w hA Γ t (formula t a y.2 col) 0 y.1)

omit [∀ t,Fintype (ι t)] in
lemma modelRead_continuous {r : ℕ} (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (f : ∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ) (t : Fin D.targets) (a : ℚ) (col : Fin r) :
    Continuous (fun y=>modelRead D G n q c hsk A w hA Γ formula f t a y col) := by
  apply continuous_prod_of_discrete_right.mpr
  intro v
  exact (f t (formula t a v col)).continuous.comp (modelEval D G n q c hsk A w hA Γ t (formula t a v col) 0).continuous

def FactorizedEmpirical (coord : ∀ e,Fin (q (D.owner e))) (s : ℕ) (P : ℕ→ℤ→Full G n q c hsk A w hA) (Z : ℕ→ℝ)
    (Obs : ℕ→∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ) : Prop :=
  ∃ d : RealCoordinates (Full G n q c hsk A w hA) (FullDim n q w),
  ∃ B : CoveredLattice d (FullLattice G n q c hsk A w hA Γ),
    SecondKind d ∧
    (∀ k f,f∈(FullFiltration G n q c hsk A w hA).level k ↔
      ∀ j,JointArrays.jointWeight (FlatN n) (FlatQ q) (FlatW w) j<k → d.coord f j=0) ∧
    (∀ f,IsRational d f → ∀ t (i : ι t) (u : Fin (q t)→ℤ),
      IsRational (c t i) ((f ⟨t,i⟩).val (fun j=>(u j:ℝ)))) ∧
    ∃ F : Factorization d B.small s (FullFiltration G n q c hsk A w hA) P Z,
    ∃ act : ∀ t,MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t),
      (∀ t (v : Shifts D),letI:=act t;Continuous (fun x : Target D G n q c hsk A w hA Γ t=>v • x)) ∧
      (∀ e x,letI:=act (D.owner e);
        unitShift D e • x = faceAction (G (D.owner e)) (n (D.owner e)) (q (D.owner e))
          (c (D.owner e)) (hsk (D.owner e)) (A (D.owner e)) (w (D.owner e)) (hA (D.owner e)) (Γ (D.owner e))
          (fun _ (_ : Fin 1)=>1) (coord e) 0 x) ∧
      letI : ∀ t,MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t):=act
      letI : MeasurableSpace ((Full G n q c hsk A w hA)⧸FullLattice G n q c hsk A w hA Γ):=borel _
      ∀ (r : ℕ) (hs : 1 ≤ s) (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
        (Fs Bs : Finset (Scale a)) (q₀ : ℕ) (_hq₀ : pivotModulus s r hs D Fs Bs∣q₀)
        (b : Scale a) (_hb : b∈Bs) (τ : ℝ) (_hτ : 0<τ),
      let π:=fun t z=>targetCoset G n q c hsk A w hA Γ (FullLattice G n q c hsk A w hA Γ) le_rfl t z
      let RN:=fun N=>modelRead D G n q c hsk A w hA Γ formula (Obs (F.state.subseq N))
      ∀ᶠ N in atTop, (((((pivotOptions s r hs D Fs).card : ℝ≥0)⁻¹/2) : ℝ≥0) : ℝ≥0∞) <
        (F.coveredEmpiricalPointLaw (FullLattice G n q c hsk A w hA Γ) N : Measure ((Full G n q c hsk A w hA)⧸FullLattice G n q c hsk A w hA Γ))
          (⋃ p∈pivotOptions s r hs D Fs,AlignmentMass.Success τ
            (centerReading D (Target D G n q c hsk A w hA Γ) π (RN N) Fs q₀ b p)
            (translatedReading D (Target D G n q c hsk A w hA Γ) π (RN N) Fs q₀ b p))

 

theorem factorized_empirical
    (s : ℕ) (P : ℕ→ℤ→Full G n q c hsk A w hA) (Z : ℕ→ℝ)
    (hh : FactorizedPhysical D G n q c hsk A w hA Γ coord s P Z)
    (hZ : ∀ N,0<Z N) (hZT : Nonempty (Fin D.targets)→Tendsto Z atTop atTop)
    (Obs : ℕ→∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ) (f : ∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ)
    (he : ∀ η : ℝ,0<η →∀ᶠ N in atTop,∀ t i y,|Obs N t i y-f t i y|<η) :
    FactorizedEmpirical D G n q c hsk A w hA Γ coord s P Z Obs
 := by
  classical
  obtain ⟨d,B,hd,hfil,hrational,F,act,hcont,hunit,hphysical⟩:=hh
  refine ⟨d,B,hd,hfil,hrational,F,act,hcont,hunit,?_⟩
  let : ∀ t,MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t):=act
  let J:=Full G n q c hsk A w hA
  let Λ:=FullLattice G n q c hsk A w hA Γ
  let : T2Space J:=d.coord.symm.t2Space
  let : SecondCountableTopology J:=d.coord.secondCountableTopology
  let : DiscreteTopology Λ:=B.discrete
  let : IsClosed (Λ : Set J):=Λ.isClosed_of_discreteTopology
  let : T2Space (J⧸Λ):=inferInstance
  let : MeasurableSpace (J⧸Λ):=borel _
  let : BorelSpace (J⧸Λ):=⟨rfl⟩
  let : T2Space (J⧸B.small):=coordinate_quotient_t2 d B.small B.integer
  let : T1Space (J⧸B.small):=T2Space.t1Space
  let : CompactSpace (J⧸B.small):=AbelianMalcevTorus.quotient_compact d B.small B.integer
  let : MeasurableSpace (J⧸B.small):=borel _
  let : BorelSpace (J⧸B.small):=⟨rfl⟩
  let : TopologicalSpace.MetrizableSpace (J⧸B.small):=coordinate_quotient_metrizable d B.small B.integer
  let : SecondCountableTopology (J⧸B.small):=inferInstance
  let : HasOuterApproxClosed (J⧸B.small):=inferInstance
  let : MeasurableSingletonClass (J⧸B.small):=⟨fun _=>isClosed_singleton.measurableSet⟩
  let : MeasurableSingletonClass (J⧸Λ):=⟨fun _=>isClosed_singleton.measurableSet⟩
  let C:=F.residueCover B.integer
  let : ∀ r,MeasurableSpace ((C r).CubeSpace (ι:=Empty)):=fun _=>borel _
  let : ∀ r,BorelSpace ((C r).CubeSpace (ι:=Empty)):=fun _=>⟨rfl⟩
  intro r hs formula Fs Bs q₀ hq₀ b hb τ hτ
  dsimp only
  let Y:=Target D G n q c hsk A w hA Γ
  let π:=fun t z=>targetCoset G n q c hsk A w hA Γ Λ le_rfl t z
  let R:=modelRead D G n q c hsk A w hA Γ formula f
  let RN:=fun N=>modelRead D G n q c hsk A w hA Γ formula (Obs (F.state.subseq N))
  have hproj : (fun t (z : J⧸B.small)=>π t (CosetCover.map B.small Λ B.le z))=
      (fun t=>(targetCoset G n q c hsk A w hA Γ B.small B.le t : (J⧸B.small)→Y t)) := by
    funext t z
    induction z using Quotient.inductionOn with | h g=>rfl
  by_cases hn : Nonempty (Fin D.targets)
  · apply F.actual_lattice_pivot_empirical_success_mass C Λ B.le hs D Fs Bs q₀ hq₀ b hb hτ
      Y π R (fun t=>(targetCoset G n q c hsk A w hA Γ Λ le_rfl t).continuous)
      (modelRead_continuous D G n q c hsk A w hA Γ formula f) hcont
      (fun r β=>by rw [hproj];exact Classical.choice (hphysical r (C r) β)) hZ (hZT hn) RN
    have he' := F.state.strictmono.tendsto_atTop.eventually (he (τ/4) (by positivity))
    filter_upwards [he'] with N hN
    intro p hp i x
    constructor
    · exact (hN _ _ _).le
    · exact (hN _ _ _).le
  · let : IsEmpty (Fin D.targets):=not_nonempty_iff.mp hn
    have hempty : IsEmpty (Comparison D Fs r) := inferInstance
    have hS (N : ℕ) :
        (⋃ p∈pivotOptions s r hs D Fs,AlignmentMass.Success τ
          (centerReading D Y π (RN N) Fs q₀ b p)
          (translatedReading D Y π (RN N) Fs q₀ b p))=Set.univ := by
      ext x
      simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
      obtain ⟨p,hp⟩:=pivotOptions_nonempty s r hs D Fs
      exact ⟨p,hp,fun i=>isEmptyElim i⟩
    have hcard : (1:ℝ≥0)≤((pivotOptions s r hs D Fs).card:ℝ≥0) := by
      exact_mod_cast (pivotOptions_nonempty s r hs D Fs).card_pos
    have hbnd : (((((pivotOptions s r hs D Fs).card : ℝ≥0)⁻¹/2) : ℝ≥0) : ℝ≥0∞)<1 := by
      exact_mod_cast lt_of_le_of_lt (div_le_div_of_nonneg_right (inv_le_one_of_one_le₀ hcard) (by norm_num)) (by norm_num : (1:ℝ≥0)/2<1)
    exact Filter.Eventually.of_forall (fun N=>by rw [hS N];simpa using hbnd)

end SourceIntegerArrays.GlobalJoint
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates
open ConstructedWordPlan.GlobalWordPlan
open AllLevelFactorization AllLevelFactorization.Factorization MeasureTheory
open ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
open Filter
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a) {ι : Fin D.targets→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : Fin D.targets→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j)
variable (Γ : ∀ t i,Subgroup (G t i)) (coord : ∀ e,Fin (q (D.owner e)))

 

def ownBasis (t : Fin D.targets) (e : Fin D.pairs) : Fin (q t)→ℤ :=
  if h : D.owner e=t then h ▸ (Pi.single (coord e) 1) else 0

def ownInput (t : Fin D.targets) (v : Slots D) : Fin (q t)→ℤ :=
  ∑ e,v e • ownBasis D q coord t e

private def inputHom (t : Fin D.targets) : Shifts D →* Multiplicative (Fin (q t)→ℤ) where
  toFun v:=Multiplicative.ofAdd (ownInput D q coord t v.toAdd)
  map_one':=by simp [ownInput]
  map_mul' v z:=by
    change ownInput D q coord t (v.toAdd+z.toAdd)=ownInput D q coord t v.toAdd+ownInput D q coord t z.toAdd
    simp [ownInput,add_smul,Finset.sum_add_distrib]

private lemma inputHom_unit (e : Fin D.pairs) :
    inputHom D q coord (D.owner e) (unitShift D e)=Multiplicative.ofAdd (Pi.single (coord e) 1) := by
  classical
  change ∑ f,(Pi.single e (1:ℤ) : Slots D) f • ownBasis D q coord (D.owner e) f= (Pi.single (coord e) 1 : Fin (q (D.owner e))→ℤ)
  rw [Finset.sum_eq_single e]
  · simp [ownBasis]
  · intro f _ hfe
    simp [Pi.single_eq_of_ne hfe]
  · simp

@[instance_reducible]
private def inputAction {X : Type*} (k : ℕ) :
    MulAction (Multiplicative (Fin k→ℤ)) ((Fin k→ℤ)→X) where
  smul v f:=fun u=>f (u+v.toAdd)
  one_smul f:=by funext u;change f (u+0)=f u;rw [add_zero]
  mul_smul v z f:=by funext u;change f (u+(v.toAdd+z.toAdd))=f ((u+v.toAdd)+z.toAdd);rw [add_assoc]

omit [∀ t,Fintype (ι t)] in
private lemma eval_face (t : Fin D.targets) (e : Fin (q t)) (i : ι t)
    (u : Fin (q t)→ℤ) (x : Target D G n q c hsk A w hA Γ t) :
    modelEval D G n q c hsk A w hA Γ t i u
      (faceAction (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
        (fun _ (_ : Fin 1)=>1) e 0 x)=
      modelEval D G n q c hsk A w hA Γ t i (u+Pi.single e 1) x := by
  classical
  induction x using Quotient.inductionOn with | h f =>
    apply congrArg QuotientGroup.mk
    change (f i).val ((fun j=>(u j:ℝ))+(fun j=>((Pi.single e (1:ℤ) : Fin (q t)→ℤ) j:ℝ)))=(f i).val (fun j=>((u+Pi.single e 1 : Fin (q t)→ℤ) j:ℝ))
    apply congrArg (f i).val
    funext j
    by_cases he : j=e
    · subst j;simp
    · simp [Pi.single_eq_of_ne he]

omit [∀ t,Fintype (ι t)] in
private lemma eval_terminal
    [act : ∀ t,MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t)]
    (hunit : ∀ e x,
      unitShift D e • x = faceAction (G (D.owner e)) (n (D.owner e)) (q (D.owner e))
        (c (D.owner e)) (hsk (D.owner e)) (A (D.owner e)) (w (D.owner e)) (hA (D.owner e)) (Γ (D.owner e))
        (fun _ (_ : Fin 1)=>1) (coord e) 0 x)
    (t : Fin D.targets) (i : ι t) (q₀ : ℕ) (b : Scale a)
    (U : Finset (Fin D.pairs)) (hU : ∀ e∈U,D.owner e=t)
    (x : Target D G n q c hsk A w hA Γ t) :
    modelEval D G n q c hsk A w hA Γ t i 0 (terminalShift D q₀ b U • x)=
      modelEval D G n q c hsk A w hA Γ t i
        (ownInput D q coord t (terminalShift D q₀ b U).toAdd) x := by
  let := inputAction (X:=(G t i)⧸Γ t i) (q t)
  let π : Target D G n q c hsk A w hA Γ t → ((Fin (q t)→ℤ)→(G t i)⧸Γ t i):=
    fun x u=>modelEval D G n q c hsk A w hA Γ t i u x
  have he:=OwnTerminal.terminal_projection D π (unitShift D)
    (fun e=>inputHom D q coord t (unitShift D e)) t (fun e he x=>by
      subst t
      rw [inputHom_unit,hunit]
      funext u
      exact eval_face D G n q c hsk A w hA Γ (D.owner e) (coord e) i u x)
    q₀ b U hU x
  have hm:=lift_map (inputHom D q coord t)
    (letter D.index D.tail D.owner D.added (unitShift D) q₀ b) (baseWord D U)
  have hf : (fun e=>inputHom D q coord t (letter D.index D.tail D.owner D.added (unitShift D) q₀ b e))=
      letter D.index D.tail D.owner D.added (fun e=>inputHom D q coord t (unitShift D e)) q₀ b := by
    funext e
    simp [letter]
  rw [hf] at hm
  rw [←hm] at he
  have hz:=congrFun he 0
  change modelEval D G n q c hsk A w hA Γ t i 0 (terminalShift D q₀ b U • x)=
    modelEval D G n q c hsk A w hA Γ t i
      (0+ownInput D q coord t (terminalShift D q₀ b U).toAdd) x at hz
  simpa only [zero_add] using hz
 

omit [∀ t,Fintype (ι t)] in
theorem own_terminal_model_reading
    [act : ∀ t,MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t)]
    (hunit : ∀ e x,
      unitShift D e • x = faceAction (G (D.owner e)) (n (D.owner e)) (q (D.owner e))
        (c (D.owner e)) (hsk (D.owner e)) (A (D.owner e)) (w (D.owner e)) (hA (D.owner e)) (Γ (D.owner e))
        (fun _ (_ : Fin 1)=>1) (coord e) 0 x)
    {r : ℕ} (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (obs : ∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ)
    (t : Fin D.targets) (a₀ : ℚ) (col : Fin r) (q₀ : ℕ) (b : Scale a)
    (U : Finset (Fin D.pairs)) (hU : ∀ e∈U,D.owner e=t)
    (x : Target D G n q c hsk A w hA Γ t) (v : Slots D) :
    let z:=terminalShift D q₀ b U
    modelRead D G n q c hsk A w hA Γ formula obs t a₀ (z • (x,v)) col=
      obs t (formula t a₀ (z.toAdd+v) col)
        (modelEval D G n q c hsk A w hA Γ t (formula t a₀ (z.toAdd+v) col)
          (ownInput D q coord t z.toAdd) x)
 := by
  dsimp only
  change obs t (formula t a₀ ((terminalShift D q₀ b U).toAdd+v) col)
    (modelEval D G n q c hsk A w hA Γ t (formula t a₀ ((terminalShift D q₀ b U).toAdd+v) col) 0
      (terminalShift D q₀ b U • x))=_
  rw [eval_terminal D G n q c hsk A w hA Γ coord hunit t _ q₀ b U hU x]

end SourceIntegerArrays.GlobalJoint

end
end

end OAI
