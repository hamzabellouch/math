import OAI.Probability.DilutedSpin.MeasureHierarchy
import OAI.Probability.DilutedSpin.QTopologyBound
import OAI.Probability.DilutedSpin.RegularBadMass

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Set
open scoped NNReal BigOperators
noncomputable local instance finiteEncodingDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
local instance finiteEncodingMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space
local instance finiteEncodingBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma continuous_atomicProbability_joint {X ι : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T1Space X] [Fintype ι] :
    Continuous (fun z : (ι → X) × AtomicWeights ι => atomicProbability z.1 z.2) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_atomicProbability]
  apply continuous_finsetSum
  intro i _
  exact (NNReal.continuous_coe.comp ((continuous_apply i).comp
    (continuous_subtype_val.comp continuous_snd))).mul
    (f.continuous.comp ((continuous_apply i).comp continuous_fst))

namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]

noncomputable def nnWeights (P : FiniteLaw Ω) : AtomicWeights Ω :=
  ⟨fun i => ⟨P.weight i,P.nonneg i⟩, by
    apply NNReal.coe_injective
    exact (NNReal.coe_sum Finset.univ (fun i => (⟨P.weight i,P.nonneg i⟩ : ℝ≥0))).trans P.total⟩


noncomputable def asProbability {X : Type*} [MeasurableSpace X]
    (P : FiniteLaw Ω) (f : Ω → X) : ProbabilityMeasure X := atomicProbability f P.nnWeights

lemma integral_asProbability {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : FiniteLaw Ω) (f : Ω → X) (g : X → ℝ) :
    ∫ x, g x ∂(P.asProbability f)=P.expect (fun a => g (f a)) := by
  rw [asProbability,integral_atomicProbability]
  rfl

lemma measurable_asProbability {Z X : Type*} [MeasurableSpace Z]
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [T1Space X]
    [MeasurableSpace (ProbabilityMeasure X)] [BorelSpace (ProbabilityMeasure X)]
    (P : Z → FiniteLaw Ω) (f : Z → Ω → X)
    (hP : ∀ a, Measurable (fun z => (P z).weight a))
    (hf : ∀ a, Measurable (fun z => f z a)) :
    Measurable (fun z => (P z).asProbability (f z)) := by
  have hw : Measurable (fun z => (P z).nnWeights) := by
    apply Measurable.subtype_mk
    exact Measurable.of_eval (fun a => (hP a).subtype_mk)
  exact continuous_atomicProbability_joint.measurable.comp
    ((Measurable.of_eval hf).prodMk hw)

end FiniteLaw

/-- The exact one-label branching spin moment at a real message or nested
 probability message.  The last transition consists of independent q-spins. -/
noncomputable def labelMoment : (r : ℕ) → PrescribedTree (r+1) → Hierarchy r → ℝ
  | 0, .node k _, x => ∏ _ : Fin k, Real.tanh x
  | r+1, .node _ C, η => ∏ j, ∫ x, labelMoment r (C j) x ∂η.toMeasure

namespace KernelTower
variable {Ω : Type} [Fintype Ω]

noncomputable def encode : (r : ℕ) → KernelTower Ω (r+1) →
    (FinitePath Ω (r+1) → ℝ) → Hierarchy r
  | 0,T,V => Real.artanh (T.1.expect (fun a => V (a,())))
  | r+1,T,V => T.1.asProbability (fun a => encode r (T.2 a) (fun y => V (a,y)))

def TerminalInterior : (r : ℕ) → KernelTower Ω (r+1) →
    (FinitePath Ω (r+1) → ℝ) → Prop
  | 0,T,V => T.1.expect (fun a => V (a,())) ∈ Ioo (-1) 1
  | r+1,T,V => ∀ a, TerminalInterior r (T.2 a) (fun y => V (a,y))

lemma encode_moment (r : ℕ) (T : KernelTower Ω (r+1))
    (V : FinitePath Ω (r+1) → ℝ) (hV : TerminalInterior r T V)
    (S : PrescribedTree (r+1)) :
    labelMoment r S (encode r T V)=PrescribedTree.treeMean S T V := by
  induction r with
  | zero =>
    change FiniteLaw Ω × (Ω → KernelTower Ω 0) at T
    rcases T with ⟨P,Q⟩
    cases S with
    | node k C =>
      change (∏ _ : Fin k, Real.tanh (Real.artanh (P.expect (fun a => V (a,()))))) =
        ∏ j, P.expect (fun a => PrescribedTree.treeMean (C j) (Q a) (fun y => V (a,y)))
      rw [Real.tanh_artanh hV]
      apply Finset.prod_congr rfl
      intro j _
      apply FiniteLaw.expect_congr
      intro a
      cases C j
      rfl
  | succ r ih =>
    change FiniteLaw Ω × (Ω → KernelTower Ω (r+1)) at T
    rcases T with ⟨P,Q⟩
    cases S with
    | node k C =>
      change (∏ j, ∫ x, labelMoment r (C j) x ∂(P.asProbability
          (fun a => encode r (Q a) (fun y => V (a,y))))) =
        ∏ j, P.expect (fun a => PrescribedTree.treeMean (C j) (Q a) (fun y => V (a,y)))
      simp_rw [FiniteLaw.integral_asProbability]
      apply Finset.prod_congr rfl
      intro j _
      apply FiniteLaw.expect_congr
      intro a
      exact ih (Q a) (fun y => V (a,y)) (hV a) (C j)

end KernelTower
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance finiteEncodingAverageDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance finiteEncodingAverageDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_split_regular_le (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ)
    (h0 : ∀ q, 0 ≤ F q) (h1 : ∀ q, F q ≤ 1) (η : ℝ) :
    average D F ≤ average (fun q => Regular η q ∧ D q) F+
      average (fun q : α → Fin L => ¬Regular η q) (fun _ => 1) := by
  unfold average
  rw [← FiniteLaw.expect_add]
  apply FiniteLaw.expect_mono
  intro q
  dsimp only
  by_cases hd : D q <;> by_cases hr : Regular η q <;>
    simp only [hd,hr,true_and,false_and,not_true_eq_false,not_false_eq_true,ite_true,ite_false] <;>
    first
    | simpa only [zero_add] using (h0 q).trans (h1 q)
    | linarith [h1 q]

lemma weighted_sum_eq_average (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) (c : ℝ) :
    (∑ q : α → Fin L, if D q then c*(L:ℝ)⁻¹^(Fintype.card α)*F q else 0)=c*average D F := by
  rw [average_eq,Finset.sum_filter,div_eq_mul_inv,← inv_pow]
  rw [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> ring

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.PrescribedTree
open ReducedTopology DepthAverage
open scoped BigOperators
noncomputable local instance finiteEncodingTreeDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance finiteEncodingTreeDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

lemma qExpect_depth_bound {L : ℕ} [NeZero L] (k : ℕ)
    (F : PrescribedTree L → ℝ) (hF : ∀ T, 0 ≤ F T) :
    qExpect (grid L 0 L) F k (single L) ≤
      ∑ S∈boundedTopologies (k+1), shapeCharge k S *
        average (fun q : S.Vertex → Fin L => S.Admissible (fun v => q v) 0 L)
          (fun q => F (S.realize L 0 (fun v => q v))) := by
  apply (qExpect_bounded_majorant (NeZero.pos L) k F hF).trans
  apply Finset.sum_le_sum
  intro S _
  rw [← weighted_sum_eq_average]
  apply Finset.sum_le_sum
  intro q _
  by_cases hq : S.Admissible (fun v => q v) 0 L
  · simp only [hq,ite_true]
    exact mul_le_mul_of_nonneg_right (qMass_realize_le (NeZero.pos L) k S q hq) (hF _)
  · simp only [hq,ite_false,le_refl]

noncomputable def shapeBadConstant (S : ReducedTopology) : ℝ :=
  (Fintype.card S.Vertex:ℝ)+(Fintype.card S.Vertex:ℝ)^2

lemma shapeBadConstant_nonneg (S : ReducedTopology) : 0 ≤ shapeBadConstant S := by
  unfold shapeBadConstant
  positivity

lemma qExpect_regular_bound {L : ℕ} [NeZero L] (k : ℕ)
    (F : PrescribedTree L → ℝ) (h0 : ∀ T, 0 ≤ F T) (h1 : ∀ T, F T ≤ 1)
    {η : ℝ} {r : ℕ} (hηr : η*(L:ℝ) ≤ r) :
    qExpect (grid L 0 L) F k (single L) ≤
      ∑ S∈boundedTopologies (k+1), shapeCharge k S *
        (average (regularOverlapDomain S L η) (fun q => F (S.realize L 0 (fun v => q v)))+
          shapeBadConstant S*(2*(r+1:ℕ):ℝ)/(L:ℝ)) := by
  apply (qExpect_depth_bound k F h0).trans
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_left _ (shapeCharge_nonneg k S)
  apply (average_split_regular_le _ _ (fun _ => h0 _) (fun _ => h1 _) η).trans
  exact add_le_add le_rfl (nonregular_average_bound hηr)

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
local instance finiteEncodingReindexMeasurableSpace (space : TopCat) :
    MeasurableSpace space := borel space
local instance finiteEncodingReindexBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma piCongrLeft_const_apply {ι κ X : Type} [MeasurableSpace X]
    (e : ι ≃ κ) (x : κ → X) :
    (MeasurableEquiv.piCongrLeft (fun _ : ι => X) e.symm) x = fun i => x (e i) := by
  funext i
  change (Equiv.piCongrLeft (fun _ : ι => X) e.symm) x i = _
  rw [Equiv.piCongrLeft_apply]
  simp

lemma logMean_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (r : ℕ) (g : (ι → ℝ) → ℝ) (m : Fin r → ℝ) (eta : ι → Hierarchy r) :
    logMean r (fun x : κ → ℝ => g (fun i => x (e i))) m (fun j => eta (e.symm j)) =
      logMean r g m eta := by
  induction r with
  | zero => simp [logMean]
  | succ r ih =>
    change ι → ProbabilityMeasure (Hierarchy r) at eta
    simp only [logMean]
    congr 2
    have he := (measurePreserving_piCongrLeft
      (fun i : ι => (eta i).toMeasure) e.symm).integral_comp'
        (fun x : ι → Hierarchy r => Real.exp (m 0*logMean r g (fun i => m i.succ) x))
    rw [← he]
    apply integral_congr_ae
    filter_upwards [] with x
    congr 2
    simpa only [Equiv.apply_symm_apply,piCongrLeft_const_apply] using ih (fun i => m i.succ) (fun i => x (e i))

lemma trialLog_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (r : ℕ) (g : (ι → ℝ) → ℝ) (m : Fin r → ℝ) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x : κ → ℝ => g (fun i => x (e i))) = trialLog r ζ m g := by
  change ProbabilityMeasure (Hierarchy r) at ζ
  unfold trialLog
  have he := (measurePreserving_piCongrLeft
    (fun _ : ι => ζ.toMeasure) e.symm).integral_comp' (logMean r g m)
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  simpa only [Equiv.apply_symm_apply,piCongrLeft_const_apply] using logMean_reindex e r g m (fun i => x (e i))

lemma integral_sumPi_exp_add {ι κ X : Type} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (μ : ι ⊕ κ → Measure X) [∀ i,IsProbabilityMeasure (μ i)]
    (f : (ι → X) → ℝ) (g : (κ → X) → ℝ) (t : ℝ) :
    (∫ x : ι ⊕ κ → X,Real.exp (t*(f (fun i => x (.inl i))+g (fun j => x (.inr j))))
      ∂Measure.pi μ) =
    (∫ x,Real.exp (t*f x) ∂Measure.pi (fun i => μ (.inl i)))*
      (∫ y,Real.exp (t*g y) ∂Measure.pi (fun j => μ (.inr j))) := by
  have he := (measurePreserving_sumPiEquivProdPi μ).integral_comp'
    (fun z : (ι → X) × (κ → X) => Real.exp (t*f z.1)*Real.exp (t*g z.2))
  simpa only [mul_add,Real.exp_add,MeasurableEquiv.coe_sumPiEquivProdPi,Equiv.sumPiEquivProdPi_apply] using he.trans (integral_prod_mul (μ := Measure.pi (fun i => μ (.inl i)))
    (ν := Measure.pi (fun j => μ (.inr j)))
    (fun x => Real.exp (t*f x)) (fun y => Real.exp (t*g y)))

lemma logMean_sum_separate {ι κ : Type} [Fintype ι] [Fintype κ]
    (r : ℕ) (f : (ι → ℝ) → ℝ) (g : (κ → ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g) {B C : ℝ}
    (hb : ∀ x,|f x|≤B) (hc : ∀ x,|g x|≤C)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (eta : ι ⊕ κ → Hierarchy r) :
    logMean r (fun x => f (fun i => x (.inl i))+g (fun j => x (.inr j))) m eta =
      logMean r f m (fun i => eta (.inl i))+logMean r g m (fun j => eta (.inr j)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change ι ⊕ κ → ProbabilityMeasure (Hierarchy r) at eta
    simp only [logMean]
    have he : (∫ x : ι ⊕ κ → Hierarchy r,Real.exp (m 0 *
        logMean r (fun x => f (fun i => x (.inl i))+g (fun j => x (.inr j)))
          (fun i => m i.succ) x) ∂Measure.pi (fun i => (eta i).toMeasure)) =
        (∫ x,Real.exp (m 0*logMean r f (fun i => m i.succ) x)
          ∂Measure.pi (fun i => (eta (.inl i)).toMeasure))*
        (∫ y,Real.exp (m 0*logMean r g (fun i => m i.succ) y)
          ∂Measure.pi (fun j => (eta (.inr j)).toMeasure)) := by
      simp_rw [ih (fun i => m i.succ) (fun i => hm i.succ)]
      exact integral_sumPi_exp_add _ _ _ _
    rw [he]
    obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hb (fun i => m i.succ) (fun i => hm i.succ)
    obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hc (fun i => m i.succ) (fun i => hm i.succ)
    rw [Real.log_mul
      (MeasureMean.exp_integral_pos _ hfc.measurable hfb (m 0)).ne'
      (MeasureMean.exp_integral_pos _ hgc.measurable hgb (m 0)).ne',add_div]

end DilutedSpinGlass

end

end OAI
