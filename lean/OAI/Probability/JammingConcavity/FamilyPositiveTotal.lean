import Mathlib
import OAI.Probability.JammingConcavity.StableJumpIntegral

namespace OAI

/-! Family Positive Total. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma pointCloudFunctional_const_mul {A : Type} (c : ℝ≥0∞) (f : ℝ × A → ℝ≥0∞)
    (ω : PointCloud A) : pointCloudFunctional (fun z => c*f z) ω = c*pointCloudFunctional f ω := by
  unfold pointCloudFunctional poissonBinSum
  simp only [← Finset.mul_sum, ENNReal.tsum_mul_left]

lemma pointCloudFunctional_add {A : Type} (f g : ℝ × A → ℝ≥0∞) (ω : PointCloud A) :
    pointCloudFunctional (fun z => f z+g z) ω = pointCloudFunctional f ω+pointCloudFunctional g ω := by
  unfold pointCloudFunctional poissonBinSum
  simp only [Finset.sum_add_distrib, ENNReal.tsum_add]

variable {E : Type} [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]

lemma measurable_familyPositiveTotal (ms : List ℝ) {f : E → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : E × FamilyCascadeTree E ms.length => familyPositiveTotal ms f z.1 z.2) := by
  induction ms with
  | nil => exact hf.comp measurable_fst
  | cons m ms ih =>
    exact measurable_pointCloudFunctional_param ((by fun_prop : Measurable
      (fun z : E × (ℝ × (E × FamilyCascadeTree E ms.length)) => ENNReal.ofReal (z.2.1^(-1/m)))).mul
      (ih.comp (by fun_prop : Measurable (fun z : E × (ℝ × (E × FamilyCascadeTree E ms.length)) =>
        (z.1+z.2.2.1,z.2.2.2)))))

omit [MeasurableAdd₂ E] in
lemma familyPositiveTotal_mono [MeasurableAdd₂ E] (ms : List ℝ) {f g : E → ℝ≥0∞} (h : ∀ x, f x ≤ g x)
    (x : E) (ω : FamilyCascadeTree E ms.length) :
    familyPositiveTotal ms f x ω ≤ familyPositiveTotal ms g x ω := by
  induction ms generalizing x with
  | nil => exact h x
  | cons m ms ih =>
    apply pointCloudFunctional_mono
    intro z
    exact mul_le_mul_right (ih (x+z.2.1) z.2.2) _

omit [MeasurableAdd₂ E] in
lemma familyPositiveTotal_exp [MeasurableAdd₂ E] (ms : List ℝ) (u : E → ℝ) (x : E)
    (ω : FamilyCascadeTree E ms.length) :
    familyPositiveTotal ms (fun x => ENNReal.ofReal (Real.exp (u x))) x ω = familyLeafTotal ms u x ω := by
  induction ms generalizing x with
  | nil => rfl
  | cons m ms ih => simp only [familyPositiveTotal, familyLeafTotal, ih]

omit [MeasurableAdd₂ E] in
lemma familyPositiveTotal_const [MeasurableAdd₂ E] (ms : List ℝ) (c : ℝ≥0∞) (x : E)
    (ω : FamilyCascadeTree E ms.length) :
    familyPositiveTotal ms (fun _ => c) x ω = c*familyUnmarkedTotal ms ω := by
  induction ms generalizing x with
  | nil => simp [familyPositiveTotal, familyUnmarkedTotal, cascadeTotal]
  | cons m ms ih =>
    simp only [familyPositiveTotal, ih, familyUnmarkedTotal_cons]
    simp_rw [mul_left_comm (ENNReal.ofReal _) c]
    exact pointCloudFunctional_const_mul _ _ _

omit [MeasurableAdd₂ E] in
lemma familyPositiveTotal_add [MeasurableAdd₂ E] (ms : List ℝ) (f g : E → ℝ≥0∞) (x : E)
    (ω : FamilyCascadeTree E ms.length) :
    familyPositiveTotal ms (fun x => f x+g x) x ω =
      familyPositiveTotal ms f x ω+familyPositiveTotal ms g x ω := by
  induction ms generalizing x with
  | nil => rfl
  | cons m ms ih =>
    simp only [familyPositiveTotal, ih, mul_add]
    exact pointCloudFunctional_add _ _ _

lemma familyPathGibbs_positive_ratio (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (hm : ∀ m ∈ ms, 0 < m ∧ m < 1) (ν : ℕ → Measure E)
    (hν : ∀ j, IsProbabilityMeasure (ν j)) {u : E → ℝ} (hu : Measurable u)
    (hfin : FamilyMomentsFinite ms ν u) {φ : E → ℝ≥0∞} (hφ : Measurable φ) (x : E) :
    familyPathGibbs ms u φ x =ᵐ[familyCascadeLaw ms.length ν]
      (fun ω => familyPositiveTotal ms (fun z => ENNReal.ofReal (Real.exp (u z))*φ z) x ω /
        familyLeafTotal ms u x ω) := by
  induction ms generalizing ν x with
  | nil =>
    apply Eventually.of_forall
    intro ω
    simp only [familyPathGibbs, familyPositiveTotal, familyLeafTotal]
    rw [mul_comm, ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top]
  | cons m ms ih =>
    let η := familyCascadeLaw ms.length (fun j => ν (j+1))
    let := hν 0
    let : IsProbabilityMeasure η := familyCascadeLaw_probability ms.length _ (fun j => hν (j+1))
    have htms := (List.pairwise_cons.mp hms).2
    have htm := fun a ha => hm a (List.mem_cons_of_mem m ha)
    let P := familyPositiveTotal ms (fun z => ENNReal.ofReal (Real.exp (u z))*φ z)
    let T := familyLeafTotal ms u
    let F := familyPathGibbs ms u φ
    have hP := measurable_familyPositiveTotal ms ((Real.measurable_exp.comp hu).ennreal_ofReal.mul hφ)
    have hT := measurable_familyLeafTotal ms hu
    have hF := measurable_familyPathGibbs ms hu hφ
    have ha (a : E) : (fun ω => T (x+a) ω*F (x+a) ω) =ᵐ[η] P (x+a) := by
      have hi := ih htms htm (fun j => ν (j+1)) (fun j => hν (j+1)) hfin.2 (x+a)
      have hp := scaledLaw_positive η
        (familyLeafTotal_identDistrib ms htms htm (fun j => ν (j+1)) (fun j => hν (j+1)) hu hfin.2 (x+a))
        (familyUnmarkedTotal_properties ms htms htm (fun j => ν (j+1)) (fun j => hν (j+1))).1
      filter_upwards [hi,hp] with ω hi hp
      change T (x+a) ω*familyPathGibbs ms u φ (x+a) ω = _
      rw [hi]
      exact ENNReal.mul_div_cancel hp.1.ne' hp.2.ne
    have hprod : ∀ᵐ z ∂(ν 0).prod η, T (x+z.1) z.2*F (x+z.1) z.2 = P (x+z.1) z.2 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
        ((hT.mul hF).comp (by fun_prop : Measurable (fun z : E × FamilyCascadeTree E ms.length => (x+z.1,z.2))))
        (hP.comp (by fun_prop : Measurable (fun z : E × FamilyCascadeTree E ms.length => (x+z.1,z.2)))))).mpr
      exact Eventually.of_forall ha
    have he := pointCloudFunctional_mark_congr ((ν 0).prod η) (f := fun z =>
      ENNReal.ofReal (z.1^(-1/m))*T (x+z.2.1) z.2.2*F (x+z.2.1) z.2.2)
      (g := fun z => ENNReal.ofReal (z.1^(-1/m))*P (x+z.2.1) z.2.2) (by
        filter_upwards [hprod] with z hz
        intro y
        rw [mul_assoc, hz])
    filter_upwards [he] with ω hω
    change _ / _ = _ / _
    rw [hω]
    rfl
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def CascadePath : ℕ → Type
  | 0 => Unit
  | k+1 => (ℕ × ℕ) × CascadePath k

instance cascadePathEncodable : (k : ℕ) → Encodable (CascadePath k)
  | 0 => inferInstanceAs (Encodable Unit)
  | k+1 => by
    letI := cascadePathEncodable k
    exact inferInstanceAs (Encodable ((ℕ × ℕ) × CascadePath k))

def cascadePathWeight : (ms : List ℝ) → CascadeTree ms.length → CascadePath ms.length → ℝ≥0∞
  | [], _, _ => 1
  | m::ms, ω, ℓ => if ℓ.1.2 < (ω ℓ.1.1).1 then
      ENNReal.ofReal (((ℓ.1.1:ℝ)+((ω ℓ.1.1).2 ℓ.1.2).1)^(-1/m)) *
        cascadePathWeight ms ((ω ℓ.1.1).2 ℓ.1.2).2 ℓ.2 else 0

def familyPathWeight {E : Type} : (ms : List ℝ) →
    FamilyCascadeTree E ms.length → CascadePath ms.length → ℝ≥0∞
  | [], _, _ => 1
  | m::ms, ω, ℓ => if ℓ.1.2 < (ω ℓ.1.1).1 then
      ENNReal.ofReal (((ℓ.1.1:ℝ)+((ω ℓ.1.1).2 ℓ.1.2).1)^(-1/m)) *
        familyPathWeight ms ((ω ℓ.1.1).2 ℓ.1.2).2.2 ℓ.2 else 0

def familyPathMark {E : Type} [Add E] : (k : ℕ) → E →
    FamilyCascadeTree E k → CascadePath k → E
  | 0, x, _, _ => x
  | k+1, x, ω, ℓ => familyPathMark k (x+((ω ℓ.1.1).2 ℓ.1.2).2.1)
      ((ω ℓ.1.1).2 ℓ.1.2).2.2 ℓ.2

lemma familyPathWeight_zip {E : Type} (ms : List ℝ)
    (ω : CascadeTree ms.length) (y : CascadeMarkTree E ms.length) (ℓ : CascadePath ms.length) :
    familyPathWeight ms (zipCascade ms.length (ω,y)) ℓ = cascadePathWeight ms ω ℓ := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    change (if ℓ.1.2 < (ω ℓ.1.1).1 then
      ENNReal.ofReal (((ℓ.1.1:ℝ)+((ω ℓ.1.1).2 ℓ.1.2).1)^(-1/m))*
        familyPathWeight ms (zipCascade ms.length (((ω ℓ.1.1).2 ℓ.1.2).2,(y ℓ.1.1 ℓ.1.2).2)) ℓ.2 else 0) = _
    rw [ih]
    rfl

lemma tsum_familyPathWeight_terminal {E : Type} [MeasurableSpace E] [Add E]
    (ms : List ℝ) (f : E → ℝ≥0∞) (x : E) (ω : FamilyCascadeTree E ms.length) :
    (∑' ℓ : CascadePath ms.length, familyPathWeight ms ω ℓ*
      f (familyPathMark ms.length x ω ℓ)) = familyPositiveTotal ms f x ω := by
  induction ms generalizing x with
  | nil => simp [familyPathWeight, familyPathMark, familyPositiveTotal, CascadePath]
  | cons m ms ih =>
    change PointCloud (E × FamilyCascadeTree E ms.length) at ω
    have he : (∑' ℓ : CascadePath (ms.length+1), familyPathWeight (m::ms) ω ℓ*
        f (familyPathMark (ms.length+1) x ω ℓ)) =
        ∑' z : ℕ × ℕ, if z.2 < (ω z.1).1 then
          ENNReal.ofReal (((z.1:ℝ)+((ω z.1).2 z.2).1)^(-1/m))*
            familyPositiveTotal ms f (x+((ω z.1).2 z.2).2.1) ((ω z.1).2 z.2).2.2 else 0 := by
      change (∑' ℓ : (ℕ × ℕ) × CascadePath ms.length, _) = _
      rw [ENNReal.tsum_prod']
      apply tsum_congr
      intro z
      by_cases hz : z.2 < (ω z.1).1
      · simp only [familyPathWeight, familyPathMark, ite_eq_left hz, mul_assoc]
        rw [ENNReal.tsum_mul_left, ih]
      · simp only [familyPathWeight, ite_eq_right hz, zero_mul, tsum_zero]
    refine he.trans ?_
    rw [ENNReal.tsum_prod']
    simp only [familyPositiveTotal, pointCloudFunctional, poissonBinSum]
    apply tsum_congr
    intro n
    rw [tsum_eq_sum (s := Finset.range (ω n).1) (fun j hj => by
      simp only [Finset.mem_range, not_lt] at hj
      simp [not_lt.mpr hj])]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range.mp hj, ite_true]

lemma tsum_familyPathWeight {E : Type} [MeasurableSpace E] [AddMonoid E] [MeasurableAdd₂ E]
    (ms : List ℝ) (ω : FamilyCascadeTree E ms.length) :
    (∑' ℓ : CascadePath ms.length, familyPathWeight ms ω ℓ) = familyUnmarkedTotal ms ω := by
  simpa only [mul_one, familyPositiveTotal_const, one_mul] using
    tsum_familyPathWeight_terminal ms (fun _ : E => 1) 0 ω
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

abbrev CloudLabel := ℕ × ℕ

def cloudLabelPoint {A : Type*} (ω : PointCloud A) (i : CloudLabel) : ℝ × A :=
  ((i.1:ℝ)+((ω i.1).2 i.2).1, ((ω i.1).2 i.2).2)

def labelCloudIntegral {A : Type*} :
    List (CloudLabel → ℝ≥0∞) → PointCloud A → List CloudLabel → ℝ≥0∞
  | [], _, _ => 1
  | f::fs, ω, xs => by
      classical
      exact ∑' i : CloudLabel, if i.2 < (ω i.1).1 ∧ i ∉ xs then
        f i * labelCloudIntegral fs ω (i::xs) else 0

 
def rpcLabelPatternWeight : (ms : List ℝ) →
    ReplicaPattern ms.length → CascadeTree ms.length → ℝ≥0∞
  | [], _, _ => 1
  | m::ms, bs, ω => ENNReal.ofReal ((cascadeTotal (m::ms) ω).toReal ^
      (-(replicaPatternSize (ms.length+1) bs : ℝ))) *
      labelCloudIntegral (bs.map (fun b i =>
        (ENNReal.ofReal ((cloudLabelPoint ω i).1^(-1/m)) *
          cascadeTotal ms (cloudLabelPoint ω i).2)^(replicaPatternSize ms.length b) *
          rpcLabelPatternWeight ms b (cloudLabelPoint ω i).2)) ω []

def RPCLabelSamplingStatement : Prop :=
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
    (∀ᵐ ω ∂cascadeLaw ms,
      (∑' ℓ : CascadePath ms.length, cascadePathWeight ms ω ℓ / cascadeTotal ms ω) = 1) ∧
    (∀ η : ℝ, 0 ≤ η → (∀ m ∈ ms, η < m) →
      ∀ b : ReplicaPattern ms.length, ValidReplicaPattern ms.length b →
        (∫⁻ ω, ENNReal.ofReal ((cascadeTotal ms ω).toReal^η)*rpcLabelPatternWeight ms b ω ∂cascadeLaw ms) /
          ENNReal.ofReal (∫ ω, (cascadeTotal ms ω).toReal^η ∂cascadeLaw ms) =
            ENNReal.ofReal (rpcPatternProduct ms η b))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

instance cascadePathMeasurableSpace (k : ℕ) : MeasurableSpace (CascadePath k) := ⊤
instance cascadePathMeasurableSingleton (k : ℕ) : MeasurableSingletonClass (CascadePath k) :=
  ⟨fun _ => trivial⟩

def cascadeZeroPath : (k : ℕ) → CascadePath k
  | 0 => ()
  | k+1 => ((0,0),cascadeZeroPath k)

def cascadeLeafLaw (ms : List ℝ) (ω : CascadeTree ms.length) : Measure (CascadePath ms.length) := by
  classical
  exact if 0 < cascadeTotal ms ω ∧ cascadeTotal ms ω < ∞ then
    Measure.sum (fun ℓ => (cascadePathWeight ms ω ℓ / cascadeTotal ms ω) • Measure.dirac ℓ)
  else Measure.dirac (cascadeZeroPath ms.length)

def cascadeReplicaLaw (ms : List ℝ) : Measure (ℕ → CascadePath ms.length) :=
  (cascadeLaw ms).bind (fun ω => Measure.infinitePi (fun _ : ℕ => cascadeLeafLaw ms ω))

def RPCLeafKernelStatement : Prop :=
  (∀ ms : List ℝ, Measurable (cascadeLeafLaw ms) ∧
    (∀ ω, IsProbabilityMeasure (cascadeLeafLaw ms ω)) ∧
    Measurable (fun ω => Measure.infinitePi (fun _ : ℕ => cascadeLeafLaw ms ω)) ∧
    IsProbabilityMeasure (cascadeReplicaLaw ms)) ∧
  (∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
    (∀ᵐ ω ∂cascadeLaw ms, ∀ ℓ : CascadePath ms.length,
      cascadeLeafLaw ms ω {ℓ} = cascadePathWeight ms ω ℓ / cascadeTotal ms ω) ∧
    (∀ (I : Finset ℕ) (ℓ : ℕ → CascadePath ms.length),
      cascadeReplicaLaw ms {x | ∀ i ∈ I, x i = ℓ i} =
        ∫⁻ ω, ∏ i ∈ I, cascadePathWeight ms ω (ℓ i) / cascadeTotal ms ω ∂cascadeLaw ms))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

def MarkedPatternIndex {E : Type} : (k : ℕ) → MarkedReplicaPattern E k → Type
  | 0,b => Fin b.1
  | k+1,bs => (i : Fin (List.length bs)) × MarkedPatternIndex k (List.get bs i)

instance markedPatternIndexFintype {E : Type} : (k : ℕ) → (b : MarkedReplicaPattern E k) →
    Fintype (MarkedPatternIndex k b)
  | 0,_ => inferInstanceAs (Fintype (Fin _))
  | k+1,bs => by
    change List (MarkedReplicaPattern E k) at bs
    letI := fun i : Fin bs.length => markedPatternIndexFintype k (bs.get i)
    exact inferInstanceAs (Fintype ((i : Fin bs.length) × MarkedPatternIndex k (bs.get i)))

def familySampleLeafLaw {E : Type} [MeasurableSpace E] [Add E]
    (ms : List ℝ) (u : E → ℝ) (x : E) (ω : FamilyCascadeTree E ms.length) :
    Measure (CascadePath ms.length) :=
  if 0 < familyLeafTotal ms u x ω ∧ familyLeafTotal ms u x ω < ∞ then
    Measure.sum (fun ℓ =>
      (familyPathWeight ms ω ℓ * ENNReal.ofReal (Real.exp (u (familyPathMark ms.length x ω ℓ))) /
        familyLeafTotal ms u x ω) • Measure.dirac ℓ)
  else Measure.dirac (cascadeZeroPath ms.length)

 

def familySampleObservable {E : Type} [MeasurableSpace E] [Add E] :
    (ms : List ℝ) → (b : MarkedReplicaPattern E ms.length) → E →
      FamilyCascadeTree E ms.length → (MarkedPatternIndex ms.length b → CascadePath ms.length) → ℝ≥0∞
  | [],b,x,_,_ => b.2 x
  | _m::ms,bs,x,ω,ℓ =>
      ∑' a : {a : Fin (List.length bs) → CloudLabel // Function.Injective a},
        ∏ i : Fin (List.length bs),
          if ∀ j : MarkedPatternIndex ms.length (List.get bs i), (ℓ ⟨i,j⟩).1 = a.1 i then
            familySampleObservable ms (List.get bs i) (x+(cloudLabelPoint ω (a.1 i)).2.1)
              (cloudLabelPoint ω (a.1 i)).2.2 (fun j => (ℓ ⟨i,j⟩).2)
          else 0

def familySampleMean {E : Type} [MeasurableSpace E] [Add E]
    (ms : List ℝ) (b : MarkedReplicaPattern E ms.length) (u : E → ℝ) (x : E)
    (ω : FamilyCascadeTree E ms.length) : ℝ≥0∞ :=
  ∫⁻ ℓ, familySampleObservable ms b x ω ℓ
    ∂Measure.pi (fun _ : MarkedPatternIndex ms.length b => familySampleLeafLaw ms u x ω)

def FamilySampleStatement : Prop :=
  ∀ (E : Type) (_ : MeasurableSpace E) (_ : MeasurableEq E) (_ : Add E) (_ : MeasurableAdd₂ E),
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ ν : ℕ → Measure E, (∀ j, IsProbabilityMeasure (ν j)) →
  ∀ u : E → ℝ, Measurable u → FamilyMomentsFinite ms ν u →
    (∀ x ω, IsProbabilityMeasure (familySampleLeafLaw ms u x ω)) ∧
    (∀ (b : MarkedReplicaPattern E ms.length), ValidMarkedReplicaPattern ms.length b →
      ∀ η : ℝ, 0 ≤ η → (∀ m ∈ ms, η < m) → ∀ x : E,
      (∫⁻ ω, ENNReal.ofReal ((familyLeafTotal ms u x ω).toReal^η)*familySampleMean ms b u x ω
        ∂familyCascadeLaw ms.length ν) /
        ENNReal.ofReal (∫ ω, (familyLeafTotal ms u x ω).toReal^η ∂familyCascadeLaw ms.length ν) =
        ENNReal.ofReal (rpcPatternProduct ms η (markedReplicaShape ms.length b)) *
          familyReplicaMean ms b ν u x)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MicroscopicJamming
 

def rowDerivativeTest (L : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((deriv f x+L+1)/(2*(L+1)))
def rowSinglePattern (φ : ℝ → ℝ≥0∞) : (k : ℕ) → MarkedReplicaPattern ℝ k
  | 0 => (1,φ)
  | k+1 => [rowSinglePattern φ k]
 

def rowPairPattern (φ : ℝ → ℝ≥0∞) : (k : ℕ) → ℕ → MarkedReplicaPattern ℝ k
  | 0,_ => (2,fun x => (φ x)^2)
  | k+1,0 => [rowSinglePattern φ k,rowSinglePattern φ k]
  | k+1,j+1 => [rowPairPattern φ k j]
 

def RowGaussianPairStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (Δ : ℝ≥0) (j : ℕ), j ≤ ms.length → ∀ x : ℝ,
    let v := gaussianRowOperator 1 Δ u
    let rs := rowGaussianBlocks ms d
    let b := rowPairPattern (rowDerivativeTest L v) ms.length j
    (∫⁻ ω, familySampleMean ms b v x ω ∂familyCascadeLaw ms.length (rowGaussianLaw d)) =
      ENNReal.ofReal (rpcPatternProduct ms 0 (markedReplicaShape ms.length b)) *
        ENNReal.ofReal ((rowDerivativeDepthMoment rs v j x+
          2*(L+1)*deriv (gaussianRowComposition rs v) x+(L+1)^2)/(4*(L+1)^2))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

abbrev RankArray := ℕ → ℕ → ℝ

def cascadeSharedEdges : (k : ℕ) → CascadePath k → CascadePath k → ℕ
  | 0,_,_ => 0
  | k+1,x,y => if x.1 = y.1 then 1 + cascadeSharedEdges k x.2 y.2 else 0

def rpcStepLevel (ms : List ℝ) (u : ℝ) : ℕ := (ms.filter (fun m => m ≤ u)).length

def cascadeCovarianceArray (ms : List ℝ) (q : ℕ → ℝ) (Q : ℝ)
    (x : ℕ → CascadePath ms.length) : RankArray :=
  fun i j => if i=j then Q else q (cascadeSharedEdges ms.length (x i) (x j))

def rankCovarianceArray (ms : List ℝ) (q : ℕ → ℝ) (Q : ℝ) (U : RankArray) : RankArray :=
  fun i j => if i=j then Q else q (rpcStepLevel ms (U i j))

def HasRPCFiniteRankLaws (μ : Measure RankArray) : Prop :=
  ∀ (ms : List ℝ), ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (q : ℕ → ℝ) (Q : ℝ), 0 ≤ q 0 →
    (∀ i j, i ≤ j → j ≤ ms.length → q i ≤ q j) → q ms.length ≤ Q →
    μ.map (rankCovarianceArray ms q Q) =
      (cascadeReplicaLaw ms).map (cascadeCovarianceArray ms q Q)

def UniversalRPCRankStatement : Prop :=
  (∃ μ : Measure RankArray, IsProbabilityMeasure μ ∧
    (∀ᵐ U ∂μ, (∀ i, U i i=1) ∧ (∀ i j, U i j=U j i) ∧
      (∀ i j, 0 ≤ U i j ∧ U i j ≤ 1) ∧
      (∀ i j k, min (U i j) (U j k) ≤ U i k)) ∧
    (∀ p : Equiv.Perm ℕ, μ.map (fun U i j => U (p i) (p j))=μ) ∧
    μ.map (fun U => U 0 1) = volume.restrict (Set.Icc (0:ℝ) 1) ∧
    HasRPCFiniteRankLaws μ ∧
    (∀ (q : ℝ → ℝ) (Q : ℝ), Monotone q → 0 ≤ q 0 → q 1 ≤ Q →
      ∀ᵐ U ∂μ, ∀ n (a : Fin n → ℝ),
        0 ≤ ∑ i, ∑ j, a i*a j*(if i=j then Q else q (U i j)))) ∧
  (∀ μ ν : Measure RankArray, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    (∀ᵐ U ∂μ, ∀ i j, 0 ≤ U i j ∧ U i j ≤ 1) →
    (∀ᵐ U ∂ν, ∀ i j, 0 ≤ U i j ∧ U i j ≤ 1) →
    (∀ᵐ U ∂μ, ∀ i, U i i=1) → (∀ᵐ U ∂ν, ∀ i, U i i=1) →
    HasRPCFiniteRankLaws μ → HasRPCFiniteRankLaws ν → μ=ν)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
 

def rowPairIidObservable (ms : List ℝ) (φ : ℝ → ℝ≥0∞) (j : ℕ)
    (x : ℝ) (ω : FamilyCascadeTree ℝ ms.length) (ℓ : Fin 2 → CascadePath ms.length) : ℝ≥0∞ :=
  if cascadeSharedEdges ms.length (ℓ 0) (ℓ 1) = j then
    φ (familyPathMark ms.length x ω (ℓ 0)) * φ (familyPathMark ms.length x ω (ℓ 1)) else 0
 

def RowPairSemanticStatement : Prop :=
  ∀ (ms : List ℝ) (φ : ℝ → ℝ≥0∞) (j : ℕ), j ≤ ms.length →
  ∀ (u : ℝ → ℝ) (x : ℝ) (ω : FamilyCascadeTree ℝ ms.length),
    familySampleMean ms (rowPairPattern φ ms.length j) u x ω =
      ∫⁻ ℓ : Fin 2 → CascadePath ms.length, rowPairIidObservable ms φ j x ω ℓ
        ∂Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms u x ω)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
 
def rowSignedPairObservable (ms : List ℝ) (v : ℝ → ℝ) (j : ℕ)
    (x : ℝ) (ω : FamilyCascadeTree ℝ ms.length) (ℓ : Fin 2 → CascadePath ms.length) : ℝ :=
  if cascadeSharedEdges ms.length (ℓ 0) (ℓ 1) = j then
    deriv v (familyPathMark ms.length x ω (ℓ 0)) * deriv v (familyPathMark ms.length x ω (ℓ 1)) else 0
 

def RowSignedPairStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (Δ : ℝ≥0) (j : ℕ), j ≤ ms.length → ∀ x : ℝ,
    let v := gaussianRowOperator 1 Δ u
    let rs := rowGaussianBlocks ms d
    (∫ ω, (∫ ℓ : Fin 2 → CascadePath ms.length, rowSignedPairObservable ms v j x ω ℓ
        ∂Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms v x ω))
      ∂familyCascadeLaw ms.length (rowGaussianLaw d)) =
      rpcPatternProduct ms 0 (markedReplicaShape ms.length (rowPairPattern (fun _ => 1) ms.length j)) *
        rowDerivativeDepthMoment rs v j x
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
 

def RowFiniteRankTestStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (Δ : ℝ≥0) (B : ℕ → ℝ) (x : ℝ),
    let v := gaussianRowOperator 1 Δ u
    let rs := rowGaussianBlocks ms d
    (∫ ω, (∫ ℓ : Fin 2 → CascadePath ms.length,
        B (cascadeSharedEdges ms.length (ℓ 0) (ℓ 1)) *
        (deriv v (familyPathMark ms.length x ω (ℓ 0)) *
          deriv v (familyPathMark ms.length x ω (ℓ 1)))
      ∂Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms v x ω))
      ∂familyCascadeLaw ms.length (rowGaussianLaw d)) =
    ∫ s in (0:ℝ)..1, B (rpcStepLevel ms s) *
      rowDerivativeDepthMoment rs v (rpcStepLevel ms s) x
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma infinitePi_option {I E : Type*} [MeasurableSpace E]
    (μ : Measure E) (ν : I → Measure E) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (μ.prod (Measure.infinitePi ν)).map (fun z i => i.elim z.1 z.2) =
      Measure.infinitePi (fun i : Option I => i.elim μ ν) := by
  classical
  let F : E × (I → E) → Option I → E := fun z i => i.elim z.1 z.2
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp [F] <;> fun_prop
  let : ∀ i : Option I, IsProbabilityMeasure (i.elim μ ν) := fun i => by
    cases i <;> dsimp <;> infer_instance
  apply Measure.eq_infinitePi
  intro s t ht
  change ((μ.prod (Measure.infinitePi ν)).map F) ((s : Set (Option I)).pi t) = _
  rw [Measure.map_apply hF (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have he : F ⁻¹' ((s : Set (Option I)).pi t) =
      (if none ∈ s then t none else Set.univ) ×ˢ
        ((s.eraseNone : Set I).pi (fun i => t (some i))) := by
    ext z
    simp only [F, Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe,
      Finset.mem_eraseNone]
    by_cases hn : none ∈ s
    · simp only [ite_eq_left hn]
      constructor
      · intro h
        exact ⟨h none hn, fun i hi => h (some i) hi⟩
      · rintro ⟨h0,h1⟩ (_ | i) hi
        · exact h0
        · exact h1 i hi
    · simp only [ite_eq_right hn, Set.mem_univ, true_and]
      constructor
      · intro h i hi
        exact h (some i) hi
      · intro h i hi
        cases i with
        | none => exact (hn hi).elim
        | some i => exact h i hi
  rw [he, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht (some i))]
  by_cases hn : none ∈ s
  · rw [ite_eq_left hn]
    have hs : s = s.eraseNone.insertNone := by
      rw [Finset.insertNone_eraseNone, Finset.insert_eq_of_mem hn]
    conv_rhs => rw [hs, Finset.prod_insertNone]
    rfl
  · rw [ite_eq_right hn, measure_univ, one_mul]
    rw [Finset.prod_eraseNone]
    apply Finset.prod_congr rfl
    intro i hi
    cases i with
    | none => exact (hn hi).elim
    | some i => rfl
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def CascadeMarkIndex : ℕ → Type
  | 0 => Empty
  | k+1 => ℕ × (ℕ × Option (CascadeMarkIndex k))

instance cascadeMarkIndexEncodable : (k : ℕ) → Encodable (CascadeMarkIndex k)
  | 0 => inferInstanceAs (Encodable Empty)
  | k+1 => by
    letI := cascadeMarkIndexEncodable k
    exact inferInstanceAs (Encodable (ℕ × (ℕ × Option (CascadeMarkIndex k))))

def cascadeMarkDepth : (k : ℕ) → CascadeMarkIndex k → ℕ
  | 0, i => i.elim
  | k+1, (_n,_i,j) => j.elim 0 (fun j => cascadeMarkDepth k j+1)

def cascadeMarkCoordinates {E : Type} : (k : ℕ) →
    CascadeMarkTree E k → CascadeMarkIndex k → E
  | 0, _, i => i.elim
  | k+1, y, (n,i,j) => j.elim (y n i).1 (fun j => cascadeMarkCoordinates k (y n i).2 j)

lemma measurable_cascadeMarkCoordinates {E : Type} [MeasurableSpace E] (k : ℕ) :
    Measurable (cascadeMarkCoordinates (E := E) k) := by
  induction k with
  | zero => exact Measurable.of_eval (fun i => i.elim)
  | succ k ih =>
    apply Measurable.of_eval
    rintro ⟨n,i,(_ | j)⟩
    · exact (measurable_fst.comp ((measurable_pi_apply i).comp (measurable_pi_apply n)))
    · exact (measurable_pi_apply j).comp (ih.comp
        (measurable_snd.comp ((measurable_pi_apply i).comp (measurable_pi_apply n))))

lemma cascadeMarkCoordinates_law {E : Type} [MeasurableSpace E] (k : ℕ)
    (ν : ℕ → Measure E) [∀ j, IsProbabilityMeasure (ν j)] :
    (cascadeMarkLaw k ν).map (cascadeMarkCoordinates k) =
      Measure.infinitePi (fun i : CascadeMarkIndex k => ν (cascadeMarkDepth k i)) := by
  induction k generalizing ν with
  | zero =>
    change (Measure.dirac ()).map (fun (_ : Unit) => (fun (i : Empty) => (Empty.elim i : E))) = _
    rw [Measure.map_dirac]
    let : ∀ i : Empty, IsProbabilityMeasure (ν (cascadeMarkDepth 0 i)) := fun i => i.elim
    apply Measure.eq_infinitePi
    intro s t ht
    have hs : s = ∅ := Finset.eq_empty_of_forall_notMem (fun i _ => i.elim)
    simp [hs]
  | succ k ih =>
    let η := cascadeMarkLaw k (fun j => ν (j+1))
    let D : Option (CascadeMarkIndex k) → Measure E :=
      fun i => i.elim (ν 0) (fun j => ν (cascadeMarkDepth k j+1))
    let : ∀ i, IsProbabilityMeasure (D i) := fun i => by cases i <;> dsimp [D] <;> infer_instance
    let F : E × CascadeMarkTree E k → Option (CascadeMarkIndex k) → E :=
      fun z i => i.elim z.1 (cascadeMarkCoordinates k z.2)
    have hF : Measurable F := by
      apply Measurable.of_eval
      intro i
      cases i with
      | none => exact measurable_fst
      | some i =>
        exact (measurable_pi_apply i).comp
          ((measurable_cascadeMarkCoordinates k).comp measurable_snd)
    have hFlaw : ((ν 0).prod η).map F = Measure.infinitePi D := by
      rw [show F = (fun z i => i.elim z.1 z.2) ∘
        Prod.map id (cascadeMarkCoordinates (E := E) k) from rfl]
      rw [← Measure.map_map (by
        apply Measurable.of_eval
        intro i
        cases i <;> dsimp <;> fun_prop) (measurable_id.prodMap (measurable_cascadeMarkCoordinates k)),
        ← Measure.map_prod_map _ _ measurable_id (measurable_cascadeMarkCoordinates k), Measure.map_id]
      change ((ν 0).prod ((cascadeMarkLaw k (fun j => ν (j+1))).map
        (cascadeMarkCoordinates k))).map _ = _
      rw [ih, infinitePi_option]
    let G : (ℕ → E × CascadeMarkTree E k) → ℕ × Option (CascadeMarkIndex k) → E :=
      fun y j => F (y j.1) j.2
    have hG : Measurable G := by
      apply Measurable.of_eval
      intro j
      exact (measurable_pi_apply j.2).comp (hF.comp (measurable_pi_apply j.1))
    have hGlaw : (Measure.infinitePi (fun _ : ℕ => (ν 0).prod η)).map G =
        Measure.infinitePi (fun j : ℕ × Option (CascadeMarkIndex k) => D j.2) := by
      rw [show G = (MeasurableEquiv.curry ℕ (Option (CascadeMarkIndex k)) E).symm ∘
        (fun y i => F (y i)) from rfl,
        ← Measure.map_map (by fun_prop) (by fun_prop), Measure.infinitePi_map_pi (fun _ : ℕ => (ν 0).prod η) (fun _ => hF)]
      simp_rw [hFlaw]
      exact Measure.infinitePi_map_curry_symm (fun (_ : ℕ) i => D i)
    change (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      (ν 0).prod η))).map
      ((MeasurableEquiv.curry ℕ (ℕ × Option (CascadeMarkIndex k)) E).symm ∘
        (fun y : ℕ → ℕ → E × CascadeMarkTree E k => fun n => G (y n))) =
      Measure.infinitePi (fun i : ℕ × (ℕ × Option (CascadeMarkIndex k)) =>
        ν (i.2.2.elim 0 (fun j => cascadeMarkDepth k j+1)))
    have hD : (fun i : ℕ × (ℕ × Option (CascadeMarkIndex k)) =>
        ν (i.2.2.elim 0 (fun j => cascadeMarkDepth k j+1))) =
        (fun i : ℕ × (ℕ × Option (CascadeMarkIndex k)) => D i.2.2) := by
      funext i
      rcases i with ⟨n,i,(_ | j)⟩ <;> rfl
    rw [hD, ← Measure.map_map (by fun_prop) (by fun_prop),
      Measure.infinitePi_map_pi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (ν 0).prod η))
        (fun _ => hG)]
    simp_rw [hGlaw]
    exact Measure.infinitePi_map_curry_symm (fun (_ : ℕ) (i : ℕ × Option (CascadeMarkIndex k)) => D i.2)
end MicroscopicJamming

end

end OAI
