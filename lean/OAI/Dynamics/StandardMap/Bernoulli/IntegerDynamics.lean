import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Components.PowerAtomCycles
import OAI.Dynamics.StandardMap.Bernoulli.RohlinSinaiFinite

namespace OAI

section
section
open MeasureTheory Set Filter

namespace HyperbolicCoding
variable {X : Type*} [MeasurableSpace X]

def integerIterate (e : X ≃ᵐ X) (n : ℤ) (x : X) : X := (e.toEquiv^n) x

@[simp] lemma integerIterate_zero (e : X ≃ᵐ X) (x : X) : integerIterate e 0 x=x := by
  simp only [integerIterate,zpow_zero,Equiv.Perm.one_apply]
@[simp] lemma integerIterate_one (e : X ≃ᵐ X) (x : X) : integerIterate e 1 x=e x := by
  simp only [integerIterate,zpow_one,MeasurableEquiv.coe_toEquiv]
lemma integerIterate_add (e : X ≃ᵐ X) (m n : ℤ) (x : X) :
    integerIterate e (m+n) x=integerIterate e m (integerIterate e n x) := by
  simp only [integerIterate,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
lemma integerIterate_succ (e : X ≃ᵐ X) (n : ℤ) (x : X) :
    integerIterate e (n+1) x=e (integerIterate e n x) := by
  rw [add_comm,integerIterate_add,integerIterate_one]
lemma integerIterate_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : integerIterate e n x=e^[n] x := by
  simp only [integerIterate,zpow_natCast,Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv]
lemma integerIterate_neg_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : integerIterate e (-(n : ℤ)) x=e.symm^[n] x := by
  simp only [integerIterate,zpow_neg,zpow_natCast,←inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow]
  rfl
lemma integerIterate_nat_fun (e : X ≃ᵐ X) (n : ℕ) : integerIterate e (n : ℤ)=e^[n] :=
  funext (integerIterate_nat e n)
lemma integerIterate_neg_nat_fun (e : X ≃ᵐ X) (n : ℕ) : integerIterate e (-(n : ℤ))=e.symm^[n] :=
  funext (integerIterate_neg_nat e n)
lemma integerIterate_measurable (e : X ≃ᵐ X) (n : ℤ) : Measurable (integerIterate e n) := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast,integerIterate_nat_fun] using e.measurable.iterate m
  | negSucc m =>
    have hn : Int.negSucc m= -((m+1 : ℕ) : ℤ) := by omega
    simpa only [hn,integerIterate_neg_nat_fun] using e.symm.measurable.iterate (m+1)
lemma integerIterate_measurePreserving (e : X ≃ᵐ X) {μ : Measure X}
    (he : MeasurePreserving e μ μ) (n : ℤ) : MeasurePreserving (integerIterate e n) μ μ := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast,integerIterate_nat_fun] using he.iterate m
  | negSucc m =>
    have hn : Int.negSucc m= -((m+1 : ℕ) : ℤ) := by omega
    simpa only [hn,integerIterate_neg_nat_fun] using (he.symm e).iterate (m+1)

def orbitName {A : Type*} (e : X ≃ᵐ X) (α : X → A) (x : X) : ℤ → A :=
  fun n => α (integerIterate e n x)
lemma measurable_orbitName {A : Type*} [MeasurableSpace A] (e : X ≃ᵐ X) {α : X → A}
    (hα : Measurable α) : Measurable (orbitName e α) :=
  Measurable.of_eval (fun n => hα.comp (integerIterate_measurable e n))
lemma orbitName_shift {A : Type*} (e : X ≃ᵐ X) (α : X → A) (x : X) :
    orbitName e α (e x)=fun i => orbitName e α x (i+1) := by
  funext i
  simp only [orbitName,integerIterate_add,integerIterate_one]

end HyperbolicCoding

end
section
open MeasureTheory Set Filter

namespace HyperbolicCoding
variable {X A : Type*} [MeasurableSpace X]

def iterateEquiv (e : X ≃ᵐ X) (n : ℕ) : X ≃ᵐ X where
  toEquiv := e.toEquiv^n
  measurable_toFun := by simpa only [Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv] using e.measurable.iterate n
  measurable_invFun := by
    change Measurable (⇑((e.toEquiv^n)⁻¹))
    rw [←inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow]
    exact e.symm.measurable.iterate n
lemma iterateEquiv_apply (e : X ≃ᵐ X) (n : ℕ) (x : X) : iterateEquiv e n x=e^[n] x := by
  change ((e.toEquiv^n) x)=_
  rw [Equiv.Perm.coe_pow]
  rfl
lemma iterateEquiv_measurePreserving (e : X ≃ᵐ X) {μ : Measure X}
    (he : MeasurePreserving e μ μ) (n : ℕ) : MeasurePreserving (iterateEquiv e n) μ μ := by
  have hh : (iterateEquiv e n : X → X)=e^[n] := funext (iterateEquiv_apply e n)
  rw [hh]
  exact he.iterate n
lemma integerIterate_iterateEquiv (e : X ≃ᵐ X) (n : ℕ) (i : ℤ) (x : X) :
    integerIterate (iterateEquiv e n) i x=integerIterate e ((n : ℤ)*i) x := by
  change ((e.toEquiv^n)^i) x=(e.toEquiv^((n : ℤ)*i)) x
  rw [←zpow_natCast,←zpow_mul]

def blockObservation (e : X ≃ᵐ X) (α : X → A) (n : ℕ) (x : X) : Fin n → A :=
  fun j => α (integerIterate e j.val x)
lemma measurable_blockObservation [MeasurableSpace A] (e : X ≃ᵐ X) {α : X → A}
    (hα : Measurable α) (n : ℕ) : Measurable (blockObservation e α n) :=
  Measurable.of_eval (fun j => hα.comp (integerIterate_measurable e j.val))
lemma grouped_orbitName (e : X ≃ᵐ X) (α : X → A) (n : ℕ) (x : X) (i : ℤ) (j : Fin n) :
    orbitName (iterateEquiv e n) (blockObservation e α n) x i j=orbitName e α x ((n : ℤ)*i+j.val) := by
  simp only [orbitName,blockObservation,integerIterate_iterateEquiv,←integerIterate_add]
  rw [add_comm]
theorem grouped_names_separate (e : X ≃ᵐ X) (α : X → A) {n : ℕ} (hn : 0<n) {x y : X}
    (h : orbitName (iterateEquiv e n) (blockObservation e α n) x=
      orbitName (iterateEquiv e n) (blockObservation e α n) y) : orbitName e α x=orbitName e α y := by
  have hn' : (0 : ℤ)<n := by exact_mod_cast hn
  funext t
  have hmod := Int.emod_nonneg t (ne_of_gt hn')
  have hlt := Int.emod_lt_of_pos t hn'
  let j : Fin n := ⟨(t%(n : ℤ)).toNat,by omega⟩
  have hj : (j.val : ℤ)=t%(n : ℤ) := Int.toNat_of_nonneg hmod
  have hnum : (n : ℤ)*(t/n)+(j.val : ℤ)=t := by
    rw [hj,mul_comm]
    exact Int.ediv_mul_add_emod t n
  have hh := congrFun (congrFun h (t/n)) j
  simpa only [grouped_orbitName,hnum] using hh

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
lemma iterateEquiv_symm_apply {X : Type*} [MeasurableSpace X] (e : X ≃ᵐ X) (N : ℕ) (x : X) :
    (iterateEquiv e N).symm x=e.symm^[N] x := by
  change ((e.toEquiv^N)⁻¹ x)=_
  rw [←inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow]
  rfl
end HyperbolicCoding

namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology HyperbolicCoding
open scoped ENNReal
namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

theorem exists_partitions_tail_trivial {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (herg : ∀ r : ℕ,0<r → Ergodic (((standardMap k)^[N])^[r]) μ)
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ) :
    ∃ α : ℕ → ℕ → Torus → Bool,
      (∀ i j,Measurable (α i j)) ∧
      Function.Injective (fun z => fun i j => α i j z) ∧
      ∀ M : ℕ,∀ E : Set Torus,
        TailEvent μ ((standardMap k)^[N]) (joinedBinary α M) E →
        (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E) := by
  obtain ⟨α,hm,hi,hc⟩ := R.exists_partitions_doubleTail_constant hN μ hπ
  let e := iterateEquiv (standardMap_measurableEquiv k) N
  have heq : (e : Torus → Torus)=(standardMap k)^[N] := funext (iterateEquiv_apply _ N)
  have heq' : (e.symm : Torus → Torus)=(inverseMap k)^[N] := funext (iterateEquiv_symm_apply _ N)
  have he : MeasurePreserving e μ μ := by
    rw [heq]
    simpa only [Function.iterate_one] using (herg 1 (by omega)).toMeasurePreserving
  refine ⟨α,hm,hi,?_⟩
  intro M E hE
  have hα := measurable_joinedBinary hm M
  obtain ⟨C,hC⟩ := tailAtom_of_rectangle μ (B.carrierProbability.prod B.carrierProbability)
    e he (joinedBinary α M) hα hπ (by
      intro D hDf hDb
      rw [heq] at hDf
      rw [heq'] at hDb
      exact hc M D hDf hDb)
  rw [heq] at hC
  have hT : MeasurePreserving ((standardMap k)^[N]) μ μ := by rwa [heq] at he
  exact tail_trivial_of_atom hT hα herg hC E hE

end ReversibleGraphRectangle
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology BoundedSubadditive
open scoped ENNReal
namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

theorem powerAtoms_with_rectangle (hk : 0≤k) :
    ∃ P : PowerAtomFamily (standardMap_measurableEquiv k) area,
      (∀ n,QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability)
        (normalizedArea (P.atom n))) ∧
      0<area (P.atom 0∩{z | 0<standardLyapunov k hk z}) := by
  obtain ⟨C⟩ := exists_powerBirkhoffCodes k
  have hex (n : ℕ) := R.component_for_power (Nat.succ_pos n) (C n)
  choose E hE hp hInv hErg hπ using hex
  have hmem (n : ℕ) : ∀ᵐ p ∂B.carrierProbability.prod B.carrierProbability,R.torusPoint p∈E n :=
    (hπ n).ae (normalizedArea_ae_mem (hE n))
  let D : Set Torus := (⋂ n : ℕ,E n)∩{z | 0<standardLyapunov k hk z}
  have hDpos : 0<area D := by
    by_contra hn
    have hz : area D=0 := le_antisymm (not_lt.mp hn) bot_le
    have ha : ∀ᵐ z ∂area,z∉D := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hz
    obtain ⟨p,hm,hs,hn⟩ := ((ae_all_iff.mpr hmem).and
      ((R.carrier_nonsingular.ae (ae_standardLyapunov_spectrum k hk)).and (R.carrier_nonsingular.ae ha))).exists
    exact hn ⟨mem_iInter.mpr hm,R.spectrum_positive hs⟩
  let P : PowerAtomFamily (standardMap_measurableEquiv k) area := {
    atom := E
    measurable := hE
    positive := hp
    invariant := hInv
    ergodic := fun n => ergodic_restrict_of_normalized (hp n) (hErg n)
    common := ⟨D,hDpos,fun n _ hx => (mem_iInter.mp hx.1) n⟩ }
  refine ⟨P,hπ,hDpos.trans_le (measure_mono ?_)⟩
  intro x hx
  exact ⟨(mem_iInter.mp hx.1) 0,hx.2⟩

theorem exists_totally_ergodic_rectangle (hk : 0≤k) :
    ∃ (N : ℕ),0<N ∧ ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧
      (∀ r : ℕ,0<r → Ergodic (((standardMap k)^[N])^[r]) (normalizedArea E)) ∧
      QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) (normalizedArea E) := by
  obtain ⟨P,hπ,_⟩ := R.powerAtoms_with_rectangle hk
  have he : MeasurePreserving (standardMap_measurableEquiv k) area area := measurePreserving_standardMap k
  obtain ⟨n,hn⟩ := P.exists_totally_ergodic_cycle he
  let C := P.cycle he n
  refine ⟨C.period,C.positive,P.atom n,P.measurable n,P.positive n,?_,hπ n⟩
  intro r hr
  have hh := (hn r hr ⟨0,C.positive⟩).smul_measure (area (P.atom n))⁻¹
  simp only [Function.iterate_zero,preimage_id_eq,id_eq] at hh
  change Ergodic (((standardMap k)^[C.period])^[r]) (normalizedArea (P.atom n)) at hh
  exact hh

end ReversibleGraphRectangle
end StandardMapEntropy

end
section
namespace HyperbolicCoding
open MeasureTheory Filter

def GoodNames {X A : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (T : X → X) (α : X → A) : Prop :=
  ∀ᵐ x ∂μ,∀ y,ExponentiallyAsymptotic T x y →
    ∀ᶠ n : ℕ in atTop,α (T^[n] x)=α (T^[n] y)
end HyperbolicCoding

namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology HyperbolicCoding
open scoped ENNReal
namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

theorem doubleTail_constant_of_good_names {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ)
    {A : Type*} [MeasurableSpace A] (α : Torus → A)
    (hf : GoodNames μ ((standardMap k)^[N]) α)
    (hb : GoodNames μ ((inverseMap k)^[N]) α)
    (E : Set Torus)
    (hEf : TailEvent μ ((standardMap k)^[N]) α E)
    (hEb : TailEvent μ ((inverseMap k)^[N]) α E) :
    ∃ c : Prop,∀ᵐ p ∂B.carrierProbability.prod B.carrierProbability,(R.torusPoint p∈E ↔ c) := by
  obtain ⟨Qf,hQf,hSatf⟩ := tailEvent_saturation μ hf hEf
  obtain ⟨Qb,hQb,hSatb⟩ := tailEvent_saturation μ hb hEb
  have hQ := hπ.ae (hQf.and hQb)
  have hrow (a b b' : B.coordinateCarrier)
      (hx : R.torusPoint (a,b)∈Qf ∧ R.torusPoint (a,b)∈Qb)
      (hy : R.torusPoint (a,b')∈Qf ∧ R.torusPoint (a,b')∈Qb) :
      (R.torusPoint (a,b)∈E)=(R.torusPoint (a,b')∈E) :=
    propext (hSatf _ hx.1 _ hy.1 ((R.row_exponential a b b').iterate hN))
  have hcol (a a' b : B.coordinateCarrier)
      (hx : R.torusPoint (a,b)∈Qf ∧ R.torusPoint (a,b)∈Qb)
      (hy : R.torusPoint (a',b)∈Qf ∧ R.torusPoint (a',b)∈Qb) :
      (R.torusPoint (a,b)∈E)=(R.torusPoint (a',b)∈E) :=
    propext (hSatb _ hx.2 _ hy.2 ((R.column_exponential a a' b).iterate hN))
  obtain ⟨c,hc⟩ := ae_constant_of_product_rows_columns
    (F := fun p => R.torusPoint p∈E) hQ hrow hcol
  exact ⟨c,hc.mono (fun p hp => Iff.of_eq hp)⟩

theorem tail_trivial_of_good_names {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (herg : ∀ r : ℕ,0<r → Ergodic (((standardMap k)^[N])^[r]) μ)
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ)
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : Torus → A) (hα : Measurable α)
    (hf : GoodNames μ ((standardMap k)^[N]) α)
    (hb : GoodNames μ ((inverseMap k)^[N]) α) :
    ∀ E,TailEvent μ ((standardMap k)^[N]) α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E) := by
  let e := iterateEquiv (standardMap_measurableEquiv k) N
  have heq : (e : Torus → Torus)=(standardMap k)^[N] := funext (iterateEquiv_apply _ N)
  have heq' : (e.symm : Torus → Torus)=(inverseMap k)^[N] := funext (iterateEquiv_symm_apply _ N)
  have he : MeasurePreserving e μ μ := by
    rw [heq]
    simpa only [Function.iterate_one] using (herg 1 (by omega)).toMeasurePreserving
  obtain ⟨C,hC⟩ := tailAtom_of_rectangle μ (B.carrierProbability.prod B.carrierProbability)
    e he α hα hπ (by
      intro D hDf hDb
      rw [heq] at hDf
      rw [heq'] at hDb
      exact R.doubleTail_constant_of_good_names hN μ hπ α hf hb D hDf hDb)
  rw [heq] at hC
  have hT : MeasurePreserving ((standardMap k)^[N]) μ μ := by rwa [heq] at he
  exact tail_trivial_of_atom hT hα herg hC

theorem exists_good_K_partitions {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (herg : ∀ r : ℕ,0<r → Ergodic (((standardMap k)^[N])^[r]) μ)
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ) :
    ∃ α : ℕ → ℕ → Torus → Bool,
      (∀ i j,Measurable (α i j)) ∧ Function.Injective (fun z => fun i j => α i j z) ∧
      ∀ M : ℕ,GoodNames μ ((standardMap k)^[N]) (joinedBinary α M) ∧
        GoodNames μ ((inverseMap k)^[N]) (joinedBinary α M) ∧
        (∀ E,TailEvent μ ((standardMap k)^[N]) (joinedBinary α M) E →
          (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E)) := by
  obtain ⟨α,hm,hi,hf,hb⟩ := exists_good_binary_partitions μ
    ((measurePreserving_standardMap k).measurable.iterate N)
    ((measurePreserving_inverseMap k).measurable.iterate N)
  refine ⟨α,hm,hi,?_⟩
  intro M
  have hfM : GoodNames μ ((standardMap k)^[N]) (joinedBinary α M) :=
    hf.mono (fun x hx y hy => hx y hy M)
  have hbM : GoodNames μ ((inverseMap k)^[N]) (joinedBinary α M) :=
    hb.mono (fun x hx y hy => hx y hy M)
  exact ⟨hfM,hbM,R.tail_trivial_of_good_names hN μ herg hπ _ (measurable_joinedBinary hm M) hfM hbM⟩

end ReversibleGraphRectangle
end StandardMapEntropy

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def LawClose (μ ν : Measure X) (ε : ℝ) : Prop :=
  ∀ D : Set X,MeasurableSet D → |μ.real D-ν.real D|≤ε

lemma LawClose.symm {μ ν : Measure X} {ε : ℝ} (h : LawClose μ ν ε) : LawClose ν μ ε := by
  intro D hD
  rw [abs_sub_comm]
  exact h D hD

lemma LawClose.triangle {μ ν κ : Measure X} {ε δ : ℝ}
    (h : LawClose μ ν ε) (h' : LawClose ν κ δ) : LawClose μ κ (ε+δ) := by
  intro D hD
  exact (abs_sub_le (μ.real D) (ν.real D) (κ.real D)).trans (add_le_add (h D hD) (h' D hD))

lemma LawClose.map {μ ν : Measure X} {ε : ℝ} (h : LawClose μ ν ε)
    {f : X → Y} (hf : Measurable f) : LawClose (μ.map f) (ν.map f) ε := by
  intro D hD
  simp only [Measure.real,Measure.map_apply hf hD]
  exact h _ (hD.preimage hf)

lemma real_prod_apply (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D : Set (X×Y)} (hD : MeasurableSet D) :
    (μ.prod ν).real D=∫ x,ν.real ((Prod.mk x) ⁻¹' D) ∂μ := by
  rw [Measure.real,Measure.prod_apply hD]
  exact (integral_toReal (measurable_measure_prodMk_left hD).aemeasurable
    (Filter.Eventually.of_forall (fun _ => measure_lt_top ν _))).symm

lemma integrable_real_section (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    {D : Set (X×Y)} (hD : MeasurableSet D) :
    Integrable (fun x => ν.real ((Prod.mk x) ⁻¹' D)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_measure_prodMk_left hD).ennreal_toReal.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_le_one)

lemma LawClose.prod_same_left (μ : Measure X) [IsProbabilityMeasure μ]
    {ν η : Measure Y} [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    {ε : ℝ} (h : LawClose ν η ε) : LawClose (μ.prod ν) (μ.prod η) ε := by
  intro D hD
  rw [real_prod_apply μ ν hD,real_prod_apply μ η hD,
    ←integral_sub (integrable_real_section μ ν hD) (integrable_real_section μ η hD)]
  calc
    _≤∫ x,|ν.real ((Prod.mk x) ⁻¹' D)-η.real ((Prod.mk x) ⁻¹' D)| ∂μ := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (fun x => ν.real ((Prod.mk x) ⁻¹' D)-η.real ((Prod.mk x) ⁻¹' D)))
    _≤∫ _x : X,ε ∂μ := integral_mono_ae
      ((integrable_real_section μ ν hD).sub (integrable_real_section μ η hD)).abs
      (integrable_const ε) (Filter.Eventually.of_forall (fun x => h _ (hD.preimage measurable_prodMk_left)))
    _=ε := by simp

lemma LawClose.prod_same_right {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) (η : Measure Y) [IsProbabilityMeasure η] :
    LawClose (μ.prod η) (ν.prod η) ε := by
  simpa only [Measure.prod_swap] using (h.prod_same_left η).map measurable_swap

lemma LawClose.prod {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η κ : Measure Y} [IsProbabilityMeasure η] [IsProbabilityMeasure κ]
    {ε δ : ℝ} (h : LawClose μ ν ε) (h' : LawClose η κ δ) :
    LawClose (μ.prod η) (ν.prod κ) (ε+δ) :=
  (h.prod_same_right η).triangle (h'.prod_same_left ν)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open Set Filter
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem decreasing_projection_limit (K : ℕ → Submodule ℝ V)
    [∀ n,(K n).HasOrthogonalProjection]
    (hK : Antitone K) (hclosed : ∀ n,IsClosed (K n : Set V)) (f : V) :
    ∃ g : V,(∀ n,g∈K n) ∧ Tendsto (fun n => (K n).starProjection f) atTop (𝓝 g) := by
  let p (n : ℕ) : V := (K n).starProjection f
  have hid {n m : ℕ} (hnm : n ≤ m) :
      ‖p n-p m‖^2=‖p n‖^2-‖p m‖^2 := by
    have hcomp : (K m).starProjection (p n)=p m := by
      exact congrArg (fun L : V →L[ℝ] V => L f) (Submodule.starProjection_comp_starProjection_of_le (hK hnm))
    have ho := Submodule.starProjection_inner_eq_zero (K := K m) (p n) (p m)
      ((K m).starProjection_apply_mem f)
    rw [hcomp,inner_sub_left,real_inner_self_eq_norm_sq] at ho
    rw [norm_sub_sq_real]
    linarith
  have hanti : Antitone (fun n => ‖p n‖^2) := by
    intro n m hnm
    have hh := hid hnm
    nlinarith [sq_nonneg ‖p n-p m‖]
  have ht := tendsto_atTop_ciInf hanti (show BddBelow (range (fun n => ‖p n‖^2)) from
    ⟨0,by rintro _ ⟨n,rfl⟩; exact sq_nonneg _⟩)
  have hc : CauchySeq p := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp ht.cauchySeq (ε^2) (sq_pos_of_pos hε)
    refine ⟨N,?_⟩
    intro n hn
    have hn' := hN n hn
    rw [Real.dist_eq] at hn'
    have hab := (abs_sub_comm (‖p n‖^2) (‖p N‖^2)) ▸ hn'
    have hdiff : ‖p N-p n‖^2<ε^2 := by
      rw [hid hn]
      exact lt_of_le_of_lt (le_abs_self _) hab
    rw [dist_comm,dist_eq_norm]
    nlinarith [norm_nonneg (p N-p n)]
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨g,?_,hg⟩
  intro n
  exact (hclosed n).mem_of_tendsto hg ((eventually_ge_atTop n).mono (fun m hnm => hK hnm ((K m).starProjection_apply_mem f)))

end HyperbolicCoding

end
end

end OAI
