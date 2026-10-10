import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coding.FixedWindowTower

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A B : Type*} [MeasurableSpace X]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

lemma centeredWindow_orbit_shift [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (e : X ≃ᵐ X) (p : X → A) (R : ℕ) (x : X) :
    centeredWindow R (orbitName e p (e^[R] x))=word e p (2*R+1) x := by
  funext i
  change p (integerIterate e ((i.val : ℤ)-R) (e^[R] x))=p (e^[i.val] x)
  rw [←integerIterate_nat e R x,←integerIterate_add,sub_add_cancel,integerIterate_nat]

variable [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

lemma centered_decoder_error_eq (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : X → B) (p : X → A) (hα : Measurable α) (hp : Measurable p)
    (R : ℕ) (D : (Fin (2*R+1) → A) → B) :
    μ.real {x | α x≠D (centeredWindow R (orbitName e p x))}=
      μ.real {x | α (e^[R] x)≠D (word e p (2*R+1) x)} := by
  have hD : Measurable (fun x => D (centeredWindow R (orbitName e p x))) :=
    (measurable_of_countable D).comp ((measurable_centeredWindow R).comp (measurable_orbitName e hp))
  have hset : {x | α (e^[R] x)≠D (word e p (2*R+1) x)}=
      (e^[R]) ⁻¹' {x | α x≠D (centeredWindow R (orbitName e p x))} := by
    ext x
    simp only [mem_ofPred_eq,mem_preimage,centeredWindow_orbit_shift]
  have hm : MeasurableSet {x | α x≠D (centeredWindow R (orbitName e p x))} := (measurableSet_eq_fun hα hD).compl
  rw [hset,Measure.real,Measure.real,(he.iterate R).measure_preimage hm.nullMeasurableSet]

lemma centered_decoder_perturbation [StandardBorelSpace X] [Nonempty A]
    (μ : Measure X) [IsFiniteMeasure μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : X → B) (p q : X → A) (hα : Measurable α) (hp : Measurable p) (hq : Measurable q)
    (R : ℕ) (D : (Fin (2*R+1) → A) → B) :
    μ.real {x | α x≠D (centeredWindow R (orbitName e q x))}≤
      μ.real {x | α x≠D (centeredWindow R (orbitName e p x))}+
        (2*R+1 : ℕ)*μ.real {x | p x≠q x} := by
  rw [centered_decoder_error_eq μ e he α q hα hq R D,
    centered_decoder_error_eq μ e he α p hα hp R D]
  exact finite_decoder_perturbation μ e he p q hp hq (fun x => α (e^[R] x)) _ D
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

theorem exact_iid_decoder_density (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0 < weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)))
    (α : X → B) (hα : Measurable α)
    (happrox : ∀ ε : ℝ,0 < ε → ∃ r : X → A×B,Measurable r ∧ WeakBernoulliProcess μ e r ∧
      μ.real {x | (p x,α x)≠r x} < ε)
    (zero one : A) (h01 : zero≠one) {η : ℝ} (hη : 0 < η) :
    ∃ q : X → A,∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → B,Measurable q ∧
      MeasurePreserving (orbitName e q) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
      μ.real {x | p x≠q x} < η ∧
      μ.real {x | α x≠D (centeredWindow R (orbitName e q x))} < η := by
  obtain ⟨R,D,hproduce⟩ := fixed_decoder_arbitrary_tests μ e he htotal p hp β hβ hβsum hβentropy
    H hcode α hα happrox zero one h01 (half_pos hη)
  let c : ℝ := η/(4*((2*R+1 : ℕ)+1))
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨L,δ,hδ,hcomplete⟩ := seeded_exact_iid_limit μ e he htotal β hβ hβsum hβentropy H zero one h01 hc
  obtain ⟨q₀,hq₀,hpaint,hfixed,hlaw,hrate⟩ := hproduce L δ δ hδ hδ
  obtain ⟨q,hq,hcodeq,hclose⟩ := hcomplete q₀ hq₀ hlaw hrate.le
  have hwidth : (0 : ℝ)≤(2*R+1 : ℕ) := Nat.cast_nonneg _
  have hceq : c*(4*((2*R+1 : ℕ)+1))=η := by dsimp [c]; field_simp
  have hcη : c≤η/4 := by nlinarith only [hceq,hc,hwidth]
  have hWc : (2*R+1 : ℕ)*c≤η/4 := by nlinarith only [hceq,hc,hwidth]
  refine ⟨q,R,D,hq,hcodeq,?_,?_⟩
  · have hh := disagreement_triangle μ p q₀ q
    linarith only [hh,hpaint,hclose,hcη,hη]
  · rw [centered_decoder_error_eq μ e he.toMeasurePreserving α q hα hq R D]
    have hh := finite_decoder_perturbation μ e he.toMeasurePreserving q₀ q hq₀ hq (fun x => α (e^[R] x)) (2*R+1) D
    have hd := mul_le_mul_of_nonneg_left hclose.le hwidth
    linarith only [hh,hfixed,hd,hWc,hη]

theorem exact_iid_decoder_density_of_separating_wb (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (ξ : ℕ → ℕ → X → Bool) (hξ : ∀ i j,Measurable (ξ i j))
    (hsep : Function.Injective (fun x => fun i j => ξ i j x))
    (hwb : ∀ M,WeakBernoulliProcess μ e (joinedBinary ξ M))
    (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0 < weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)))
    (α : X → B) (hα : Measurable α) (zero one : A) (h01 : zero≠one) {η : ℝ} (hη : 0 < η) :
    ∃ q : X → A,∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → B,Measurable q ∧
      MeasurePreserving (orbitName e q) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
      μ.real {x | p x≠q x} < η ∧
      μ.real {x | α x≠D (centeredWindow R (orbitName e q x))} < η := by
  apply exact_iid_decoder_density μ e he htotal p hp β hβ hβsum hβentropy H hcode α hα _ zero one h01 hη
  intro ε hε
  obtain ⟨r,hr,hwr,herr⟩ := separating_wb_approximation μ e ξ hξ hsep hwb
    (fun x => (p x,α x)) (hp.prodMk hα) hε
  refine ⟨r,hr,hwr,?_⟩
  rwa [disagreement_symm]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma budget_geometric_decay (b : ℕ → ℝ) (hb : ∀ n,b (n+1)≤b n/2) (n k : ℕ) :
    b (n+k)≤b n*(1/2 : ℝ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,pow_succ]
    have hh := hb (n+k)
    nlinarith only [ih,hh]

lemma geometric_tail_distance (μ : Measure X) [IsFiniteMeasure μ]
    (q : ℕ → X → A) (b : ℕ → ℝ) (hpos : ∀ n,0≤b n)
    (hb : ∀ n,b (n+1)≤b n/2)
    (hpaint : ∀ n,μ.real {x | q n x≠q (n+1) x}≤b n/2) (n k : ℕ) :
    μ.real {x | q n x≠q (n+k) x}≤b n := by
  let η : ℕ → ℝ := fun j => b n/2*(1/2 : ℝ)^j
  have hstep (j : ℕ) : μ.real {x | q (n+j) x≠q (n+(j+1)) x}≤η j := by
    have h := hpaint (n+j)
    have hh := budget_geometric_decay b hb n j
    dsimp [η]
    rw [Nat.add_succ]
    nlinarith only [h,hh]
  have hh := sequence_distance_le_sum μ (fun j => q (n+j)) η hstep k
  simp only [Nat.add_zero] at hh
  apply hh.trans
  simp only [η,←Finset.mul_sum]
  have hs := mul_le_mul_of_nonneg_left (sum_geometric_two_le k) (show 0≤b n/2 from div_nonneg (hpos n) (by norm_num))
  nlinarith only [hs]

lemma geometric_tail_limit [MeasurableEq A]
    (μ : Measure X) [IsFiniteMeasure μ] (q : ℕ → X → A) (p : X → A)
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    (b : ℕ → ℝ) (hpos : ∀ n,0≤b n) (hb : ∀ n,b (n+1)≤b n/2)
    (hpaint : ∀ n,μ.real {x | q n x≠q (n+1) x}≤b n/2) (n : ℕ) :
    μ.real {x | q n x≠p x}≤b n := by
  have ht : Tendsto (fun j : ℕ => n+j) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat n
  have hl : ∀ᵐ x ∂μ,∀ᶠ j : ℕ in atTop,q (n+j) x=p x :=
    hlim.mono (fun x hx => ht.eventually hx)
  exact partition_limit_distance_bound μ (fun j => q (n+j)) p (q n) (fun j => hq _) hp hl
    (fun k => geometric_tail_distance μ q b hpos hb hpaint n k)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology

lemma exists_post_decoder_budget (W : ℕ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ b : ℝ,0 < b ∧ b≤c ∧ (W : ℝ)*b≤ε := by
  let b := min c (ε/((W : ℝ)+1))
  have hW : (0 : ℝ)≤W := Nat.cast_nonneg W
  have hb : 0 < b := lt_min hc (by positivity)
  have hsmall : b≤ε/((W : ℝ)+1) := min_le_right _ _
  have hh := (le_div_iff₀ (by positivity : (0 : ℝ)<(W : ℝ)+1)).mp hsmall
  exact ⟨b,hb,min_le_left _ _,by nlinarith only [hh,hb]⟩
end HyperbolicCoding
end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal NNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]

structure GeneratingIIDStage (μ : Measure X) (e : X ≃ᵐ X) (β : A → ℝ)
    (α : ℕ → ℕ → X → Bool) (n : ℕ) where
  partition : X → A
  measurable_partition : Measurable partition
  iid : MeasurePreserving (orbitName e partition) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β))
  radius : ℕ
  decoder : (Fin (2*radius+1) → A) → ((Fin (n+1) × Fin (n+1)) → Bool)
  error : μ.real {x | joinedBinary α (n+1) x≠decoder (centeredWindow radius (orbitName e partition x))} <
    (1/2 : ℝ)^(n+2)
  budget : ℝ
  budget_pos : 0 < budget
  budget_small : (2*radius+1 : ℕ)*budget≤(1/2 : ℝ)^(n+2)

lemma generating_iid_stage (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0 < weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x))
    (hwb : ∀ M,WeakBernoulliProcess μ e (joinedBinary α M))
    (zero one : A) (h01 : zero≠one)
    (p : X → A) (hp : Measurable p)
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)))
    (n : ℕ) {η c : ℝ} (hη : 0 < η) (hc : 0 < c) :
    ∃ S : GeneratingIIDStage μ e β α n,
      μ.real {x | p x≠S.partition x} < η ∧ S.budget≤c := by
  have hε : 0 < (1/2 : ℝ)^(n+2) := by positivity
  obtain ⟨q,R,D,hq,hcodeq,hpaint,hdecode⟩ := exact_iid_decoder_density_of_separating_wb μ e he htotal
    α hα hsep hwb p hp β hβ hβsum hβentropy H hcode (joinedBinary α (n+1))
    (measurable_joinedBinary hα _) zero one h01 (lt_min hη hε)
  obtain ⟨b,hb,hbc,hbudget⟩ := exists_post_decoder_budget (2*R+1) hε hc
  refine ⟨⟨q,hq,hcodeq,R,D,hdecode.trans_le (min_le_right _ _),b,hb,hbudget⟩,?_,hbc⟩
  exact hpaint.trans_le (min_le_left _ _)

theorem generating_iid_partition (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0 < weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x))
    (hwb : ∀ M,WeakBernoulliProcess μ e (joinedBinary α M))
    (zero one : A) (h01 : zero≠one)
    (p₀ : X → A) (hp₀ : Measurable p₀)
    (hcode₀ : MeasurePreserving (orbitName e p₀) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β))) :
    ∃ p : X → A,Measurable p ∧
      MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
      ∀ n : ℕ,∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → ((Fin (n+1) × Fin (n+1)) → Bool),
        μ.real {x | joinedBinary α (n+1) x≠D (centeredWindow R (orbitName e p x))}≤2*(1/2 : ℝ)^(n+2) := by
  have hstart := generating_iid_stage μ e he htotal β hβ hβsum hβentropy H α hα hsep hwb
    zero one h01 p₀ hp₀ hcode₀ 0 zero_lt_one zero_lt_one
  let S₀ : GeneratingIIDStage μ e β α 0 := Classical.choose hstart
  have hnext (n : ℕ) (S : GeneratingIIDStage μ e β α n) :
      ∃ T : GeneratingIIDStage μ e β α (n+1),
        μ.real {x | S.partition x≠T.partition x} < S.budget/2 ∧ T.budget≤S.budget/2 :=
    generating_iid_stage μ e he htotal β hβ hβsum hβentropy H α hα hsep hwb
      zero one h01 S.partition S.measurable_partition S.iid (n+1) (half_pos S.budget_pos) (half_pos S.budget_pos)
  let next (n : ℕ) (S : GeneratingIIDStage μ e β α n) : GeneratingIIDStage μ e β α (n+1) :=
    Classical.choose (hnext n S)
  let z : (n : ℕ) → GeneratingIIDStage μ e β α n := fun n =>
    Nat.rec (motive:=fun n => GeneratingIIDStage μ e β α n) S₀ next n
  let q : ℕ → X → A := fun n => (z n).partition
  let b : ℕ → ℝ := fun n => (z n).budget
  have hq (n : ℕ) : Measurable (q n) := (z n).measurable_partition
  have hbpos (n : ℕ) : 0 < b n := (z n).budget_pos
  have hb0 : b 0≤1 := (Classical.choose_spec hstart).2
  have hb (n : ℕ) : b (n+1)≤b n/2 := (Classical.choose_spec (hnext n (z n))).2
  have hpaint (n : ℕ) : μ.real {x | q n x≠q (n+1) x} < b n/2 :=
    (Classical.choose_spec (hnext n (z n))).1
  have hgeom (n : ℕ) : μ.real {x | q (n+1) x≠q n x} < ((1/2 : ℝ≥0)^n : ℝ) := by
    rw [disagreement_symm]
    have hdecay := budget_geometric_decay b hb 0 n
    simp only [Nat.zero_add] at hdecay
    have hbn : b n≤(1/2 : ℝ)^n := hdecay.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb0 (by positivity : 0≤(1/2 : ℝ)^n))
    have hh : b n/2≤b n := by linarith only [hbpos n]
    have hc := (hpaint n).trans_le (hh.trans hbn)
    simpa only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using hc
  obtain ⟨p,hp,hlim⟩ := exists_partition_limit μ q hq (geometric_repainting_summable μ q hgeom)
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  have hlaw (n : ℕ) : LawClose (μ.map (word e (q n) n))
      (Measure.pi (fun _ : Fin n => finiteWeightLaw β)) (1/(n+1 : ℝ)) := by
    rw [word_law_of_iid_factor μ e (q n) (hq n) (finiteWeightLaw β) (z n).iid]
    intro S hS
    simp only [sub_self,abs_zero]
    positivity
  have hcode := iid_law_of_growing_forward_words μ e he.toMeasurePreserving q hq p hp hlim
    (finiteWeightLaw β) (fun n => 1/(n+1 : ℝ)) tendsto_one_div_add_atTop_nhds_zero_nat hlaw
  refine ⟨p,hp,hcode,?_⟩
  intro n
  refine ⟨(z n).radius,(z n).decoder,?_⟩
  have htail := geometric_tail_limit μ q p hq hp hlim b (fun n => (hbpos n).le) hb (fun n => (hpaint n).le) n
  have hh := centered_decoder_perturbation μ e he.toMeasurePreserving (joinedBinary α (n+1))
    (q n) p (measurable_joinedBinary hα _) (hq n) hp (z n).radius (z n).decoder
  have hd := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg (2*(z n).radius+1) : (0 : ℝ)≤_)
  have he := (z n).error
  have hb := (z n).budget_small
  change _≤_+_ at hh
  change _ < (1/2 : ℝ)^(n+2) at he
  change (2*(z n).radius+1 : ℕ)*b n≤(1/2 : ℝ)^(n+2) at hb
  linarith only [hh,hd,he,hb]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

theorem binary_factors_of_joined_decoders (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (p : X → A) (α : ℕ → ℕ → X → Bool)
    (hdecode : ∀ n : ℕ,∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → ((Fin (n+1) × Fin (n+1)) → Bool),
      μ.real {x | joinedBinary α (n+1) x≠D (centeredWindow R (orbitName e p x))}≤2*(1/2 : ℝ)^(n+2)) :
    ∀ i j : ℕ,∀ ε : ℝ,0 < ε → ∃ g : (ℤ → A) → Bool,Measurable g ∧
      μ {x | g (orbitName e p x)≠α i j x} < ENNReal.ofReal ε := by
  intro i j ε hε
  have hz : Tendsto (fun n : ℕ => 2*(1/2 : ℝ)^(n+2)) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ) < 1)
    simpa using tendsto_const_nhds.mul (hp.comp (tendsto_add_atTop_nat 2))
  obtain ⟨n,hnε,hnlarge⟩ := ((hz.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop (max i j))).exists
  obtain ⟨R,D,hD⟩ := hdecode n
  have hi : i < n+1 := by omega
  have hj : j < n+1 := by omega
  let ij : Fin (n+1) × Fin (n+1) := (⟨i,hi⟩,⟨j,hj⟩)
  let g : (ℤ → A) → Bool := fun w => D (centeredWindow R w) ij
  have hg : Measurable g := (measurable_pi_apply ij).comp
    ((measurable_of_countable D).comp (measurable_centeredWindow R))
  have hsub : {x | g (orbitName e p x)≠α i j x}⊆
      {x | joinedBinary α (n+1) x≠D (centeredWindow R (orbitName e p x))} := by
    intro x hx heq
    have hh := congrFun heq ij
    exact hx hh.symm
  have hh : μ.real {x | g (orbitName e p x)≠α i j x} < ε :=
    ((measureReal_mono (μ:=μ) hsub).trans hD).trans_lt hnε
  refine ⟨g,hg,?_⟩
  rw [←ENNReal.ofReal_toReal (measure_ne_top μ {x | g (orbitName e p x)≠α i j x})]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hh
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

theorem bernoulli_model_of_generating_iid (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (p : X → A) (hp : Measurable p) (β : Measure A) [IsProbabilityMeasure β]
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => β)))
    (α : ℕ → ℕ → X → Bool) (hsep : Function.Injective (fun x => fun i j => α i j x))
    (hdecode : ∀ n : ℕ,∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → ((Fin (n+1) × Fin (n+1)) → Bool),
      μ.real {x | joinedBinary α (n+1) x≠D (centeredWindow R (orbitName e p x))}≤2*(1/2 : ℝ)^(n+2)) :
    ∃ βR : Measure ℝ,IsProbabilityMeasure βR ∧
      ∃ (encode : X → (ℤ → ℝ)) (decode : (ℤ → ℝ) → X),
        MeasurePreserving encode μ (Measure.infinitePi (fun _ : ℤ => βR)) ∧
        MeasurePreserving decode (Measure.infinitePi (fun _ : ℤ => βR)) μ ∧
        (∀ᵐ x ∂μ,decode (encode x)=x) ∧
        (∀ᵐ w ∂Measure.infinitePi (fun _ : ℤ => βR),encode (decode w)=w) ∧
        (∀ᵐ x ∂μ,encode (e x)=fun i : ℤ => encode x (i+1)) := by
  have hsep' : Function.Injective (fun x => fun i : ℕ × ℕ => α i.1 i.2 x) := by
    intro x y h
    apply hsep
    funext i j
    exact congrFun h (i,j)
  obtain ⟨d,hd,hl,_hr⟩ := measurable_decoder_of_generating_approximations μ (orbitName e p)
    (measurable_orbitName e hp) (fun i : ℕ × ℕ => α i.1 i.2) hsep'
    (fun i => binary_factors_of_joined_decoders μ e p α hdecode i.1 i.2)
  rw [hcode.map_eq] at hd
  let b : A → ℝ := embeddingReal A
  have hb : MeasurableEmbedding b := measurableEmbedding_embeddingReal A
  let βR := β.map b
  have : IsProbabilityMeasure βR := inferInstance
  let F : (ℤ → A) → (ℤ → ℝ) := fun w i => b (w i)
  let G : (ℤ → ℝ) → (ℤ → A) := fun w i => hb.invFun (w i)
  have hF : Measurable F := Measurable.of_eval (fun index => hb.measurable.comp (measurable_pi_apply index))
  have hG : Measurable G := Measurable.of_eval (fun index => hb.measurable_invFun.comp (measurable_pi_apply index))
  have hGF (w : ℤ → A) : G (F w)=w := funext (fun i => hb.leftInverse_invFun (w i))
  have hmpF : MeasurePreserving F (Measure.infinitePi (fun _ : ℤ => β))
      (Measure.infinitePi (fun _ : ℤ => βR)) :=
    ⟨hF,Measure.infinitePi_map_pi _ (fun _ => hb.measurable)⟩
  have hmpG : MeasurePreserving G (Measure.infinitePi (fun _ : ℤ => βR))
      (Measure.infinitePi (fun _ : ℤ => β)) := by
    refine ⟨hG,?_⟩
    rw [←hmpF.map_eq,Measure.map_map hG hF,show G ∘ F=id from funext hGF,Measure.map_id]
  let encode : X → (ℤ → ℝ) := F ∘ orbitName e p
  let decode : (ℤ → ℝ) → X := d ∘ G
  have hE : MeasurePreserving encode μ (Measure.infinitePi (fun _ : ℤ => βR)) := hmpF.comp hcode
  have hD : MeasurePreserving decode (Measure.infinitePi (fun _ : ℤ => βR)) μ := hd.comp hmpG
  have hleft : ∀ᵐ x ∂μ,decode (encode x)=x := by
    filter_upwards [hl] with x hx
    exact (congrArg d (hGF (orbitName e p x))).trans hx
  refine ⟨βR,inferInstance,encode,decode,hE,hD,hleft,?_,?_⟩
  · rw [←hE.map_eq]
    apply (ae_map_iff hE.measurable.aemeasurable
      (measurableSet_eq_fun (hE.measurable.comp hD.measurable) measurable_id)).mpr
    filter_upwards [hleft] with x hx
    exact congrArg encode hx
  · exact ae_of_all _ (fun x => funext (fun i => congrArg b (congrFun (orbitName_shift e p x) i)))

end HyperbolicCoding

end

end OAI
