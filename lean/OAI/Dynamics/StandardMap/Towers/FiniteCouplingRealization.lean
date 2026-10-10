import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coupling.AtomlessFinitePartition

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

omit [MeasurableSingletonClass B] in
theorem realize_finite_coupling_finite (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (p : X → A) (hp : Measurable p) (t : B → ℝ) (R : MatrixCoupling (mass μ p) t) :
    ∃ q : X → B,Measurable q ∧ ∀ a b,mass μ (fun x => (p x,q x)) (a,b)=R.weight a b := by
  have hh (a : A) : ∃ q : X → B,Measurable q ∧
      ∀ b,μ.real ((p ⁻¹' {a})∩q ⁻¹' {b})=R.weight a b :=
    exists_finite_random_variable μ (hp (measurableSet_singleton a)) (R.weight a) (R.nonneg a) (R.row a)
  choose q hq hqr using hh
  let q' : X → B := fun x => q (p x) x
  have hq' : Measurable q' := (measurable_from_prod_countable_right
    (f:=fun ax : A×X => q ax.1 ax.2) hq).comp (hp.prodMk measurable_id)
  refine ⟨q',hq',fun a b => ?_⟩
  have hset : (fun x => (p x,q' x)) ⁻¹' {(a,b)}=(p ⁻¹' {a})∩q a ⁻¹' {b} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,mem_inter_iff,q']
    constructor
    · rintro ⟨ha,hb⟩
      exact ⟨ha,by simpa only [ha] using hb⟩
    · rintro ⟨ha,hb⟩
      exact ⟨ha,by simpa only [ha] using hb⟩
  simpa only [mass,hset,Measure.real] using hqr a b

omit [StandardBorelSpace X] [Nonempty B] in
lemma integral_cost_of_realization (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) (q : X → B) (hq : Measurable q)
    {t : B → ℝ} (R : MatrixCoupling (mass μ p) t)
    (hR : ∀ a b,mass μ (fun x => (p x,q x)) (a,b)=R.weight a b) (c : A → B → ℝ) :
    (∫ x,c (p x) (q x) ∂μ)=R.cost c := by
  rw [←sum_mass_mul_integral μ (fun x => (p x,q x)) (hp.prodMk hq) (fun ab => c ab.1 ab.2)]
  simp only [Fintype.sum_prod_type,hR,MatrixCoupling.cost]

omit [StandardBorelSpace X] in
lemma finite_symbolCost_integral (μ : Measure X) [IsFiniteMeasure μ]
    (p q : X → A) (hp : Measurable p) (hq : Measurable q) :
    (∫ x,symbolCost (p x) (q x) ∂μ)=μ.real {x | p x≠q x} := by
  have hm : MeasurableSet {x | p x≠q x} := (measurableSet_eq_fun hp hq).compl
  have he : (fun x => symbolCost (p x) (q x))={x | p x≠q x}.indicator (fun _ : X => (1 : ℝ)) := by
    funext x
    by_cases hx : p x=q x <;> simp [symbolCost,hx]
  rw [he]
  change (∫ x,{x | p x≠q x}.indicator (fun _ : X => (1 : ℝ)) x ∂μ)=_
  rw [integral_indicator hm]
  simp

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

omit [MeasurableSingletonClass B] in
theorem exists_independent_finite_phase (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (p : X → A) (hp : Measurable p) :
    ∃ q : X → B,Measurable q ∧ ∀ b : B,
      (μ.restrict (q ⁻¹' {b})).map p=(Fintype.card B : ℝ≥0∞)⁻¹ • μ.map p := by
  have hn : (Fintype.card B : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  let R : MatrixCoupling (mass μ p) (fun _ : B => (μ univ).toReal/(Fintype.card B : ℝ)) := {
    weight := fun a _ => mass μ p a/(Fintype.card B : ℝ)
    nonneg := fun a _ => div_nonneg (mass_nonneg μ p a) (Nat.cast_nonneg _)
    row := fun a => by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      exact mul_div_cancel₀ _ hn
    col := fun _ => by rw [←Finset.sum_div,mass_sum μ p hp] }
  obtain ⟨q,hq,hpq⟩ := realize_finite_coupling_finite μ p hp _ R
  refine ⟨q,hq,fun b => ?_⟩
  apply Measure.ext_of_singleton
  intro a
  have hfin : (Fintype.card B : ℝ≥0∞)⁻¹≠⊤ := by
    exact ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero)
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top hfin (measure_ne_top _ _))).mp
  rw [Measure.map_apply hp (measurableSet_singleton a),Measure.restrict_apply (hp (measurableSet_singleton a)),
    ENNReal.toReal_mul,Measure.map_apply hp (measurableSet_singleton a)]
  have he : p ⁻¹' {a}∩q ⁻¹' {b}=(fun x => (p x,q x)) ⁻¹' {(a,b)} := by
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,Prod.mk.injEq]
  rw [he]
  change mass μ (fun x => (p x,q x)) (a,b)=_
  rw [hpq]
  change mass μ p a/(Fintype.card B : ℝ)=_
  rw [ENNReal.toReal_inv,ENNReal.toReal_natCast]
  exact div_eq_inv_mul _ _

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Nonempty B] in
lemma finite_phase_factor {C : Type*} [MeasurableSpace C]
    (μ : Measure X) (p : X → A) (hp : Measurable p) (q : X → B) (b : B)
    (h : (μ.restrict (q ⁻¹' {b})).map p=(Fintype.card B : ℝ≥0∞)⁻¹ • μ.map p)
    (g : A → C) (hg : Measurable g) :
    (μ.restrict (q ⁻¹' {b})).map (g ∘ p)=(Fintype.card B : ℝ≥0∞)⁻¹ • μ.map (g ∘ p) := by
  rw [←Measure.map_map hg hp,h,Measure.map_smul,Measure.map_map hg hp]
  exact hg.aemeasurable

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
variable {X I A : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [Countable I] [MeasurableSpace A]

local instance disjointIndexOptionMeasurableSpace : MeasurableSpace (Option I) := ⊤
local instance disjointIndexOptionMeasurableSingletonClass : MeasurableSingletonClass (Option I) :=
  ⟨fun _ => trivial⟩

noncomputable def disjointIndex (s : I → Set X) (x : X) : Option I :=
  by
    classical
    exact if h : ∃ i,x∈s i then some h.choose else none

omit [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] in
lemma disjointIndex_some (s : I → Set X) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (x : X) (i : I) : disjointIndex s x=some i ↔ x∈s i := by
  classical
  unfold disjointIndex
  split_ifs with h
  · constructor
    · intro he
      have hi : h.choose=i := Option.some.inj he
      exact hi ▸ h.choose_spec
    · intro hx
      congr 1
      by_contra hne
      exact Set.disjoint_left.mp (hd hne) h.choose_spec hx
  · have hx : x∉s i := fun hx => h ⟨i,hx⟩
    simp [hx]

omit [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] in
lemma disjointIndex_none (s : I → Set X) (x : X) :
    disjointIndex s x=none ↔ x∉⋃ i,s i := by
  classical
  simp only [disjointIndex]
  split_ifs with h
  · have hx : x∈⋃ i,s i := mem_iUnion.mpr h
    simp [hx]
  · have hx : x∉⋃ i,s i := by simpa only [mem_iUnion] using h
    simp [hx]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_disjointIndex (s : I → Set X) (hs : ∀ i,MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) : Measurable (disjointIndex s) := by
  apply measurable_to_countable'
  intro i
  cases i with
  | none =>
    have he : (disjointIndex s) ⁻¹' {none}=(⋃ i,s i)ᶜ := by
      ext x
      exact disjointIndex_none s x
    rw [he]
    exact (MeasurableSet.iUnion hs).compl
  | some i =>
    have he : (disjointIndex s) ⁻¹' {some i}=s i := by
      ext x
      exact disjointIndex_some s hd x i
    rw [he]
    exact hs i

noncomputable def disjointPaste (s : I → Set X) (f : I → X → A) (f₀ : X → A) (x : X) : A :=
  match disjointIndex s x with
  | none => f₀ x
  | some i => f i x

omit [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
  [MeasurableSpace A] in
lemma disjointPaste_on (s : I → Set X) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : I → X → A) (f₀ : X → A) {i : I} {x : X} (hx : x∈s i) :
    disjointPaste s f f₀ x=f i x := by
  unfold disjointPaste
  rw [(disjointIndex_some s hd x i).mpr hx]
omit [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
  [MeasurableSpace A] in
lemma disjointPaste_off (s : I → Set X) (f : I → X → A) (f₀ : X → A)
    {x : X} (hx : x∉⋃ i,s i) : disjointPaste s f f₀ x=f₀ x := by
  unfold disjointPaste
  rw [(disjointIndex_none s x).mpr hx]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_disjointPaste (s : I → Set X) (hs : ∀ i,MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (f : I → X → A)
    (hf : ∀ i,Measurable (f i)) (f₀ : X → A) (hf₀ : Measurable f₀) :
    Measurable (disjointPaste s f f₀) := by
  let F : Option I×X → A := fun ix => match ix.1 with
    | none => f₀ ix.2
    | some i => f i ix.2
  have hF : Measurable F := measurable_from_prod_countable_right (fun i => by
    cases i
    · exact hf₀
    · exact hf _)
  exact hF.comp ((measurable_disjointIndex s hs hd).prodMk measurable_id)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X : Type*} [MeasurableSpace X]

def entryLevel (T : X → X) (B : Set X) (n : ℕ) : Set X :=
  {x | T^[n] x∈B ∧ ∀ j<n,T^[j] x∉B}

lemma measurableSet_entryLevel {T : X → X} (hT : Measurable T) {B : Set X}
    (hB : MeasurableSet B) (n : ℕ) : MeasurableSet (entryLevel T B n) := by
  have heq : entryLevel T B n=(T^[n] ⁻¹' B) ∩ ⋂ j : ℕ,⋂ (_ : j<n),(T^[j] ⁻¹' B)ᶜ := by
    ext x
    simp only [entryLevel,mem_ofPred_eq,mem_inter_iff,mem_iInter,mem_compl_iff,mem_preimage]
  rw [heq]
  exact (hB.preimage (hT.iterate n)).inter
    (MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ => (hB.preimage (hT.iterate j)).compl)))

omit [MeasurableSpace X] in
lemma entryLevel_disjoint (T : X → X) (B : Set X) {n m : ℕ} (hnm : n≠m) :
    Disjoint (entryLevel T B n) (entryLevel T B m) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hnm with h|h
  · exact hy.2 n h hx.1
  · exact hx.2 m h hy.1

omit [MeasurableSpace X] in
lemma mem_entryLevel_iterate {T : X → X} {B : Set X} {n i : ℕ} (hi : i≤n)
    {x : X} (hx : x∈entryLevel T B n) : T^[i] x∈entryLevel T B (n-i) := by
  constructor
  · simpa only [←Function.iterate_add_apply,Nat.sub_add_cancel hi] using hx.1
  · intro j hj
    rw [←Function.iterate_add_apply]
    exact hx.2 (j+i) (by omega)

lemma mem_entryLevel_back (e : X ≃ᵐ X) {B : Set X} {n j : ℕ} {x : X}
    (hx : x∈entryLevel e B n) (hpast : ∀ i : ℕ, (0 < i) → (i ≤ j) → e.symm^[i] x∉B) :
    e.symm^[j] x∈entryLevel e B (n+j) := by
  have hi : Function.LeftInverse (e : X → X) e.symm := e.apply_symm_apply
  constructor
  · rw [Function.iterate_add_apply,hi.iterate j x]
    exact hx.1
  · intro l hl
    by_cases hj : j≤l
    · have heq : l=(l-j)+j := by omega
      rw [heq,Function.iterate_add_apply,hi.iterate j x]
      exact hx.2 (l-j) (by omega)
    · have hlj : j=l+(j-l) := by omega
      rw [hlj,Function.iterate_add_apply,hi.iterate l]
      exact hpast (j-l) (by omega) (by omega)

lemma ae_exists_entry {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) {B : Set X} (hB : MeasurableSet B) (hBp : 0<μ B) :
    ∀ᵐ x ∂μ,∃ n : ℕ,x∈entryLevel T B n := by
  classical
  let H : Set X := ⋃ n : ℕ,T^[n] ⁻¹' B
  have hH : MeasurableSet H := MeasurableSet.iUnion (fun n => hB.preimage (hT.measurable.iterate n))
  have hsub : T ⁻¹' H⊆H := by
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n+1,by simpa only [mem_preimage,Function.iterate_succ_apply] using hn⟩
  have heq : T ⁻¹' H =ᵐ[μ] H := ae_eq_of_ae_subset_of_measure_ge
    (Filter.Eventually.of_forall hsub) (hT.toMeasurePreserving.measure_preimage hH.nullMeasurableSet).ge
    (hH.preimage hT.measurable).nullMeasurableSet (measure_ne_top μ H)
  have hp : 0<μ H := hBp.trans_le (measure_mono (fun x hx => mem_iUnion.mpr ⟨0,hx⟩))
  have hfull : ∀ᵐ x ∂μ,x∈H := by
    rcases hT.quasiErgodic.ae_mem_or_ae_notMem₀ hH.nullMeasurableSet heq with hh|hh
    · exact hh
    · have : μ H=0 := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hh
      exact (hp.ne' this).elim
  filter_upwards [hfull] with x hx
  have hex : ∃ n : ℕ,T^[n] x∈B := mem_iUnion.mp hx
  exact ⟨Nat.find hex,Nat.find_spec hex,fun j hj => Nat.find_min hex hj⟩

def entryTowerBase (e : X ≃ᵐ X) (B : Set X) (N : ℕ) : Set X :=
  ⋃ q : ℕ,entryLevel e B (q*N+(N-1))

lemma measurableSet_entryTowerBase (e : X ≃ᵐ X) {B : Set X} (hB : MeasurableSet B) (N : ℕ) :
    MeasurableSet (entryTowerBase e B N) :=
  MeasurableSet.iUnion (fun _ => measurableSet_entryLevel e.measurable hB _)

lemma entryTower_disjoint (e : X ≃ᵐ X) (B : Set X) {N : ℕ} (hN : 0<N)
    (i j : Fin N) (hij : i≠j) :
    Disjoint ((e^[i.val]) '' entryTowerBase e B N) ((e^[j.val]) '' entryTowerBase e B N) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y,hy,rfl⟩ ⟨z,hz,heq⟩
  obtain ⟨q,hq⟩ := mem_iUnion.mp hy
  obtain ⟨r,hr⟩ := mem_iUnion.mp hz
  have hqi : i.val≤q*N+(N-1) := by omega
  have hrj : j.val≤r*N+(N-1) := by omega
  have hx := mem_entryLevel_iterate hqi hq
  have hz := mem_entryLevel_iterate hrj hr
  rw [heq] at hz
  have he : q*N+(N-1)-i.val=r*N+(N-1)-j.val := by
    by_contra hne
    exact Set.disjoint_left.mp (entryLevel_disjoint e B hne) hx hz
  have hi : (q*N+(N-1)-i.val)%N=N-1-i.val := by
    rw [Nat.add_sub_assoc (by omega : i.val≤N-1),Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  have hj : (r*N+(N-1)-j.val)%N=N-1-j.val := by
    rw [Nat.add_sub_assoc (by omega : j.val≤N-1),Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  have hh := congrArg (fun n => n%N) he
  rw [hi,hj] at hh
  exact hij (Fin.ext (by omega))

lemma entryTower_covers (e : X ≃ᵐ X) (B : Set X) {N : ℕ} (hN : 0<N) {x : X}
    (hx : ∃ n : ℕ,x∈entryLevel e B n)
    (hpast : ∀ i : ℕ, (0 < i) → (i < N) → e.symm^[i] x∉B) :
    x∈⋃ j : Fin N,(e^[j.val]) '' entryTowerBase e B N := by
  obtain ⟨n,hn⟩ := hx
  let j := N-1-n%N
  have hj : j<N := by dsimp [j]; omega
  have hnum : n+j=(n/N)*N+(N-1) := by
    have hd := Nat.mod_add_div n N
    have hm := Nat.mod_lt n hN
    rw [Nat.mul_comm] at hd
    dsimp [j]
    omega
  apply mem_iUnion.mpr
  refine ⟨⟨j,hj⟩,e.symm^[j] x,?_,?_⟩
  · apply mem_iUnion.mpr
    refine ⟨n/N,?_⟩
    rw [←hnum]
    exact mem_entryLevel_back e hn (fun i hi hij => hpast i hi (hij.trans_lt hj))
  · exact (show Function.LeftInverse (e : X → X) e.symm from e.apply_symm_apply).iterate j x

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology BigOperators
variable {X : Type*} [MeasurableSpace X]

lemma measurableSet_iterate_image (e : X ≃ᵐ X) {U : Set X} (hU : MeasurableSet U) (j : ℕ) :
    MeasurableSet ((e^[j]) '' U) := by
  have hh := (iterateEquiv e j).measurableSet_image.mpr hU
  simpa only [funext (iterateEquiv_apply e j)] using hh

lemma entryTower_error {μ : Measure X} [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : Ergodic e μ) {B : Set X} (hB : MeasurableSet B) (hBp : 0<μ B)
    {N : ℕ} (hN : 0<N) :
    μ (⋃ j : Fin N,(e^[j.val]) '' entryTowerBase e B N)ᶜ≤(N : ℝ≥0∞)*μ B := by
  classical
  have hc : (⋃ j : Fin N,(e^[j.val]) '' entryTowerBase e B N)ᶜ ≤ᵐ[μ]
      (⋃ j : Fin N,(e.symm^[j.val]) ⁻¹' B) := by
    filter_upwards [ae_exists_entry he hB hBp] with x hx hnot
    by_contra hbad
    apply hnot
    apply entryTower_covers e B hN hx
    intro i _hi hiN hmem
    exact hbad (mem_iUnion.mpr ⟨⟨i,hiN⟩,hmem⟩)
  calc
    _≤μ (⋃ j : Fin N,(e.symm^[j.val]) ⁻¹' B) := measure_mono_ae hc
    _≤∑' j : Fin N,μ ((e.symm^[j.val]) ⁻¹' B) := measure_iUnion_le _
    _=(N : ℝ≥0∞)*μ B := by
      simp only [((he.toMeasurePreserving.symm e).iterate _).measure_preimage hB.nullMeasurableSet,
        tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma exists_small_positive_marker [TopologicalSpace X] [SecondCountableTopology X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] {δ : ℝ≥0∞} (hδ : 0<δ) :
    ∃ B : Set X,MeasurableSet B ∧ 0<μ B ∧ μ B<δ := by
  obtain ⟨x,hx⟩ := μ.nonempty_support (by exact NeZero.ne μ)
  obtain ⟨B,hxB,hBm,hB⟩ := (Set.singleton x).exists_isOpen_lt_of_lt δ (by simpa using hδ : μ {x}<δ)
  exact ⟨B,hBm.measurableSet,(μ.mem_support_iff_forall x).mp hx B (hBm.mem_nhds (hxB (mem_singleton x))),hB⟩

theorem exists_rohlin_tower [TopologicalSpace X] [SecondCountableTopology X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular]
    (e : X ≃ᵐ X) (he : Ergodic e μ) {N : ℕ} (hN : 0<N) {ε : ℝ} (hε : 0<ε) :
    ∃ U : Set X,MeasurableSet U ∧
      (∀ i j : Fin N,i≠j → Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)) ∧
      μ (⋃ j : Fin N,(e^[j.val]) '' U)ᶜ<ENNReal.ofReal ε := by
  have hNc : (N : ℝ≥0∞)≠0 := by exact_mod_cast hN.ne'
  have hNf : (N : ℝ≥0∞)≠⊤ := by simp
  have hd : 0<ENNReal.ofReal ε/(N : ℝ≥0∞) := ENNReal.div_pos (ENNReal.ofReal_pos.mpr hε).ne' hNf
  obtain ⟨B,hB,hBp,hBs⟩ := exists_small_positive_marker μ hd
  refine ⟨entryTowerBase e B N,measurableSet_entryTowerBase e hB N,entryTower_disjoint e B hN,?_⟩
  apply (entryTower_error e he hB hBp hN).trans_lt
  rw [mul_comm]
  exact (ENNReal.lt_div_iff_mul_lt (Or.inl hNc) (Or.inl hNf)).mp hBs

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]

noncomputable def paintTower (e : X ≃ᵐ X) (U : Set X) (N : ℕ)
    (B : X → (Fin N → A)) (p : X → A) : X → A :=
  disjointPaste (fun i : Fin N => (e^[i.val]) '' U)
    (fun i x => B (e.symm^[i.val] x) i) p

omit [Fintype A] [MeasurableSingletonClass A] in
lemma measurable_paintTower (e : X ≃ᵐ X) {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    {B : X → (Fin N → A)} (hB : Measurable B) {p : X → A} (hp : Measurable p) :
    Measurable (paintTower e U N B p) :=
  measurable_disjointPaste (fun i : Fin N => (e^[i.val]) '' U) (fun i => measurableSet_iterate_image e hU i.val) hd _
    (fun i => ((measurable_pi_apply i).comp hB).comp (e.symm.measurable.iterate i.val)) _ hp

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma paintTower_level (e : X ≃ᵐ X) (U : Set X) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (B : X → (Fin N → A)) (p : X → A) {x : X} (hx : x∈U) (i : Fin N) :
    paintTower e U N B p (e^[i.val] x)=B x i := by
  unfold paintTower
  rw [disjointPaste_on _ hd _ _ (mem_image_of_mem _ hx)]
  rw [(show Function.LeftInverse e.symm (e : X → X) from e.symm_apply_apply).iterate i.val x]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma paintTower_word (e : X ≃ᵐ X) (U : Set X) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (B : X → (Fin N → A)) (p : X → A) {x : X} (hx : x∈U) :
    word e (paintTower e U N B p) N x=B x := by
  funext i
  exact paintTower_level e U N hd B p hx i

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma paintTower_off (e : X ≃ᵐ X) (U : Set X) (N : ℕ)
    (B : X → (Fin N → A)) (p : X → A) {x : X}
    (hx : x∉⋃ i : Fin N,(e^[i.val]) '' U) : paintTower e U N B p x=p x :=
  disjointPaste_off _ _ _ hx

lemma measure_iterate_image (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (U : Set X) (i : ℕ) : μ ((e^[i]) '' U)=μ U := by
  have hmp : MeasurePreserving (iterateEquiv e i).symm μ μ :=
    (show MeasurePreserving (iterateEquiv e i) μ μ from by
      simpa only [funext (iterateEquiv_apply e i)] using he.iterate i).symm _
  have hset : (e^[i]) '' U=(iterateEquiv e i).symm ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change (iterateEquiv e i).symm ((iterateEquiv e i) y)∈U
      simpa only [MeasurableEquiv.symm_apply_apply] using hy
    · intro hx
      refine ⟨(iterateEquiv e i).symm x,hx,?_⟩
      exact (iterateEquiv e i).apply_symm_apply x
  rw [hset]
  exact hmp.measure_preimage_equiv U

theorem paintTower_repaint (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    {B : X → (Fin N → A)} (hB : Measurable B) {p : X → A} (hp : Measurable p) :
    μ {x | p x≠paintTower e U N B p x}=
      ∑ i : Fin N,μ (U∩{x | p (e^[i.val] x)≠B x i}) := by
  let S (i : Fin N) : Set X := U∩{x | p (e^[i.val] x)≠B x i}
  have hS (i : Fin N) : MeasurableSet (S i) := hU.inter
    (measurableSet_eq_fun (hp.comp (e.measurable.iterate i.val)) ((measurable_pi_apply i).comp hB)).compl
  have himg (i : Fin N) : (e^[i.val]) '' S i⊆(e^[i.val]) '' U := image_mono inter_subset_left
  have hdisj : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' S i) ((e^[j.val]) '' S j)) :=
    fun i j hij => (hd hij).mono (himg i) (himg j)
  have hset : {x | p x≠paintTower e U N B p x}=⋃ i : Fin N,(e^[i.val]) '' S i := by
    ext x
    constructor
    · intro hx
      have hin : x∈⋃ i : Fin N,(e^[i.val]) '' U := by
        by_contra ho
        exact hx (paintTower_off e U N B p ho).symm
      obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hin
      refine mem_iUnion.mpr ⟨i,y,⟨hy,?_⟩,rfl⟩
      simpa only [mem_ofPred_eq,paintTower_level e U N hd B p hy i] using hx
    · intro hx
      obtain ⟨i,y,⟨hy,hbad⟩,rfl⟩ := mem_iUnion.mp hx
      simpa only [mem_ofPred_eq,paintTower_level e U N hd B p hy i] using hbad
  rw [hset,measure_iUnion hdisj (fun i => measurableSet_iterate_image e (hS i) i.val),tsum_fintype]
  exact Finset.sum_congr rfl (fun i _ => measure_iterate_image μ e he (S i) i.val)

end HyperbolicCoding

end
end

end OAI
