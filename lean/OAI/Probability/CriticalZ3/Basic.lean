import OAI.Probability.CriticalZ3.Model

namespace OAI

universe uE uOmega uV

open MeasureTheory ProbabilityTheory

namespace CriticalZ3

@[simp] theorem parameter_coe {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (parameter p : ℝ) = p := by
  simp [parameter, min_eq_right hp.2, max_eq_right hp.1]

@[simp] theorem parameter_zero : parameter 0 = 0 := Subtype.ext (by simp [parameter])
@[simp] theorem parameter_one : parameter 1 = 1 := Subtype.ext (by simp [parameter])

instance bondLaw_probability (p : ℝ) : IsProbabilityMeasure (bondLaw p) := by
  unfold bondLaw
  infer_instance

instance siteLaw_probability (p : ℝ) : IsProbabilityMeasure (siteLaw p) := by
  unfold siteLaw
  infer_instance

@[simp] theorem bondLaw_zero : bondLaw 0 = Measure.dirac (fun _ => false) := by
  simp [bondLaw]

@[simp] theorem siteLaw_zero : siteLaw 0 = Measure.dirac (fun _ => false) := by
  simp [siteLaw]

@[simp] theorem bondLaw_one : bondLaw 1 = Measure.dirac (fun _ => true) := by
  simp [bondLaw]

@[simp] theorem siteLaw_one : siteLaw 1 = Measure.dirac (fun _ => true) := by
  simp [siteLaw]

theorem nearestNeighbor_symm {x y : Vertex} (h : NearestNeighbor x y) :
    NearestNeighbor y x := by
  obtain ⟨i, h⟩ := h
  exact ⟨i, h.symm⟩

theorem bondOpen_symm {ω : BondConfig} {x y : Vertex} (h : BondOpen ω x y) :
    BondOpen ω y x := h.symm

theorem siteOpen_symm {ω : SiteConfig} {x y : Vertex} (h : SiteOpen ω x y) :
    SiteOpen ω y x := ⟨nearestNeighbor_symm h.1, h.2.2, h.2.1⟩

/-- Finite path length, used solely to prove measurability of reachability. -/
def PathLength {V : Type uV} (r : V → V → Prop) : ℕ → V → V → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, PathLength r n x z ∧ r z y

theorem pathLength_rtg {V : Type uV} {r : V → V → Prop} {n : ℕ} {x y : V}
    (h : PathLength r n x y) : Relation.ReflTransGen r x y := by
  induction n generalizing y with
  | zero => cases h; exact .refl
  | succ n ih =>
    obtain ⟨z, hz, hy⟩ := h
    exact (ih hz).tail hy

theorem rtg_iff_exists_pathLength {V : Type uV} {r : V → V → Prop} {x y : V} :
    Relation.ReflTransGen r x y ↔ ∃ n, PathLength r n x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail y z _ hy ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, y, hn, hy⟩
  · rintro ⟨n, hn⟩
    exact pathLength_rtg hn

theorem measurableSet_rtg {Ω : Type uOmega} {V : Type uV} [MeasurableSpace Ω] [Countable V]
    (r : Ω → V → V → Prop) (hr : ∀ x y, MeasurableSet {ω | r ω x y}) (x y : V) :
    MeasurableSet {ω | Relation.ReflTransGen (r ω) x y} := by
  have hpath (n : ℕ) (x y : V) : MeasurableSet {ω | PathLength (r ω) n x y} := by
    induction n generalizing x y with
    | zero => simp only [PathLength]; exact MeasurableSet.const _
    | succ n ih =>
      simp only [PathLength, Set.ofPred_exists]
      exact MeasurableSet.iUnion (fun z => (ih x z).inter (hr z y))
  simp only [rtg_iff_exists_pathLength, Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n => hpath n x y)

theorem measurableSet_bondOpen (x y : Vertex) :
    MeasurableSet {ω : BondConfig | BondOpen ω x y} := by
  unfold BondOpen
  simp only [Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion (fun i => (MeasurableSet.const _).inter
      (measurableSet_eq_fun (measurable_pi_apply (x, i)) measurable_const))
  · exact MeasurableSet.iUnion (fun i => (MeasurableSet.const _).inter
      (measurableSet_eq_fun (measurable_pi_apply (y, i)) measurable_const))

theorem measurableSet_siteOpen (x y : Vertex) :
    MeasurableSet {ω : SiteConfig | SiteOpen ω x y} := by
  exact (MeasurableSet.const _).inter
    ((measurableSet_eq_fun (measurable_pi_apply x) measurable_const).inter
      (measurableSet_eq_fun (measurable_pi_apply y) measurable_const))

theorem measurableSet_bondConnected (x y : Vertex) :
    MeasurableSet {ω : BondConfig | BondConnected ω x y} :=
  measurableSet_rtg BondOpen measurableSet_bondOpen x y

theorem measurableSet_siteConnected (x y : Vertex) :
    MeasurableSet {ω : SiteConfig | SiteConnected ω x y} :=
  (measurableSet_eq_fun (measurable_pi_apply x) measurable_const).inter
    (measurableSet_rtg SiteOpen measurableSet_siteOpen x y)

theorem infinite_iff_escape_finset {V : Type uV} (s : Set V) :
    s.Infinite ↔ ∀ t : Finset V, ∃ y ∈ s, y ∉ t := by
  classical
  constructor
  · exact fun hs t => hs.exists_notMem_finset t
  · intro h hs
    obtain ⟨y, hy, hn⟩ := h hs.toFinset
    exact hn (hs.mem_toFinset.mpr hy)

theorem measurableSet_infinite_fiber {Ω : Type uOmega} {V : Type uV} [MeasurableSpace Ω] [Countable V]
    (r : Ω → V → Prop) (hr : ∀ y, MeasurableSet {ω | r ω y}) :
    MeasurableSet {ω | {y | r ω y}.Infinite} := by
  simp only [infinite_iff_escape_finset, Set.mem_ofPred_eq]
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro t
  rw [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun y => (hr y).inter (MeasurableSet.const _))

theorem measurableSet_bondInfiniteAt (x : Vertex) : MeasurableSet (bondInfiniteAt x) :=
  measurableSet_infinite_fiber (fun ω y => BondConnected ω x y)
    (measurableSet_bondConnected x)

theorem measurableSet_siteInfiniteAt (x : Vertex) : MeasurableSet (siteInfiniteAt x) :=
  measurableSet_infinite_fiber (fun ω y => SiteConnected ω x y)
    (measurableSet_siteConnected x)

/-- An infinite nearest-neighbor ray, used to certify supercriticality at one. -/
def ray (x : Vertex) (n : ℕ) : Vertex :=
  fun j => x j + if j = 0 then (n : ℤ) else 0

@[simp] theorem ray_zero (x : Vertex) : ray x 0 = x := by
  ext j
  simp [ray]

@[simp] theorem ray_succ (x : Vertex) (n : ℕ) : ray x (n + 1) = step (ray x n) 0 := by
  ext j
  by_cases hj : j = 0
  · subst j; simp [ray, step]; omega
  · simp [ray, step, hj, Ne.symm hj]

theorem ray_injective (x : Vertex) : Function.Injective (ray x) := by
  intro n m h
  have he := congrFun h 0
  simp only [ray] at he
  exact Int.ofNat_inj.mp (add_left_cancel he)

theorem bondConnected_open_ray (x : Vertex) (n : ℕ) :
    BondConnected (fun _ => true) x (ray x n) := by
  induction n with
  | zero => rw [ray_zero]; exact .refl
  | succ n ih =>
    apply ih.tail
    exact Or.inl ⟨0, ray_succ x n, rfl⟩

theorem siteConnected_open_ray (x : Vertex) (n : ℕ) :
    SiteConnected (fun _ => true) x (ray x n) := by
  refine ⟨rfl, ?_⟩
  induction n with
  | zero => rw [ray_zero]
  | succ n ih =>
    apply ih.tail
    exact ⟨⟨0, Or.inl (ray_succ x n)⟩, rfl, rfl⟩

theorem bondCluster_open_infinite (x : Vertex) : (bondCluster (fun _ => true) x).Infinite :=
  (Set.infinite_range_of_injective (ray_injective x)).mono
    (by rintro y ⟨n, rfl⟩; exact bondConnected_open_ray x n)

theorem siteCluster_open_infinite (x : Vertex) : (siteCluster (fun _ => true) x).Infinite :=
  (Set.infinite_range_of_injective (ray_injective x)).mono
    (by rintro y ⟨n, rfl⟩; exact siteConnected_open_ray x n)

@[simp] theorem bondCluster_closed (x : Vertex) : bondCluster (fun _ => false) x = {x} := by
  ext y
  change Relation.ReflTransGen (BondOpen (fun _ => false)) x y ↔ y = x
  apply Relation.reflTransGen_iff_eq
  intro y h
  rcases h with ⟨i, _, hi⟩ | ⟨i, _, hi⟩ <;> cases hi

@[simp] theorem siteCluster_closed (x : Vertex) : siteCluster (fun _ => false) x = ∅ := by
  ext y
  simp [siteCluster, SiteConnected]

@[simp] theorem bondLaw_zero_infinite (x : Vertex) : bondLaw 0 (bondInfiniteAt x) = 0 := by
  rw [bondLaw_zero, Measure.dirac_apply' _ (measurableSet_bondInfiniteAt x)]
  simp [bondInfiniteAt]

@[simp] theorem siteLaw_zero_infinite (x : Vertex) : siteLaw 0 (siteInfiniteAt x) = 0 := by
  rw [siteLaw_zero, Measure.dirac_apply' _ (measurableSet_siteInfiniteAt x)]
  simp [siteInfiniteAt]

@[simp] theorem bondLaw_one_infinite (x : Vertex) : bondLaw 1 (bondInfiniteAt x) = 1 := by
  rw [bondLaw_one, Measure.dirac_apply' _ (measurableSet_bondInfiniteAt x)]
  simp [bondInfiniteAt, bondCluster_open_infinite]

@[simp] theorem siteLaw_one_infinite (x : Vertex) : siteLaw 1 (siteInfiniteAt x) = 1 := by
  rw [siteLaw_one, Measure.dirac_apply' _ (measurableSet_siteInfiniteAt x)]
  simp [siteInfiniteAt, siteCluster_open_infinite]

theorem bond_supercritical_nonempty :
    {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < bondLaw p (bondInfiniteAt 0)}.Nonempty :=
  ⟨1, by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, bondLaw_one_infinite]; trivial⟩

theorem site_supercritical_nonempty :
    {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < siteLaw p (siteInfiniteAt 0)}.Nonempty :=
  ⟨1, by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, siteLaw_one_infinite]; trivial⟩

theorem bondCritical_mem : bondCritical ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_csInf bond_supercritical_nonempty (fun _ hp => hp.1.1)
  · exact csInf_le ⟨0, fun _ hp => hp.1.1⟩ (by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, bondLaw_one_infinite]; trivial)

theorem siteCritical_mem : siteCritical ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_csInf site_supercritical_nonempty (fun _ hp => hp.1.1)
  · exact csInf_le ⟨0, fun _ hp => hp.1.1⟩ (by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, siteLaw_one_infinite]; trivial)

theorem bond_subcritical_origin {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hlt : p < bondCritical) : bondLaw p (bondInfiniteAt 0) = 0 := by
  by_contra h
  have hpos := bot_lt_iff_ne_bot.mpr h
  have hc : bondCritical ≤ p := csInf_le ⟨0, fun _ hr => hr.1.1⟩ ⟨hp, hpos⟩
  exact (not_le_of_gt hlt) hc

theorem site_subcritical_origin {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hlt : p < siteCritical) : siteLaw p (siteInfiniteAt 0) = 0 := by
  by_contra h
  have hpos := bot_lt_iff_ne_bot.mpr h
  have hc : siteCritical ≤ p := csInf_le ⟨0, fun _ hr => hr.1.1⟩ ⟨hp, hpos⟩
  exact (not_le_of_gt hlt) hc

/-! Finite alterations, tail invariance, and the infinite seed limit. -/

/-- A path with finitely many types of exceptional arrivals ends in the
unperturbed component of its starting point or of an exceptional vertex. -/
theorem rtg_covered_by_roots {V : Type uV} {r s : V → V → Prop} {F : Set V}
    (h : ∀ a b, r a b → s a b ∨ b ∈ F) {x y : V}
    (hxy : Relation.ReflTransGen r x y) :
    ∃ z ∈ insert x F, Relation.ReflTransGen s z y := by
  induction hxy with
  | refl => exact ⟨x, Set.mem_insert x F, .refl⟩
  | @tail a b _ hab ih =>
    rcases h a b hab with hs | hb
    · obtain ⟨z,hz,hza⟩ := ih
      exact ⟨z,hz,hza.tail hs⟩
    · exact ⟨b,Set.mem_insert_of_mem x hb,.refl⟩

theorem finite_components_of_finite_perturbation {V : Type uV} {r s : V → V → Prop}
    {F : Set V} (hF : F.Finite) (h : ∀ a b, r a b → s a b ∨ b ∈ F)
    (hs : ∀ x, {y | Relation.ReflTransGen s x y}.Finite) (x : V) :
    {y | Relation.ReflTransGen r x y}.Finite := by
  apply ((hF.insert x).biUnion (fun z _ => hs z)).subset
  intro y hy
  obtain ⟨z,hz,hzy⟩ := rtg_covered_by_roots h hy
  exact Set.mem_iUnion₂.mpr ⟨z,hz,hzy⟩

theorem infinite_component_of_perturbation {V : Type uV} {r s : V → V → Prop}
    {F : Set V} (hF : F.Finite) (h : ∀ a b, r a b → s a b ∨ b ∈ F)
    (hr : ∃ x, {y | Relation.ReflTransGen r x y}.Infinite) :
    ∃ x, {y | Relation.ReflTransGen s x y}.Infinite := by
  by_contra hn
  push Not at hn
  obtain ⟨x,hx⟩ := hr
  exact hx (finite_components_of_finite_perturbation hF h hn x)

/-- A negative coordinate step, needed only to list all finitely many neighbors. -/
def backstep (x : Vertex) (i : Fin 3) : Vertex := fun j => x j - if i = j then 1 else 0

@[simp] theorem step_backstep (x : Vertex) (i : Fin 3) : step (backstep x i) i = x := by
  funext j
  simp [step, backstep]

@[simp] theorem backstep_step (x : Vertex) (i : Fin 3) : backstep (step x i) i = x := by
  funext j
  simp [step, backstep]

theorem nearestNeighbor_iff_steps (x y : Vertex) :
    NearestNeighbor x y ↔ ∃ i, y = step x i ∨ y = backstep x i := by
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i,Or.inl hi⟩
    · exact ⟨i,Or.inr (by rw [hi,backstep_step])⟩
  · rintro ⟨i,hi | hi⟩
    · exact ⟨i,Or.inl hi⟩
    · exact ⟨i,Or.inr (by rw [hi,step_backstep])⟩

theorem finite_neighbors (x : Vertex) : {y | NearestNeighbor x y}.Finite := by
  apply ((Set.finite_range (step x)).union (Set.finite_range (backstep x))).subset
  intro y hy
  obtain ⟨i,hi | hi⟩ := (nearestNeighbor_iff_steps x y).mp hy
  · exact Or.inl ⟨i,hi.symm⟩
  · exact Or.inr ⟨i,hi.symm⟩

def bondExistsInfinite : Set BondConfig := {ω | ∃ x, (bondCluster ω x).Infinite}
def siteExistsInfinite : Set SiteConfig := {ω | ∃ x, (siteCluster ω x).Infinite}

theorem measurableSet_bondExistsInfinite : MeasurableSet bondExistsInfinite := by
  simpa only [bondExistsInfinite,bondInfiniteAt,Set.iUnion_ofPred] using
    (MeasurableSet.iUnion (fun x => measurableSet_bondInfiniteAt x))

theorem measurableSet_siteExistsInfinite : MeasurableSet siteExistsInfinite := by
  simpa only [siteExistsInfinite,siteInfiniteAt,Set.iUnion_ofPred] using
    (MeasurableSet.iUnion (fun x => measurableSet_siteInfiniteAt x))

theorem bondExistsInfinite_of_finite_alteration {ω ω' : BondConfig}
    (J : Finset Bond) (hagree : ∀ e ∉ J, ω' e = ω e) (hω : ω ∈ bondExistsInfinite) :
    ω' ∈ bondExistsInfinite := by
  let F : Set Vertex := ((fun e : Bond => e.1) '' (J : Set Bond)) ∪
    ((fun e : Bond => step e.1 e.2) '' (J : Set Bond))
  have hF : F.Finite := (J.finite_toSet.image _).union (J.finite_toSet.image _)
  apply infinite_component_of_perturbation hF (s := BondOpen ω') (r := BondOpen ω) _ hω
  intro a b hab
  rcases hab with ⟨i,hb,hi⟩ | ⟨i,ha,hi⟩
  · by_cases hj : (a,i) ∈ J
    · exact Or.inr (Or.inr ⟨(a,i),hj,hb.symm⟩)
    · exact Or.inl (Or.inl ⟨i,hb,(hagree (a,i) hj).trans hi⟩)
  · by_cases hj : (b,i) ∈ J
    · exact Or.inr (Or.inl ⟨(b,i),hj,rfl⟩)
    · exact Or.inl (Or.inr ⟨i,ha,(hagree (b,i) hj).trans hi⟩)

theorem bondExistsInfinite_finite_alteration {ω ω' : BondConfig}
    (J : Finset Bond) (hagree : ∀ e ∉ J, ω' e = ω e) :
    ω' ∈ bondExistsInfinite ↔ ω ∈ bondExistsInfinite :=
  ⟨bondExistsInfinite_of_finite_alteration J (fun e he => (hagree e he).symm),
    bondExistsInfinite_of_finite_alteration J hagree⟩

theorem siteOpen_open_left {ω : SiteConfig} {x y : Vertex} (h : SiteOpen ω x y) :
    ω x = true := h.2.1

theorem siteOpen_open_right {ω : SiteConfig} {x y : Vertex} (h : SiteOpen ω x y) :
    ω y = true := h.2.2

theorem siteRtg_from_closed {ω : SiteConfig} {x y : Vertex} (hx : ω x ≠ true)
    (h : Relation.ReflTransGen (SiteOpen ω) x y) : y = x := by
  induction h with
  | refl => rfl
  | @tail a b _ hab ih =>
    exact (hx (ih ▸ siteOpen_open_left hab)).elim

theorem siteInfinite_iff_rtg_infinite (ω : SiteConfig) (x : Vertex) :
    (siteCluster ω x).Infinite ↔ {y | Relation.ReflTransGen (SiteOpen ω) x y}.Infinite := by
  by_cases hx : ω x = true
  · simp only [siteCluster,SiteConnected,hx,true_and]
  · have he : {y | Relation.ReflTransGen (SiteOpen ω) x y} = {x} := by
      ext y
      exact ⟨siteRtg_from_closed hx, fun hy => by rw [Set.mem_singleton_iff.mp hy]; exact .refl⟩
    simp [siteCluster,SiteConnected,hx,he]

theorem siteExistsInfinite_of_finite_alteration {ω ω' : SiteConfig}
    (J : Finset Vertex) (hagree : ∀ e ∉ J, ω' e = ω e) (hω : ω ∈ siteExistsInfinite) :
    ω' ∈ siteExistsInfinite := by
  let F : Set Vertex := (J : Set Vertex) ∪ ⋃ x ∈ (J : Set Vertex), {y | NearestNeighbor x y}
  have hF : F.Finite := J.finite_toSet.union
    (J.finite_toSet.biUnion (fun x _ => finite_neighbors x))
  have hh : ∀ a b, SiteOpen ω a b → SiteOpen ω' a b ∨ b ∈ F := by
    intro a b hab
    by_cases ha : a ∈ J
    · exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨a,ha,hab.1⟩))
    by_cases hb : b ∈ J
    · exact Or.inr (Or.inl hb)
    · exact Or.inl ⟨hab.1,(hagree a ha).trans hab.2.1,(hagree b hb).trans hab.2.2⟩
  obtain ⟨x,hx⟩ := hω
  obtain ⟨y,hy⟩ := infinite_component_of_perturbation hF hh
    ⟨x,(siteInfinite_iff_rtg_infinite ω x).mp hx⟩
  exact ⟨y,(siteInfinite_iff_rtg_infinite ω' y).mpr hy⟩

theorem siteExistsInfinite_finite_alteration {ω ω' : SiteConfig}
    (J : Finset Vertex) (hagree : ∀ e ∉ J, ω' e = ω e) :
    ω' ∈ siteExistsInfinite ↔ ω ∈ siteExistsInfinite :=
  ⟨siteExistsInfinite_of_finite_alteration J (fun e he => (hagree e he).symm),
    siteExistsInfinite_of_finite_alteration J hagree⟩

open Filter
open scoped Topology

/-- Kolmogorov zero-one law in the finite-alteration form needed here. This
is proved for arbitrary independent bit coordinates, not assumed for clusters. -/
theorem zero_one_of_finite_alteration {E : Type uE} (μ : Measure (E → Bool))
    (hi : iIndepFun (fun e (ω : E → Bool) => ω e) μ)
    (A : Set (E → Bool)) (hA : MeasurableSet A)
    (hinv : ∀ (J : Finset E) (ω ω' : E → Bool),
      (∀ e ∉ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) : μ A = 0 ∨ μ A = 1 := by
  classical
  let M : E → MeasurableSpace (E → Bool) :=
    fun e => MeasurableSpace.comap (fun ω => ω e) inferInstance
  have hM : ∀ e, M e ≤ (inferInstance : MeasurableSpace (E → Bool)) := fun e => (measurable_pi_apply e).comap_le
  have hmi : iIndep M μ := (iIndepFun_iff_iIndep _ _ _).mp hi
  have htail : MeasurableSet[limsup M cofinite] A := by
    rw [Filter.limsup_eq_iInf_iSup]
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro s
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro hs
    have hc : sᶜ.Finite := Filter.mem_cofinite.mp hs
    let f : (E → Bool) → (E → Bool) := fun ω e => if e ∈ s then ω e else false
    have hf : @Measurable (E → Bool) (E → Bool) (⨆ e ∈ s, M e) inferInstance f := by
      apply @Measurable.of_eval (E → Bool) E (fun _ => Bool) (⨆ e ∈ s, M e) _ f
      intro e
      by_cases he : e ∈ s
      · simp only [f,ite_eq_left he]
        exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
      · simp only [f,ite_eq_right he]
        exact measurable_const
    have heq : f ⁻¹' A = A := by
      ext ω
      apply hinv hc.toFinset ω (f ω)
      intro e he
      have hes : e ∈ s := by simpa only [Set.Finite.mem_toFinset,Set.mem_compl_iff,not_not] using he
      simp only [f,ite_eq_left hes]
    rw [← heq]
    exact hf hA
  apply measure_zero_or_one_of_measurableSet_limsup hM hmi
    (p := fun s : Set E => s.Finite) (ns := fun J : Finset E => (J : Set E))
    (fun s hs => Filter.mem_cofinite.mpr (by simpa only [compl_compl] using hs)) _
    (fun J => J.finite_toSet) (fun e => ⟨{e},by simp⟩) htail
  intro J K
  exact ⟨J ∪ K, by simp, by simp⟩

theorem bondExistsInfinite_zero_one (p : ℝ) :
    bondLaw p bondExistsInfinite = 0 ∨ bondLaw p bondExistsInfinite = 1 := by
  apply zero_one_of_finite_alteration (bondLaw p)
    (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))
    bondExistsInfinite measurableSet_bondExistsInfinite
  intro J ω ω' h
  exact bondExistsInfinite_finite_alteration J h

theorem siteExistsInfinite_zero_one (p : ℝ) :
    siteLaw p siteExistsInfinite = 0 ∨ siteLaw p siteExistsInfinite = 1 := by
  apply zero_one_of_finite_alteration (siteLaw p)
    (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))
    siteExistsInfinite measurableSet_siteExistsInfinite
  intro J ω ω' h
  exact siteExistsInfinite_finite_alteration J h

theorem bondExistsInfinite_one {p : ℝ} (hp : 0 < bondLaw p (bondInfiniteAt 0)) :
    bondLaw p bondExistsInfinite = 1 := by
  apply (bondExistsInfinite_zero_one p).resolve_left
  have h : 0 < bondLaw p bondExistsInfinite := hp.trans_le
    (measure_mono (fun _ h => ⟨0,h⟩))
  exact ne_of_gt h

theorem siteExistsInfinite_one {p : ℝ} (hp : 0 < siteLaw p (siteInfiniteAt 0)) :
    siteLaw p siteExistsInfinite = 1 := by
  apply (siteExistsInfinite_zero_one p).resolve_left
  have h : 0 < siteLaw p siteExistsInfinite := hp.trans_le
    (measure_mono (fun _ h => ⟨0,h⟩))
  exact ne_of_gt h

def cube (c : Vertex) (n : ℕ) : Set Vertex :=
  Set.Icc (fun i => c i - (n : ℤ)) (fun i => c i + (n : ℤ))

theorem mem_cube {c x : Vertex} {n : ℕ} :
    x ∈ cube c n ↔ ∀ i, c i - (n : ℤ) ≤ x i ∧ x i ≤ c i + (n : ℤ) := by
  simp only [cube,Set.mem_Icc,Pi.le_def,forall_and]

theorem cube_finite (c : Vertex) (n : ℕ) : (cube c n).Finite := Set.finite_Icc _ _

theorem cube_mono (c : Vertex) : Monotone (cube c) := by
  intro m n h x hx
  rw [mem_cube] at hx ⊢
  intro i
  have hn : (m : ℤ) ≤ n := by exact_mod_cast h
  obtain ⟨h₁,h₂⟩ := hx i
  constructor <;> omega

theorem exists_mem_cube (c x : Vertex) : ∃ n, x ∈ cube c n := by
  let n := Finset.univ.sup (fun i : Fin 3 => (x i - c i).natAbs)
  refine ⟨n,mem_cube.mpr (fun i => ?_)⟩
  have hn : ((x i - c i).natAbs : ℤ) ≤ n := by
    exact_mod_cast (Finset.le_sup (f := fun i : Fin 3 => (x i - c i).natAbs) (Finset.mem_univ i))
  have hu := Int.le_natAbs (a := x i - c i)
  have hl := Int.le_natAbs (a := -(x i - c i))
  simp only [Int.natAbs_neg] at hl
  constructor <;> omega

@[simp] theorem iUnion_cube (c : Vertex) : (⋃ n, cube c n) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
  exact exists_mem_cube c x

def bondSeedInfinite (c : Vertex) (n : ℕ) : Set BondConfig :=
  {ω | ∃ x ∈ cube c n, ω ∈ bondInfiniteAt x}
def siteSeedInfinite (c : Vertex) (n : ℕ) : Set SiteConfig :=
  {ω | ∃ x ∈ cube c n, ω ∈ siteInfiniteAt x}

theorem bondSeedInfinite_mono (c : Vertex) : Monotone (bondSeedInfinite c) := by
  intro m n h ω ⟨x,hx,hi⟩
  exact ⟨x,cube_mono c h hx,hi⟩
theorem siteSeedInfinite_mono (c : Vertex) : Monotone (siteSeedInfinite c) := by
  intro m n h ω ⟨x,hx,hi⟩
  exact ⟨x,cube_mono c h hx,hi⟩

theorem measurableSet_bondSeedInfinite (c : Vertex) (n : ℕ) :
    MeasurableSet (bondSeedInfinite c n) := by
  simp only [bondSeedInfinite,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro x
  by_cases hx : x ∈ cube c n
  · simpa only [hx,Set.ofPred_true,Set.univ_inter,Set.ofPred_mem_eq] using measurableSet_bondInfiniteAt x
  · simp only [hx,Set.ofPred_false,Set.empty_inter,MeasurableSet.empty]
theorem measurableSet_siteSeedInfinite (c : Vertex) (n : ℕ) :
    MeasurableSet (siteSeedInfinite c n) := by
  simp only [siteSeedInfinite,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro x
  by_cases hx : x ∈ cube c n
  · simpa only [hx,Set.ofPred_true,Set.univ_inter,Set.ofPred_mem_eq] using measurableSet_siteInfiniteAt x
  · simp only [hx,Set.ofPred_false,Set.empty_inter,MeasurableSet.empty]

theorem iUnion_bondSeedInfinite (c : Vertex) :
    (⋃ n, bondSeedInfinite c n) = bondExistsInfinite := by
  ext ω
  simp only [Set.mem_iUnion,bondSeedInfinite,bondExistsInfinite,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n,x,_,hx⟩; exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    obtain ⟨n,hn⟩ := exists_mem_cube c x
    exact ⟨n,x,hn,hx⟩
theorem iUnion_siteSeedInfinite (c : Vertex) :
    (⋃ n, siteSeedInfinite c n) = siteExistsInfinite := by
  ext ω
  simp only [Set.mem_iUnion,siteSeedInfinite,siteExistsInfinite,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n,x,_,hx⟩; exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    obtain ⟨n,hn⟩ := exists_mem_cube c x
    exact ⟨n,x,hn,hx⟩

theorem bondSeedInfinite_tendsto_one {p : ℝ}
    (hp : 0 < bondLaw p (bondInfiniteAt 0)) (c : Vertex) :
    Tendsto (fun n => bondLaw p (bondSeedInfinite c n)) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := bondLaw p) (bondSeedInfinite_mono c)
  simpa only [iUnion_bondSeedInfinite,bondExistsInfinite_one hp,Function.comp_def] using h

theorem siteSeedInfinite_tendsto_one {p : ℝ}
    (hp : 0 < siteLaw p (siteInfiniteAt 0)) (c : Vertex) :
    Tendsto (fun n => siteLaw p (siteSeedInfinite c n)) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := siteLaw p) (siteSeedInfinite_mono c)
  simpa only [iUnion_siteSeedInfinite,siteExistsInfinite_one hp,Function.comp_def] using h

/-- The closed-cube vertex boundary used by the finite-scale argument. -/
def cubeBoundary (c : Vertex) (n : ℕ) : Set Vertex :=
  {x | x ∈ cube c n ∧ ∃ i, x i = c i - (n : ℤ) ∨ x i = c i + (n : ℤ)}

def Within {V : Type uV} (D : Set V) (r : V → V → Prop) (x y : V) : Prop :=
  x ∈ D ∧ y ∈ D ∧ r x y

theorem rtg_first_exit {V : Type uV} {r : V → V → Prop} {D : Set V} {x y : V}
    (h : Relation.ReflTransGen r x y) (hx : x ∈ D) (hy : y ∉ D) :
    ∃ a ∈ D, ∃ b ∉ D, Relation.ReflTransGen (Within D r) x a ∧ r a b := by
  have hh : ∀ {z}, Relation.ReflTransGen r x z →
      (z ∈ D ∧ Relation.ReflTransGen (Within D r) x z) ∨
      ∃ a ∈ D, ∃ b ∉ D, Relation.ReflTransGen (Within D r) x a ∧ r a b := by
    intro z hz
    induction hz with
    | refl => exact Or.inl ⟨hx,.refl⟩
    | @tail a b _ hab ih =>
      rcases ih with ⟨ha,hi⟩ | he
      · by_cases hb : b ∈ D
        · exact Or.inl ⟨hb,hi.tail ⟨ha,hb,hab⟩⟩
        · exact Or.inr ⟨a,ha,b,hb,hi,hab⟩
      · exact Or.inr he
  exact (hh h).resolve_left (fun h => hy h.1)

theorem nearestNeighbor_exit_boundary {c x y : Vertex} {n : ℕ}
    (hx : x ∈ cube c n) (hy : y ∉ cube c n) (hxy : NearestNeighbor x y) :
    x ∈ cubeBoundary c n := by
  refine ⟨hx,?_⟩
  rw [mem_cube] at hx hy
  push Not at hy
  obtain ⟨i,hi⟩ := hy
  obtain ⟨k,hk | hk⟩ := hxy
  · subst y
    by_cases hki : k = i
    · subst k
      refine ⟨i,Or.inr ?_⟩
      have hxi := hx i
      simp only [step,ite_true] at hi
      omega
    · have hxi := hx i
      simp only [step,ite_eq_right hki,add_zero] at hi
      omega
  · subst x
    by_cases hki : k = i
    · subst k
      refine ⟨i,Or.inl ?_⟩
      have hxi := hx i
      simp only [step,ite_true] at hxi ⊢
      omega
    · have hxi := hx i
      simp only [step,ite_eq_right hki,add_zero] at hxi
      omega

theorem bondOpen_neighbor {ω : BondConfig} {x y : Vertex} (h : BondOpen ω x y) :
    NearestNeighbor x y := by
  rcases h with ⟨i,hi,_⟩ | ⟨i,hi,_⟩
  · exact ⟨i,Or.inl hi⟩
  · exact ⟨i,Or.inr hi⟩

def bondSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) : Set BondConfig :=
  {ω | ∃ x ∈ cube c m, ∃ y ∈ T,
    Relation.ReflTransGen (Within (cube c n) (BondOpen ω)) x y}
def siteSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) : Set SiteConfig :=
  {ω | ∃ x ∈ cube c m, ω x = true ∧ ∃ y ∈ T,
    Relation.ReflTransGen (Within (cube c n) (SiteOpen ω)) x y}

/-- An infinite component supplies a finite path to the cube boundary;
this uses no uniqueness or unproved infinite-path theorem. -/
theorem bondSeedInfinite_subset_reachesBoundary (c : Vertex) {m n : ℕ} (hmn : m ≤ n) :
    bondSeedInfinite c m ⊆ bondSeedReaches c m n (cubeBoundary c n) := by
  rintro ω ⟨x,hxm,hx⟩
  have hnot : ¬bondCluster ω x ⊆ cube c n := fun h => hx ((cube_finite c n).subset h)
  obtain ⟨y,hy,hyn⟩ := Set.not_subset.mp hnot
  obtain ⟨a,ha,b,hb,hpath,hab⟩ := rtg_first_exit hy (cube_mono c hmn hxm) hyn
  exact ⟨x,hxm,a,nearestNeighbor_exit_boundary ha hb (bondOpen_neighbor hab),hpath⟩

theorem siteSeedInfinite_subset_reachesBoundary (c : Vertex) {m n : ℕ} (hmn : m ≤ n) :
    siteSeedInfinite c m ⊆ siteSeedReaches c m n (cubeBoundary c n) := by
  rintro ω ⟨x,hxm,hx⟩
  have hnot : ¬siteCluster ω x ⊆ cube c n := fun h => hx ((cube_finite c n).subset h)
  obtain ⟨y,hy,hyn⟩ := Set.not_subset.mp hnot
  obtain ⟨a,ha,b,hb,hpath,hab⟩ := rtg_first_exit hy.2 (cube_mono c hmn hxm) hyn
  exact ⟨x,hxm,hy.1,a,nearestNeighbor_exit_boundary ha hb hab.1,hpath⟩

end CriticalZ3

end OAI
