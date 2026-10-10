import Mathlib
import OAI.Analysis.HardSphere.Geometry.SimplePath
import OAI.Analysis.HardSphere.Paths.SkeletonHitConstant

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice
attribute [local instance] Classical.propDecidable

lemma mem_axisSteps_of_between (a b k : ℤ) (hl : min a b ≤ k) (hu : k ≤ max a b) :
    k = a ∨ k ∈ axisSteps a b := by
  by_cases ha : k = a
  · exact Or.inl ha
  right
  unfold axisSteps
  split_ifs with h
  · simp only [min_eq_left h] at hl
    simp only [max_eq_right h] at hu
    apply List.mem_map.mpr
    refine ⟨(k-a-1).toNat,List.mem_range.mpr ?_,?_⟩ <;> omega
  · simp only [min_eq_right (by omega : b ≤ a)] at hl
    simp only [max_eq_left (by omega : b ≤ a)] at hu
    apply List.mem_map.mpr
    refine ⟨(a-k-1).toNat,List.mem_range.mpr ?_,?_⟩ <;> omega

lemma refineStep_final (a b : Vertex) : b ∈ refineStep a b := by
  have h2 := mem_axisSteps_of_between (a 2) (b 2) (b 2) (min_le_right _ _) (le_max_right _ _)
  have h1 := mem_axisSteps_of_between (a 1) (b 1) (b 1) (min_le_right _ _) (le_max_right _ _)
  have hb : ![b 0,b 1,b 2] = b := by ext j; fin_cases j <;> rfl
  rcases h2 with h2|h2
  · rcases h1 with h1|h1
    · have he : ![b 0,a 1,a 2] = b := by rw [← h1,← h2,hb]
      simp [refineStep,he]
    · apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨b 1,h1,by rw [← h2,hb]⟩
  · apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨b 2,h2,hb⟩

lemma refineStep_reach (a b : Vertex) (hfirst : b 0 = a 0+1) :
    withinReach nearestStep {x | x=a ∨ x∈refineStep a b} a b := by
  let D : Set Vertex := {x | x=a ∨ x∈refineStep a b}
  let u : Vertex := ![b 0,a 1,a 2]
  let v : Vertex := ![b 0,b 1,a 2]
  have hu : u∈D := Or.inr (by simp [refineStep,u])
  have h1 : withinReach nearestStep D a u := by
    apply Relation.ReflTransGen.single
    refine ⟨Or.inl rfl,hu,0,?_,?_⟩
    · simp only [u,Matrix.cons_val_zero,hfirst]; norm_num
    · intro j hj
      fin_cases j <;> simp_all [u]
  have h2 : withinReach nearestStep D u v := by
    have h := withinReach_axis u 1 (a 1) (b 1) (D:=D) ?_
    · convert h using 1 <;> ext j <;> fin_cases j <;> simp [u,v]
    intro k hk hk'
    rcases mem_axisSteps_of_between (a 1) (b 1) k hk hk' with rfl|hmem
    · change Function.update u 1 (u 1)∈D
      simpa only [Function.update_eq_self] using hu
    · right
      apply List.mem_append_left
      apply List.mem_append_right
      refine List.mem_map.mpr ⟨k,hmem,?_⟩
      ext j; fin_cases j <;> simp [u]
  have hv : v∈D := by
    rcases mem_axisSteps_of_between (a 1) (b 1) (b 1) (min_le_right _ _) (le_max_right _ _) with h|h
    · simpa [v,h] using hu
    · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨b 1,h,rfl⟩)))
  have h3 : withinReach nearestStep D v b := by
    have h := withinReach_axis v 2 (a 2) (b 2) (D:=D) ?_
    · convert h using 1 <;> ext j <;> fin_cases j <;> simp [v]
    intro k hk hk'
    rcases mem_axisSteps_of_between (a 2) (b 2) k hk hk' with rfl|hmem
    · change Function.update v 2 (v 2)∈D
      simpa only [Function.update_eq_self] using hv
    · right
      apply List.mem_append_right
      refine List.mem_map.mpr ⟨k,hmem,?_⟩
      ext j; fin_cases j <;> simp [v]
  exact h1.trans (h2.trans h3)

lemma baseVertex_mem_level (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) (t : ℕ) :
    baseVertex n d ω t ∈ levelList n d ω t := by
  cases t with
  | zero => simp [levelList]
  | succ t => exact refineStep_final _ _

lemma level_mem_occurrence (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) (t : ℕ) (ht : t ≤ n)
    {x : Vertex} (hx : x∈levelList n d ω t) : x∈occurrenceList n d ω :=
  List.mem_flatMap.mpr ⟨t,List.mem_range.mpr (by omega),hx⟩

lemma occurrence_reach (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) :
    withinReach nearestStep {x | x∈occurrenceList n d ω}
      (baseVertex n d ω 0) (baseVertex n d ω n) := by
  have H : ∀t, t≤n → withinReach nearestStep {x | x∈occurrenceList n d ω}
      (baseVertex n d ω 0) (baseVertex n d ω t) := by
    intro t
    induction t with
    | zero => intro _; exact .refl
    | succ t ih =>
      intro ht
      apply (ih (by omega)).trans
      apply withinReach_mono (D:={x | x=baseVertex n d ω t ∨ x∈refineStep
        (baseVertex n d ω t) (baseVertex n d ω (t+1))})
      · intro x hx
        rcases hx with rfl|hx
        · exact level_mem_occurrence n d ω t (by omega) (baseVertex_mem_level n d ω t)
        · exact level_mem_occurrence n d ω (t+1) ht hx
      · apply refineStep_reach
        simp [baseVertex]
  exact H n le_rfl

lemma nearestStep_add (v : Vertex) {x y : Vertex} (h : nearestStep x y) :
    nearestStep (v+x) (v+y) := by
  obtain ⟨j,hj,hr⟩ := h
  refine ⟨j,?_,fun i hi ↦ by simpa using congrArg (v i+·) (hr i hi)⟩
  simpa only [Pi.add_apply,add_sub_add_left_eq_sub] using hj

lemma withinReach_add (v : Vertex) {D : Set Vertex} {x y : Vertex}
    (h : withinReach nearestStep D x y) :
    withinReach nearestStep ((v+·) '' D) (v+x) (v+y) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact .refl
  | single h => exact .single ⟨mem_image_of_mem _ h.1,mem_image_of_mem _ h.2.1,nearestStep_add v h.2.2⟩
  | trans _ _ ih ih' => exact ih.trans ih'

def liftedSkeleton (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) : Finset Vertex :=
  ((occurrenceList n d ω).map (v+·)).toFinset

lemma liftedSkeleton_mem (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) {x : Vertex} :
    x∈liftedSkeleton n d v ω ↔ ∃y∈occurrenceList n d ω,v+y=x := by
  simp [liftedSkeleton]

lemma liftedSkeleton_reach (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) :
    withinReach nearestStep (↑(liftedSkeleton n d v ω))
      (v+baseVertex n d ω 0) (v+baseVertex n d ω n) := by
  apply withinReach_mono _ (withinReach_add v (occurrence_reach n d ω))
  rintro x ⟨y,hy,rfl⟩
  exact (liftedSkeleton_mem _ _ _ _).mpr ⟨y,hy,rfl⟩

lemma liftedSkeleton_initial (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) :
    v ∈ liftedSkeleton n d v ω := by
  exact (liftedSkeleton_mem _ _ _ _).mpr ⟨0,occurrenceList_initial n d ω,add_zero v⟩

lemma liftedSkeleton_final (n : ℕ) (hn : 0<n) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) :
    v+![(n:ℤ),d 0,d 1] ∈ liftedSkeleton n d v ω := by
  apply (liftedSkeleton_mem _ _ _ _).mpr
  refine ⟨baseVertex n d ω n,level_mem_occurrence n d ω n le_rfl
    (baseVertex_mem_level n d ω n),?_⟩
  rw [baseVertex_final n hn]

instance finsetVertexMeasurableSpace : MeasurableSpace (Finset Vertex) := ⊤
instance finsetVertexDiscreteMeasurableSpace : DiscreteMeasurableSpace (Finset Vertex) :=
  ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

@[fun_prop] lemma measurable_liftedSkeleton (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) :
    Measurable (liftedSkeleton n d v) :=
  (measurable_of_countable (fun xs : List Vertex ↦ (xs.map (v+·)).toFinset)).comp
    (measurable_occurrenceList n d)

def ConnectedSkeleton (v w : Vertex) :=
  {Γ : Finset Vertex // v∈Γ ∧ w∈Γ ∧ withinReach nearestStep (↑Γ) v w}

instance (v w : Vertex) : MeasurableSpace (ConnectedSkeleton v w) := inferInstanceAs
  (MeasurableSpace {Γ : Finset Vertex // v∈Γ ∧ w∈Γ ∧ withinReach nearestStep (↑Γ) v w})
instance (v w : Vertex) : Countable (ConnectedSkeleton v w) := inferInstanceAs
  (Countable {Γ : Finset Vertex // v∈Γ ∧ w∈Γ ∧ withinReach nearestStep (↑Γ) v w})
instance (v w : Vertex) : DiscreteMeasurableSpace (ConnectedSkeleton v w) := inferInstanceAs
  (DiscreteMeasurableSpace {Γ : Finset Vertex // v∈Γ ∧ w∈Γ ∧ withinReach nearestStep (↑Γ) v w})

lemma exists_connected_detour {K : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (B : Finset (DiscreteTorus K)) (v w : Vertex)
    (hB : acceptedEnvironment (R+2) B v w) (Γ : ConnectedSkeleton v w) :
    ∃ p : SimpleGoodPath B (torusProjection K v) (torusProjection K w),
      ∀ x∈p.val.support, x∈Γ.val.image (torusProjection K) ∨
        shellAttachment R B (Γ.val.image (torusProjection K)) x := by
  obtain ⟨p,hp,ha⟩ := periodic_good_detour hK R B
    (small_star_of_no_large (by omega) B hB.1) Γ.val Γ.property.1 Γ.property.2.1
    hB.2 Γ.property.2.2
  exact ⟨⟨p,hp,fun x hx ↦ (ha x hx).1⟩,fun x hx ↦ (ha x hx).2⟩

def connectedDetour {K : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (B : Finset (DiscreteTorus K)) (v w : Vertex)
    (hB : acceptedEnvironment (R+2) B v w) (Γ : ConnectedSkeleton v w) :
    SimplePath (torusProjection K v) (torusProjection K w) :=
  forgetGood (Classical.choose (exists_connected_detour hK R B v w hB Γ))

lemma connectedDetour_spec {K : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (B : Finset (DiscreteTorus K)) (v w : Vertex)
    (hB : acceptedEnvironment (R+2) B v w) (Γ : ConnectedSkeleton v w) :
    ∀ x∈(connectedDetour hK R B v w hB Γ).val.support, x∉B ∧
      (x∈Γ.val.image (torusProjection K) ∨ shellAttachment R B (Γ.val.image (torusProjection K)) x) := by
  intro x hx
  exact ⟨(Classical.choose (exists_connected_detour hK R B v w hB Γ)).property.2 x hx,
    Classical.choose_spec (exists_connected_detour hK R B v w hB Γ) x hx⟩

def connectedSample (n : ℕ) (hn : 0<n) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) :
    ConnectedSkeleton v (v+![(n:ℤ),d 0,d 1]) :=
  ⟨liftedSkeleton n d v ω,liftedSkeleton_initial n d v ω,liftedSkeleton_final n hn d v ω,
    by simpa only [baseVertex_initial,baseVertex_final n hn,add_zero] using
      liftedSkeleton_reach n d v ω⟩

@[fun_prop] lemma measurable_connectedSample (n : ℕ) (hn : 0<n) (d : Fin 2 → ℤ) (v : Vertex) :
    Measurable (connectedSample n hn d v) := by
  exact Measurable.subtype_mk (measurable_liftedSkeleton n d v)

def dyadicDetour {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) (ω : Noise) :
    SimplePath (torusProjection K v) (torusProjection K (v+![(n:ℤ),d 0,d 1])) :=
  connectedDetour hK R B v _ hB (connectedSample n hn d v ω)

@[fun_prop] lemma measurable_dyadicDetour {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) :
    Measurable (dyadicDetour hK R hn d v B hB) :=
  (measurable_of_countable (connectedDetour hK R B v _ hB)).comp
    (measurable_connectedSample n hn d v)

lemma dyadicDetour_spec {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) (ω : Noise) :
    ∀ x∈(dyadicDetour hK R hn d v B hB ω).val.support, x∉B ∧
      (x∈(liftedSkeleton n d v ω).image (torusProjection K) ∨
        shellAttachment R B ((liftedSkeleton n d v ω).image (torusProjection K)) x) :=
  connectedDetour_spec hK R B v _ hB _

def nominalBase (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) : Fin (n+1) → Vertex :=
  fun i ↦ v+baseVertex n d ω i.val

def projectedSkeleton (K n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) :
    Finset (DiscreteTorus K) := (liftedSkeleton n d v ω).image (torusProjection K)

lemma nominalBase_first (n : ℕ) (d : Fin 2 → ℤ) (v : Vertex) (ω : Noise) (i : Fin (n+1)) :
    nominalBase n d v ω i 0 = v 0+i.val := by rfl

lemma nominalBase_speed (n : ℕ) (hn : 0<n) (d : Fin 2 → ℤ) (hd : ∀j, |d j|≤n)
    (v : Vertex) (ω : Noise) (i j : Fin (n+1)) (k : Fin 3) :
    |nominalBase n d v ω i k-nominalBase n d v ω j k|≤3*|(i.val:ℤ)-j.val| := by
  simp only [nominalBase,Pi.add_apply,add_sub_add_left_eq_sub]
  have h := baseVertex_lipschitz n hn d hd ω i.val j.val (by omega) (by omega) k
  have hp := abs_nonneg ((i.val:ℤ)-j.val)
  omega

lemma projectedSkeleton_cover (K n : ℕ) (hn : 0<n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j|≤n) (v : Vertex) (ω : Noise) :
    ∀ x∈projectedSkeleton K n d v ω,
      ∃ i, torusNear K 3 (torusProjection K (nominalBase n d v ω i)) x := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨z,hz,rfl⟩ := (liftedSkeleton_mem _ _ _ _).mp hy
  obtain ⟨t,ht,hz⟩ := List.mem_flatMap.mp hz
  have ht' : t≤n := by have := List.mem_range.mp ht; omega
  refine ⟨⟨t,by omega⟩,projection_near (fun j ↦ ?_)⟩
  simp only [nominalBase,Pi.add_apply,add_sub_add_left_eq_sub]
  rw [abs_sub_comm]
  exact (levelList_mem n hn d hd ω t ht' z hz).2 j |>.trans (by norm_num)

lemma nominalBase_near_deviation {K n r : ℕ} (hn : 0<n) (hnK : 8*n≤K)
    (d : Fin 2 → ℤ) (v : Vertex) (ω ω' : Noise) (i : Fin (n+1))
    (hnear : torusNear K r (torusProjection K (nominalBase n d v ω i))
      (torusProjection K (nominalBase n d v ω' i))) :
    twoCopyDistance (min i.val (n-i.val)) (ω,ω') ≤ (r:ℝ)+1 := by
  have hsmall (j : Fin 3) : 2*|nominalBase n d v ω i j-nominalBase n d v ω' i j|≤(K:ℤ) := by
    have h := same_time_floor_bound n i.val (by omega) d ω ω' j
    have hn' : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hn
    have hK' : 8*(n:ℝ)≤(K:ℝ) := by exact_mod_cast hnK
    simp only [nominalBase,Pi.add_apply,add_sub_add_left_eq_sub]
    have hh : 2*|(baseVertex n d ω i.val j:ℝ)-(baseVertex n d ω' i.val j:ℝ)|≤(K:ℝ) := by linarith
    exact_mod_cast hh
  have hb := (torusNear_least_iff _ _ hsmall).mp hnear
  have hdist : periodicDistance K (baseVertex n d ω i.val) (baseVertex n d ω' i.val)≤(r:ℝ) := by
    apply periodicDistance_le _ _ _ _ (by positivity)
    intro j
    have h := hb j
    simp only [nominalBase,Pi.add_apply,add_sub_add_left_eq_sub] at h
    exact_mod_cast h
  exact (same_time_deviation_le K n hn hnK d ω ω' i.val (by omega)).trans (by linarith)

lemma dyadicDetour_charge {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) (ω ω' : Noise) :
    (simpleEncounter R (dyadicDetour hK R hn d v B hB ω)
      (dyadicDetour hK R hn d v B hB ω'):ℝ) ≤
    ((encounterSet (torusNear K R) (projectedSkeleton K n d v ω)
      (projectedSkeleton K n d v ω')).card:ℝ)+
      (encounterConstant R:ℝ)*∑ F∈badComponents (torusRangeGraph K (R+2)) B,
        if torusContact (R+2) F (projectedSkeleton K n d v ω) ∧
          torusContact (R+2) F (projectedSkeleton K n d v ω') then (F.card:ℝ) else 0 := by
  let u := dyadicDetour hK R hn d v B hB ω
  let u' := dyadicDetour hK R hn d v B hB ω'
  have h := torus_detour_charge R B (projectedSkeleton K n d v ω) (projectedSkeleton K n d v ω')
    u.val.support.toFinset u'.val.support.toFinset
    (fun x hx ↦ dyadicDetour_spec hK R hn d v B hB ω x (List.mem_toFinset.mp hx))
    (fun x hx ↦ dyadicDetour_spec hK R hn d v B hB ω' x (List.mem_toFinset.mp hx))
  have h' := h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (encounterConstant_detour R)) _)
  have hr := (Nat.cast_le (α:=ℝ)).mpr h'
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_sum,Finset.sum_filter,Nat.cast_ite,
    Nat.cast_zero,simpleEncounter,u,u'] using hr

lemma geometric_term_soft {B δ q : ℝ} (hB : 0<B) (hq : 0≤q)
    (hqsmall : q*Real.exp 1≤1/2) (m : ℕ) (hδ : δ≤B*((m+1:ℕ):ℝ)) :
    q^(m+1) ≤ (q*Real.exp 1*Real.exp (-δ/B))*(1/2:ℝ)^m := by
  have he : Real.exp (-((m+1:ℕ):ℝ))≤Real.exp (-δ/B) := by
    apply Real.exp_le_exp.mpr
    have h : δ/B≤((m+1:ℕ):ℝ) := (div_le_iff₀ hB).mpr (by simpa [mul_comm] using hδ)
    simpa only [neg_div] using neg_le_neg h
  have hcancel : Real.exp (-((m+1:ℕ):ℝ))*Real.exp (((m+1:ℕ):ℝ)) = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  calc
    q^(m+1) = q^(m+1)*(Real.exp (-((m+1:ℕ):ℝ))*Real.exp (((m+1:ℕ):ℝ))) := by rw [hcancel,mul_one]
    _ ≤ q^(m+1)*(Real.exp (-δ/B)*Real.exp (((m+1:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le) (pow_nonneg hq _)
    _ = (q*Real.exp 1*Real.exp (-δ/B))*(q*Real.exp 1)^m := by
      have hm : Real.exp (m:ℝ)=(Real.exp 1)^m := by rw [← Real.exp_nat_mul,mul_one]
      rw [Nat.cast_add,Nat.cast_one,Real.exp_add,hm,mul_pow,pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hq (Real.exp_pos _).le) hqsmall m)
      (by positivity)

lemma geometric_soft_sum {B δ q : ℝ} (hB : 0<B) (hq : 0≤q)
    (hqsmall : q*Real.exp 1≤1/2) (r : ℕ → ℝ) (hr : ∀m, r m≤B*((m+1:ℕ):ℝ)) :
    (∑' m : ℕ, if δ≤r m then (ENNReal.ofReal q)^(m+1) else 0)≤
      ENNReal.ofReal (2*q*Real.exp 1*Real.exp (-δ/B)) := by
  calc
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (q*Real.exp 1*Real.exp (-δ/B))*(1/2:ℝ≥0∞)^m := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs with h
      · have hb := ENNReal.ofReal_le_ofReal (geometric_term_soft hB hq hqsmall m (h.trans (hr m)))
        simpa only [ENNReal.ofReal_mul (by positivity : 0≤q*Real.exp 1*Real.exp (-δ/B)),
          ENNReal.ofReal_pow hq,ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/2),
          ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using hb
      · exact zero_le
    _ = ENNReal.ofReal (q*Real.exp 1*Real.exp (-δ/B))*2 := by
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
      norm_num
    _ = _ := by rw [← ENNReal.ofReal_ofNat 2,← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

lemma exp_soft_dominates_one {B δ : ℝ} (hB : 0<B) (hδ : δ≤B) :
    1≤Real.exp 1*Real.exp (-δ/B) := by
  rw [← Real.exp_add]
  apply Real.one_le_exp
  have h := (div_le_one hB).mpr hδ
  rw [neg_div]; linarith

def dyadicRadius (R : ℕ) : ℕ := candidateConstant (R+2)+4*(R+6)+1

lemma dyadicRadius_pos (R : ℕ) : 0<dyadicRadius R := by unfold dyadicRadius; omega

lemma dyadic_nominal_potential {K n : ℕ} [NeZero K] (R : ℕ)
    (hn : 0<n) (hnK : 8*n≤K) (d : Fin 2 → ℤ) (hd : ∀j, |d j|≤n)
    (v : Vertex) (ω ω' : Noise) (κ t : ℝ) (hκ : 0≤κ) (ht : 0≤t)
    (hq : ((candidateConstant (R+2):ℝ)*t)*Real.exp 1≤1/2) :
    κ*((encounterSet (torusNear K R) (projectedSkeleton K n d v ω)
      (projectedSkeleton K n d v ω')).card:ℝ)+
      (∑ F∈candidateSets (torusRangeGraph K (R+2)),
        if torusContact (R+2) F (projectedSkeleton K n d v ω) ∧
          torusContact (R+2) F (projectedSkeleton K n d v ω') then t^F.card else 0) ≤
    Real.exp 1*((encounterConstant R:ℝ)*κ+2*((candidateConstant (R+2):ℝ)*t))*
      ∑ j∈Finset.range (n+1), Real.exp
        (-twoCopyDistance (min j (n-j)) (ω,ω')/(dyadicRadius R:ℝ)) := by
  let U := nominalBase n d v ω
  let U' := nominalBase n d v ω'
  let Γ := projectedSkeleton K n d v ω
  let Γ' := projectedSkeleton K n d v ω'
  let A := candidateConstant (R+2)
  let b : ℝ := dyadicRadius R
  let δ (i : Fin (n+1)) := twoCopyDistance (min i.val (n-i.val)) (ω,ω')
  let f (i : Fin (n+1)) := Real.exp (-δ i/b)
  have hb : 0<b := by dsimp [b]; exact_mod_cast dyadicRadius_pos R
  have hfirst := nominalBase_first n d v ω
  have hfirst' := nominalBase_first n d v ω'
  have hspeed := nominalBase_speed n hn d hd v ω'
  have hcover := projectedSkeleton_cover K n hn d hd v ω
  have hcover' := projectedSkeleton_cover K n hn d hd v ω'
  have hnear (r : ℕ) (i : Fin (n+1)) : torusNear K r (torusProjection K (U i))
      (torusProjection K (U' i)) → δ i≤(r:ℝ)+1 :=
    nominalBase_near_deviation hn hnK d v ω ω' i
  have hN := nominal_encounter_bound R (by omega : 2*n≤K) U U' (v 0)
    hfirst hfirst' hspeed Γ Γ' hcover hcover'
  have hcard : ((Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
        (torusProjection K (U i)) (torusProjection K (U' i)))).card:ℝ) ≤ Real.exp 1*∑ i, f i := by
    have he : ((Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
        (torusProjection K (U i)) (torusProjection K (U' i)))).card:ℝ)=
        ∑ i : Fin (n+1), if torusNear K (4*(R+6)) (torusProjection K (U i))
          (torusProjection K (U' i)) then (1:ℝ) else 0 := by
      rw [← Finset.sum_filter]; simp
    rw [he,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · apply exp_soft_dominates_one hb
      exact (hnear _ i hi).trans (by
        dsimp [b]
        exact_mod_cast (show 4*(R+6)+1≤dyadicRadius R by unfold dyadicRadius; omega))
    · exact (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
  have hNr : κ*((encounterSet (torusNear K R) Γ Γ').card:ℝ)≤
      ((encounterConstant R:ℝ)*κ)*Real.exp 1*∑ i,f i := by
    have hh : ((encounterSet (torusNear K R) Γ Γ').card:ℝ)≤(encounterConstant R:ℝ)*
      ((Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
        (torusProjection K (U i)) (torusProjection K (U' i)))).card:ℝ) := by exact_mod_cast hN
    have hc := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg (encounterConstant R) : (0:ℝ)≤_)
    have hh' := mul_le_mul_of_nonneg_left (hh.trans hc) hκ
    nlinarith [hh']
  have hF := contact_candidate_potential (R+2) (by omega : 2*n≤K) U U' (v 0)
    hfirst hfirst' hspeed Γ Γ' hcover hcover' (ENNReal.ofReal t)
  have hFe : ENNReal.ofReal (∑ F∈candidateSets (torusRangeGraph K (R+2)),
      if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then t^F.card else 0)≤
      ∑ i : Fin (n+1), ENNReal.ofReal (2*((A:ℝ)*t)*Real.exp 1*f i) := by
    have hcast : ENNReal.ofReal (∑ F∈candidateSets (torusRangeGraph K (R+2)),
        if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then t^F.card else 0)=
        ∑ F∈candidateSets (torusRangeGraph K (R+2)),
          if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (ENNReal.ofReal t)^F.card else 0 := by
      rw [ENNReal.ofReal_sum_of_nonneg (by intro F _; split_ifs <;> positivity)]
      apply Finset.sum_congr rfl
      intro F _
      split_ifs <;> simp [ENNReal.ofReal_pow ht]
    rw [hcast]
    refine hF.trans (Finset.sum_le_sum fun i _ ↦ ?_)
    refine le_trans (ENNReal.tsum_le_tsum (fun m ↦ ?_))
      (geometric_soft_sum hb (mul_nonneg (Nat.cast_nonneg A) ht) hq
        (fun m ↦ (((12*(R+2)+24)*(m+1):ℕ):ℝ)+1) (fun m ↦ ?_))
    · by_cases h : torusNear K ((12*(R+2)+24)*(m+1))
          (torusProjection K (U i)) (torusProjection K (U' i))
      · rw [ite_eq_left h,ite_eq_left (hnear _ i h)]
        apply pow_le_pow_left'
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg A),ENNReal.ofReal_natCast]
        exact mul_le_mul' (by exact_mod_cast candidateConstant_growth (R+2)) le_rfl
      · rw [ite_eq_right h]; exact zero_le
    · have ha := candidateConstant_radius (R+2)
      have ha' : (12*(R+2)+24)*(m+1)+1≤dyadicRadius R*(m+1) := by
        dsimp [dyadicRadius]
        nlinarith
      dsimp [b]; exact_mod_cast ha'
  rw [← ENNReal.ofReal_sum_of_nonneg (by intro i _; dsimp [f]; positivity)] at hFe
  have hFr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hFe
  rw [← Finset.mul_sum] at hFr
  have hbound := add_le_add hNr hFr
  have heq : (∑ i : Fin (n+1),f i)=∑ j∈Finset.range (n+1), Real.exp
      (-twoCopyDistance (min j (n-j)) (ω,ω')/(dyadicRadius R:ℝ)) := by
    exact Fin.sum_univ_eq_sum_range
      (fun j ↦ Real.exp (-twoCopyDistance (min j (n-j)) (ω,ω')/(dyadicRadius R:ℝ))) (n+1)
  rw [heq] at hbound
  calc
    _ ≤ _ := hbound
    _ = _ := by dsimp [A]; ring

end HardSphere.DyadicSkeleton
end
end

end OAI
