import OAI.Probability.FKMaps.Inventory
import OAI.Probability.FKMaps.TreeCode

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

instance : TopologicalSpace Letter := ⊥
instance : DiscreteTopology Letter := ⟨rfl⟩
instance : MeasurableSpace Letter := ⊤
instance : BorelSpace Letter := ⟨(borel_eq_top_of_discrete).symm⟩

structure Parameters where
  p : ℝ
  lower : 1/2<p
  upper : p<1

lemma Parameters.pos (P : Parameters) : 0<P.p := by linarith [P.lower]

def Parameters.ofQ (q : ℝ) (hq : 4<q) : Parameters where
  p := Real.sqrt q/(Real.sqrt q+2)
  lower := by
    have hs : 2<Real.sqrt q := (Real.lt_sqrt (by norm_num)).mpr (by nlinarith)
    exact (lt_div_iff₀ (by positivity)).mpr (by linarith)
  upper := by
    apply (div_lt_one (by positivity : 0<Real.sqrt q+2)).mpr
    linarith

def mass (P : Parameters) : Letter → ℝ
  | .burger _ => 1/4
  | .order none => P.p/2
  | .order (some _) => (1-P.p)/4

lemma mass_pos (P : Parameters) (a : Letter) : 0 < mass P a := by
  cases a with
  | burger b => norm_num [mass]
  | order a => cases a <;> dsimp [mass] <;> linarith [P.pos,P.upper]

lemma sum_letters {β : Type*} [AddCommMonoid β] (f : Letter → β) :
    ∑ a,f a = f (.burger false)+f (.burger true)+f (.order (some false))+
      f (.order (some true))+f (.order none) := by
  have h : (Finset.univ : Finset Letter)=
      {.burger false,.burger true,.order (some false),.order (some true),.order none} := by
    ext a; cases a with
    | burger b => cases b <;> simp
    | order a => cases a with
      | none => simp
      | some b => cases b <;> simp
  rw [h]
  simp [add_assoc]

lemma mass_sum (P : Parameters) : ∑ a,mass P a=1 := by
  rw [sum_letters]
  simp only [mass]
  ring

def law (P : Parameters) : PMF Letter := PMF.ofFintype (fun a => ENNReal.ofReal (mass P a)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (mass_pos P a).le),mass_sum]
  simp)

lemma law_singleton (P : Parameters) (a : Letter) :
    (law P).toMeasure {a}=ENNReal.ofReal (mass P a) := by
  simp [law]

lemma law_real_singleton (P : Parameters) (a : Letter) :
    (law P).toMeasure.real {a}=mass P a := by
  rw [measureReal_def,law_singleton,ENNReal.toReal_ofReal (mass_pos P a).le]

lemma integral_law (P : Parameters) (f : Letter → ℝ) :
    ∫ a,f a ∂(law P).toMeasure=∑ a,mass P a*f a := by
  rw [integral_fintype]
  · simp [law_real_singleton]
  · exact integrableOn_univ.mp (IntegrableOn.of_finite (Set.finite_univ) : IntegrableOn f Set.univ (law P).toMeasure)

lemma integral_increment (P : Parameters) :
    ∫ a,(a.increment:ℝ) ∂(law P).toMeasure=0 := by
  rw [integral_law,sum_letters]
  simp only [mass,Letter.increment,Int.cast_one,Int.cast_neg,mul_one,mul_neg]
  ring

def streamLaw (P : Parameters) (ι : Type*) : Measure (ι → Letter) :=
  Measure.infinitePi (fun _ : ι => (law P).toMeasure)
instance (P : Parameters) (ι : Type*) : IsProbabilityMeasure (streamLaw P ι) := by
  unfold streamLaw; infer_instance

def signSum (x : ℕ → Letter) (n : ℕ) : ℤ :=
  ∑ i∈Finset.range n,(x i).increment

lemma signSum_succ (x : ℕ → Letter) (n : ℕ) :
    signSum x (n+1)=signSum x n+(x n).increment := Finset.sum_range_succ _ _

lemma increment_bounds (a : Letter) : -1≤a.increment ∧ a.increment≤1 ∧ a.increment≠0 := by
  cases a <;> norm_num [Letter.increment]

/-- Recurrence of the actual raw-word signs. This uses the proved integer
martingale recurrence theorem, not a recurrence hypothesis. -/
theorem signs_hit_one (P : Parameters) :
    ∀ᵐ x ∂streamLaw P ℕ,∃ n,signSum x n=1 := by
  let X : ℕ → (ℕ → Letter) → ℝ := fun n x => -((x n).increment:ℝ)
  have hm (n : ℕ) : StronglyMeasurable (X n) := by
    exact (measurable_of_countable (fun a : Letter => -(a.increment:ℝ))).comp (measurable_pi_apply n) |>.stronglyMeasurable
  let ℱ := Filtration.natural X hm
  let S : ℕ → (ℕ → Letter) → ℤ := fun n x => 1-signSum x (n+1)
  have hInt : Integrable (fun a : Letter => -(a.increment:ℝ)) (law P).toMeasure :=
    integrableOn_univ.mp (IntegrableOn.of_finite (Set.finite_univ) :
      IntegrableOn (fun a : Letter => -(a.increment:ℝ)) Set.univ (law P).toMeasure)
  have hz : ∫ a,-(a.increment:ℝ) ∂(law P).toMeasure=0 := by
    rw [integral_neg,integral_increment,neg_zero]
  have hM : Martingale (fun n x => (S n x:ℝ)) ℱ (streamLaw P ℕ) := by
    have h := TreeCoding.independent_sum_martingale X hm
      (fun n => (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) n).integrable_comp_of_integrable hInt)
      (iIndepFun_infinitePi (X := fun _ (a : Letter) => -(a.increment:ℝ)) (fun _ => measurable_of_countable _))
      (fun n => by
        change (∫ x,((fun a : Letter => -(a.increment:ℝ)) (x n)) ∂streamLaw P ℕ)=0
        exact ((measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) n).hasLaw.integral_comp
          (f := fun a : Letter => -(a.increment:ℝ)) (measurable_of_countable _).aestronglyMeasurable).trans hz)
    convert (martingale_const ℱ (streamLaw P ℕ) (1:ℝ)).add h using 1
    ext n x
    simp [S,signSum,X,Finset.sum_neg_distrib,sub_eq_add_neg]
  have hS : StronglyAdapted ℱ S := by
    intro n
    have hh : Measurable[ℱ n] (fun x => Int.floor (S n x:ℝ)) :=
      Int.measurable_floor.comp (hM.stronglyMeasurable n).measurable
    simpa only [Int.floor_intCast] using hh.stronglyMeasurable
  have h₀ (x : ℕ → Letter) : 0≤S 0 x := by
    simpa [S,signSum,sub_nonneg] using (increment_bounds (x 0)).2.1
  have hstep (n : ℕ) (x : ℕ → Letter) : S n x-1≤S (n+1) x := by
    dsimp [S]
    rw [signSum_succ x (n+1)]
    have := (increment_bounds (x (n+1))).2.1
    omega
  have hjump : ∀ᵐ x ∂streamLaw P ℕ,∃ᶠ n in atTop,S (n+1) x≠S n x := by
    filter_upwards [] with x
    apply Filter.Eventually.frequently
    filter_upwards [] with n
    dsimp [S]
    rw [signSum_succ x (n+1)]
    have := (increment_bounds (x (n+1))).2.2
    omega
  filter_upwards [TreeCoding.integer_martingale_hits_zero (S := S) hS hM h₀ hstep hjump] with x hx
  obtain ⟨n,hn⟩ := hx
  exact ⟨n+1,by dsimp [S] at hn; omega⟩

end FKCRT.Inventory
end



noncomputable section
open scoped BigOperators
namespace FKCRT.Inventory

lemma pop_fixed (b : Bool) (s : List Bool) :
    pop (some b) s = if b∈s then some (s.erase b) else none := by
  induction s with
  | nil => simp [pop]
  | cons c s ih =>
    by_cases h : c=b
    · subst c; simp [pop,eligible]
    · have hc : b≠c := Ne.symm h
      simp [pop,eligible,h,hc,ih]

lemma pop_flexible (s : List Bool) : pop none s = s.tail?.map id := by
  cases s <;> simp [pop,eligible]

inductive TypedLetter where
  | burger : Bool → TypedLetter
  | order : Bool → TypedLetter
  deriving DecidableEq, Fintype

def TypedLetter.fixed : TypedLetter → Letter
  | .burger b => .burger b
  | .order b => .order (some b)

def stackTypedStep (s : List Bool) : TypedLetter → Option (List Bool)
  | .burger b => some (b::s)
  | .order b => pop (some b) s

def identifyOne (s : List Bool) : Letter → Option (TypedLetter × List Bool)
  | .burger b => some (.burger b,b::s)
  | .order (some b) => (pop (some b) s).map (fun t => (.order b,t))
  | .order none => match s with
      | [] => none
      | b::t => some (.order b,t)

def identify : List Letter → List Bool → Option (List TypedLetter × List Bool)
  | [],s => some ([],s)
  | a::w,s => do
      let (b,t) ← identifyOne s a
      let (v,r) ← identify w t
      pure (b::v,r)

def stackTypedRun : List TypedLetter → List Bool → Option (List Bool)
  | [],s => some s
  | a::w,s => (stackTypedStep s a).bind (stackTypedRun w)

lemma identifyOne_step {s t : List Bool} {a : Letter} {b : TypedLetter}
    (h : identifyOne s a = some (b,t)) : step ⟨[],s⟩ a = ⟨[],t⟩ ∧ stackTypedStep s b = some t := by
  cases a with
  | burger c => simp only [identifyOne,Option.some.injEq,Prod.mk.injEq] at h; rcases h with ⟨rfl,rfl⟩; exact ⟨rfl,rfl⟩
  | order x => cases x with
    | none => cases s with
      | nil => simp [identifyOne] at h
      | cons c r =>
        simp only [identifyOne,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        simp [step,stackTypedStep,pop,eligible]
    | some c =>
      cases hp : pop (some c) s with
      | none => simp [identifyOne,hp] at h
      | some r =>
        simp only [identifyOne,hp,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        simp [step,stackTypedStep,hp]

lemma identifyOne_none {s : List Bool} {a : Letter} (h : identifyOne s a = none) :
    (step ⟨[],s⟩ a).orders.length = 1 := by
  cases a with
  | burger b => simp [identifyOne] at h
  | order x => cases x with
    | none => cases s <;> simp_all [identifyOne,step,pop]
    | some b =>
      have hp : pop (some b) s = none := by simpa [identifyOne] using h
      simp [step,hp]

lemma identify_sound {w : List Letter} {s t : List Bool} {v : List TypedLetter}
    (h : identify w s=some (v,t)) :
    run w ⟨[],s⟩=⟨[],t⟩ ∧ stackTypedRun v s=some t ∧ v.length=w.length := by
  induction w generalizing s t v with
  | nil => simp only [identify,Option.some.injEq,Prod.mk.injEq] at h; rcases h with ⟨rfl,rfl⟩; exact ⟨rfl,rfl,rfl⟩
  | cons a w ih =>
    cases hx : identifyOne s a with
    | none => simp [identify,hx] at h
    | some x =>
      obtain ⟨b,r⟩ := x
      cases hy : identify w r with
      | none => simp [identify,hx,hy] at h
      | some y =>
        obtain ⟨u,z⟩ := y
        simp [identify,hx,hy] at h
        rcases h with ⟨rfl,rfl⟩
        obtain ⟨hr,ht,hl⟩ := ih hy
        obtain ⟨hs,hb⟩ := identifyOne_step hx
        exact ⟨by rw [run,hs,hr],by rw [stackTypedRun,hb,Option.bind_some,ht],by simp [hl]⟩

lemma identify_complete {w : List Letter} {s t : List Bool}
    (h : run w ⟨[],s⟩=⟨[],t⟩) : ∃ v, identify w s=some (v,t) := by
  induction w generalizing s t with
  | nil => cases h; exact ⟨[],rfl⟩
  | cons a w ih =>
    cases hx : identifyOne s a with
    | none =>
      have hle := orders_length_le_run w (step ⟨[],s⟩ a)
      rw [show run w (step ⟨[],s⟩ a)=⟨[],t⟩ from h, identifyOne_none hx] at hle
      simp at hle
    | some x =>
      obtain ⟨b,r⟩ := x
      have hs := (identifyOne_step hx).1
      rw [run,hs] at h
      obtain ⟨v,hv⟩ := ih h
      exact ⟨b::v,by simp [identify,hx,hv]⟩

lemma emptyReducing_iff_identify (w : List Letter) :
    EmptyReducing w ↔ ∃ v, identify w []=some (v,[]) := by
  constructor
  · exact identify_complete
  · rintro ⟨v,hv⟩; exact (identify_sound hv).1

lemma identify_fixed {w : List TypedLetter} {s t : List Bool} (h : stackTypedRun w s = some t) :
    identify (w.map TypedLetter.fixed) s = some (w,t) := by
  induction w generalizing s with
  | nil => simp only [stackTypedRun,Option.some.injEq] at h; subst s; rfl
  | cons a w ih =>
    cases hx : stackTypedStep s a with
    | none => simp [stackTypedRun,hx] at h
    | some r =>
      have hh : identifyOne s a.fixed=some (a,r) := by
        cases a <;> simp_all [stackTypedStep,TypedLetter.fixed,identifyOne]
      have hy := ih (by simpa only [stackTypedRun,hx,Option.bind_some] using h)
      simp [identify,hh,hy]

end FKCRT.Inventory
end


noncomputable section
open scoped BigOperators
namespace FKCRT.Inventory

/-- A fixed typed closing is flexible exactly when its type is the freshest
burger still present. This is a property of the identified word, not of marks. -/
def flexibleClosing (s : List Bool) : TypedLetter → Prop
  | .burger _ => False
  | .order b => s.head?=some b
instance (s : List Bool) (a : TypedLetter) : Decidable (flexibleClosing s a) := by
  cases a <;> unfold flexibleClosing <;> infer_instance

def origins (s : List Bool) (a : TypedLetter) : Finset Letter :=
  {a.fixed} ∪ if flexibleClosing s a then {.order none} else ∅

lemma identifyOne_typedStep {s t : List Bool} {a : TypedLetter}
    (h : stackTypedStep s a=some t) :
    ∀ x : Letter, identifyOne s x=some (a,t) ↔ x∈origins s a := by
  intro x
  cases a with
  | burger b =>
    simp only [stackTypedStep,Option.some.injEq] at h
    subst t
    cases x with
    | burger c => simp [identifyOne,origins,flexibleClosing,TypedLetter.fixed]
    | order c =>
      cases c with
      | none => cases s <;> simp [identifyOne,origins,flexibleClosing,TypedLetter.fixed]
      | some c => cases pop (some c) s <;> simp [identifyOne,origins,flexibleClosing,TypedLetter.fixed]
  | order b =>
    change pop (some b) s=some t at h
    cases x with
    | burger c =>
      by_cases he : flexibleClosing s (.order b) <;> simp [identifyOne,origins,he,TypedLetter.fixed]
    | order c => cases c with
      | none =>
        cases s with
        | nil => simp [pop] at h
        | cons d r =>
          by_cases hd : d=b
          · subst d
            have ht : r=t := by simpa [pop,eligible] using h
            subst t
            simp [identifyOne,origins,flexibleClosing,TypedLetter.fixed]
          · simp [identifyOne,origins,flexibleClosing,TypedLetter.fixed,hd]
      | some c =>
        by_cases hc : c=b
        · subst c; simp [identifyOne,h,origins,flexibleClosing,TypedLetter.fixed]
        · cases pop (some c) s <;> simp [identifyOne,origins,TypedLetter.fixed,hc] <;> split_ifs <;> simp

lemma identifyOne_unique {s t r : List Bool} {x : Letter} {a b : TypedLetter}
    (h : identifyOne s x=some (a,t)) (h' : identifyOne s x=some (b,r)) : a=b ∧ t=r := by
  simpa only [Option.some.injEq,Prod.mk.injEq] using h.symm.trans h'

def markings : List TypedLetter → List Bool → Finset (List Letter)
  | [],_ => {[]}
  | a::v,s => match stackTypedStep s a with
      | none => ∅
      | some t => (origins s a).biUnion (fun x => (markings v t).image (x::·))

lemma mem_markings {v : List TypedLetter} {s : List Bool} {w : List Letter} :
    w∈markings v s ↔ ∃ t, identify w s=some (v,t) := by
  induction v generalizing s w with
  | nil =>
    cases w with
    | nil => simp [markings,identify]
    | cons x w =>
      constructor
      · simp [markings]
      · rintro ⟨t,ht⟩
        have hh := (identify_sound ht).2.2
        simp at hh
  | cons a v ih =>
    cases hs : stackTypedStep s a with
    | none =>
      simp only [markings,hs,Finset.notMem_empty,false_iff,not_exists]
      intro t ht
      obtain ⟨_,hu,_⟩ := identify_sound ht
      simp [stackTypedRun,hs] at hu
    | some r =>
      constructor
      · simp only [markings,hs,Finset.mem_biUnion,Finset.mem_image]
        rintro ⟨x,hx,z,hz,rfl⟩
        obtain ⟨t,ht⟩ := ih.mp hz
        have hh := (identifyOne_typedStep hs x).mpr hx
        exact ⟨t,by simp [identify,hh,ht]⟩
      · rintro ⟨t,ht⟩
        cases w with
        | nil => simp [identify] at ht
        | cons x w =>
          cases hh : identifyOne s x with
          | none => simp [identify,hh] at ht
          | some z =>
            obtain ⟨b,u⟩ := z
            cases hw : identify w u with
            | none => simp [identify,hh,hw] at ht
            | some y =>
              obtain ⟨v',t'⟩ := y
              simp [identify,hh,hw] at ht
              obtain ⟨⟨rfl,rfl⟩,rfl⟩ := ht
              have hur := (identifyOne_step hh).2
              rw [hs,Option.some.injEq] at hur
              subst u
              rw [markings,hs]
              apply Finset.mem_biUnion.mpr
              refine ⟨x,(identifyOne_typedStep hs x).mp hh,?_⟩
              exact Finset.mem_image.mpr ⟨w,ih.mpr ⟨t',hw⟩,rfl⟩

def wordMass (P : Parameters) (w : List Letter) : ℝ := (w.map (mass P)).prod

def flexibleCount : List TypedLetter → List Bool → ℕ
  | [],_ => 0
  | a::v,s => match stackTypedStep s a with
      | none => 0
      | some t => (if flexibleClosing s a then 1 else 0)+flexibleCount v t

lemma origins_mass (P : Parameters) (s : List Bool) (a : TypedLetter) :
    (∑ x∈origins s a,mass P x) =
      mass P a.fixed * (1+2*P.p/(1-P.p))^(if flexibleClosing s a then 1 else 0) := by
  have hp : 1-P.p≠0 := ne_of_gt (by linarith [P.upper])
  by_cases h : flexibleClosing s a
  · cases a with
    | burger b => simp [flexibleClosing] at h
    | order b =>
      simp [origins,h,TypedLetter.fixed,mass]
      field_simp
      ring
  · simp [origins,h]

lemma markings_mass (P : Parameters) {v : List TypedLetter} {s t : List Bool}
    (h : stackTypedRun v s=some t) :
    (∑ w∈markings v s,wordMass P w) =
      wordMass P (v.map TypedLetter.fixed)*(1+2*P.p/(1-P.p))^(flexibleCount v s) := by
  induction v generalizing s with
  | nil => simp [markings,wordMass,flexibleCount]
  | cons a v ih =>
    cases hs : stackTypedStep s a with
    | none => simp [stackTypedRun,hs] at h
    | some r =>
      have hr : stackTypedRun v r=some t := by simpa only [stackTypedRun,hs,Option.bind_some] using h
      have hd : (origins s a : Set Letter).PairwiseDisjoint
          (fun x => (markings v r).image (x::·)) := by
        intro x _ y _ hxy
        apply Finset.disjoint_left.mpr
        intro w hx hy
        obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨z,_,he⟩ := Finset.mem_image.mp hy
        exact hxy (List.cons.inj he).1.symm
      rw [markings,hs,Finset.sum_biUnion hd]
      simp_rw [Finset.sum_image (fun x _ y _ hxy => List.cons.inj hxy |>.2)]
      simp only [wordMass,List.map_cons,List.prod_cons]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul,origins_mass]
      rw [show (∑ w∈markings v r,(w.map (mass P)).prod)=
          wordMass P (v.map TypedLetter.fixed)*(1+2*P.p/(1-P.p))^flexibleCount v r from ih hr]
      simp only [wordMass,flexibleCount,hs,pow_add]
      ring

end FKCRT.Inventory
end


noncomputable section
open scoped BigOperators
namespace FKCRT.Inventory

lemma stack_pop_fixed_count {b : Bool} {s t : List Bool} (h : pop (some b) s=some t) (c : Bool) :
    t.count c + (if b=c then 1 else 0) = s.count c := by
  rw [pop_fixed] at h
  split_ifs at h with hb
  · cases h
    by_cases hc : b=c
    · subst c
      simp only [ite_true,List.count_erase_self]
      have hp := List.count_pos_iff.mpr hb
      omega
    · simp [List.count_erase_of_ne (Ne.symm hc),hc]

lemma typedRun_append (v w : List TypedLetter) (s : List Bool) :
    stackTypedRun (v++w) s = (stackTypedRun v s).bind (stackTypedRun w) := by
  induction v generalizing s with
  | nil => rfl
  | cons a v ih =>
    simp only [List.cons_append,stackTypedRun]
    cases stackTypedStep s a <;> simp_all

lemma typedRun_balance {v : List TypedLetter} {s t : List Bool} (h : stackTypedRun v s=some t)
    (c : Bool) : t.count c+v.count (.order c)=s.count c+v.count (.burger c) := by
  induction v generalizing s with
  | nil => simp only [stackTypedRun,Option.some.injEq] at h; subst t; simp
  | cons a v ih =>
    cases a with
    | burger b =>
      have hh := ih (s := b::s) (by simpa only [stackTypedRun,stackTypedStep,Option.bind_some] using h)
      by_cases hb : b=c <;> simp_all
      omega
    | order b =>
      cases hs : pop (some b) s with
      | none => simp [stackTypedRun,stackTypedStep,hs] at h
      | some r =>
        have hh := ih (s := r) (by simpa only [stackTypedRun,stackTypedStep,hs,Option.bind_some] using h)
        have hr := stack_pop_fixed_count hs c
        by_cases hb : b=c <;> simp_all
        omega

lemma typedRun_prefix {v w : List TypedLetter} {s t : List Bool}
    (h : stackTypedRun w s=some t) (hv : v<+:w) : ∃ r,stackTypedRun v s=some r := by
  obtain ⟨z,rfl⟩ := hv
  rw [typedRun_append] at h
  cases hh : stackTypedRun v s with
  | none => simp [hh] at h
  | some r => exact ⟨r,rfl⟩

lemma typedRun_prefix_count {w : List TypedLetter} {s t : List Bool}
    (h : stackTypedRun w s=some t) {v : List TypedLetter} (hv : v<+:w) (c : Bool) :
    v.count (.order c)≤ s.count c+v.count (.burger c) := by
  obtain ⟨r,hr⟩ := typedRun_prefix h hv
  have hh := typedRun_balance hr c
  omega

/-- Successful typed words are exactly the shuffles of two nonnegative paths;
final emptiness will make both paths Dyck words. -/
lemma typedRun_exists_iff (w : List TypedLetter) (s : List Bool) :
    (∃ t,stackTypedRun w s=some t) ↔
      ∀ v,v<+:w → ∀ c : Bool,v.count (.order c)≤ s.count c+v.count (.burger c) := by
  constructor
  · rintro ⟨t,ht⟩ v hv c
    exact typedRun_prefix_count ht hv c
  · intro h
    induction w generalizing s with
    | nil => exact ⟨s,rfl⟩
    | cons a w ih =>
      have ha (c : Bool) := h [a] (by exact ⟨w,rfl⟩) c
      have hs : ∃ r,stackTypedStep s a=some r := by
        cases a with
        | burger b => exact ⟨b::s,rfl⟩
        | order b =>
          have hb : b∈s := by
            apply List.count_pos_iff.mp
            have hh := ha b
            exact lt_of_lt_of_le (by norm_num : (0:ℕ)<1) (by simpa using hh)
          exact ⟨s.erase b,by simp [stackTypedStep,pop_fixed,hb]⟩
      obtain ⟨r,hr⟩ := hs
      have hstep (c : Bool) : r.count c+[a].count (.order c)=s.count c+[a].count (.burger c) :=
        typedRun_balance (by simpa [stackTypedRun] using hr : stackTypedRun [a] s=some r) c
      obtain ⟨t,ht⟩ := ih r (by
        intro v hv c
        have hh := h (a::v) (by obtain ⟨z,rfl⟩ := hv; exact ⟨z,rfl⟩) c
        have hs := hstep c
        simp only [List.count_cons,List.count_nil] at hh hs
        omega)
      exact ⟨t,by simp only [stackTypedRun,hr,Option.bind_some,ht]⟩

def colorStep (c : Bool) : TypedLetter → Option DyckStep
  | .burger b => if b=c then some .U else none
  | .order b => if b=c then some .D else none

def colorWord (c : Bool) (w : List TypedLetter) : List DyckStep := w.filterMap (colorStep c)

lemma colorWord_counts (c : Bool) (w : List TypedLetter) :
    (colorWord c w).count .U=w.count (.burger c) ∧
    (colorWord c w).count .D=w.count (.order c) := by
  induction w with
  | nil => simp [colorWord]
  | cons a w ih =>
    cases a with
    | burger b => by_cases hb : b=c <;> simp_all [colorWord,colorStep]
    | order b => by_cases hb : b=c <;> simp_all [colorWord,colorStep]

/-- The precise source identification: each type separately is a genuine
Mathlib Dyck word, with no assumption about flexible marks. -/
def identifiedDyck {w : List TypedLetter} (h : stackTypedRun w []=some []) (c : Bool) : DyckWord where
  toList := colorWord c w
  count_U_eq_count_D := by
    have hh := typedRun_balance h c
    simpa only [colorWord_counts,List.count_nil,zero_add] using hh.symm
  count_D_le_count_U i := by
    obtain ⟨v,hv,he⟩ := List.prefix_filterMap_iff.mp (List.take_prefix i (colorWord c w))
    rw [he]
    change (colorWord c v).count .D≤(colorWord c v).count .U
    rw [(colorWord_counts c v).1,(colorWord_counts c v).2]
    simpa only [List.count_nil,zero_add] using typedRun_prefix_count h hv c

lemma typedRun_empty_iff (w : List TypedLetter) :
    stackTypedRun w []=some [] ↔
    (∀ c : Bool,w.count (.burger c)=w.count (.order c)) ∧
    (∀ v,v<+:w → ∀ c : Bool,v.count (.order c)≤v.count (.burger c)) := by
  constructor
  · intro h
    refine ⟨fun c => ?_,fun v hv c => ?_⟩
    · simpa only [List.count_nil,zero_add] using (typedRun_balance h c).symm
    · simpa only [List.count_nil,zero_add] using typedRun_prefix_count h hv c
  · rintro ⟨he,hp⟩
    obtain ⟨t,ht⟩ := (typedRun_exists_iff w []).mpr (by simpa using hp)
    have hz (c : Bool) : t.count c=0 := by
      have hh := typedRun_balance ht c
      rw [List.count_nil,zero_add,he c] at hh
      omega
    have htn : t=[] := by
      cases t with
      | nil => rfl
      | cons b t => have hh := hz b; simp at hh
    simpa only [htn] using ht

lemma fixed_word_mass (P : Parameters) (w : List TypedLetter) :
    wordMass P (w.map TypedLetter.fixed) =
      (1/4:ℝ)^(w.count (.burger false)+w.count (.burger true)) *
      ((1-P.p)/4)^(w.count (.order false)+w.count (.order true)) := by
  induction w with
  | nil => simp [wordMass]
  | cons a w ih =>
    cases a with
    | burger b => cases b <;> simp_all [wordMass,TypedLetter.fixed,mass,add_assoc,add_left_comm,add_comm] <;> ring
    | order b => cases b <;> simp_all [wordMass,TypedLetter.fixed,mass,add_assoc,add_left_comm,add_comm] <;> ring

lemma typedLetter_length (w : List TypedLetter) :
    w.length=w.count (.burger false)+w.count (.burger true)+w.count (.order false)+w.count (.order true) := by
  induction w with
  | nil => simp
  | cons a w ih => cases a with
    | burger b => cases b <;> simp_all <;> omega
    | order b => cases b <;> simp_all <;> omega

/-- Exact finite flexible-marking weight from words.tex (markedweight). The
remaining map activity correspondence must identify `flexibleCount`. -/
theorem empty_markings_mass (P : Parameters) {w : List TypedLetter}
    (h : stackTypedRun w []=some []) :
    (∑ v∈markings w [],wordMass P v) =
      ((1-P.p)/16)^(w.length/2)*(1+2*P.p/(1-P.p))^(flexibleCount w []) := by
  rw [markings_mass P h,fixed_word_mass]
  obtain ⟨he,_⟩ := (typedRun_empty_iff w).mp h
  have hl := typedLetter_length w
  have hf := he false
  have ht := he true
  have hh : w.length/2=w.count (.order false)+w.count (.order true) := by omega
  rw [hf,ht,hh,← mul_pow]
  congr 2
  ring

end FKCRT.Inventory
end

end OAI
