import Mathlib
import OAI.Probability.ThorpRouting.Contact.ModifiedStageEquiv

namespace OAI

namespace ThorpNine.Contact

namespace Thorp.SparseContact
open scoped BigOperators Classical

noncomputable def typedMarks {N : Type*} [Fintype N] (d : ℕ)
    (A : N → Finset (Card d)) (ω : N → (SwitchIndex d → Bool)) : Finset (N × Card d) :=
  typedSet (fun t => butterflyMarks d (A t) (ω t))

lemma typedMarks_card {N : Type*} [Fintype N] (d : ℕ)
    (A : N → Finset (Card d)) (ω : N → (SwitchIndex d → Bool)) :
    (typedMarks d A ω).card = ∑ t, (A t).card := by
  classical
  rw [typedMarks, typedSet_card]
  apply Finset.sum_congr rfl
  intro t _
  exact Finset.card_image_of_injective _ (butterflyPerm d (decodeButterfly d (ω t))).injective

lemma typedMarks_inclusion {N : Type*} [Fintype N] (d : ℕ)
    (A : N → Finset (Card d)) (D : Finset (N × Card d)) :
    inclusionMoment (typedMarks d A) D ≤
      ∏ v ∈ D, ((A v.1).card:ℝ)/(2:ℝ)^d := by
  classical
  have he : inclusionMoment (typedMarks d A) D =
      ∏ t, inclusionMoment (butterflyMarks d (A t)) (fiber D t) := by
    rw [inclusionMoment_eq]
    have hh (ω : N → (SwitchIndex d → Bool)) :
        (if D ⊆ typedMarks d A ω then (1:ℝ) else 0) =
        ∏ t, if fiber D t ⊆ butterflyMarks d (A t) (ω t) then (1:ℝ) else 0 := by
      rw [Fintype.prod_boole]
      simp only [typedMarks, subset_typedSet]
    rw [finiteMean_congr hh]
    simp only [inclusionMoment_eq]
    exact finiteMean_pi_prod (ι := N) (Ω := fun _ => SwitchIndex d → Bool)
      (fun t (ω : SwitchIndex d → Bool) =>
        if fiber D t ⊆ butterflyMarks d (A t) ω then (1:ℝ) else 0)
  have hprod : (∏ v ∈ D, ((A v.1).card:ℝ)/(2:ℝ)^d) =
      ∏ t, ∏ x ∈ fiber D t, ((A t).card:ℝ)/(2:ℝ)^d := by
    conv_lhs => rw [← typedSet_fiber D]
    exact typedSet_prod _ _
  rw [he, hprod]
  apply Finset.prod_le_prod₀
  · intro t _; exact inclusionMoment_nonneg _ _
  · intro t _
    simpa only [Finset.prod_const] using butterflyMarks_inclusion d (A t) (fiber D t)

noncomputable def returnRoute {N : Type*} (d : ℕ) (b : N → Butterfly d)
    (v : N × Card d) : Finset (SwitchIndex d) :=
  routeDomain d ((butterflyPerm d (b v.1)).symm v.2) v.2

noncomputable def returnGraph {N : Type*} (d : ℕ) (b : N → Butterfly d) :
    SimpleGraph (N × Card d) where
  Adj v w := v ≠ w ∧ ¬Disjoint (returnRoute d b v) (returnRoute d b w)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hh => h.2 hh.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma returnRoute_card {N : Type*} (d : ℕ) (b : N → Butterfly d) (v : N × Card d) :
    (returnRoute d b v).card = d := card_routeDomain _ _ _

lemma mem_returnRoute {N : Type*} (d : ℕ) (b : N → Butterfly d)
    (t : N) (y : Card d) (i : SwitchIndex d) :
    i ∈ returnRoute d b (t,y) ↔
      y = butterflyPerm d (b t) (switchUsers d (b t) i).1 ∨
      y = butterflyPerm d (b t) (switchUsers d (b t) i).2 := by
  have h := mem_routeDomain_iff_user d (b t) ((butterflyPerm d (b t)).symm y) i
  simpa only [Equiv.apply_symm_apply, returnRoute, Equiv.eq_symm_apply, eq_comm] using h

lemma returnRoute_incidence {N : Type*} [Fintype N] (d : ℕ) (b : N → Butterfly d)
    (p : N → ℝ) (i : SwitchIndex d) :
    (∑ v : N × Card d, if i ∈ returnRoute d b v then p v.1 else 0) =
      2 * ∑ t, p t := by
  classical
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hne : butterflyPerm d (b t) (switchUsers d (b t) i).1 ≠
      butterflyPerm d (b t) (switchUsers d (b t) i).2 :=
    (butterflyPerm d (b t)).injective.ne (switchUsers_ne d (b t) i)
  simp only [mem_returnRoute]
  have he (y : Card d) :
      (if y = butterflyPerm d (b t) (switchUsers d (b t) i).1 ∨
        y = butterflyPerm d (b t) (switchUsers d (b t) i).2 then p t else 0) =
      (if y = butterflyPerm d (b t) (switchUsers d (b t) i).1 then p t else 0) +
      (if y = butterflyPerm d (b t) (switchUsers d (b t) i).2 then p t else 0) := by
    split_ifs <;> simp_all
  simp only [he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma returnGraph_degree {N : Type*} [Fintype N] (d : ℕ) (b : N → Butterfly d)
    (p : N → ℝ) (hp : ∀ t, 0 ≤ p t) (v : N × Card d) :
    (∑ w, if (returnGraph d b).Adj v w then p w.1 else 0) ≤
      2*d*∑ t, p t := by
  classical
  calc
    _ ≤ ∑ w, ∑ i ∈ returnRoute d b v, if i ∈ returnRoute d b w then p w.1 else 0 := by
      apply Finset.sum_le_sum
      intro w _
      split_ifs with h
      · obtain ⟨i, hi, hw⟩ := Finset.not_disjoint_iff.mp h.2
        have hh := Finset.single_le_sum
          (f := fun i => if i ∈ returnRoute d b w then p w.1 else 0)
          (fun i _ => by split_ifs; exact hp _; exact le_rfl) hi
        simpa only [ite_eq_left hw] using hh
      · exact Finset.sum_nonneg (fun i _ => by split_ifs; exact hp _; exact le_rfl)
    _ = ∑ i ∈ returnRoute d b v, ∑ w, if i ∈ returnRoute d b w then p w.1 else 0 :=
      Finset.sum_comm
    _ = _ := by simp only [returnRoute_incidence, Finset.sum_const, returnRoute_card,
        nsmul_eq_mul]; ring

lemma typed_weight_sum {N : Type*} [Fintype N] (d : ℕ)
    (A : N → Finset (Card d)) :
    (∑ v : N × Card d, ((A v.1).card:ℝ)/(2:ℝ)^d) = ∑ t, ((A t).card:ℝ) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.sum_const, Finset.card_univ, card_positions, Nat.cast_pow,
    Nat.cast_ofNat, nsmul_eq_mul]
  field_simp

lemma mixed_return_noIsolated {N : Type*} [Fintype N] (d : ℕ)
    (A : N → Finset (Card d)) (b : N → Butterfly d) (k : ℕ)
    (hk : ∑ t, (A t).card = k)
    (hδ : 0 < 2*(d:ℝ)*k/(2:ℝ)^d) (hδ1 : 2*(d:ℝ)*k/(2:ℝ)^d ≤ 1) :
    finiteMean (fun ω : N → (SwitchIndex d → Bool) =>
      if NoIsolated (returnGraph d b) (typedMarks d A ω) then (1:ℝ) else 0) ≤
      (2*(d:ℝ)*k/(2:ℝ)^d)^((k:ℝ)/2) * Real.exp (Real.exp 1*k) := by
  have hs : (∑ t, ((A t).card:ℝ)) = k := by exact_mod_cast hk
  have hm := noIsolated_probability_le (returnGraph d b) (typedMarks d A) k
    (fun ω => (typedMarks_card d A ω).trans hk)
    (fun v => ((A v.1).card:ℝ)/(2:ℝ)^d) (fun v => by positivity)
    (typedMarks_inclusion d A) _ hδ hδ1
    (fun v => (returnGraph_degree d b (fun t => ((A t).card:ℝ)/(2:ℝ)^d)
      (fun t => by positivity) v).trans_eq (by rw [← Finset.sum_div, hs]; ring))
  simpa only [typed_weight_sum, hs] using hm


lemma mean_fresh_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (v : ι → Bool) (f : (ι → Bool) → ℝ)
    (hf : ∀ i ∈ s, ∀ ω, f (QueryTree.flipCoin i ω) = f ω) :
    finiteMean (fun ω => if ∀ i ∈ s, ω i = v i then f ω else 0) =
      finiteMean f / (2:ℝ)^s.card := by
  induction s using Finset.induction_on with
  | empty => simp [finiteMean]
  | @insert i s hi ih =>
    let g := fun ω => if ∀ j ∈ s, ω j = v j then f ω else 0
    have hg : ∀ ω, g (QueryTree.flipCoin i ω) = g ω := by
      intro ω
      have he : (∀ j ∈ s, QueryTree.flipCoin i ω j = v j) ↔ ∀ j ∈ s, ω j = v j := by
        apply forall₂_congr
        intro j hj
        rw [QueryTree.flipCoin_apply_ne i j (fun h => hi (h ▸ hj))]
      simp only [g, he, hf i (Finset.mem_insert_self _ _) ω]
    have he (ω : ι → Bool) :
        (if ∀ j ∈ insert i s, ω j = v j then f ω else 0) =
        (if ω i = v i then g ω else 0) := by
      by_cases h : ω i = v i <;> simp [h,g]
    rw [finiteMean_congr he, QueryTree.mean_indicator_bit g i (v i) hg]
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    change finiteMean (fun ω => if ∀ j ∈ s, ω j = v j then f ω else 0) / 2 = _
    rw [hs, Finset.card_insert_of_notMem hi, pow_succ]
    ring

noncomputable def endpointProb {L : Type*} (d : ℕ) (A : Finset L)
    (x y : L → Card d) : ℝ := by
  classical
  exact finiteMean (fun ω : SwitchIndex d → Bool =>
    if ∀ i ∈ A, butterflyPerm d (decodeButterfly d ω) (x i) = y i then (1:ℝ) else 0)

lemma endpointProb_nonneg {L : Type*} (d : ℕ) (A : Finset L)
    (x y : L → Card d) : 0 ≤ endpointProb d A x y := by
  classical
  exact finiteMean_nonneg (fun _ => by positivity)

lemma endpointProb_insert_isolated {L : Type*} (d : ℕ) (A : Finset L)
    (x y : L → Card d) (i : L)
    (hiso : ∀ j ∈ A, Disjoint (routeDomain d (x i) (y i)) (routeDomain d (x j) (y j))) :
    endpointProb d (insert i A) x y = endpointProb d A x y / (2:ℝ)^d := by
  classical
  let f := fun ω : SwitchIndex d → Bool =>
    if ∀ j ∈ A, butterflyPerm d (decodeButterfly d ω) (x j) = y j then (1:ℝ) else 0
  have hf : ∀ t ∈ routeDomain d (x i) (y i), ∀ ω, f (QueryTree.flipCoin t ω) = f ω := by
    intro t ht ω
    have he : (∀ j ∈ A, butterflyPerm d (decodeButterfly d (QueryTree.flipCoin t ω)) (x j) = y j) ↔
        ∀ j ∈ A, butterflyPerm d (decodeButterfly d ω) (x j) = y j := by
      apply forall₂_congr
      intro j hj
      rw [butterfly_endpoint_iff, butterfly_endpoint_iff]
      apply forall₂_congr
      intro s hs
      rw [QueryTree.flipCoin_apply_ne t s (fun h =>
        Finset.disjoint_left.mp (hiso j hj) ht (h ▸ hs))]
    simp only [f, he]
  have he (ω : SwitchIndex d → Bool) :
      (if ∀ j ∈ insert i A, butterflyPerm d (decodeButterfly d ω) (x j) = y j then (1:ℝ) else 0) =
      (if ∀ t ∈ routeDomain d (x i) (y i), ω t = routeValue d (x i) (y i) t then f ω else 0) := by
    by_cases h : butterflyPerm d (decodeButterfly d ω) (x i) = y i
    · have hh := (butterfly_endpoint_iff d ω (x i) (y i)).mp h
      rw [ite_eq_left hh]
      simp only [Finset.forall_mem_insert, h, true_and, f]
    · have hh := mt (butterfly_endpoint_iff d ω (x i) (y i)).mpr h
      simp only [Finset.forall_mem_insert, h, false_and, hh, ite_false]
  change finiteMean _ = _
  rw [finiteMean_congr he, mean_fresh_cylinder _ _ f hf, card_routeDomain]
  rfl

noncomputable def partialKernel {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x y : L → Card d) : ℝ :=
  ((2:ℝ)^d)^A.card / ((2:ℝ)^d)^(Fintype.card L) * endpointProb d A x y

lemma partialKernel_insert_isolated {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x y : L → Card d) (i : L) (hi : i ∉ A)
    (hiso : ∀ j ∈ A, Disjoint (routeDomain d (x i) (y i)) (routeDomain d (x j) (y j))) :
    partialKernel d (insert i A) x y = partialKernel d A x y := by
  classical
  rw [partialKernel, endpointProb_insert_isolated d A x y i hiso,
    Finset.card_insert_of_notMem hi, pow_succ, partialKernel]
  field_simp

def ContactEvent {L : Type*} (d : ℕ) (x y : L → Card d) : Prop :=
  ∀ i, ∃ j, i ≠ j ∧ ¬Disjoint (routeDomain d (x i) (y i)) (routeDomain d (x j) (y j))

lemma alternating_cube_cancel {L : Type*} [Fintype L] (f : Finset L → ℝ)
    (i : L) (hf : ∀ A, i ∉ A → f (insert i A) = f A) :
    (∑ A : Finset L, (-1:ℝ)^A.card * f A) = 0 := by
  classical
  have hi : i ∈ (Finset.univ : Finset L) := Finset.mem_univ _
  rw [← Finset.powerset_univ, ← Finset.insert_erase hi, Finset.sum_powerset_insert]
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro A hA
    have hiA : i ∉ A := fun hh => Finset.notMem_erase i Finset.univ
      ((Finset.mem_powerset.mp hA) hh)
    rw [hf A hiA, Finset.card_insert_of_notMem hiA, pow_succ]
    ring
  · exact Finset.notMem_erase _ _

lemma alternating_kernel_cancel {L : Type*} [Fintype L] (d : ℕ)
    (x y : L → Card d) (h : ¬ContactEvent d x y) :
    (∑ A : Finset L, (-1:ℝ)^A.card * partialKernel d A x y) = 0 := by
  classical
  unfold ContactEvent at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  apply alternating_cube_cancel _ i
  intro A hiA
  apply partialKernel_insert_isolated d A x y i hiA
  intro j hj
  exact hi j (fun hij => hiA (hij ▸ hj))


noncomputable def networkOf {L : Type*} (A : Finset L) (i : L) : Option L := by
  classical
  exact if i ∈ A then none else some i

noncomputable def mixedTuple {L : Type*} (d : ℕ) (A : Finset L)
    (ω : Option L → (SwitchIndex d → Bool)) (x : L → Card d) : L → Card d :=
  fun i => butterflyPerm d (decodeButterfly d (ω (networkOf A i))) (x i)

noncomputable def mixedReturn {L : Type*} (d : ℕ) (A : Finset L)
    (ω : Option L → (SwitchIndex d → Bool)) (y : L → Card d) : L → Card d :=
  fun i => (butterflyPerm d (decodeButterfly d (ω (networkOf A i)))).symm (y i)

noncomputable def labelsOf {L : Type*} (A : Finset L) : Option L → Finset L := by
  classical
  exact fun t => match t with
    | none => A
    | some i => if i ∈ A then ∅ else {i}

lemma mem_labelsOf {L : Type*} (A : Finset L) (i : L) (t : Option L) :
    i ∈ labelsOf A t ↔ networkOf A i = t := by
  classical
  cases t with
  | none => simp [labelsOf, networkOf]
  | some j => by_cases hj : j ∈ A <;> by_cases hi : i ∈ A <;> simp_all [labelsOf, networkOf] <;> intro h <;> subst j <;> contradiction

lemma mixedTuple_eq_iff {L : Type*} (d : ℕ) (A : Finset L)
    (ω : Option L → (SwitchIndex d → Bool)) (x y : L → Card d) :
    mixedTuple d A ω x = y ↔ ∀ t, ∀ i ∈ labelsOf A t,
      butterflyPerm d (decodeButterfly d (ω t)) (x i) = y i := by
  constructor
  · intro h t i hi
    have he := congrFun h i
    simpa only [mixedTuple, mem_labelsOf A i t |>.mp hi] using he
  · intro h
    funext i
    exact h (networkOf A i) i (mem_labelsOf A i _ |>.mpr rfl)

lemma mixedReturn_eq_iff {L : Type*} (d : ℕ) (A : Finset L)
    (ω : Option L → (SwitchIndex d → Bool)) (y z : L → Card d) :
    mixedReturn d A ω y = z ↔ mixedTuple d A ω z = y := by
  constructor
  · intro h
    funext i
    exact (Equiv.symm_apply_eq _).mp (congrFun h i) |>.symm
  · intro h
    funext i
    exact (Equiv.symm_apply_eq _).mpr (congrFun h i).symm

lemma endpointProb_singleton {L : Type*} (d : ℕ) (i : L) (x y : L → Card d) :
    endpointProb d {i} x y = 1/(2:ℝ)^d := by
  classical
  simpa [endpointProb] using butterfly_single_card_uniform d (x i) (y i)

lemma mixedTuple_mass {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x y : L → Card d) :
    finiteMean (fun ω : Option L → (SwitchIndex d → Bool) =>
      if mixedTuple d A ω x = y then (1:ℝ) else 0) = partialKernel d A x y := by
  classical
  have he (ω : Option L → (SwitchIndex d → Bool)) :
      (if mixedTuple d A ω x = y then (1:ℝ) else 0) =
      ∏ t, if ∀ i ∈ labelsOf A t, butterflyPerm d (decodeButterfly d (ω t)) (x i) = y i
        then (1:ℝ) else 0 := by
    simp only [Fintype.prod_boole, mixedTuple_eq_iff]
  rw [finiteMean_congr he]
  rw [finiteMean_pi_prod (fun t (w : SwitchIndex d → Bool) =>
    if ∀ i ∈ labelsOf A t, butterflyPerm d (decodeButterfly d w) (x i) = y i then (1:ℝ) else 0)]
  have hfac (t : Option L) : (finiteMean (fun w : SwitchIndex d → Bool =>
      if ∀ i ∈ labelsOf A t, butterflyPerm d (decodeButterfly d w) (x i) = y i then (1:ℝ) else 0)) =
      endpointProb d (labelsOf A t) x y := by
        unfold endpointProb
        apply finiteMean_congr
        intro w
        split_ifs <;> rfl
  simp only [hfac]
  rw [Fintype.prod_option]
  have hi (i : L) : endpointProb d (labelsOf A (some i)) x y =
      if i ∈ A then 1 else 1/(2:ℝ)^d := by
    by_cases h : i ∈ A
    · simp [labelsOf, h, endpointProb, finiteMean_const]
    · simp only [labelsOf, ite_eq_right h, endpointProb_singleton]
  rw [show labelsOf A none = A from rfl]
  simp only [hi]
  have hp : (∏ i : L, if i ∈ A then (1:ℝ) else 1/(2:ℝ)^d) =
      (1/(2:ℝ)^d)^((Fintype.card L) - A.card) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul]
    simp only [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.prod_const, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  rw [hp, partialKernel, one_div, inv_pow]
  have hc : A.card ≤ Fintype.card L := Finset.card_le_univ _
  have hn : (((2:ℝ)^d)^A.card) * (((2:ℝ)^d)^(Fintype.card L - A.card)) =
      ((2:ℝ)^d)^(Fintype.card L) := by rw [← pow_add, Nat.add_sub_of_le hc]
  have hnz : ((2:ℝ)^d)^(Fintype.card L) ≠ 0 := by positivity
  have hmz : ((2:ℝ)^d)^(Fintype.card L - A.card) ≠ 0 := by positivity
  field_simp
  rw [← hn]
  ring

lemma mixedReturn_mass {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (y z : L → Card d) :
    finiteMean (fun ω : Option L → (SwitchIndex d → Bool) =>
      if mixedReturn d A ω y = z then (1:ℝ) else 0) = partialKernel d A z y := by
  simpa only [mixedReturn_eq_iff] using mixedTuple_mass d A z y

noncomputable def mixedInitial {L : Type*} (d : ℕ) (A : Finset L)
    (x : L → Card d) (t : Option L) : Finset (Card d) := by
  classical
  exact (labelsOf A t).image x

lemma typedMarks_mixedInitial {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L → Card d) (ω : Option L → (SwitchIndex d → Bool)) :
    typedMarks d (mixedInitial d A x) ω = Finset.univ.image
      (fun i => (networkOf A i, mixedTuple d A ω x i)) := by
  classical
  ext v
  simp only [typedMarks, mem_typedSet, butterflyMarks, mixedInitial,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z, ⟨i,hi,rfl⟩, hv⟩
    have ht := mem_labelsOf A i v.1 |>.mp hi
    exact ⟨i, Prod.ext ht (by simpa only [mixedTuple, ht] using hv)⟩
  · rintro ⟨i, hi⟩
    have ht := congrArg Prod.fst hi
    have hv := congrArg Prod.snd hi
    change networkOf A i = v.1 at ht
    change mixedTuple d A ω x i = v.2 at hv
    exact ⟨x i, ⟨i, mem_labelsOf A i v.1 |>.mpr ht, rfl⟩,
      by simpa only [mixedTuple, ht] using hv⟩

lemma typedTuple_injective {L : Type*} (d : ℕ) (A : Finset L)
    (x : L → Card d) (hx : Function.Injective x)
    (ω : Option L → (SwitchIndex d → Bool)) :
    Function.Injective (fun i => (networkOf A i, mixedTuple d A ω x i)) := by
  intro i j h
  have ht := congrArg Prod.fst h
  have hv := congrArg Prod.snd h
  change networkOf A i = networkOf A j at ht
  dsimp only [mixedTuple] at hv
  rw [ht] at hv
  exact hx ((butterflyPerm d (decodeButterfly d (ω (networkOf A j)))).injective hv)

lemma mixedInitial_card {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L → Card d) (hx : Function.Injective x) :
    (∑ t, (mixedInitial d A x t).card) = Fintype.card L := by
  classical
  let ω : Option L → (SwitchIndex d → Bool) := fun _ _ => false
  rw [← typedMarks_card d (mixedInitial d A x) ω, typedMarks_mixedInitial,
    Finset.card_image_of_injective _ (typedTuple_injective d A x hx ω), Finset.card_univ]

lemma contactEvent_mixedReturn_iff {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L → Card d) (hx : Function.Injective x)
    (ω b : Option L → (SwitchIndex d → Bool)) :
    ContactEvent d (mixedReturn d A b (mixedTuple d A ω x)) (mixedTuple d A ω x) ↔
      NoIsolated (returnGraph d (fun t => decodeButterfly d (b t)))
        (typedMarks d (mixedInitial d A x) ω) := by
  classical
  rw [typedMarks_mixedInitial]
  let f := fun i => (networkOf A i, mixedTuple d A ω x i)
  have hf : Function.Injective f := typedTuple_injective d A x hx ω
  constructor
  · intro h v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,hij,hc⟩ := h i
    exact ⟨f j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _,rfl⟩,
      hf.ne hij, hc⟩
  · intro h i
    obtain ⟨v,hv,hij,hc⟩ := h (f i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨j, fun he => hij (congrArg f he), hc⟩

lemma probability_mixed_contact {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L → Card d) (hx : Function.Injective x)
    (b : Option L → (SwitchIndex d → Bool))
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    finiteMean (fun ω : Option L → (SwitchIndex d → Bool) =>
      if ContactEvent d (mixedReturn d A b (mixedTuple d A ω x)) (mixedTuple d A ω x)
        then (1:ℝ) else 0) ≤
      (2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
        Real.exp (Real.exp 1*(Fintype.card L)) := by
  classical
  simp only [contactEvent_mixedReturn_iff d A x hx]
  convert mixed_return_noIsolated d (mixedInitial d A x) (fun t => decodeButterfly d (b t))
      (Fintype.card L) (mixedInitial_card d A x hx) hδ hδ1 using 1
  congr 1
  exact Subsingleton.elim _ _


lemma finiteMean_pushforward {Ω X : Type*} [Fintype Ω] [Fintype X]
    (g : Ω → X) (f : X → ℝ) :
    finiteMean (fun ω => f (g ω)) =
      ∑ y, finiteMean (fun ω => if g ω = y then (1:ℝ) else 0) * f y := by
  classical
  simp_rw [← finiteMean_mul_const, ← finiteMean_sum]
  apply finiteMean_congr
  intro ω
  simp

lemma mixedTuple_expectation {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L → Card d) (f : (L → Card d) → ℝ) :
    finiteMean (fun ω : Option L → (SwitchIndex d → Bool) => f (mixedTuple d A ω x)) =
      ∑ y, partialKernel d A x y * f y := by
  classical
  rw [finiteMean_pushforward (fun ω : Option L → (SwitchIndex d → Bool) => mixedTuple d A ω x) f]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  convert mixedTuple_mass d A x y using 1
  congr 1
  funext ω
  split_ifs <;> rfl

lemma mixedReturn_expectation {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (y : L → Card d) (f : (L → Card d) → ℝ) :
    finiteMean (fun ω : Option L → (SwitchIndex d → Bool) => f (mixedReturn d A ω y)) =
      ∑ z, partialKernel d A z y * f z := by
  classical
  rw [finiteMean_pushforward (fun ω : Option L → (SwitchIndex d → Bool) => mixedReturn d A ω y) f]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  convert mixedReturn_mass d A y z using 1
  congr 1
  funext ω
  split_ifs <;> rfl

lemma partialKernel_nonneg {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x y : L → Card d) : 0 ≤ partialKernel d A x y :=
  mul_nonneg (by positivity) (endpointProb_nonneg d A x y)

noncomputable def retainedKernel {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L ↪ Card d) (y : L → Card d) : ℝ := by
  classical
  exact if ContactEvent d x y then partialKernel d A x y else 0

lemma retainedKernel_nonneg {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L ↪ Card d) (y : L → Card d) : 0 ≤ retainedKernel d A x y := by
  classical
  unfold retainedKernel
  split_ifs
  · exact partialKernel_nonneg d A x y
  · exact le_rfl

lemma retainedKernel_le {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L ↪ Card d) (y : L → Card d) : retainedKernel d A x y ≤ partialKernel d A x y := by
  classical
  unfold retainedKernel
  split_ifs
  · exact le_rfl
  · exact partialKernel_nonneg d A x y

lemma retained_square_row {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (x : L ↪ Card d)
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    (∑ x' : L ↪ Card d, ∑ y : L → Card d, retainedKernel d A x y * retainedKernel d A x' y) ≤
      (2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
        Real.exp (Real.exp 1*(Fintype.card L)) := by
  classical
  let f := fun y z : L → Card d => if ContactEvent d z y then (1:ℝ) else 0
  have hsub (y : L → Card d) : (∑ x' : L ↪ Card d, retainedKernel d A x' y) ≤
      ∑ z : L → Card d, partialKernel d A z y * f y z := by
    have he (x' : L ↪ Card d) : retainedKernel d A x' y = partialKernel d A x' y * f y x' := by
      unfold retainedKernel f
      split_ifs <;> ring
    simp_rw [he]
    rw [← Finset.sum_image (f := fun z => partialKernel d A z y * f y z)
      (Function.Embedding.coe_injective.injOn)]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro z _ _
    exact mul_nonneg (partialKernel_nonneg d A z y) (by dsimp [f]; positivity)
  calc
    _ = ∑ y, retainedKernel d A x y * ∑ x' : L ↪ Card d, retainedKernel d A x' y := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ y, partialKernel d A x y * ∑ z : L → Card d, partialKernel d A z y * f y z := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul (retainedKernel_le d A x y) (hsub y)
        (Finset.sum_nonneg (fun x' _ => retainedKernel_nonneg d A x' y)) (partialKernel_nonneg d A x y)
    _ = finiteMean (fun ω : Option L → (SwitchIndex d → Bool) =>
        finiteMean (fun b : Option L → (SwitchIndex d → Bool) =>
          f (mixedTuple d A ω x) (mixedReturn d A b (mixedTuple d A ω x)))) := by
      rw [mixedTuple_expectation d A x (fun y =>
        finiteMean (fun b : Option L → (SwitchIndex d → Bool) => f y (mixedReturn d A b y)))]
      simp only [mixedReturn_expectation]
    _ = finiteMean (fun b : Option L → (SwitchIndex d → Bool) =>
        finiteMean (fun ω : Option L → (SwitchIndex d → Bool) =>
          f (mixedTuple d A ω x) (mixedReturn d A b (mixedTuple d A ω x)))) := finiteMean_comm _
    _ ≤ _ := by
      apply (finiteMean_mono (fun b => probability_mixed_contact d A x x.injective b hδ hδ1)).trans_eq
      exact finiteMean_const _

noncomputable def rectOperator {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) : EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ X :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun x => ∑ y, (P x y : ℂ)*v y)
      map_add' := by
        intro v w
        ext x
        simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        ext x
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        change (∑ y, (P x y : ℂ)*(c*v y)) = c*∑ y, (P x y : ℂ)*v y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring }

@[simp] lemma rectOperator_apply {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) (v : EuclideanSpace ℂ Y) (x : X) :
    rectOperator P v x = ∑ y, (P x y:ℂ)*v y := rfl

lemma rectOperator_adjoint {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) : ContinuousLinearMap.adjoint (rectOperator P) =
      rectOperator (fun y x => P x y) := by
  apply Eq.symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simp only [PiLp.inner_apply, RCLike.inner_apply, rectOperator_apply,
    map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma rectOperator_comp_transpose {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) : (rectOperator P).comp (rectOperator (fun y x => P x y)) =
      rectOperator (fun x x' => ∑ y, P x y * P x' y) := by
  ext v x
  simp only [ContinuousLinearMap.comp_apply, rectOperator_apply, Finset.mul_sum,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x' _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma rectOperator_norm_sq_le {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ x, (∑ x', ∑ y, P x y * P x' y) ≤ B) :
    ‖rectOperator P‖^2 ≤ B := by
  let S := fun x x' => ∑ y, P x y * P x' y
  have hs : ∀ x x', S x x' = S x' x := by
    intro x x'
    unfold S
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hbound : ‖rectOperator S‖ ≤ B := by
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    exact DensityTransfer.schur_bound S
      (fun x x' => Finset.sum_nonneg (fun y _ => mul_nonneg (hP x y) (hP x' y))) B hB
      hrow (fun x' => by
        calc (∑ x, S x x') = ∑ x, S x' x := Finset.sum_congr rfl (fun x _ => hs x x')
             _ ≤ B := hrow x') v
  have hn := ContinuousLinearMap.norm_adjoint_comp_self
    (ContinuousLinearMap.adjoint (rectOperator P))
  rw [ContinuousLinearMap.adjoint_adjoint, (ContinuousLinearMap.adjoint.norm_map _),
    rectOperator_adjoint, rectOperator_comp_transpose] at hn
  rw [pow_two, ← hn]
  exact hbound

lemma retained_norm_sq {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    ‖rectOperator (retainedKernel d A)‖^2 ≤
      (2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
        Real.exp (Real.exp 1*(Fintype.card L)) :=
  rectOperator_norm_sq_le _ (retainedKernel_nonneg d A) _ (by positivity)
    (fun x => retained_square_row d A x hδ hδ1)


noncomputable def pointStabilizer {α : Type*} (A : Finset α) : Subgroup (Equiv.Perm α) where
  carrier := {p | ∀ x ∈ A, p x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by intro p q hp hq x hx; change p (q x) = x; rw [hq x hx, hp x hx]
  inv_mem' := by intro p hp x hx; exact (Equiv.Perm.inv_eq_iff_eq).mpr (hp x hx).symm

lemma swap_mem_pointStabilizer {α : Type*} [DecidableEq α] (A : Finset α)
    (x y : α) (hx : x ∉ A) (hy : y ∉ A) : Equiv.swap x y ∈ pointStabilizer A := by
  intro z hz
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ hz)) (fun h => hy (h ▸ hz))

lemma point_symmetrizer_zero (μ : YoungDiagram) (A : Finset (Specht.Cell μ))
    (hA : A.card < μ.card - μ.rowLen 0) (v : Specht.Tabloid μ → ℂ) (hv : v ∈ Specht.space μ) :
    Specht.symmetrizer (pointStabilizer A) (Specht.tabloidRep μ) v = 0 := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p,rfl⟩ := hv
    let e : {x : Specht.Cell μ // p x ∉ A} ≃ {x : Specht.Cell μ // x ∉ A} :=
      { toFun := fun x => ⟨p x.1,x.2⟩
        invFun := fun x => ⟨p.symm x.1, by simpa only [p.apply_symm_apply] using x.2⟩
        left_inv := fun x => by apply Subtype.ext; exact p.symm_apply_apply _
        right_inv := fun x => by apply Subtype.ext; exact p.apply_symm_apply _ }
    have hc : μ.rowLen 0 < Fintype.card {x : Specht.Cell μ // p x ∉ A} := by
      rw [Fintype.card_congr e, Fintype.card_subtype_compl, Specht.card_cell, Fintype.card_coe]
      have hr := Specht.rowLen_zero_le_card μ
      omega
    obtain ⟨x,y,hne,hcol⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun x : {x : Specht.Cell μ // p x ∉ A} => Specht.colIndex x.1)
      (by simpa only [Fintype.card_fin] using hc)
    have hxy : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
    let h : pointStabilizer A := ⟨Equiv.swap (p x.1) (p y.1),
      swap_mem_pointStabilizer A _ _ x.2 y.2⟩
    apply Specht.symmetrizer_eq_zero_of_neg _ _ h
    change Specht.tabloidRep μ (Equiv.swap (p x.1) (p y.1))
      (Specht.tabloidRep μ p (Specht.polytabloid μ)) = -Specht.tabloidRep μ p (Specht.polytabloid μ)
    rw [←Module.End.mul_apply, ←map_mul, ←Equiv.mul_swap_eq_swap_mul]
    rw [map_mul, Module.End.mul_apply,
      Specht.swap_polytabloid x.1 y.1 hxy (congrArg Fin.val hcol), map_neg]
  | zero => exact map_zero _
  | add v w hv hw ihv ihw => simp only [map_add,ihv,ihw,add_zero]
  | smul a v hv ih => simp only [map_smul,ih,smul_zero]

lemma point_fixed_zero (μ : YoungDiagram) (A : Finset (Specht.Cell μ))
    (hA : A.card < μ.card - μ.rowLen 0) (v : Specht.Tabloid μ → ℂ) (hv : v ∈ Specht.space μ)
    (hfix : ∀ p, p ∈ pointStabilizer A → Specht.tabloidRep μ p v = v) : v = 0 := by
  classical
  have hz := point_symmetrizer_zero μ A hA v hv
  have he : Specht.symmetrizer (pointStabilizer A) (Specht.tabloidRep μ) v =
      (Fintype.card (pointStabilizer A) : ℂ) • v := by
    simp only [Specht.symmetrizer, LinearMap.sum_apply, hfix _ (Subtype.prop _),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  rw [he] at hz
  exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast Fintype.card_ne_zero)

lemma point_unitary_fixed_zero (μ : YoungDiagram) (A : Finset (Specht.Cell μ))
    (hA : A.card < μ.card - μ.rowLen 0) (v : Specht.hilbertSpace μ)
    (hfix : ∀ p, p ∈ pointStabilizer A → Specht.unitaryRepresentation μ p v = v) : v = 0 := by
  let w := (Specht.spaceHilbertEquiv μ).symm v
  have hw : ∀ p, p ∈ pointStabilizer A → Specht.tabloidRep μ p w.val = w.val := by
    intro p hp
    have he := congrArg ((Specht.spaceHilbertEquiv μ).symm) (hfix p hp)
    change Specht.representation μ p w = w at he
    exact congrArg Subtype.val he
  have hz := point_fixed_zero μ A hA w.val w.prop hw
  have hw0 : w = 0 := Subtype.ext hz
  have he := congrArg (Specht.spaceHilbertEquiv μ) hw0
  simpa only [w, LinearEquiv.apply_symm_apply, map_zero] using he

lemma point_relabelled_fixed_zero {α : Type*} [Fintype α] (μ : YoungDiagram)
    (e : α ≃ Specht.Cell μ) (A : Finset α) (hA : A.card < μ.card - μ.rowLen 0)
    (v : Specht.hilbertSpace μ)
    (hfix : ∀ p, p ∈ pointStabilizer A → Specht.relabelledUnitary μ e p v = v) : v = 0 := by
  classical
  apply point_unitary_fixed_zero μ (A.image e) (by simpa only [Finset.card_image_of_injective _ e.injective] using hA) v
  intro p hp
  have hf : e.symm.permCongr p ∈ pointStabilizer A := by
    intro x hx
    have hh := hp (e x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, hh, e.symm_apply_apply]
  have hh := hfix _ hf
  change Specht.unitaryRepresentation μ (e.permCongr (e.symm.permCongr p)) v = v at hh
  have he : e.permCongr (e.symm.permCongr p) = p := by
    apply Equiv.ext
    intro x
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, e.apply_symm_apply]
  simpa only [he] using hh


section Orbit
variable {G X V : Type*} [Group G] [Fintype G] [Fintype X]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀ = x)
    (ρ : Representation ℂ G V) (w : V) (hw : UnitaryFinite.IsFixed a x₀ ρ w)

noncomputable def orbitVector (x : X) : V := ρ (UnitaryFinite.representative a x₀ ha x) w

include hw in
omit [Fintype G] [Fintype X] [FiniteDimensional ℂ V] in
lemma orbitVector_at (g : G) : orbitVector a x₀ ha ρ w (a g x₀) = ρ g w := by
  apply ext_inner_right ℂ
  intro v
  exact UnitaryFinite.coefficient_at a x₀ ha ρ w hw v g

include hw in
omit [Fintype G] [Fintype X] [FiniteDimensional ℂ V] in
lemma orbitVector_action (g : G) (x : X) :
    orbitVector a x₀ ha ρ w (a g x) = ρ g (orbitVector a x₀ ha ρ w x) := by
  obtain ⟨h,rfl⟩ := ha x
  rw [←Equiv.Perm.mul_apply, ←map_mul, orbitVector_at a x₀ ha ρ w hw,
    orbitVector_at a x₀ ha ρ w hw, map_mul, Module.End.mul_apply]
end Orbit

def Harmonic {L α : Type*} [Fintype L] [Fintype α] (f : EuclideanSpace ℂ (L ↪ α)) : Prop :=
  ∀ (A : Finset L), A ≠ Finset.univ → ∀ z : L → α,
    (∑ y : L ↪ α, if ∀ i ∈ A, y i = z i then f y else 0) = 0

lemma normalizedCoefficient_harmonic {L α : Type*} [Fintype L] [Fintype α]
    (μ : YoungDiagram) (e : α ≃ Specht.Cell μ)
    (hk : Fintype.card L = μ.card - μ.rowLen 0) (x₀ : L ↪ α)
    (w : Specht.hilbertSpace μ)
    (hw : UnitaryFinite.IsFixed UnitaryFinite.tupleAction x₀ (Specht.relabelledUnitary μ e) w)
    (v : Specht.hilbertSpace μ) :
    Harmonic (UnitaryFinite.normalizedCoefficient UnitaryFinite.tupleAction x₀
      (UnitaryFinite.tupleAction_transitive x₀) (Specht.relabelledUnitary μ e) w v) := by
  classical
  intro A hA z
  let ρ := Specht.relabelledUnitary μ e
  let F := orbitVector UnitaryFinite.tupleAction x₀ (UnitaryFinite.tupleAction_transitive x₀) ρ w
  let S : Specht.hilbertSpace μ := ∑ y : L ↪ α, if ∀ i ∈ A, y i = z i then F y else 0
  have hcard : (A.image z).card < μ.card - μ.rowLen 0 := by
    apply (Finset.card_image_le).trans_lt
    rw [← hk]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hA)
  have hz : S = 0 := by
    apply point_relabelled_fixed_zero μ e (A.image z) hcard
    intro p hp
    change ρ p S = S
    simp only [S, map_sum, apply_ite, map_zero]
    apply Fintype.sum_equiv (UnitaryFinite.tupleAction p)
    intro y
    have he : (∀ i ∈ A, UnitaryFinite.tupleAction p y i = z i) ↔ ∀ i ∈ A, y i = z i := by
      apply forall₂_congr
      intro i hi
      have hpi : p (z i) = z i := hp _ (Finset.mem_image.mpr ⟨i, hi,rfl⟩)
      change p (y i) = z i ↔ y i = z i
      exact (show (p (y i) = z i) ↔ p (y i) = p (z i) by rw [hpi]).trans p.injective.eq_iff
    simp only [he]
    split_ifs
    · exact (orbitVector_action UnitaryFinite.tupleAction x₀
        (UnitaryFinite.tupleAction_transitive x₀) ρ w hw p y).symm
    · rfl
  let c : ℂ := Real.sqrt ((Module.finrank ℂ (Specht.hilbertSpace μ):ℝ)/(Fintype.card (L ↪ α):ℝ))
  calc
    _ = c * inner ℂ S v := by
      dsimp only [S]
      rw [sum_inner (𝕜 := ℂ) Finset.univ _ v, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp_all only [UnitaryFinite.normalizedCoefficient, PiLp.smul_apply,
        smul_eq_mul, UnitaryFinite.coefficient, F, orbitVector, inner_zero_left (𝕜 := ℂ), mul_zero, c, ρ]
    _ = 0 := by rw [hz, inner_zero_left (𝕜 := ℂ) v, mul_zero]


lemma sum_injections {L α M : Type*} [Fintype L] [Fintype α] [AddCommMonoid M]
    (F : (L → α) → M) (hF : ∀ y, ¬Function.Injective y → F y = 0) :
    (∑ y : L → α, F y) = ∑ y : L ↪ α, F y := by
  classical
  rw [← Finset.sum_image Function.Embedding.coe_injective.injOn]
  apply Eq.symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  apply hF y
  intro h
  exact hy (Finset.mem_image.mpr ⟨⟨y,h⟩, Finset.mem_univ _, rfl⟩)

noncomputable def zeroExtend {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) : EuclideanSpace ℂ (L → α) := by
  classical
  exact WithLp.toLp 2 (fun y => if h : Function.Injective y then f ⟨y,h⟩ else 0)

@[simp] lemma zeroExtend_inj {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) (y : L ↪ α) : zeroExtend f y = f y := by
  classical
  simp only [zeroExtend, WithLp.ofLp_toLp, dite_eq_left y.injective]
  congr 1

lemma zeroExtend_noninj {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) (y : L → α) (hy : ¬Function.Injective y) : zeroExtend f y = 0 := by
  classical
  simp only [zeroExtend, WithLp.ofLp_toLp, dite_eq_right hy]

lemma sum_zeroExtend_mul {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) (g : (L → α) → ℂ) :
    (∑ y : L → α, g y * zeroExtend f y) = ∑ y : L ↪ α, g y * f y := by
  rw [sum_injections _ (fun y hy => by rw [zeroExtend_noninj f y hy, mul_zero])]
  simp only [zeroExtend_inj]

lemma norm_zeroExtend {L α : Type*} [Fintype L] [Fintype α]
    (f : EuclideanSpace ℂ (L ↪ α)) : ‖zeroExtend f‖ = ‖f‖ := by
  have hs : ‖zeroExtend f‖^2 = ‖f‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      sum_injections _ (fun y hy => by rw [zeroExtend_noninj f y hy]; simp)]
    simp only [zeroExtend_inj]
  nlinarith [norm_nonneg (zeroExtend f), norm_nonneg f]

lemma partial_proper_zero {L : Type*} [Fintype L] (d : ℕ) (A : Finset L)
    (hA : A ≠ Finset.univ) (f : EuclideanSpace ℂ (L ↪ Card d)) (hf : Harmonic f) :
    rectOperator (fun (x : L ↪ Card d) (y : L → Card d) => partialKernel d A x y) (zeroExtend f) = 0 := by
  classical
  ext x
  rw [rectOperator_apply, sum_zeroExtend_mul]
  change (∑ y : L ↪ Card d, (partialKernel d A x y : ℂ) * f y) = 0
  simp only [partialKernel, endpointProb, finiteMean, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_sum, Complex.ofReal_natCast]
  simp_rw [div_eq_mul_inv, mul_assoc, ← Finset.mul_sum]
  rw [mul_eq_zero]
  right
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro ω _
  calc
    _ = ∑ y : L ↪ Card d, (↑(Fintype.card (SwitchIndex d → Bool)) : ℂ)⁻¹ *
        (if ∀ i ∈ A, y i = butterflyPerm d (decodeButterfly d ω) (x i) then f y else 0) :=
      by
        apply Finset.sum_congr rfl
        intro y _
        have hh : (∀ i ∈ A, butterflyPerm d (decodeButterfly d ω) (x i) = y i) ↔
            (∀ i ∈ A, y i = butterflyPerm d (decodeButterfly d ω) (x i)) :=
          forall₂_congr fun _ _ => eq_comm
        by_cases h : ∀ i ∈ A, butterflyPerm d (decodeButterfly d ω) (x i) = y i
        · simp only [ite_eq_left h, ite_eq_left (hh.mp h), Complex.ofReal_one, one_mul]
        · simp only [ite_eq_right h, ite_eq_right (mt hh.mpr h), Complex.ofReal_zero, zero_mul, mul_zero]
    _ = 0 := by
      rw [← Finset.mul_sum]
      apply mul_eq_zero_of_right
      convert hf A hA (fun i => butterflyPerm d (decodeButterfly d ω) (x i)) using 1
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> rfl

lemma partial_full_action {L : Type*} [Fintype L] (d : ℕ)
    (f : EuclideanSpace ℂ (L ↪ Card d)) :
    rectOperator (fun (x : L ↪ Card d) (y : L → Card d) => partialKernel d Finset.univ x y) (zeroExtend f) =
      DensityTransfer.applyKernel (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
        (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f := by
  classical
  ext x
  rw [rectOperator_apply, sum_zeroExtend_mul]
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  simp only [partialKernel, Finset.card_univ, div_self (by positivity : ((2:ℝ)^d)^(Fintype.card L) ≠ 0),
    one_mul, endpointProb, UnitaryFinite.actionKernel]
  apply finiteMean_congr
  intro ω
  congr 1
  simp only [Finset.mem_univ, forall_const, Function.Embedding.ext_iff]
  rfl

lemma alternating_retained_eq {L : Type*} [Fintype L] (d : ℕ)
    (x : L ↪ Card d) (y : L → Card d) :
    (∑ A : Finset L, (-1:ℝ)^A.card * retainedKernel d A x y) =
      ∑ A : Finset L, (-1:ℝ)^A.card * partialKernel d A x y := by
  classical
  by_cases h : ContactEvent d x y
  · simp only [retainedKernel, ite_eq_left h]
  · simp only [retainedKernel, ite_eq_right h, mul_zero, Finset.sum_const_zero]
    exact (alternating_kernel_cancel d x y h).symm

lemma alternating_harmonic_action {L : Type*} [Fintype L] (d : ℕ)
    (f : EuclideanSpace ℂ (L ↪ Card d)) (hf : Harmonic f) :
    (∑ A : Finset L, ((-1:ℂ)^A.card) • rectOperator (retainedKernel d A) (zeroExtend f)) =
      ((-1:ℂ)^(Fintype.card L)) • DensityTransfer.applyKernel
        (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
          (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f := by
  classical
  calc
    _ = ∑ A : Finset L, ((-1:ℂ)^A.card) •
        rectOperator (fun (x : L ↪ Card d) y => partialKernel d A x y) (zeroExtend f) := by
      ext x
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, rectOperator_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Finset L)))]
      apply Finset.sum_congr rfl
      intro y _
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      congr 1
      have he := congrArg (fun t : ℝ => (t:ℂ)) (alternating_retained_eq d x y)
      simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
        Complex.ofReal_one] using he
    _ = ((-1:ℂ)^(Fintype.card L)) •
        rectOperator (fun (x : L ↪ Card d) y => partialKernel d Finset.univ x y) (zeroExtend f) := by
      rw [Finset.sum_eq_single (Finset.univ : Finset L)]
      · simp only [Finset.card_univ]
      · intro A _ hA
        rw [partial_proper_zero d A hA f hf, smul_zero]
      · simp
    _ = _ := by rw [partial_full_action]

lemma harmonic_action_bound {L : Type*} [Fintype L] (d : ℕ)
    (f : EuclideanSpace ℂ (L ↪ Card d)) (hf : Harmonic f)
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    ‖DensityTransfer.applyKernel (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
      (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f‖ ≤
      (2:ℝ)^(Fintype.card L) *
        Real.sqrt ((2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
          Real.exp (Real.exp 1*(Fintype.card L))) * ‖f‖ := by
  classical
  let B := (2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
          Real.exp (Real.exp 1*(Fintype.card L))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnorm (A : Finset L) : ‖rectOperator (retainedKernel d A)‖ ≤ Real.sqrt B := by
    have hh := retained_norm_sq d A hδ hδ1
    have hs := Real.sq_sqrt hB
    have hn := Real.sqrt_nonneg B
    nlinarith
  calc
    _ = ‖((-1:ℂ)^(Fintype.card L)) • DensityTransfer.applyKernel
        (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
          (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f‖ := by
      simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ = ‖∑ A : Finset L, ((-1:ℂ)^A.card) • rectOperator (retainedKernel d A) (zeroExtend f)‖ := by
      rw [alternating_harmonic_action d f hf]
    _ ≤ ∑ A : Finset L, ‖((-1:ℂ)^A.card) • rectOperator (retainedKernel d A) (zeroExtend f)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ A : Finset L, Real.sqrt B * ‖f‖ := by
      apply Finset.sum_le_sum
      intro A _
      simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      calc _ ≤ ‖rectOperator (retainedKernel d A)‖ * ‖zeroExtend f‖ :=
              ContinuousLinearMap.le_opNorm _ _
           _ ≤ Real.sqrt B * ‖zeroExtend f‖ := mul_le_mul_of_nonneg_right (hnorm A) (norm_nonneg _)
           _ = _ := by rw [norm_zeroExtend]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]; ring

lemma harmonic_action_zero_one {L : Type*} [Fintype L] (d : ℕ)
    (hL : Fintype.card L = 1) (f : EuclideanSpace ℂ (L ↪ Card d)) (hf : Harmonic f) :
    DensityTransfer.applyKernel (UnitaryFinite.actionKernel UnitaryFinite.tupleAction
      (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))) f = 0 := by
  classical
  obtain ⟨i,hi⟩ := Fintype.card_eq_one_iff.mp hL
  have hz (A : Finset L) : rectOperator (retainedKernel d A) = 0 := by
    ext v x
    have hh (y : L → Card d) : ¬ContactEvent d x y := by
      intro h
      obtain ⟨j,hj,_⟩ := h i
      exact hj (hi j).symm
    simp only [rectOperator_apply, retainedKernel, ite_eq_right (hh _), Complex.ofReal_zero,
      zero_mul, Finset.sum_const_zero, zero_apply, PiLp.zero_apply]
  have he := alternating_harmonic_action d f hf
  simp only [hz, zero_apply, smul_zero, Finset.sum_const_zero, hL, pow_one,
    neg_smul, one_smul] at he
  exact neg_eq_zero.mp he.symm


lemma exists_exact_fixed_unit {α L : Type*} [Fintype α] [Fintype L]
    (μ : YoungDiagram) (e : α ≃ Specht.Cell μ) (x₀ : L ↪ α)
    (hL : Fintype.card L = μ.card - μ.rowLen 0) :
    ∃ w : Specht.hilbertSpace μ,
      UnitaryFinite.IsFixed UnitaryFinite.tupleAction x₀ (Specht.relabelledUnitary μ e) w ∧ ‖w‖ = 1 := by
  let K := UnitaryFinite.fixedSpace (V := Specht.hilbertSpace μ) UnitaryFinite.tupleAction x₀ (Specht.relabelledUnitary μ e)
  have hd : 0 < Module.finrank ℂ (Specht.hilbertSpace μ) := by
    rw [Specht.finrank_hilbertSpace]
    exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr (Specht.space_ne_bot μ))
  have hdim := Specht.relabelled_tuple_dimension μ e x₀
  rw [hL, Nat.choose_self, mul_one] at hdim
  have hm : 0 < Module.finrank ℂ K := by
    by_contra h
    have hz : Module.finrank ℂ K = 0 := by omega
    change _ ≤ Module.finrank ℂ K * _ at hdim
    rw [hz, zero_mul] at hdim
    omega
  let B := stdOrthonormalBasis ℂ K
  let i : Fin (Module.finrank ℂ K) := ⟨0,hm⟩
  exact ⟨(B i).val, (B i).prop, B.orthonormal.norm_eq_one i⟩

lemma sweep_forward_norm {d : ℕ} (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    ‖sweepOperator d μ e rev‖ = ‖sweepOperator d μ e false‖ := by
  cases rev
  · rfl
  · simp only [sweepOperator, Bool.false_eq_true, ite_false, ite_true]
    rw [UnitaryFinite.sampleOperator_inv _ (Specht.relabelledUnitary_unitary μ e),
      ContinuousLinearMap.adjoint.norm_map]

lemma sweep_norm_le_one (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    ‖sweepOperator d μ e rev‖ ≤ 1 :=
  UnitaryFinite.sampleOperator_norm_le _ (Specht.relabelledUnitary_unitary μ e) _

section Generic
variable {L V : Type*} [Fintype L] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

lemma sample_sweep_bound (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    [Representation.IsIrreducible ρ] (hρ : UnitaryFinite.IsUnitary ρ)
    (x₀ : L ↪ Card d) (w : V) (hw : UnitaryFinite.IsFixed UnitaryFinite.tupleAction x₀ ρ w)
    (hn : ‖w‖ = 1)
    (hh : ∀ v, Harmonic (UnitaryFinite.normalizedCoefficient UnitaryFinite.tupleAction x₀
      (UnitaryFinite.tupleAction_transitive x₀) ρ w v))
    (hδ : 0 < 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d ≤ 1) :
    ‖UnitaryFinite.sampleOperator ρ (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))‖ ≤
      (2:ℝ)^(Fintype.card L) *
        Real.sqrt ((2*(d:ℝ)*(Fintype.card L)/(2:ℝ)^d)^((Fintype.card L:ℝ)/2) *
          Real.exp (Real.exp 1*(Fintype.card L))) := by
  rw [← ContinuousLinearMap.adjoint.norm_map (UnitaryFinite.sampleOperator ρ
    (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω))),
    ← UnitaryFinite.sampleOperator_inv ρ hρ]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [UnitaryFinite.sampleOperator_inv_apply]
  have ha := harmonic_action_bound d _ (hh v) hδ hδ1
  rw [UnitaryFinite.coefficient_random UnitaryFinite.tupleAction x₀
    (UnitaryFinite.tupleAction_transitive x₀) ρ hρ _ w hw,
    UnitaryFinite.normalizedCoefficient_norm _ _ _ ρ hρ w hw hn,
    UnitaryFinite.normalizedCoefficient_norm _ _ _ ρ hρ w hw hn] at ha
  exact ha

lemma sample_sweep_zero_one (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    [Representation.IsIrreducible ρ] (hρ : UnitaryFinite.IsUnitary ρ)
    (x₀ : L ↪ Card d) (w : V) (hw : UnitaryFinite.IsFixed UnitaryFinite.tupleAction x₀ ρ w)
    (hn : ‖w‖ = 1)
    (hh : ∀ v, Harmonic (UnitaryFinite.normalizedCoefficient UnitaryFinite.tupleAction x₀
      (UnitaryFinite.tupleAction_transitive x₀) ρ w v))
    (hL : Fintype.card L = 1) :
    UnitaryFinite.sampleOperator ρ (fun ω : SwitchIndex d → Bool => butterflyPerm d (decodeButterfly d ω)) = 0 := by
  apply ContinuousLinearMap.adjoint.injective
  rw [map_zero, ← UnitaryFinite.sampleOperator_inv ρ hρ]
  apply ContinuousLinearMap.ext
  intro v
  rw [UnitaryFinite.sampleOperator_inv_apply]
  have ha := harmonic_action_zero_one d hL _ (hh v)
  have he := congrArg norm ha
  rw [UnitaryFinite.coefficient_random UnitaryFinite.tupleAction x₀
    (UnitaryFinite.tupleAction_transitive x₀) ρ hρ _ w hw,
    UnitaryFinite.normalizedCoefficient_norm _ _ _ ρ hρ w hw hn, norm_zero] at he
  exact norm_eq_zero.mp he
end Generic

lemma sweep_norm_bound (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hδ : 0 < 2*(d:ℝ)*(μ.card - μ.rowLen 0 : ℕ)/(2:ℝ)^d)
    (hδ1 : 2*(d:ℝ)*(μ.card - μ.rowLen 0 : ℕ)/(2:ℝ)^d ≤ 1) (rev : Bool) :
    ‖sweepOperator d μ e rev‖ ≤ (2:ℝ)^(μ.card - μ.rowLen 0) *
      Real.sqrt ((2*(d:ℝ)*(μ.card - μ.rowLen 0 : ℕ)/(2:ℝ)^d)^(((μ.card - μ.rowLen 0 : ℕ):ℝ)/2) *
        Real.exp (Real.exp 1*(μ.card - μ.rowLen 0 : ℕ))) := by
  classical
  let x₀ : Specht.Tail μ ↪ Card d := (Function.Embedding.subtype _).trans e.symm.toEmbedding
  obtain ⟨w,hw,hn⟩ := exists_exact_fixed_unit μ e x₀ (Specht.tail_card μ)
  let := Specht.relabelledUnitary_irreducible μ e
  rw [sweep_forward_norm μ e rev]
  have hh (v : Specht.hilbertSpace μ) : Harmonic (UnitaryFinite.normalizedCoefficient
      (V := Specht.hilbertSpace μ) UnitaryFinite.tupleAction x₀
      (UnitaryFinite.tupleAction_transitive x₀) (Specht.relabelledUnitary μ e) w v) :=
    normalizedCoefficient_harmonic μ e (Specht.tail_card μ) x₀ w hw v
  have he := sample_sweep_bound (V := Specht.hilbertSpace μ) (L := Specht.Tail μ) d (Specht.relabelledUnitary μ e)
  have he := he (Specht.relabelledUnitary_unitary μ e) x₀ w hw hn hh
  have he := he (by simpa only [Specht.tail_card] using hδ) (by simpa only [Specht.tail_card] using hδ1)
  simpa only [sweepOperator, Bool.false_eq_true, ite_false, Specht.tail_card] using he

lemma sweep_zero_one (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hk : μ.card - μ.rowLen 0 = 1) (rev : Bool) : sweepOperator d μ e rev = 0 := by
  classical
  let x₀ : Specht.Tail μ ↪ Card d := (Function.Embedding.subtype _).trans e.symm.toEmbedding
  obtain ⟨w,hw,hn⟩ := exists_exact_fixed_unit μ e x₀ (Specht.tail_card μ)
  let := Specht.relabelledUnitary_irreducible μ e
  have hh (v : Specht.hilbertSpace μ) : Harmonic (UnitaryFinite.normalizedCoefficient
      (V := Specht.hilbertSpace μ) UnitaryFinite.tupleAction x₀
      (UnitaryFinite.tupleAction_transitive x₀) (Specht.relabelledUnitary μ e) w v) :=
    normalizedCoefficient_harmonic μ e (Specht.tail_card μ) x₀ w hw v
  have he := sample_sweep_zero_one (V := Specht.hilbertSpace μ) (L := Specht.Tail μ) d (Specht.relabelledUnitary μ e)
  have he := he (Specht.relabelledUnitary_unitary μ e) x₀ w hw hn hh
  have he := he ((Specht.tail_card μ).trans hk)
  have hz : sweepOperator d μ e false = 0 := by
    simpa only [sweepOperator, Bool.false_eq_true, ite_false] using he
  apply (norm_eq_zero (a := sweepOperator d μ e rev)).mp
  rw [sweep_forward_norm μ e rev, hz]
  exact @norm_zero (Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ) _

end Thorp.SparseContact

namespace Thorp.SparseContact

noncomputable def contactConstant : ℝ := 32 * Real.exp (2 * Real.exp 1)

lemma contactConstant_gt_one : 1 < contactConstant := by
  have h : 1 ≤ Real.exp (2 * Real.exp 1) := Real.one_le_exp (by positivity)
  unfold contactConstant
  linarith

lemma contactConstant_gt_two : 2 < contactConstant := by
  have h : 1 ≤ Real.exp (2 * Real.exp 1) := Real.one_le_exp (by positivity)
  unfold contactConstant
  linarith

lemma inflated_contact_bound {δ : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    ((2:ℝ)^k * Real.sqrt (δ^((k:ℝ)/2) * Real.exp (Real.exp 1*k)))^2 =
      ((contactConstant/2)*δ)^((k:ℝ)/2) := by
  have hC : 0 ≤ contactConstant/2 := by have := contactConstant_gt_one; positivity
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.mul_rpow hC hδ]
  have hc : contactConstant/2 = Real.exp (2*(Real.log 4+Real.exp 1)) := by
    unfold contactConstant
    rw [show 2*(Real.log 4+Real.exp 1) = Real.log 4*2+2*Real.exp 1 by ring,
      Real.exp_add, Real.exp_mul (Real.log 4) 2, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
    ring
  rw [hc, ←Real.exp_mul]
  have hpow : ((2:ℝ)^k)^2 = Real.exp (Real.log 4 * k) := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num only [pow_two]
    rw [Real.exp_mul (Real.log 4) k, Real.exp_log (by norm_num : (0:ℝ)<4), Real.rpow_natCast]
  rw [hpow]
  calc
    _ = (Real.exp (Real.log 4*k)*Real.exp (Real.exp 1*k))*δ^((k:ℝ)/2) := by ring
    _ = _ := by rw [←Real.exp_add]; congr 2; ring

lemma contact_crude_arithmetic {C d q : ℝ} (hC : 1 ≤ C) (hd : 1 ≤ d) (hq : 0 ≤ q) (k : ℕ) :
    (C*d*q)^((k:ℝ)/2) ≤ C^k*(1+d)^(C*k)*q^((k:ℝ)/2) := by
  rw [Real.mul_rpow (by positivity) hq, Real.mul_rpow (by positivity) (by positivity)]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hC (by linarith [Nat.cast_nonneg (α := ℝ) k])
  · calc
      d^((k:ℝ)/2) ≤ (1+d)^((k:ℝ)/2) := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ ≤ (1+d)^(C*k) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  · positivity
  · positivity


lemma sweep_sharp_bound (d : ℕ) (hd : 1 ≤ d) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hk : 1 ≤ μ.card - μ.rowLen 0) (rev : Bool) :
    ‖sweepOperator d μ e rev‖^2 ≤ min 1
      ((contactConstant*d*(μ.card - μ.rowLen 0 : ℕ)/(2:ℝ)^d)^(((μ.card - μ.rowLen 0 : ℕ):ℝ)/2)) := by
  let k := μ.card - μ.rowLen 0
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hδ : 0 < 2*(d:ℝ)*k/(2:ℝ)^d := by positivity
  have hOne : ‖sweepOperator d μ e rev‖^2 ≤ 1 := by
    have h := sweep_norm_le_one d μ e rev
    have h0 := norm_nonneg (sweepOperator d μ e rev)
    nlinarith
  refine le_min hOne ?_
  have he : contactConstant * d * (k:ℝ)/(2:ℝ)^d =
      (contactConstant/2)*(2*(d:ℝ)*k/(2:ℝ)^d) := by ring
  change _ ≤ (contactConstant * d * (k:ℝ)/(2:ℝ)^d)^((k:ℝ)/2)
  rw [he]
  by_cases hs : 2*(d:ℝ)*k/(2:ℝ)^d ≤ 1
  · have h := sweep_norm_bound d μ e hδ hs rev
    have hb : 0 ≤ (2:ℝ)^k * Real.sqrt
        ((2*(d:ℝ)*k/(2:ℝ)^d)^((k:ℝ)/2)*Real.exp (Real.exp 1*k)) := by positivity
    calc
      _ ≤ ((2:ℝ)^k * Real.sqrt
          ((2*(d:ℝ)*k/(2:ℝ)^d)^((k:ℝ)/2)*Real.exp (Real.exp 1*k)))^2 :=
        (sq_le_sq₀ (norm_nonneg (sweepOperator d μ e rev)) hb).mpr h
      _ = _ := inflated_contact_bound hδ.le k
  · apply hOne.trans
    apply Real.one_le_rpow
    · have hc : 1 ≤ contactConstant/2 := by have := contactConstant_gt_two; linarith
      exact one_le_mul_of_one_le_of_one_le hc (le_of_lt (lt_of_not_ge hs))
    · positivity

theorem uniform_sparse_contact : MainStatement := by
  refine ⟨contactConstant, contactConstant, (lt_trans (by norm_num) contactConstant_gt_one),
    (lt_trans (by norm_num) contactConstant_gt_one), ?_⟩
  intro d hd μ e k hk _ rev
  have hs := sweep_sharp_bound d hd μ e hk rev
  refine ⟨hs, ?_, ?_⟩
  · intro hk1
    exact sweep_zero_one d μ e hk1 rev
  · apply (hs.trans (min_le_right _ _)).trans
    change (contactConstant * d * (k:ℝ)/(2:ℝ)^d)^((k:ℝ)/2) ≤ _
    rw [mul_div_assoc]
    exact contact_crude_arithmetic contactConstant_gt_one.le
      (by exact_mod_cast hd) (by positivity) k

end Thorp.SparseContact

end ThorpNine.Contact

end OAI
