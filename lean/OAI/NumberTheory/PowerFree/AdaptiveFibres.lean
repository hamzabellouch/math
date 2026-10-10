import OAI.NumberTheory.PowerFree.StoppingTrees

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

theorem card_image_le_mul_fibers {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] (S : Finset α) (f : α → β) (g : α → γ) (L : ℕ)
    (hL : ∀ b ∈ S.image f, ((S.filter fun a => f a = b).image g).card ≤ L) :
    (S.image g).card ≤ (S.image f).card * L := by
  classical
  have hsub : S.image g ⊆ (S.image f).biUnion fun b => (S.filter fun a => f a = b).image g := by
    intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_biUnion.mpr ⟨f a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,
      Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩,rfl⟩⟩
  calc
    _ ≤ ((S.image f).biUnion fun b => (S.filter fun a => f a = b).image g).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ b ∈ S.image f, ((S.filter fun a => f a = b).image g).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ S.image f, L := Finset.sum_le_sum hL
    _ = _ := by simp

noncomputable def adaptiveStateAt {K V σ α : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) : ℕ → ℕ → σ → α → σ
  | 0, _, s, _ => s
  | m+1, i, s, a =>
    let t := adaptiveStateAt W next m i s a
    next (i+m) t (W (i+m) t a)

theorem adaptiveStateAt_tail {K V σ α : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) (m i : ℕ) (s : σ) (a : α) :
    adaptiveStateAt W next m (i+1) (next i s (W i s a)) a =
      adaptiveStateAt W next (m+1) i s a := by
  induction m with
  | zero => simp [adaptiveStateAt]
  | succ m ih =>
    simp only [adaptiveStateAt,ih]
    rw [show i+1+m = i+(m+1) by omega]

theorem adaptiveStateAt_mem_states {K V σ α : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) (m j i : ℕ) (s : σ) (a : α)
    (hj : j ≤ m) : adaptiveStateAt W next j i s a ∈ adaptiveStates W next m i s a := by
  induction m generalizing j i s with
  | zero =>
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simp [adaptiveStateAt,adaptiveStates]
  | succ m ih =>
    cases j with
    | zero => simp [adaptiveStateAt,adaptiveStates]
    | succ j =>
      rw [← adaptiveStateAt_tail]
      exact List.mem_cons_of_mem _ (ih j (i+1) _ (by omega))

noncomputable def physicalStateAt {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n :=
  adaptiveStateAt (physicalKernel (E := E) G d z.val) (physicalNext G d A h e z.val) i 0 (start z) B

@[simp] theorem physicalStateAt_zero {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (z : G.points) : physicalStateAt (E := E) G d A h e start B 0 z = start z := rfl

theorem physicalStateAt_succ {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    physicalStateAt (E := E) G d A h e start B (i+1) z =
      physicalNext G d A h e z.val i (physicalStateAt (E := E) G d A h e start B i z)
        (physicalKernel (E := E) G d z.val i (physicalStateAt (E := E) G d A h e start B i z) B) := by
  simp only [physicalStateAt,adaptiveStateAt,Nat.zero_add]

theorem physicalStateAt_good {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    PhysicalState G h (pathDegreeBudget n d A h e i) z.val
      (physicalStateAt (E := E) G d A h e start B i z) := by
  induction i with
  | zero => exact hs z
  | succ i ih =>
    rw [physicalStateAt_succ]
    exact (physical_step (E := E) G d A h e z.val z.property i _ ih B).1

noncomputable def pastBlockPrimes {r : ℕ} (B : Fin r → Finset ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun j => j.val < i).biUnion B

@[simp] theorem pastBlockPrimes_zero {r : ℕ} (B : Fin r → Finset ℕ) :
    pastBlockPrimes B 0 = ∅ := by simp [pastBlockPrimes]

theorem pastBlockPrimes_succ {r : ℕ} (B : Fin r → Finset ℕ) (i : ℕ) :
    pastBlockPrimes B (i+1) = cumulativeBlockPrimes B i := by
  simp only [pastBlockPrimes,cumulativeBlockPrimes,Nat.lt_succ_iff]

theorem cumulativeBlockPrimes_eq_union {r : ℕ} (B : Fin r → Finset ℕ) (i : Fin r) :
    cumulativeBlockPrimes B i.val = pastBlockPrimes B i.val ∪ B i := by
  classical
  ext p
  simp only [cumulativeBlockPrimes,pastBlockPrimes,Finset.mem_biUnion,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_union]
  constructor
  · rintro ⟨j,hj,hp⟩
    rcases lt_or_eq_of_le hj with hj | hj
    · exact Or.inl ⟨j,hj,hp⟩
    · have he : j = i := Fin.ext hj
      subst j
      exact Or.inr hp
  · rintro (⟨j,hj,hp⟩ | hp)
    · exact ⟨j,hj.le,hp⟩
    · exact ⟨i,le_rfl,hp⟩

theorem residueTuple_cumulative_eq {n r : ℕ} (B : Fin r → Finset ℕ) (i : Fin r)
    (z w : Fin n → ℤ) (hprev : residueTuple (pastBlockPrimes B i.val) z = residueTuple (pastBlockPrimes B i.val) w)
    (hnew : residueTuple (B i) z = residueTuple (B i) w) :
    residueTuple (cumulativeBlockPrimes B i.val) z = residueTuple (cumulativeBlockPrimes B i.val) w := by
  apply (residueTuple_eq_iff _ _ _).mpr
  intro p hp j
  rw [cumulativeBlockPrimes_eq_union] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (residueTuple_eq_iff _ _ _).mp hprev p hp j
  · exact (residueTuple_eq_iff _ _ _).mp hnew p hp j

noncomputable def physicalNode {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n) ×
      (∀ p : pastBlockPrimes B i, Fin n → ZMod p.val) :=
  (physicalStateAt (E := E) G d A h e start B i z, residueTuple (pastBlockPrimes B i) z.val)

theorem physical_fixed_residue_children {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) (S : Finset G.points)
    (hstate : ∀ w ∈ S, physicalStateAt (E := E) G d A h e start B i w =
      physicalStateAt (E := E) G d A h e start B i z)
    (hres : ∀ w ∈ S, residueTuple (cumulativeBlockPrimes B i) w.val =
      residueTuple (cumulativeBlockPrimes B i) z.val) :
    (S.image (physicalNode (E := E) G d A h e start B (i+1))).card ≤
      kernelCountBudget (d i) h (pathDegreeBudget n d A h e i) *
        patchCountBudget n A h (kernelDegreeBudget (d i) h (pathDegreeBudget n d A h e i)) := by
  classical
  let s := physicalStateAt (E := E) G d A h e start B i z
  let W := physicalKernel (E := E) G d z.val i s B
  let L := kernelChildList G (d i) A h (pathDegreeBudget n d A h e i) s.1 W
  have hz := physicalStateAt_good (E := E) G d A h e start hs B i z
  have hL := kernelChildList_spec G (d i) A h (pathDegreeBudget n d A h e i) s.1 W hz.1
  let f := fun t : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n =>
    (t, residueTuple (pastBlockPrimes B (i+1)) z.val)
  have hsub : S.image (physicalNode (E := E) G d A h e start B (i+1)) ⊆ L.toFinset.image f := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    have hsw := physicalStateAt_good (E := E) G d A h e start hs B i w
    have hstep := physical_step (E := E) G d A h e w.val w.property i _ hsw B
    have hkernel : physicalKernel (E := E) G d w.val i s B = W := by
      unfold W physicalKernel
      congr 1
      exact evaluationCell_eq_of_congruent _ _ _ _ _ ((residueTuple_eq_iff _ _ _).mp (hres w hw))
    have hm : physicalStateAt (E := E) G d A h e start B (i+1) w ∈ L := by
      rw [physicalStateAt_succ]
      have hm := hstep.2.1
      rw [hstate w hw] at hm ⊢
      change physicalNext G d A h e w.val i s (physicalKernel (E := E) G d w.val i s B) ∈ L
      change physicalNext G d A h e w.val i s (physicalKernel (E := E) G d w.val i s B) ∈
        kernelChildList G (d i) A h (pathDegreeBudget n d A h e i) s.1 (physicalKernel (E := E) G d w.val i s B) at hm
      rw [hkernel] at hm ⊢
      exact hm
    refine Finset.mem_image.mpr ⟨_,List.mem_toFinset.mpr hm,?_⟩
    apply Prod.ext
    · rfl
    · change residueTuple (pastBlockPrimes B (i+1)) z.val = residueTuple (pastBlockPrimes B (i+1)) w.val
      rw [pastBlockPrimes_succ]
      exact (hres w hw).symm
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans
    ((List.toFinset_card_le L).trans hL.1))

end

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

theorem physical_node_branch_bound {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : Fin r) (z : G.points) (S : Finset G.points)
    (hnode : ∀ w ∈ S, physicalNode (E := E) G d A h e start B i.val w =
      physicalNode (E := E) G d A h e start B i.val z)
    (q M b : ℕ) (hM : 1 ≤ M)
    (hdim : affineDimension (physicalStateAt (E := E) G d A h e start B i.val z).1 ≤ q)
    (hprime : ∀ p ∈ B i, p.Prime) (hupper : ∀ p ∈ B i, p ≤ M)
    (hbad : ∀ w ∈ S, ((B i).filter fun p : ℕ => (p : ℤ) ∣
      eval w.val (physicalStateAt (E := E) G d A h e start B i.val w).2.minor).card ≤ b) :
    (S.image (physicalNode (E := E) G d A h e start B (i.val+1))).card ≤
      (2^(B i).card * ((pathDegreeBudget n d A h e i.val+1)^n)^(B i).card *
        M^(q*(B i).card+n*b)) *
      (kernelCountBudget (d i.val) h (pathDegreeBudget n d A h e i.val) *
        patchCountBudget n A h (kernelDegreeBudget (d i.val) h (pathDegreeBudget n d A h e i.val))) := by
  classical
  let P := (physicalStateAt (E := E) G d A h e start B i.val z).2
  let s := physicalStateAt (E := E) G d A h e start B i.val z
  have hg := physicalStateAt_good (E := E) G d A h e start hs B i.val z
  have hstate (w : G.points) (hw : w ∈ S) :
      physicalStateAt (E := E) G d A h e start B i.val w = s :=
    congrArg Prod.fst (hnode w hw)
  have hprev (w : G.points) (hw : w ∈ S) :
      residueTuple (pastBlockPrimes B i.val) w.val = residueTuple (pastBlockPrimes B i.val) z.val :=
    congrArg Prod.snd (hnode w hw)
  let label : G.points → ∀ p : B i, Fin n → ZMod p.val := fun w => residueTuple (B i) w.val
  let K := kernelCountBudget (d i.val) h (pathDegreeBudget n d A h e i.val) *
        patchCountBudget n A h (kernelDegreeBudget (d i.val) h (pathDegreeBudget n d A h e i.val))
  have hfib (a) (ha : a ∈ S.image label) :
      ((S.filter fun w => label w = a).image (physicalNode (E := E) G d A h e start B (i.val+1))).card ≤ K := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    apply physical_fixed_residue_children G d A h e start hs B i.val v
    · intro w hw
      obtain ⟨hw,_⟩ := Finset.mem_filter.mp hw
      exact (hstate w hw).trans (hstate v hv).symm
    · intro w hw
      obtain ⟨hw,hr⟩ := Finset.mem_filter.mp hw
      exact residueTuple_cumulative_eq B i w.val v.val
        ((hprev w hw).trans (hprev v hv).symm) hr
  have hres : (S.image label).card ≤
      2^(B i).card * ((pathDegreeBudget n d A h e i.val+1)^n)^(B i).card * M^(q*(B i).card+n*b) := by
    let Z := S.image (fun w => w.val)
    have hfree : Nat.card P.free ≤ q := hg.2.1.1.trans_le hdim
    have hD : ∀ j, (P.equations j).totalDegree ≤ pathDegreeBudget n d A h e i.val := by
      obtain ⟨dd,hdd,hd,_⟩ := hg.2.2.1
      exact fun j => (hd j).trans hdd
    have hroot : ∀ w ∈ Z, ∀ j, eval w (P.equations j) = 0 := by
      rintro w hw j
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      have hgv := physicalStateAt_good (E := E) G d A h e start hs B i.val v
      rw [hstate v hv] at hgv
      exact IntegerPatch.eval_equation_zero hgv.2.1 hgv.2.2.2.1 j
    have hb : ∀ w ∈ Z, ((B i).filter fun p : ℕ => (p : ℤ) ∣ eval w P.minor).card ≤ b := by
      rintro w hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      have hvb := hbad v hv
      rw [hstate v hv] at hvb
      exact hvb
    have hc := P.card_residue_image (pathDegreeBudget n d A h e i.val) q M b hM hfree hD
      (B i) hprime hupper Z hroot hb
    simpa only [Z,Finset.image_image,Function.comp_def,label] using hc
  exact (card_image_le_mul_fibers S label _ K hfib).trans (Nat.mul_le_mul_right K hres)

end

open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

noncomputable def activePoints {α : Type*} (S : Finset α) (stop : α → ℕ) (i : ℕ) : Finset α :=
  S.filter fun z => i ≤ stop z

theorem activePoints_succ_subset {α : Type*} (S : Finset α) (stop : α → ℕ) (i : ℕ) :
    activePoints S stop (i+1) ⊆ activePoints S stop i := by
  intro z hz
  obtain ⟨hz,hi⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hz,by omega⟩

theorem active_node_count {α : Type*} {β : ℕ → Type*} [∀ i, DecidableEq (β i)] (S : Finset α)
    (stop : α → ℕ) (node : (i : ℕ) → α → β i) (B : ℕ → ℕ) (r C : ℕ)
    (hzero : ((activePoints S stop 0).image (node 0)).card ≤ C)
    (hchild : ∀ i < r, ∀ a ∈ (activePoints S stop (i+1)).image (node i),
      (((activePoints S stop (i+1)).filter fun z => node i z = a).image (node (i+1))).card ≤ B i) :
    ∀ i ≤ r, ((activePoints S stop i).image (node i)).card ≤ C*∏ j ∈ Finset.range i, B j := by
  intro i hi
  induction i with
  | zero => simpa using hzero
  | succ i ih =>
    have hcount := card_image_le_mul_fibers (activePoints S stop (i+1)) (node i) (node (i+1)) (B i)
      (hchild i (by omega))
    have hsub := Finset.card_le_card (Finset.image_subset_image (f := node i) (activePoints_succ_subset S stop i))
    calc
      _ ≤ ((activePoints S stop (i+1)).image (node i)).card * B i := hcount
      _ ≤ ((activePoints S stop i).image (node i)).card * B i := Nat.mul_le_mul_right _ hsub
      _ ≤ (C * ∏ j ∈ Finset.range i, B j) * B i := Nat.mul_le_mul_right _ (ih (by omega))
      _ = _ := by rw [Finset.prod_range_succ,mul_assoc]

theorem active_stopping_count {α : Type*} {β : ℕ → Type*} [∀ i, DecidableEq (β i)] (S : Finset α)
    (stop : α → ℕ) (node : (i : ℕ) → α → β i) (B : ℕ → ℕ) (r L : ℕ)
    (hstop : ∀ z ∈ S, stop z ≤ r)
    (hnodes : ∀ i ≤ r, ((activePoints S stop i).image (node i)).card ≤ B i)
    (hterminal : ∀ i ≤ r, ∀ a ∈ (activePoints S stop i).image (node i),
      (S.filter fun z => stop z = i ∧ node i z = a).card ≤ L) :
    S.card ≤ (∑ i ∈ Finset.range (r+1), B i)*L := by
  classical
  have hs (i : ℕ) (hi : i ≤ r) : (S.filter fun z => stop z = i).card ≤ B i * L := by
    let T := S.filter fun z => stop z = i
    have hsub : T ⊆ activePoints S stop i := by
      intro z hz
      obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz,he.ge⟩
    have hf (a) (ha : a ∈ T.image (node i)) :
        ((T.filter fun z => node i z = a).image id).card ≤ L := by
      have ha' : a ∈ (activePoints S stop i).image (node i) := Finset.image_subset_image hsub ha
      simpa only [Finset.image_id,Finset.filter_filter,T] using hterminal i hi a ha'
    have hh := card_image_le_mul_fibers T (node i) id L hf
    rw [Finset.image_id] at hh
    exact hh.trans (Nat.mul_le_mul_right _ ((Finset.card_le_card (Finset.image_subset_image hsub)).trans (hnodes i hi)))
  calc
    S.card = ∑ i ∈ Finset.range (r+1), (S.filter fun z => stop z = i).card :=
      Finset.card_eq_sum_card_fiberwise (fun z hz => Finset.mem_range.mpr (by have := hstop z hz; omega))
    _ ≤ ∑ i ∈ Finset.range (r+1), B i * L := Finset.sum_le_sum (fun i hi => hs i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem physical_initial_node_count {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (S : Finset G.points)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n))
    (hs : ∀ z ∈ S, start z ∈ L) :
    (S.image (physicalNode (E := E) G d A h e start B 0)).card ≤ L.length := by
  classical
  let f := fun t : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n =>
    (t,residueTuple (pastBlockPrimes B 0) (fun _ : Fin n => 0))
  have hsub : S.image (physicalNode (E := E) G d A h e start B 0) ⊆ L.toFinset.image f := by
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_image.mpr ⟨start z,List.mem_toFinset.mpr (hs z hz),?_⟩
    apply Prod.ext
    · rfl
    · apply (residueTuple_eq_iff _ _ _).mpr
      simp
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (List.toFinset_card_le L))

end QuarticPowerFree

end OAI
