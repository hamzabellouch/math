import OAI.NumberTheory.PowerFree.WeightedRelations

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

noncomputable def physicalPathProduct {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (z : G.points) : ℤ :=
  ((adaptiveStates (physicalKernel (E := E) G d z.val) (physicalNext G d A h e z.val)
    m 0 (start z) B).map (fun t => eval z.val t.2.minor)).prod

theorem physical_minor_dvd_pathProduct {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (z : G.points) (i : ℕ) (hi : i ≤ m) :
    eval z.val (physicalStateAt (E := E) G d A h e start B i z).2.minor ∣
      physicalPathProduct (E := E) G d A h e m start B z := by
  apply List.dvd_prod
  apply List.mem_map.mpr
  exact ⟨physicalStateAt (E := E) G d A h e start B i z,
    adaptiveStateAt_mem_states _ _ m i 0 _ B hi,rfl⟩

def PhysicalRegular {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (ξ : ℝ) (z : G.points) : Prop :=
  ∀ j, ((∑ p ∈ B j, if (p : ℤ) ∣ physicalPathProduct (E := E) G d A h e m start B z
    then (1 : ℝ) else 0) / (B j).card) ≤ ξ

theorem filter_card_le_of_fraction {α : Type*} (S : Finset α) (P : α → Prop)
    [DecidablePred P] (ξ : ℝ)
    (h : (∑ p ∈ S, if P p then (1 : ℝ) else 0) / S.card ≤ ξ) :
    ((S.filter P).card : ℝ) ≤ ξ*S.card := by
  by_cases hs : S.card = 0
  · have he := Finset.card_eq_zero.mp hs
    subst S
    simp
  have hp : (0 : ℝ) < S.card := by exact_mod_cast (Nat.pos_of_ne_zero hs)
  rw [Finset.sum_boole] at h
  exact (div_le_iff₀ hp).mp h

theorem PhysicalRegular.bad_minor {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (ξ : ℝ) (z : G.points)
    (hz : PhysicalRegular (E := E) G d A h e m start B ξ z) (i : ℕ) (hi : i ≤ m) (j : Fin r) :
    (((B j).filter fun p : ℕ => (p:ℤ) ∣ eval z.val
      (physicalStateAt (E := E) G d A h e start B i z).2.minor).card : ℝ) ≤ ξ*(B j).card := by
  have hsub : ((B j).filter fun p : ℕ => (p:ℤ) ∣ eval z.val
      (physicalStateAt (E := E) G d A h e start B i z).2.minor) ⊆
      ((B j).filter fun p : ℕ => (p:ℤ) ∣ physicalPathProduct (E := E) G d A h e m start B z) := by
    intro p hp
    obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp,hd.trans (physical_minor_dvd_pathProduct G d A h e m start B z i hi)⟩
  calc
    _ ≤ (((B j).filter fun p : ℕ =>
        (p:ℤ) ∣ physicalPathProduct (E := E) G d A h e m start B z).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := filter_card_le_of_fraction _ _ ξ (hz j)

theorem cumulative_good_prime_product {r : ℕ} (B : Fin r → Finset ℕ)
    (hdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b)) (i : ℕ) (v : ℤ)
    (X ζ ξ : ℝ) (hX : 1 ≤ X) (hζ : 0 ≤ ζ)
    (hlo : ∀ j p, p ∈ B j → X^ζ ≤ (p:ℝ))
    (hbad : ∀ j, (((B j).filter fun p : ℕ => (p:ℤ) ∣ v).card : ℝ) ≤ ξ*(B j).card) :
    X^((1-ξ)*ζ*∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val ≤ i), ((B j).card : ℝ)) ≤
      ∏ p ∈ (cumulativeBlockPrimes B i).filter (fun p : ℕ => ¬ (p:ℤ) ∣ v), (p:ℝ) := by
  classical
  let J := Finset.univ.filter (fun j : Fin r => j.val ≤ i)
  let Q := (cumulativeBlockPrimes B i).filter (fun p : ℕ => ¬ (p:ℤ) ∣ v)
  have hg (j : Fin r) : (1-ξ)*(B j).card ≤
      (((B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v).card : ℝ) := by
    have hc := Finset.card_filter_add_card_filter_not (s := B j) (fun p : ℕ => (p:ℤ) ∣ v)
    have hcr : (((B j).filter fun p : ℕ => (p:ℤ) ∣ v).card : ℝ) +
      (((B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v).card : ℝ) = (B j).card := by exact_mod_cast hc
    nlinarith [hbad j]
  have heq : Q = J.biUnion (fun j => (B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v) := by
    ext p
    simp only [Q,J,cumulativeBlockPrimes,Finset.mem_filter,Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨j,hj,hp⟩,hg⟩
      exact ⟨j,hj,hp,hg⟩
    · rintro ⟨j,hj,hp,hg⟩
      exact ⟨⟨j,hj,hp⟩,hg⟩
  have hpair : (J : Set (Fin r)).PairwiseDisjoint
      (fun j => (B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v) := by
    intro a _ b _ hab
    exact (hdisj a b hab).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcard : (1-ξ)*(∑ j ∈ J, ((B j).card : ℝ)) ≤ (Q.card : ℝ) := by
    rw [heq,Finset.card_biUnion hpair,Nat.cast_sum,Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hg j)
  calc
    _ ≤ X^(ζ*(Q.card : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hX
      nlinarith
    _ = (X^ζ)^Q.card := Real.rpow_mul_natCast (zero_le_one.trans hX) ζ Q.card
    _ = ∏ _p ∈ Q, X^ζ := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod₀
      · intro p _; exact Real.rpow_nonneg (zero_le_one.trans hX) _
      · intro p hp
        obtain ⟨j,_,hpj⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hp).1
        exact hlo j p hpj

end

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

noncomputable def firstStop (r : ℕ) (P : ℕ → Prop) : ℕ :=
  Nat.find (show ∃ i, i = r ∨ P i from ⟨r,Or.inl rfl⟩)

theorem firstStop_le (r : ℕ) (P : ℕ → Prop) : firstStop r P ≤ r :=
  Nat.find_min' _ (Or.inl rfl)

theorem firstStop_spec (r : ℕ) (P : ℕ → Prop) : firstStop r P = r ∨ P (firstStop r P) :=
  Nat.find_spec (show ∃ i, i = r ∨ P i from ⟨r,Or.inl rfl⟩)

theorem firstStop_not_before (r : ℕ) (P : ℕ → Prop) {i : ℕ} (hi : i < firstStop r P) : ¬ P i :=
  fun hp => Nat.find_min _ hi (Or.inr hp)

theorem dimension_until_firstStop (r : ℕ) (dim : ℕ → ℕ) (Ex : ℕ → Prop)
    (hzero : dim 0 ≤ r) (hmono : ∀ i < r, dim (i+1) ≤ dim i)
    (hstep : ∀ i < r, ¬ Ex i → dim i = r-i → dim (i+1) < dim i) :
    ∀ i ≤ firstStop r (fun i => Ex i ∨ dim i = 0), dim i ≤ r-i := by
  intro i
  induction i with
  | zero => intro _; simpa using hzero
  | succ i ih =>
    intro hi
    have his : i < firstStop r (fun i => Ex i ∨ dim i = 0) := by omega
    have hir : i < r := lt_of_lt_of_le his (firstStop_le _ _)
    have hd := ih his.le
    have hstop := firstStop_not_before r (fun i => Ex i ∨ dim i = 0) his
    by_cases he : dim i = r-i
    · have hs := hstep i hir (fun h => hstop (Or.inl h)) he
      omega
    · have hm := hmono i hir
      omega

theorem firstStop_terminal (r : ℕ) (dim : ℕ → ℕ) (Ex : ℕ → Prop)
    (hzero : dim 0 ≤ r) (hmono : ∀ i < r, dim (i+1) ≤ dim i)
    (hstep : ∀ i < r, ¬ Ex i → dim i = r-i → dim (i+1) < dim i) :
    let t := firstStop r (fun i => Ex i ∨ dim i = 0)
    Ex t ∨ dim t = 0 := by
  dsimp only
  rcases firstStop_spec r (fun i => Ex i ∨ dim i = 0) with he | hp
  · right
    have hd := dimension_until_firstStop r dim Ex hzero hmono hstep
      (firstStop r (fun i => Ex i ∨ dim i = 0)) le_rfl
    rw [he,Nat.sub_self] at hd
    rw [he]
    exact Nat.eq_zero_of_le_zero hd
  · exact hp

theorem physical_fiber_le_points {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) (S : Finset G.points) :
    (S.filter fun w => physicalNode (E := E) G d A h e start B i w =
      physicalNode (E := E) G d A h e start B i z).card ≤
    (G.points.filter (PointOn (physicalStateAt (E := E) G d A h e start B i z).1)).card := by
  classical
  let F := S.filter fun w => physicalNode (E := E) G d A h e start B i w =
    physicalNode (E := E) G d A h e start B i z
  have hsub : F.image (fun w : G.points => w.val) ⊆
      G.points.filter (PointOn (physicalStateAt (E := E) G d A h e start B i z).1) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w,hw,hwx⟩
    rw [← hwx]
    have hn := (Finset.mem_filter.mp hw).2
    have he := congrArg Prod.fst hn
    change physicalStateAt (E := E) G d A h e start B i w =
      physicalStateAt (E := E) G d A h e start B i z at he
    have hp := (physicalStateAt_good (E := E) G d A h e start hs B i w).2.2.2.1
    rw [he] at hp
    exact Finset.mem_filter.mpr ⟨w.property,hp⟩
  calc
    _ = (F.image (fun w : G.points => w.val)).card :=
      (Finset.card_image_of_injective F Subtype.val_injective).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem physical_dimension_mono {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) :
    affineDimension (physicalStateAt (E := E) G d A h e start B (i+1) z).1 ≤
      affineDimension (physicalStateAt (E := E) G d A h e start B i z).1 := by
  rw [physicalStateAt_succ]
  exact (physical_step (E := E) G d A h e z.val z.property i _
    (physicalStateAt_good (E := E) G d A h e start hs B i z) B).2.2.2.2.1

end

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

theorem physical_stopped_count {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (S : Finset G.points) (M b : Fin r → ℕ)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)) (T : ℕ)
    (Ex : Ideal (MvPolynomial (Fin n) ℂ) → Prop)
    (hstart : ∀ z ∈ S, start z ∈ L) (hT : 1 ≤ T)
    (hroot : ∀ z ∈ S, affineDimension (start z).1 ≤ r)
    (hM : ∀ i, 1 ≤ M i) (hprime : ∀ i, ∀ p ∈ B i, p.Prime)
    (hupper : ∀ i, ∀ p ∈ B i, p ≤ M i)
    (hbad : ∀ i : Fin r, ∀ z ∈ S,
      ((B i).filter fun p : ℕ => (p:ℤ) ∣ eval z.val
        (physicalStateAt (E := E) G d A h e start B i.val z).2.minor).card ≤ b i)
    (hcut : ∀ i < r, ∀ z ∈ S,
      ¬ Ex (physicalStateAt (E := E) G d A h e start B i z).1 →
      affineDimension (physicalStateAt (E := E) G d A h e start B i z).1 = r-i →
      affineDimension (physicalStateAt (E := E) G d A h e start B (i+1) z).1 <
        affineDimension (physicalStateAt (E := E) G d A h e start B i z).1)
    (hex : ∀ i ≤ r, ∀ z ∈ S,
      Ex (physicalStateAt (E := E) G d A h e start B i z).1 →
      (G.points.filter (PointOn (physicalStateAt (E := E) G d A h e start B i z).1)).card ≤ T) :
    S.card ≤ (∑ i ∈ Finset.range (r+1), L.length * ∏ j ∈ Finset.range i,
      if hj : j < r then physicalBranchAllowance n d A h e B M b
        (fun k => r-k.val) ⟨j,hj⟩ else 1) * T := by
  classical
  let dim := fun z i => affineDimension (physicalStateAt (E := E) G d A h e start B i z).1
  let ex := fun z i => Ex (physicalStateAt (E := E) G d A h e start B i z).1
  let stop := fun z => firstStop r (fun i => ex z i ∨ dim z i = 0)
  have hm (z) (i) (_hi : i < r) : dim z (i+1) ≤ dim z i :=
    physical_dimension_mono G d A h e start hs B i z
  have hz (z) (hz : z ∈ S) : dim z 0 ≤ r := hroot z hz
  have hc (z) (hz : z ∈ S) (i) (hi : i < r) :
      ¬ ex z i → dim z i = r-i → dim z (i+1) < dim z i := hcut i hi z hz
  have hd (z) (hz' : z ∈ S) := dimension_until_firstStop r (dim z) (ex z) (hz z hz') (hm z) (hc z hz')
  have ht (z) (hz' : z ∈ S) := firstStop_terminal r (dim z) (ex z) (hz z hz') (hm z) (hc z hz')
  apply physical_forest_count G d A h e start hs B S stop M b (fun k => r-k.val) L T
    hstart (fun _ _ => firstStop_le _ _) hM hprime hupper
  · intro i z hz hi
    exact hd z hz i.val hi.le
  · intro i z hz _
    exact hbad i z hz
  · intro i hi z hz hzi
    have hsub : (S.filter fun w => stop w = i ∧ physicalNode (E := E) G d A h e start B i w =
        physicalNode (E := E) G d A h e start B i z) ⊆
        S.filter (fun w => physicalNode (E := E) G d A h e start B i w =
        physicalNode (E := E) G d A h e start B i z) := by
      intro w hw
      obtain ⟨hw,_,hn⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hw,hn⟩
    apply (Finset.card_le_card hsub).trans
    have hterm : ex z i ∨ dim z i = 0 := by
      have hh := ht z hz
      change ex z (stop z) ∨ dim z (stop z) = 0 at hh
      simpa only [hzi] using hh
    rcases hterm with he | he
    · exact (physical_fiber_le_points G d A h e start hs B i z S).trans (hex i hi z hz he)
    · exact (physical_zeroDim_fiber G d A h e start hs B i z S he).trans hT

end

theorem finite_prime_pool (N M : ℕ) (hM : M ≠ 0) :
    ∃ P : Finset ℕ, P.card = N ∧ ∀ p ∈ P, p.Prime ∧ M < p ∧ p ≤ 2^N*M := by
  induction N with
  | zero => exact ⟨∅,by simp,by simp⟩
  | succ N ih =>
    obtain ⟨P,hcard,hP⟩ := ih
    obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2^N*M)
      (Nat.mul_ne_zero (by positivity) hM)
    have hnot : p ∉ P := fun h => (not_lt_of_ge (hP p h).2.2) hlo
    refine ⟨insert p P,by simp [hnot,hcard],?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · refine ⟨hp,?_,?_⟩
      · exact (Nat.le_mul_of_pos_left M (by positivity : 0 < 2^N)).trans_lt hlo
      · simpa only [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hhi
    · obtain ⟨hqprime,hqlo,hqhi⟩ := hP q hq
      refine ⟨hqprime,hqlo,hqhi.trans ?_⟩
      exact Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by decide) (Nat.le_succ N))

theorem disjoint_prime_pools (r t : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    ∃ P : Fin r → Finset ℕ,
      (∀ i, (P i).card = t) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      ∀ i p, p ∈ P i → p.Prime ∧ x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2^(r*t+1)*x := by
  classical
  obtain ⟨Q,hcard,hQ⟩ := finite_prime_pool (r*t) ⌈x⌉₊
    (Nat.ne_of_gt (Nat.ceil_pos.mpr (zero_lt_one.trans_le hx)))
  let e : (Fin r × Fin t) ≃ Q := Fintype.equivOfCardEq (by simp [hcard])
  let P : Fin r → Finset ℕ := fun i => Finset.univ.image (fun j => (e (i,j)).val)
  have hinj (i : Fin r) : Function.Injective (fun j => (e (i,j)).val) := by
    intro j k he
    exact (Prod.mk.inj (e.injective (Subtype.ext he))).2
  refine ⟨P,?_,?_,?_⟩
  · intro i
    simp only [P,Finset.card_image_of_injective _ (hinj i),Finset.card_univ,Fintype.card_fin]
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hpi
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hpj
    exact hij (Prod.mk.inj (e.injective (Subtype.ext (ha.trans hb.symm)))).1
  · intro i p hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hprime,hlo,hhi⟩ := hQ _ (e (i,j)).property
    refine ⟨hprime,(Nat.le_ceil x).trans (by exact_mod_cast hlo.le),?_⟩
    have hc : (⌈x⌉₊ : ℝ) ≤ 2*x := (Nat.ceil_lt_add_one (zero_le_one.trans hx)).le.trans (by linarith)
    calc
      ((e (i,j)).val : ℝ) ≤ (2 : ℝ)^(r*t)*(⌈x⌉₊ : ℝ) := by exact_mod_cast hhi
      _ ≤ 2^(r*t)*(2*x) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2^(r*t+1)*x := by rw [pow_succ]; ring

end QuarticPowerFree

end OAI
