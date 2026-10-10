import OAI.NumberTheory.PowerFree.PrimePools

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

def physicalDegreeRecord (n A h : ℕ) (chooseDegree : ℕ → ℕ → ℕ) (e : ℕ) : ℕ → ℕ
  | 0 => e
  | i+1 => patchDegreeBudget n A h
      (kernelDegreeBudget (chooseDegree i (physicalDegreeRecord n A h chooseDegree e i)) h
        (physicalDegreeRecord n A h chooseDegree e i))

theorem physicalDegreeRecord_eq_path (n A h e : ℕ) (chooseDegree : ℕ → ℕ → ℕ) :
    ∀ i, pathDegreeBudget n (fun j => chooseDegree j (physicalDegreeRecord n A h chooseDegree e j))
      A h e i = physicalDegreeRecord n A h chooseDegree e i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih => simp only [pathDegreeBudget,physicalDegreeRecord,ih]

theorem physical_degree_schedule (n A h e r : ℕ) (chooseDegree : ℕ → ℕ → ℕ) :
    ∃ d : ℕ → ℕ, ∃ E : ℕ, ∀ i < r,
      d i = chooseDegree i (pathDegreeBudget n d A h e i) ∧ d i ≤ E := by
  let d := fun j => chooseDegree j (physicalDegreeRecord n A h chooseDegree e j)
  refine ⟨d,(Finset.range r).sup d,?_⟩
  intro i hi
  refine ⟨?_,Finset.le_sup (f := d) (Finset.mem_range.mpr hi)⟩
  dsimp only [d]
  rw [physicalDegreeRecord_eq_path]

theorem physical_block_width (a γ ζ : ℝ) (T t : ℕ)
    (ha : 0 ≤ a) (hγ : 0 < γ) (hζ : 0 < ζ) (hwidth : ζ*T ≤ γ)
    (hlo : ⌊(a+γ)/ζ⌋₊ < t) (hhi : t ≤ ⌊(a+γ)/ζ⌋₊+T) :
    a+γ ≤ ζ*t ∧ ζ*t ≤ a+2*γ := by
  have hx : 0 ≤ (a+γ)/ζ := div_nonneg (by linarith) hζ.le
  have hfloor : (⌊(a+γ)/ζ⌋₊:ℝ) ≤ (a+γ)/ζ := Nat.floor_le hx
  have ht : (a+γ)/ζ < (t:ℝ) := (Nat.floor_lt hx).mp hlo
  have htc : (t:ℝ) ≤ (⌊(a+γ)/ζ⌋₊:ℝ)+T := by exact_mod_cast hhi
  constructor
  · exact (div_lt_iff₀ hζ).mp ht |>.le.trans_eq (mul_comm _ _)
  · have hh := (le_div_iff₀ hζ).mp hfloor
    nlinarith

theorem physical_cumulative_margin {r : ℕ} (a δ : Fin r → ℝ) (t : Fin r → ℕ)
    (γ ζ ξ : ℝ) (ha : ∀ i, 0 ≤ a i) (hγ : 0 < γ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hloss : ξ*((∑ i, a i)+(r:ℝ)*γ) ≤ γ/2)
    (hwidth : ∀ i, a i+γ ≤ ζ*t i)
    (hδ : ∀ i, δ i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), a j) :
    ∀ i, δ i+γ/2 ≤ (1-ξ)*ζ*∑ j ∈
      Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), (t j:ℝ) := by
  classical
  intro i
  let J := Finset.univ.filter (fun j : Fin r => j.val ≤ i.val)
  have hiJ : i ∈ J := by simp [J]
  have hcard : 1 ≤ J.card := Finset.one_le_card.mpr ⟨i,hiJ⟩
  have hcardr : J.card ≤ r := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  have hs : ∑ j ∈ J, a j ≤ ∑ j, a j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => ha j)
  have hsum : (∑ j ∈ J, a j)+(J.card:ℝ)*γ ≤ ζ*∑ j ∈ J, (t j:ℝ) := by
    simpa only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
      using Finset.sum_le_sum (fun j (_ : j ∈ J) => hwidth j)
  have hcr : (J.card:ℝ) ≤ r := by exact_mod_cast hcardr
  have hc1 : (1:ℝ) ≤ J.card := by exact_mod_cast hcard
  have hg : γ ≤ (J.card:ℝ)*γ := by nlinarith
  have hsmall : ξ*((∑ j ∈ J, a j)+(J.card:ℝ)*γ) ≤ γ/2 :=
    (mul_le_mul_of_nonneg_left (by nlinarith) hξ0).trans hloss
  have hmul := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hξ1)
  have hd := hδ i
  change δ i ≤ ∑ j ∈ J, a j at hd
  dsimp only [J] at *
  nlinarith

end
section
open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_stagewise_stopped_count {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (S : Finset G.points) (M b : Fin r → ℕ)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)) (T : ℕ)
    (Ex : ℕ → Ideal (MvPolynomial (Fin n) ℂ) → Prop)
    (hstart : ∀ z ∈ S, start z ∈ L) (hT : 1 ≤ T)
    (hroot : ∀ z ∈ S, affineDimension (start z).1 ≤ r)
    (hM : ∀ i, 1 ≤ M i) (hprime : ∀ i, ∀ p ∈ B i, p.Prime)
    (hupper : ∀ i, ∀ p ∈ B i, p ≤ M i)
    (hbad : ∀ i : Fin r, ∀ z ∈ S,
      ((B i).filter fun p : ℕ => (p:ℤ) ∣ eval z.val
        (physicalStateAt (E := E) G d A h e start B i.val z).2.minor).card ≤ b i)
    (hcut : ∀ i < r, ∀ z ∈ S,
      ¬ Ex i (physicalStateAt (E := E) G d A h e start B i z).1 →
      affineDimension (physicalStateAt (E := E) G d A h e start B i z).1 = r-i →
      affineDimension (physicalStateAt (E := E) G d A h e start B (i+1) z).1 <
        affineDimension (physicalStateAt (E := E) G d A h e start B i z).1)
    (hex : ∀ i ≤ r, ∀ z ∈ S,
      Ex i (physicalStateAt (E := E) G d A h e start B i z).1 →
      (G.points.filter (PointOn (physicalStateAt (E := E) G d A h e start B i z).1)).card ≤ T) :
    S.card ≤ (∑ i ∈ Finset.range (r+1), L.length * ∏ j ∈ Finset.range i,
      if hj : j < r then physicalBranchAllowance n d A h e B M b
        (fun k => r-k.val) ⟨j,hj⟩ else 1) * T := by
  classical
  let dim := fun z i => affineDimension (physicalStateAt (E := E) G d A h e start B i z).1
  let ex := fun z i => Ex i (physicalStateAt (E := E) G d A h e start B i z).1
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

section
open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_initial_context {n : ℕ} (G : KernelGeometry n) (A h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (hd : affineDimension I ≤ h) (he : affineDegree I ≤ e)
    (hG : ∀ z ∈ G.points, PointOn I z) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n),
      L.length ≤ patchCountBudget n A h e ∧
    ∃ start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n,
      ∀ z, start z ∈ L ∧ PhysicalState G h (patchDegreeBudget n A h e) z.val (start z) ∧
        I ≤ (start z).1 ∧ EquationLock (start z).1 G.points A := by
  classical
  obtain ⟨L,hL,hgood,hcover⟩ := bounded_integer_patch_cover A h e I hd he G.points hG
    G.height G.one_le_height G.bounded
  choose start hstart hcov using fun z : G.points => hcover z.val z.property
  refine ⟨L,hL,start,fun z => ⟨hstart z,?_,?_,?_⟩⟩
  · have hs := hgood (start z) (hstart z)
    exact ⟨⟨hs.1,hs.2.2.1,hs.2.2.2.1⟩,hs.2.2.2.2.1,hs.2.2.2.2.2.1,hcov z⟩
  · exact (hgood _ (hstart z)).2.1
  · exact (hgood _ (hstart z)).2.2.2.2.2.2

theorem physicalStateAt_context {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hstart : ∀ z, I ≤ (start z).1 ∧ EquationLock (start z).1 G.points A)
    (i : ℕ) (z : G.points) :
    I ≤ (physicalStateAt (E := E) G d A h e start B i z).1 ∧
      EquationLock (physicalStateAt (E := E) G d A h e start B i z).1 G.points A := by
  induction i with
  | zero => exact hstart z
  | succ i ih =>
    have step := physical_step (E := E) G d A h e z.val z.property i _
      (physicalStateAt_good (E := E) G d A h e start hs B i z) B
    rw [physicalStateAt_succ]
    refine ⟨ih.1.trans step.2.2.1,?_⟩
    exact ((kernelChildList_spec G (d i) A h (pathDegreeBudget n d A h e i) _ _
      (physicalStateAt_good (E := E) G d A h e start hs B i z).1).2.1 _ step.2.1).1.2.2.2.2.2.2

end

section
open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_hilbert_stage_cuts {n r : ℕ} (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (δ c : Fin r → ℝ) (ν Cbox : ℝ)
    (hδ : ∀ i, 0 < δ i) (hc : ∀ i, 0 ≤ c i) (hν : 0 < ν) (hC : 1 ≤ Cbox) :
    ∃ D : Fin r → ℕ, ∃ X₀ : ℝ, ∀ X : ℝ, X₀ < X →
      ∀ (E : ℕ) (G : KernelGeometry n) (d : ℕ → ℕ) (A h e : ℕ),
      (∀ i : Fin r, D i ≤ d i.val ∧ d i.val ≤ E) →
      (∀ w ∈ G.points, ∀ j, |(w j : ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n),
      (∀ z, PhysicalState G h e z.val (start z)) →
      ∀ (B : Fin r → Finset ℕ) (ξ ζ : ℝ), 1 ≤ X → 0 ≤ ζ →
      (∀ a b, a ≠ b → Disjoint (B a) (B b)) →
      (∀ j p, p ∈ B j → p.Prime ∧ X^ζ ≤ (p:ℝ)) →
      (∀ i : Fin r, δ i+ν ≤ (1-ξ)*ζ*∑ j ∈
        Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), ((B j).card:ℝ)) →
      ∀ (i : Fin r) (z : G.points), PhysicalRegular (E := E) G d A h e r start B ξ z →
      affineDimension (physicalStateAt (E := E) G d A h e start B i.val z).1 = r-i.val →
      (∀ T : ℝ, 1 ≤ T → T^(r-i.val) / (((r-i.val).factorial : ℝ)*(δ i)^(r-i.val)) -
        c i*T^(r-i.val-1) ≤ weightedHilbert
          (physicalStateAt (E := E) G d A h e start B i.val z).1 ω T) →
      affineDimension (physicalStateAt (E := E) G d A h e start B (i.val+1) z).1 <
        affineDimension (physicalStateAt (E := E) G d A h e start B i.val z).1 := by
  classical
  choose D X₀ hcut using fun i : Fin r => physical_weighted_descent ω hω (r-i.val)
    (by omega) (δ i) ν (c i) Cbox (hδ i) hν (hc i) hC
  refine ⟨D,∑ i, |X₀ i|,?_⟩
  intro X hX E G d A h e hD hbox start hs B ξ ζ hX1 hζ hdisj hp hnum i z hz hdim hH
  have hXi : X₀ i < X := lt_of_le_of_lt ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (X₀ j)) (Finset.mem_univ i))) hX
  let s := physicalStateAt (E := E) G d A h e start B i.val z
  let Q := (cumulativeBlockPrimes B i.val).filter (fun p : ℕ => ¬ (p:ℤ) ∣ eval z.val s.2.minor)
  have hprod : X^(δ i+ν) ≤ ∏ p ∈ Q, (p:ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hX1 (hnum i)).trans
      (cumulative_good_prime_product B hdisj i.val (eval z.val s.2.minor) X ζ ξ hX1 hζ
        (fun j p hpj => (hp j p hpj).2)
        (fun j => PhysicalRegular.bad_minor G d A h e r start B ξ z hz i.val i.isLt.le j))
  rw [physicalStateAt_succ]
  apply hcut i X hXi r E G d A h e i.val (hD i).1 (hD i).2 hbox z.val z.property s
    (physicalStateAt_good (E := E) G d A h e start hs B i.val z) hdim hH B Q
    (Finset.filter_subset _ _)
  · intro p hpp
    obtain ⟨j,_,hpj⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hpp).1
    exact (hp j p hpj).1
  · intro p hpp
    exact (Finset.mem_filter.mp hpp).2
  · exact hprod

theorem physical_regular_count {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (M : Fin r → ℕ) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)) (T : ℕ)
    (Ex : ℕ → Ideal (MvPolynomial (Fin n) ℂ) → Prop)
    (hstart : ∀ z, start z ∈ L) (hT : 1 ≤ T)
    (hroot : ∀ z, affineDimension (start z).1 ≤ r)
    (hM : ∀ i, 1 ≤ M i) (hprime : ∀ i, ∀ p ∈ B i, p.Prime)
    (hupper : ∀ i, ∀ p ∈ B i, p ≤ M i)
    (hhalf : (G.points.card:ℝ)/2 ≤ (Finset.univ.filter
      (PhysicalRegular (E := E) G d A h e r start B ξ)).card)
    (hcut : ∀ i < r, ∀ z, PhysicalRegular (E := E) G d A h e r start B ξ z →
      ¬ Ex i (physicalStateAt (E := E) G d A h e start B i z).1 →
      affineDimension (physicalStateAt (E := E) G d A h e start B i z).1 = r-i →
      affineDimension (physicalStateAt (E := E) G d A h e start B (i+1) z).1 <
        affineDimension (physicalStateAt (E := E) G d A h e start B i z).1)
    (hex : ∀ i ≤ r, ∀ z, Ex i (physicalStateAt (E := E) G d A h e start B i z).1 →
      (G.points.filter (PointOn (physicalStateAt (E := E) G d A h e start B i z).1)).card ≤ T) :
    G.points.card ≤ 2*(∑ i ∈ Finset.range (r+1), L.length * ∏ j ∈ Finset.range i,
      if hj : j < r then physicalBranchAllowance n d A h e B M
        (fun k => ⌊ξ*(B k).card⌋₊) (fun k => r-k.val) ⟨j,hj⟩ else 1) * T := by
  classical
  let S := Finset.univ.filter (PhysicalRegular (E := E) G d A h e r start B ξ)
  have hS (z) (hz : z ∈ S) : PhysicalRegular (E := E) G d A h e r start B ξ z :=
    (Finset.mem_filter.mp hz).2
  have hc := physical_stagewise_stopped_count G d A h e start hs B S M
    (fun k => ⌊ξ*(B k).card⌋₊) L T Ex (fun z _ => hstart z) hT (fun z _ => hroot z)
    hM hprime hupper
    (fun i z hz => (Nat.le_floor_iff (mul_nonneg hξ (Nat.cast_nonneg _))).mpr
      (PhysicalRegular.bad_minor G d A h e r start B ξ z (hS z hz) i.val i.isLt.le i))
    (fun i hi z hz => hcut i hi z (hS z hz)) (fun i hi z _ => hex i hi z)
  have hhalf' : G.points.card ≤ 2*S.card := by
    have hh : (G.points.card : ℝ) ≤ 2*(S.card : ℝ) := by linarith
    exact_mod_cast hh
  exact hhalf'.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hc)

end

open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_branch_power_bound {r : ℕ} (n : ℕ) (d : ℕ → ℕ) (A h e : ℕ)
    (U : Fin r → ℕ) (q : Fin r → ℕ) (K ξ : ℝ) (hK : 1 ≤ K) (hξ : 0 ≤ ξ) :
    ∃ C : Fin r → ℝ, (∀ i, 1 ≤ C i) ∧
    ∀ X ζ : ℝ, 1 ≤ X → 0 ≤ ζ → ∀ (B : Fin r → Finset ℕ) (M : Fin r → ℕ),
      (∀ i, (B i).card ≤ U i) → (∀ i, (M i : ℝ) ≤ K*X^ζ) →
      ∀ i, (physicalBranchAllowance n d A h e B M (fun k => ⌊ξ*(B k).card⌋₊) q i : ℝ) ≤
        C i*X^(ζ*((q i:ℝ)*(U i:ℝ)+(n:ℝ)*ξ*(U i:ℝ))) := by
  classical
  let F := fun i : Fin r => kernelCountBudget (d i.val) h (pathDegreeBudget n d A h e i.val) *
    patchCountBudget n A h (kernelDegreeBudget (d i.val) h (pathDegreeBudget n d A h e i.val))
  let m := fun i : Fin r => q i*U i+n*⌊ξ*U i⌋₊
  let C := fun i : Fin r => max 1 ((2:ℝ)^(U i)*(((pathDegreeBudget n d A h e i.val+1:ℕ):ℝ)^n)^(U i)*
    K^(m i)*(F i:ℝ))
  refine ⟨C,fun i => le_max_left _ _,?_⟩
  intro X ζ hX hζ B M hU hM i
  have hxc : 1 ≤ K*X^ζ := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hX hζ)
  have hm : q i*(B i).card+n*⌊ξ*(B i).card⌋₊ ≤ m i := by
    apply Nat.add_le_add (Nat.mul_le_mul_left _ (hU i))
    apply Nat.mul_le_mul_left
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hU i) hξ
  have hpow : (M i:ℝ)^(q i*(B i).card+n*⌊ξ*(B i).card⌋₊) ≤ (K*X^ζ)^(m i) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (hM i) _).trans (pow_le_pow_right₀ hxc hm)
  have he : ζ*(m i:ℝ) ≤ ζ*((q i:ℝ)*(U i:ℝ)+(n:ℝ)*ξ*(U i:ℝ)) := by
    have hh := Nat.floor_le (mul_nonneg hξ (Nat.cast_nonneg (U i)))
    dsimp only [m]
    push_cast
    apply mul_le_mul_of_nonneg_left _ hζ
    calc
      _ ≤ (q i:ℝ)*U i+n*(ξ*U i) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n))
      _ = _ := by ring
  have hdeg : 1 ≤ ((pathDegreeBudget n d A h e i.val+1:ℕ):ℝ)^n := by
    apply one_le_pow₀
    exact_mod_cast Nat.le_add_left 1 _
  calc
    _ = (2:ℝ)^(B i).card * (((pathDegreeBudget n d A h e i.val+1:ℕ):ℝ)^n)^(B i).card *
      (M i:ℝ)^(q i*(B i).card+n*⌊ξ*(B i).card⌋₊) * (F i:ℝ) := by
        simp only [physicalBranchAllowance,F,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    _ ≤ (2:ℝ)^(U i) * (((pathDegreeBudget n d A h e i.val+1:ℕ):ℝ)^n)^(U i) *
      (K*X^ζ)^(m i) * (F i:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul _ hpow (pow_nonneg (Nat.cast_nonneg _) _) (by positivity)
        exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (hU i))
          (pow_le_pow_right₀ hdeg (hU i)) (by positivity) (by positivity)
    _ = ((2:ℝ)^(U i) * (((pathDegreeBudget n d A h e i.val+1:ℕ):ℝ)^n)^(U i) *
      K^(m i)*(F i:ℝ))*X^(ζ*(m i:ℝ)) := by
        rw [mul_pow,← Real.rpow_mul_natCast (zero_le_one.trans hX)]
        ring
    _ ≤ C i*X^(ζ*(m i:ℝ)) := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (zero_le_one.trans hX) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX he)
      ((le_max_left _ _ : (1:ℝ) ≤ C i).trans' zero_le_one)

theorem stopped_forest_power_bound {r : ℕ} (L : ℕ) (b : Fin r → ℕ)
    (C κ : Fin r → ℝ) (hC : ∀ i, 1 ≤ C i) (hκ : ∀ i, 0 ≤ κ i)
    (X : ℝ) (hX : 1 ≤ X) (hb : ∀ i, (b i : ℝ) ≤ C i*X^(κ i)) :
    ((∑ i ∈ Finset.range (r+1), L * ∏ j ∈ Finset.range i,
      if hj : j < r then b ⟨j,hj⟩ else 1 : ℕ):ℝ) ≤
      (r+1:ℕ)*(L:ℝ)*(∏ j, C j)*X^(∑ j, κ j) := by
  classical
  let F : ℕ → ℝ := fun j => if hj : j < r then C ⟨j,hj⟩*X^(κ ⟨j,hj⟩) else 1
  have hF : ∀ j, 1 ≤ F j := by
    intro j
    dsimp only [F]
    split_ifs with hj
    · exact one_le_mul_of_one_le_of_one_le (hC ⟨j,hj⟩) (Real.one_le_rpow hX (hκ ⟨j,hj⟩))
    · rfl
  have hprod (i : ℕ) (hi : i ≤ r) :
      ((∏ j ∈ Finset.range i, if hj : j < r then b ⟨j,hj⟩ else 1 : ℕ):ℝ) ≤
        (∏ j, C j)*X^(∑ j, κ j) := by
    calc
      _ ≤ ∏ j ∈ Finset.range i, F j := by
        rw [Nat.cast_prod]
        apply Finset.prod_le_prod₀
        · intro j _; exact Nat.cast_nonneg _
        · intro j _
          dsimp only [F]
          split_ifs with hj
          · exact hb ⟨j,hj⟩
          · norm_num
      _ ≤ ∏ j ∈ Finset.range r, F j :=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.range_mono hi)
          (fun j _ => zero_le_one.trans (hF j)) (fun j _ _ => hF j)
      _ = ∏ j : Fin r, C j*X^(κ j) := by
        rw [← Fin.prod_univ_eq_prod_range]
        simp [F]
      _ = _ := by rw [Finset.prod_mul_distrib,Real.rpow_sum_of_pos (zero_lt_one.trans_le hX)]
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _i ∈ Finset.range (r+1), (L:ℝ)*((∏ j, C j)*X^(∑ j, κ j)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left (hprod i (by have := Finset.mem_range.mp hi; omega)) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end QuarticPowerFree

end OAI
