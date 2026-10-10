import Mathlib
import OAI.Combinatorics.SharpRamsey.Validation.ValidationTools

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {Ω Y : Type*} [Fintype Ω]
theorem produced_exclusion (X W : Finset Ω) (hX : X.Nonempty) (hW : W.Nonempty)
    (hsub : X⊆W) (h : ℕ) (hh : 0<h) (Good : (Fin h → Ω) → Prop)
    (hGood : (9/10:ℝ) ≤ prob (uniformMass X) h Good)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (y : Y) (m : ℕ) :
    PublicTables.integral (rowLaw W hW h) (implementAccept X Good)
      (fun z => if ¬pass R q z y then 1 else 0) m ≤
        6*q*(∑ x∈univ.filter (fun x => R x y),uniformMass X x) := by
  have hd := public_iid_domination X W hX hW hsub h Good hGood
    (fun z => if ¬pass R q z y then 1 else 0) (by intro z; split_ifs <;> norm_num) m
  simp only [mul_ite,mul_one,mul_zero] at hd
  apply hd.trans
  have he := mul_le_mul_of_nonneg_left
    (pointwise_exclusion (uniformMass X) (uniform_nonneg X) (uniform_total hX) R q hq h hh y)
    (show (0:ℝ)≤10/9 by norm_num)
  apply he.trans
  have hp : 0≤∑ x∈univ.filter (fun x => R x y),uniformMass X x :=
    sum_nonneg (fun x _ => uniform_nonneg X x)
  nlinarith [mul_nonneg hq.le hp]

end
end SharpLogRamsey.Validation

namespace SharpLogRamsey.PublicTables
open Finset
open scoped BigOperators Classical
variable {Ω : Type*} [Fintype Ω]

theorem failure_exp (p : Law Ω) (A : Ω → Prop) [DecidablePred A] (m : ℕ) :
    1-integral p A (fun _ => 1) m ≤ Real.exp (-(m:ℝ)*acceptProb p A) := by
  rw [production_probability]
  have hp : 0≤1-acceptProb p A := sub_nonneg.mpr (acceptProb_le_one p A)
  have he := pow_le_pow_left₀ hp (Real.one_sub_le_exp_neg (acceptProb p A)) m
  calc
    _ = (1-acceptProb p A)^m := by ring
    _ ≤ Real.exp (-acceptProb p A)^m := he
    _ = _ := by
      rw [←Real.exp_nat_mul]
      congr 1
      ring

end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.Incidence
open Finset
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem low_incidence_half_target_mass {n : ℕ} (hdim : Module.finrank K V = n+3)
    (w : Projectivization K V → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (M : ℝ) (hM : ∀ x, w x ≤ M)
    (v : Projectivization K (Module.Dual K V) → ℝ) (N : ℝ)
    (hN0 : 0 ≤ N) (hN : ∀ y, v y ≤ N) :
    (∑ y ∈ univ.filter (fun y => weightedIncidences SharpLogRamsey.Incidence.Incident w y <
      1/(2*(Nat.card K:ℝ))), v y) ≤ 36*(Nat.card K:ℝ)^(n+3)*M*N := by
  let q : ℝ := Nat.card K
  let u : ℝ := ∑ i ∈ range (n+2), q^i
  let p : ℝ := u/(∑ i ∈ range (n+3), q^i)
  let B := univ.filter (fun y => weightedIncidences SharpLogRamsey.Incidence.Incident w y < 1/(2*q))
  have hq : 2 ≤ q := by
    change (2:ℝ) ≤ Nat.card K
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)
  have hq0 : 0 < q := by linarith
  have hu : 1 ≤ u := by
    have hs := single_le_sum (f := fun i => q^i)
      (fun i _ => pow_nonneg hq0.le i) (show 0 ∈ range (n+2) by simp)
    simpa [u] using hs
  have hvpos : 0 < ∑ i ∈ range (n+3), q^i := by
    rw [geom_sum_succ]
    change 0 < q*u+1
    positivity
  have hp : 2/(3*q) ≤ p := by
    change 2/(3*q) ≤ u/(∑ i ∈ range (n+3), q^i)
    apply (div_le_div_iff₀ (by positivity) hvpos).mpr
    rw [geom_sum_succ]
    change 2*(q*u+1) ≤ u*(3*q)
    nlinarith
  have hnorm : (∑ x, w x^2) ≤ M := by
    calc
      _ ≤ ∑ x, M*w x := by
        apply sum_le_sum
        intro x _
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (hM x) (hw x)
      _ = M := by rw [← mul_sum, ht, mul_one]
  have hvar := (projective_variance_le hdim w).trans
    (mul_le_mul_of_nonneg_left hnorm (show 0 ≤ q^(n+1) by positivity))
  change (∑ y, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p*(∑ x, w x))^2) ≤ q^(n+1)*M at hvar
  rw [ht, mul_one] at hvar
  have hc : (B.card:ℝ)*(1/(6*q))^2 ≤ q^(n+1)*M := by
    calc
      _ = ∑ _y ∈ B, (1/(6*q))^2 := by simp
      _ ≤ ∑ y ∈ B, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p)^2 := by
        apply sum_le_sum
        intro y hy
        have hb : weightedIncidences SharpLogRamsey.Incidence.Incident w y < 1/(2*q) := (mem_filter.mp hy).2
        have hg : 1/(6*q) ≤ p-weightedIncidences SharpLogRamsey.Incidence.Incident w y := by
          have he : 2/(3*q)-1/(2*q) = 1/(6*q) := by field_simp; ring
          linarith
        have hi : 0 ≤ 1/(6*q) := by positivity
        nlinarith
      _ ≤ ∑ y, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p)^2 := by
        apply sum_le_sum_of_subset_of_nonneg (subset_univ B)
        intro y _ _
        positivity
      _ ≤ _ := hvar
  have hmult := mul_le_mul_of_nonneg_right hc (show 0 ≤ 36*q^2 by positivity)
  have hcancel : (B.card:ℝ)*(1/(6*q))^2*(36*q^2) = B.card := by
    field_simp
    ring
  rw [hcancel] at hmult
  have he : q^(n+1)*M*(36*q^2) = 36*q^(n+3)*M := by
    rw [show n+3 = (n+1)+2 by omega, pow_add]
    ring
  rw [he] at hmult
  change (∑ y ∈ B, v y) ≤ _
  calc
    _ ≤ ∑ _y ∈ B, N := by apply sum_le_sum; intro y _; exact hN y
    _ = (B.card:ℝ)*N := by simp
    _ ≤ (36*q^(n+3)*M)*N := mul_le_mul_of_nonneg_right hmult hN0

end SharpLogRamsey.Incidence

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds SharpLogRamsey.Incidence
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem projective_low_card {n : ℕ} (hdim : Module.finrank K V=n+3)
    (X : Finset (Projectivization K V)) (hX : X.Nonempty)
    (U : Finset (Projectivization K (Module.Dual K V))) :
    ((U.filter (fun y => (∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass X x)
      <1/(2*(Nat.card K:ℝ)))).card:ℝ) ≤ 36*(Nat.card K:ℝ)^(n+3)/(X.card:ℝ) := by
  have hu (x : Projectivization K V) : uniformMass X x ≤ (X.card:ℝ)⁻¹ := by
    unfold uniformMass
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.mpr (Nat.cast_nonneg X.card)
  have hb := low_incidence_half_target_mass hdim (uniformMass X) (uniform_nonneg X)
    (uniform_total hX) (X.card:ℝ)⁻¹ hu (fun _ => (1:ℝ)) 1 (by norm_num) (by simp)
  simp only [sum_const, nsmul_eq_mul, mul_one,div_eq_mul_inv] at hb ⊢
  apply le_trans _ hb
  apply Nat.cast_le.mpr
  apply card_le_card
  intro y hy
  simp only [mem_filter,mem_univ,true_and] at hy ⊢
  simpa only [weightedIncidences,←sum_filter] using hy.2

theorem projective_cap_mean {n : ℕ} (hdim : Module.finrank K V=n+3)
    (X : Finset (Projectivization K V)) (hX : X.Nonempty)
    (U : Finset (Projectivization K (Module.Dual K V))) (h : ℕ) :
    (∑ z : Fin h → Projectivization K V, rowWeight (uniformMass X) z*
      ((cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) U z).card:ℝ)) ≤
        36*(Nat.card K:ℝ)^(n+3)/(X.card:ℝ)+
          (U.card:ℝ)*Real.exp (1-(h:ℝ)/(20*(Nat.card K:ℝ))) := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast (Nat.card_pos (α:=K))
  exact (cap_mean_le (uniformMass X) (uniform_nonneg X) (uniform_total hX)
    SharpLogRamsey.Incidence.Incident _ hq h U).trans (add_le_add (projective_low_card hdim X hX U) le_rfl)

theorem projective_ideal_acceptance {n : ℕ} (hdim : Module.finrank K V=n+3)
    (X : Finset (Projectivization K V)) (hX : X.Nonempty)
    (U T : Finset (Projectivization K (Module.Dual K V))) (hT : T.Nonempty)
    (h : ℕ) (hh : 0<h) (M : ℝ) (hM : 0<M)
    (hsize : 36*(Nat.card K:ℝ)^(n+3)/(X.card:ℝ)+
      (U.card:ℝ)*Real.exp (1-(h:ℝ)/(20*(Nat.card K:ℝ))) ≤ M/20)
    (hsparse : (∑ y∈T,∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass X x)
      ≤ (T.card:ℝ)/(10000*(Nat.card K:ℝ))) :
    (9/10:ℝ) ≤ prob (uniformMass X) h (fun z =>
      ((cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) U z).card:ℝ)≤M ∧
      ((T.filter (fun y => ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) z y)).card:ℝ)≤(T.card:ℝ)/100) := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast (Nat.card_pos (α:=K))
  apply acceptance_mass (uniformMass X) (uniform_nonneg X) (uniform_total hX)
    SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) h U T M hM hT
  · exact (projective_cap_mean hdim X hX U h).trans hsize
  · apply (loss_mean_le (uniformMass X) (uniform_nonneg X) (uniform_total hX)
      SharpLogRamsey.Incidence.Incident _ hq h hh T).trans
    have hs := mul_le_mul_of_nonneg_left hsparse (show 0≤5*(Nat.card K:ℝ) by positivity)
    apply hs.trans_eq
    field_simp
    ring

end
end SharpLogRamsey.Validation

namespace SharpLogRamsey.PublicTables
open Finset
open scoped BigOperators Classical
universe u
variable {Ω : Type u}

def rowAt : (n : ℕ) → Table Ω n → Fin n → Ω
  | 0, _, i => Fin.elim0 i
  | n+1, z, i => Fin.cases z.1 (rowAt n z.2) i

noncomputable def firstIndex (A : Ω → Prop) [DecidablePred A] :
    (n : ℕ) → Table Ω n → Option (Fin n)
  | 0, _ => none
  | n+1, z => if A z.1 then some 0 else (firstIndex A n z.2).map Fin.succ

theorem reconstruct_first (A : Ω → Prop) [DecidablePred A] (n : ℕ) (z : Table Ω n) :
    (firstIndex A n z).map (rowAt n z) = first A n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (if A z.1 then some 0 else (firstIndex A n z.2).map Fin.succ).map
      (rowAt (n+1) z) = if A z.1 then some z.1 else first A n z.2
    by_cases ha : A z.1
    · simp only [ha,ite_true,Option.map_some,rowAt,Fin.cases_zero]
    · simp only [ha,ite_false,Option.map_map]
      have hf : rowAt (n+1) z ∘ Fin.succ = rowAt n z.2 := by
        funext i
        simp only [Function.comp_apply,rowAt,Fin.cases_succ]
      rw [hf,ih]

theorem first_valid (A : Ω → Prop) [DecidablePred A] (n : ℕ) (z : Table Ω n)
    (x : Ω) (hx : first A n z=some x) : A x := by
  induction n with
  | zero => cases hx
  | succ n ih =>
    change (if A z.1 then some z.1 else first A n z.2)=some x at hx
    split_ifs at hx with ha
    · have : z.1=x := Option.some.inj hx
      simpa only [this] using ha
    · exact ih z.2 hx

theorem index_valid (A : Ω → Prop) [DecidablePred A] (n : ℕ) (z : Table Ω n)
    (i : Fin n) (hi : firstIndex A n z=some i) : A (rowAt n z i) := by
  have he := reconstruct_first A n z
  rw [hi,Option.map_some] at he
  exact first_valid A n z _ he.symm

end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {Ω Y : Type*} [Fintype Ω]

def GoodCap (R : Ω → Y → Prop) (q : ℝ) (U T : Finset Y) (M : ℝ)
    {h : ℕ} (z : Fin h → Ω) : Prop :=
  ((cap R q U z).card:ℝ)≤M ∧
    ((T.filter (fun y => ¬pass R q z y)).card:ℝ)≤(T.card:ℝ)/100

omit [Fintype Ω] in
lemma cap_capture {R : Ω → Y → Prop} [Fintype Ω] {q : ℝ} {U T : Finset Y}
    {M : ℝ} {h : ℕ} {z : Fin h → Ω} (hT : T⊆U) (hg : GoodCap R q U T M z) :
    (99:ℝ)*(T.card:ℝ) ≤ 100*((T∩cap R q U z).card:ℝ) := by
  have he : T∩cap R q U z = T.filter (pass R q z) := by
    ext y
    simp only [mem_inter,cap,mem_filter]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hT h.1,h.2⟩⟩
  rw [he]
  have ht := card_filter_add_card_filter_not (s:=T) (pass R q z)
  have ht' : ((T.filter (pass R q z)).card:ℝ)+
      ((T.filter (fun y => ¬pass R q z y)).card:ℝ) = T.card := by exact_mod_cast ht
  have hl := hg.2
  linarith

theorem decoded_cap (X : Finset Ω) (R : Ω → Y → Prop)
    (q : ℝ) (U T : Finset Y) (hT : T⊆U) (M : ℝ) (h m : ℕ)
    (table : PublicTables.Table (Fin h → Ω) m) (i : Fin m)
    (hi : PublicTables.firstIndex (implementAccept X (GoodCap R q U T M)) m table=some i) :
    let C := cap R q U (PublicTables.rowAt m table i)
    C⊆U ∧ (C.card:ℝ)≤M ∧ (99:ℝ)*(T.card:ℝ)≤100*((T∩C).card:ℝ) := by
  have hg := (PublicTables.index_valid (implementAccept X (GoodCap R q U T M)) m table i hi).2
  exact ⟨filter_subset _ _,hg.1,cap_capture hT hg⟩

omit [Fintype Ω] in
lemma uniform_sum_mono {X₀ X E : Finset Ω} (hX : X.Nonempty) (h₀ : X₀.Nonempty)
    (hsub : X₀⊆X) (c : ℝ) (hc : 0<c) (hcap : c*(X.card:ℝ)≤(X₀.card:ℝ)) :
    (∑ x∈E,uniformMass X₀ x) ≤ c⁻¹*(∑ x∈E,uniformMass X x) := by
  rw [uniform_sum,uniform_sum]
  have hx : 0<(X.card:ℝ) := by exact_mod_cast card_pos.mpr hX
  have hx₀ : 0<(X₀.card:ℝ) := by exact_mod_cast card_pos.mpr h₀
  have he : ((E∩X₀).card:ℝ)≤((E∩X).card:ℝ) := by
    exact_mod_cast card_le_card (show E∩X₀ ⊆ E∩X from
      fun _ hx => mem_inter.mpr ⟨(mem_inter.mp hx).1,hsub (mem_inter.mp hx).2⟩)
  apply (le_inv_mul_iff₀ hc).mpr
  apply (le_div_iff₀ hx).mpr
  rw [show c*(((E∩X₀).card:ℝ)/(X₀.card:ℝ))*(X.card:ℝ) =
    (c*(X.card:ℝ)*((E∩X₀).card:ℝ))/(X₀.card:ℝ) by ring]
  apply (div_le_iff₀ hx₀).mpr
  have h1 := mul_le_mul_of_nonneg_left hcap (show 0≤((E∩X).card:ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left he (show 0≤c*(X.card:ℝ) by positivity)
  nlinarith

theorem original_exclusion (X₀ X W : Finset Ω) (hX₀ : X₀.Nonempty)
    (hX : X.Nonempty) (hW : W.Nonempty) (hsub : X₀⊆X) (hWsub : X₀⊆W)
    (c : ℝ) (hc : 0<c) (hcap : c*(X.card:ℝ)≤(X₀.card:ℝ))
    (h : ℕ) (hh : 0<h) (Good : (Fin h → Ω) → Prop)
    (hGood : (9/10:ℝ)≤prob (uniformMass X₀) h Good)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (y : Y) (m : ℕ) :
    PublicTables.integral (rowLaw W hW h) (implementAccept X₀ Good)
      (fun z => if ¬pass R q z y then 1 else 0) m ≤
        (6/c)*q*(∑ x∈univ.filter (fun x => R x y),uniformMass X x) := by
  apply (produced_exclusion X₀ W hX₀ hW hWsub h hh Good hGood R q hq y m).trans
  have hm := mul_le_mul_of_nonneg_left (uniform_sum_mono hX hX₀ hsub c hc hcap
    (E:=univ.filter (fun x => R x y))) (show 0≤6*q by positivity)
  exact hm.trans_eq (by ring)

end
end SharpLogRamsey.Validation

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds SharpLogRamsey.Incidence
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem projective_public_validation {n : ℕ} (hdim : Module.finrank K V=n+3)
    (X W : Finset (Projectivization K V)) (hX : X.Nonempty) (hW : W.Nonempty)
    (hsub : X⊆W) (U T : Finset (Projectivization K (Module.Dual K V)))
    (hT : T.Nonempty) (h : ℕ) (hh : 0<h) (M : ℝ) (hM : 0<M)
    (hsize : 36*(Nat.card K:ℝ)^(n+3)/(X.card:ℝ)+
      (U.card:ℝ)*Real.exp (1-(h:ℝ)/(20*(Nat.card K:ℝ))) ≤ M/20)
    (hsparse : (∑ y∈T,∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass X x)
      ≤ (T.card:ℝ)/(10000*(Nat.card K:ℝ))) (m : ℕ)
    (hsearch : (Nat.card K:ℝ)≤(m:ℝ)*(((X.card:ℝ)/(W.card:ℝ))^h*(9/10))) :
    1-PublicTables.integral (rowLaw W hW h)
        (implementAccept X (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) U T M)) (fun _ => 1) m
      ≤ Real.exp (-(Nat.card K:ℝ)) ∧
    ∀ y, PublicTables.integral (rowLaw W hW h)
        (implementAccept X (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) U T M))
        (fun z => if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) z y then 1 else 0) m
      ≤ 6*(Nat.card K:ℝ)*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass X x) := by
  have hg : (9/10:ℝ)≤prob (uniformMass X) h (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) U T M) :=
    projective_ideal_acceptance hdim X hX U T hT h hh M hM hsize hsparse
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.card_pos (α:=K)
  constructor
  · apply (PublicTables.failure_exp (rowLaw W hW h) _ m).trans
    apply Real.exp_le_exp.mpr
    rw [proposal_acceptance X W hX hW hsub]
    have hmul := mul_le_mul_of_nonneg_left hg
      (show 0≤(m:ℝ)*((X.card:ℝ)/(W.card:ℝ))^h by positivity)
    nlinarith
  · intro y
    exact produced_exclusion X W hX hW hsub h hh _ hg SharpLogRamsey.Incidence.Incident _ hq y m

end
end SharpLogRamsey.Validation

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {Ω Y I : Type*} [Fintype Ω] [Fintype I]

theorem ready_exclusion (p : PublicTables.Law I) (Ready : I → Prop)
    (X : Finset Ω) (hX : X.Nonempty) (X₀ W : I → Finset Ω)
    (hX₀ : ∀ i,(X₀ i).Nonempty) (hW : ∀ i,(W i).Nonempty)
    (hsub : ∀ i,Ready i → X₀ i⊆X) (hWsub : ∀ i,Ready i → X₀ i⊆W i)
    (c : ℝ) (hc : 0<c) (hcap : ∀ i,Ready i → c*(X.card:ℝ)≤((X₀ i).card:ℝ))
    (h m : I → ℕ) (hh : ∀ i,Ready i → 0<h i)
    (Good : (i : I) → (Fin (h i) → Ω) → Prop)
    (hGood : ∀ i,Ready i → (9/10:ℝ)≤prob (uniformMass (X₀ i)) (h i) (Good i))
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (y : Y) :
    (∑ i, if Ready i then p.mass i *
      PublicTables.integral (rowLaw (W i) (hW i) (h i)) (implementAccept (X₀ i) (Good i))
        (fun z => if ¬pass R q z y then 1 else 0) (m i) else 0) ≤
      (6/c)*q*(∑ x∈univ.filter (fun x => R x y),uniformMass X x) := by
  let B := (6/c)*q*(∑ x∈univ.filter (fun x => R x y),uniformMass X x)
  have hb : 0≤B := by
    dsimp [B]
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun x _ => uniform_nonneg X x)
  calc
    _ ≤ ∑ i,p.mass i*B := by
      apply sum_le_sum
      intro i _
      split_ifs with hr
      · exact mul_le_mul_of_nonneg_left
          (original_exclusion (X₀ i) X (W i) (hX₀ i) hX (hW i) (hsub i hr)
            (hWsub i hr) c hc (hcap i hr) (h i) (hh i hr) (Good i) (hGood i hr)
            R q hq y (m i)) (p.nonneg i)
      · exact mul_nonneg (p.nonneg i) hb
    _ = _ := by rw [←sum_mul,p.total,one_mul]

end
end SharpLogRamsey.Validation

open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.PublicTables
open Finset
open scoped BigOperators Classical
noncomputable section
variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

lemma integral_weighted_sum (p : Law Ω) (A : Ω → Prop) (f : Ω → Y → ℝ)
    (w : Y → ℝ) (m : ℕ) :
    integral p A (fun z => ∑ y,w y*f z y) m =
      ∑ y,w y*integral p A (fun z => f z y) m := by
  simp only [integral_formula,accepted,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  by_cases hz : A z
  · simp only [hz,ite_true,mul_sum]
    apply sum_congr rfl
    intro y _
    ring
  · simp [hz]

end
end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds SharpLogRamsey.SupportMixtures
noncomputable section
variable {Ω Y I : Type*} [Fintype Ω] [Fintype Y] [Fintype I]

omit [Fintype Ω] in
lemma kernel_uniform (X : Finset Ω) (x : Ω) : kernel X x=uniformMass X x := by
  simp [kernel,uniformMass,one_div]

def missFraction (R : Ω → Y → Prop) (q : ℝ) (T : Finset Y)
    {h : ℕ} (z : Fin h → Ω) : ℝ :=
  ((T.filter (fun y => ¬pass R q z y)).card:ℝ)/(T.card:ℝ)

lemma missFraction_eq (R : Ω → Y → Prop) (q : ℝ) (T : Finset Y)
    {h : ℕ} (z : Fin h → Ω) :
    missFraction R q T z=∑ y,kernel T y*(if ¬pass R q z y then 1 else 0) := by
  have he (y : Y) : kernel T y*(if ¬pass R q z y then 1 else 0) =
      if y∈T.filter (fun y => ¬pass R q z y) then 1/(T.card:ℝ) else 0 := by
    by_cases hy : y∈T <;> by_cases hp : pass R q z y <;> simp [kernel,hy,hp]
  simp only [he,←sum_filter]
  have hf : univ.filter (fun y => y∈T.filter (fun y => ¬pass R q z y)) =
      T.filter (fun y => ¬pass R q z y) := by ext; simp
  rw [hf,sum_const,nsmul_eq_mul]
  unfold missFraction
  ring

lemma incidence_kernel_sum (X : Finset Ω) (T : Finset Y) (R : Ω → Y → Prop) :
    (∑ y,kernel T y*(∑ x∈univ.filter (fun x => R x y),uniformMass X x))=
      pairing (kernel X) (kernel T) (fun x y => if R x y then 1 else 0) := by
  simp only [pairing,sum_filter,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  by_cases hr : R x y <;> simp [hr,kernel_uniform,mul_comm]

theorem ready_fraction (p : PublicTables.Law I) (Ready : I → Prop)
    (X : Finset Ω) (hX : X.Nonempty) (X₀ W : I → Finset Ω)
    (hX₀ : ∀ i,(X₀ i).Nonempty) (hW : ∀ i,(W i).Nonempty)
    (hsub : ∀ i,Ready i → X₀ i⊆X) (hWsub : ∀ i,Ready i → X₀ i⊆W i)
    (c : ℝ) (hc : 0<c) (hcap : ∀ i,Ready i → c*(X.card:ℝ)≤ ((X₀ i).card:ℝ))
    (h m : I → ℕ) (hh : ∀ i,Ready i → 0<h i)
    (Good : (i : I) → (Fin (h i) → Ω) → Prop)
    (hGood : ∀ i,Ready i → (9/10:ℝ)≤ prob (uniformMass (X₀ i)) (h i) (Good i))
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (T : Finset Y) :
    (∑ i, if Ready i then p.mass i *
      PublicTables.integral (rowLaw (W i) (hW i) (h i)) (implementAccept (X₀ i) (Good i))
        (missFraction R q T) (m i) else 0) ≤
      (6/c)*q*pairing (kernel X) (kernel T) (fun x y => if R x y then 1 else 0) := by
  have he : (∑ i, if Ready i then p.mass i *
      PublicTables.integral (rowLaw (W i) (hW i) (h i)) (implementAccept (X₀ i) (Good i))
        (missFraction R q T) (m i) else 0) =
      ∑ y,kernel T y*(∑ i, if Ready i then p.mass i *
        PublicTables.integral (rowLaw (W i) (hW i) (h i)) (implementAccept (X₀ i) (Good i))
          (fun z => if ¬pass R q z y then 1 else 0) (m i) else 0) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    by_cases hi : Ready i
    · simp only [hi,ite_true]
      rw [show missFraction R q T = (fun z : Fin (h i) → Ω =>
        ∑ y,kernel T y*(if ¬pass R q z y then 1 else 0)) from
          funext (missFraction_eq R q T)]
      rw [PublicTables.integral_weighted_sum,mul_sum]
      apply sum_congr rfl
      intro y _
      ring
    · simp [hi]
  rw [he]
  calc
    _ ≤ ∑ y,kernel T y*((6/c)*q*(∑ x∈univ.filter (fun x => R x y),uniformMass X x)) := by
      apply sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left
        (ready_exclusion p Ready X hX X₀ W hX₀ hW hsub hWsub c hc hcap h m hh Good hGood
          R q hq y) (kernel_nonneg _ _)
    _ = _ := by
      rw [←incidence_kernel_sum]
      simp only [mul_sum]
      apply sum_congr rfl
      intro y _
      ring_nf

theorem independent_loss {J : Type*} [Fintype J]
    (w : I → ℝ) (v : J → ℝ) (S : I → Finset Ω) (T : J → Finset Y)
    (R : Ω → Y → Prop) (μ : Ω → ℝ) (ν : Y → ℝ) (a b C : ℝ)
    (hw : ∀ i,0≤ w i) (hv : ∀ j,0≤ v j) (hC : 0≤ C)
    (hS : ∀ x,mixture w S x≤ a*μ x) (hT : ∀ y,mixture v T y≤ b*ν y)
    (loss : I → J → ℝ)
    (hloss : ∀ i j,loss i j≤ C*pairing (kernel (S i)) (kernel (T j))
      (fun x y => if R x y then 1 else 0)) :
    (∑ i,∑ j,w i*v j*loss i j)≤ C*a*b*pairing μ ν (fun x y => if R x y then 1 else 0) := by
  calc
    _ ≤ ∑ i,∑ j,w i*v j*(C*pairing (kernel (S i)) (kernel (T j))
        (fun x y => if R x y then 1 else 0)) := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hloss i j) (mul_nonneg (hw i) (hv j))
    _ = C*(∑ i,∑ j,w i*v j*pairing (kernel (S i)) (kernel (T j))
        (fun x y => if R x y then 1 else 0)) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ C*(a*b*pairing μ ν (fun x y => if R x y then 1 else 0)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact independent_pairing_le w v S T _ μ ν a b hw hv (by intros; split_ifs <;> norm_num) hS hT
    _ = _ := by ring

end
end SharpLogRamsey.Validation

end

end OAI
