import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Hits
import OAI.Combinatorics.RamseyFive.Geometry.CoreGeometry

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module
open scoped LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

theorem count_subspaces : Nat.card (Submodule K V)≤
    (finrank K V+1)*Nat.card V^(finrank K V) := by
  classical
  let : Finite V := Module.finite_of_finite K
  let f : (Σ r : Fin (finrank K V+1),Fin r.val → V) → Submodule K V :=
    fun v => Submodule.span K (Set.range v.2)
  have hf : Function.Surjective f := by
    intro U
    let r : Fin (finrank K V+1) := ⟨finrank K U,Nat.lt_succ_of_le (Submodule.finrank_le U)⟩
    use ⟨r,fun i => (Module.finBasis K U i).val⟩
    change Submodule.span K (Set.range (U.subtype ∘ Module.finBasis K U))=U
    rw [Set.range_comp,←Submodule.map_span,(Module.finBasis K U).span_eq,
      Submodule.map_subtype_top]
  have hc := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_sigma] at hc
  calc
    _ ≤ ∑ r : Fin (finrank K V+1),Nat.card (Fin r.val → V) := hc
    _ ≤ ∑ _r : Fin (finrank K V+1),Nat.card V^finrank K V := by
      apply Finset.sum_le_sum
      intro r _
      rw [Nat.card_fun,Nat.card_fin]
      exact Nat.pow_le_pow_right (Nat.card_pos (α := V)) (Nat.le_of_lt_succ r.isLt)
    _ = _ := by simp

omit [FiniteDimensional K V] in

theorem card_rectangle (U : Submodule K (Module.Dual K V)) :
    Nat.card {ab : ℙ K V × ℙ K (Module.Dual K V) //
      ab.1.submodule≤U.dualCoannihilator ∧ ab.2.submodule≤U} =
      (∑ i∈Finset.range (finrank K U.dualCoannihilator),Nat.card K^i)*
      (∑ i∈Finset.range (finrank K U),Nat.card K^i) := by
  let e : {ab : ℙ K V × ℙ K (Module.Dual K V) //
      ab.1.submodule≤U.dualCoannihilator ∧ ab.2.submodule≤U} ≃
      {a : ℙ K V // a.submodule≤U.dualCoannihilator} ×
        {b : ℙ K (Module.Dual K V) // b.submodule≤U} :=
    { toFun := fun ab => (⟨ab.val.1,ab.property.1⟩,⟨ab.val.2,ab.property.2⟩)
      invFun := fun ab => ⟨(ab.1.val,ab.2.val),⟨ab.1.property,ab.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_prod,
    SharpRamseyFive.ProjectiveIncidence.card_subspacePoints,
    SharpRamseyFive.ProjectiveIncidence.card_subspacePoints]

theorem card_rectangle_le (hdim : finrank K V=5)
    (U : Submodule K (Module.Dual K V)) :
    (Nat.card {ab : ℙ K V × ℙ K (Module.Dual K V) //
      ab.1.submodule≤U.dualCoannihilator ∧ ab.2.submodule≤U}:ℝ)≤4*(Nat.card K:ℝ)^3 := by
  rw [card_rectangle]
  push_cast
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq U
  rw [hdim] at hd
  by_cases hU : finrank K U=0
  · simp only [hU,Finset.range_zero,Finset.sum_empty,mul_zero]
    positivity
  by_cases hD : finrank K U.dualCoannihilator=0
  · simp only [hD,Finset.range_zero,Finset.sum_empty,zero_mul]
    positivity
  have hpow : (finrank K U.dualCoannihilator-1)+(finrank K U-1)=3 := by omega
  calc
    _ ≤ (2*(Nat.card K:ℝ)^(finrank K U.dualCoannihilator-1))*
        (2*(Nat.card K:ℝ)^(finrank K U-1)) :=
      mul_le_mul (geometric_card_bound _ hq _) (geometric_card_bound _ hq _)
        (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    _ = 4*(Nat.card K:ℝ)^((finrank K U.dualCoannihilator-1)+(finrank K U-1)) := by
      rw [pow_add]; ring
    _ = _ := by rw [hpow]
end SharpRamseyFive.CoreGeometry

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

lemma exp_single_hit (p : Law α) (H : Finset α) :
    (∑ a,p a*Real.exp (if a∈H then 1 else 0))=
      1+(Real.exp 1-1)*eventMass p H := by
  have ht (a : α) : p a*Real.exp (if a∈H then 1 else 0)=
      p a+(Real.exp 1-1)*(if a∈H then p a else 0) := by
    split_ifs
    · ring
    · simp
  simp only [ht,Finset.sum_add_distrib,←Finset.mul_sum,p.sum_one]
  rw [←Finset.sum_filter,Finset.filter_univ_mem]
  rfl

theorem exp_hits (p : Law α) (H : Finset α) (n : ℕ) :
    (∑ x,iid p (Fin n) x*Real.exp (hits H x))=
      (1+(Real.exp 1-1)*eventMass p H)^n := by
  induction n with
  | zero => simp [iid,hits]
  | succ n hn =>
    rw [sum_iid_succ]
    have ht (a : α) (x : Fin n → α) :
        p a*iid p (Fin n) x*Real.exp (hits H (Fin.cons a x))=
        (p a*Real.exp (if a∈H then 1 else 0))*(iid p (Fin n) x*Real.exp (hits H x)) := by
      rw [hits_cons,Real.exp_add]
      ring
    simp_rw [ht,←Finset.mul_sum,hn,←Finset.sum_mul,exp_single_hit]
    rw [pow_succ]
    ring

theorem exp_hits_le (p : Law α) (H : Finset α) (n : ℕ) :
    (∑ x,iid p (Fin n) x*Real.exp (hits H x))≤
      Real.exp (2*n*eventMass p H) := by
  rw [exp_hits]
  have hm := eventMass_nonneg p H
  have hone : 1≤Real.exp 1 := Real.one_le_exp (by norm_num)
  have htwo : Real.exp 1-1≤2 := by linarith [Real.exp_one_lt_d9]
  calc
    _ ≤ (Real.exp (2*eventMass p H))^n := by
      apply pow_le_pow_left₀ (by positivity)
      have h := Real.add_one_le_exp (2*eventMass p H)
      nlinarith
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring

theorem iid_occupancy_tail (p : Law α) (H : Finset α) (n : ℕ) (M : ℝ) :
    eventMass (iid p (Fin n)) (Finset.univ.filter fun x => M≤hits H x)≤
      Real.exp (2*n*eventMass p H-M) := by
  have hh := event_markov (iid p (Fin n)) (fun x => Real.exp (hits H x))
    (fun x => (Real.exp_pos _).le) (Real.exp M)
    (Finset.univ.filter fun x => M≤hits H x) (by
      intro x hx
      exact Real.exp_le_exp.mpr (Finset.mem_filter.mp hx).2)
  have hl := hh.trans (exp_hits_le p H n)
  apply (mul_le_mul_iff_right₀ (Real.exp_pos M)).mp
  calc
    _ ≤ Real.exp (2*n*eventMass p H) := hl
    _ = Real.exp M*Real.exp (2*n*eventMass p H-M) := by
      rw [←Real.exp_add]; congr 1; ring

lemma event_biUnion_le {ι : Type*} [Fintype ι] (p : Law α) (E : ι → Finset α) :
    eventMass p (Finset.univ.biUnion E)≤∑ i,eventMass p (E i) := by
  have ht (a : α) : (if a∈Finset.univ.biUnion E then p a else 0)≤
      ∑ i,if a∈E i then p a else 0 := by
    by_cases ha : a∈Finset.univ.biUnion E
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp ha
      simp only [ha,ite_true]
      have h := Finset.single_le_sum (s := Finset.univ) (f := fun i => if a∈E i then p a else 0)
        (fun i _ => by split_ifs; exact p.nonneg a; exact le_rfl) (Finset.mem_univ i)
      simpa only [hi,ite_true] using h
    · simp only [ha,ite_false]
      exact Finset.sum_nonneg fun i _ => by split_ifs; exact p.nonneg a; exact le_rfl
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => ht a)
  rw [Finset.sum_comm] at h
  simpa only [←Finset.sum_filter,Finset.filter_univ_mem,eventMass] using h

theorem all_occupancy_tail {ι : Type*} [Fintype ι] (p : Law α)
    (H : ι → Finset α) (n : ℕ) (μ M : ℝ)
    (hμ : ∀ i,(n:ℝ)*eventMass p (H i)≤μ) :
    eventMass (iid p (Fin n)) (Finset.univ.biUnion fun i =>
      Finset.univ.filter fun x => M≤hits (H i) x)≤
      (Fintype.card ι:ℝ)*Real.exp (2*μ-M) := by
  calc
    _ ≤ ∑ i,eventMass (iid p (Fin n)) (Finset.univ.filter fun x => M≤hits (H i) x) :=
      by
        convert event_biUnion_le (iid p (Fin n)) (fun i =>
          Finset.univ.filter fun x => M≤hits (H i) x) using 1
        congr 1
        ext x
        simp
    _ ≤ ∑ _i : ι,Real.exp (2*μ-M) := Finset.sum_le_sum fun i _ =>
      (iid_occupancy_tail p (H i) n M).trans (Real.exp_le_exp.mpr (by linarith [hμ i]))
    _ = _ := by simp
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators
variable {α : Type*} [Fintype α]

noncomputable def uniform (h : 0<Fintype.card α) : Law α where
  mass _ := 1/(Fintype.card α:ℝ)
  nonneg _ := by positivity
  sum_one := by
    have hh : (Fintype.card α:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt h
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_one_div_cancel hh

lemma uniform_event (h : 0<Fintype.card α) (E : Finset α) :
    eventMass (uniform h) E=(E.card:ℝ)/(Fintype.card α:ℝ) := by
  simp [eventMass,uniform,div_eq_mul_inv]
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.RectangleGeometry
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
  SharpRamseyFive.CoreGeometry
open scoped LinearAlgebra.Projectivization BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

abbrev Flag := {ab : ℙ K V × ℙ K (Module.Dual K V) // Incident ab.1 ab.2}

theorem card_flags : Nat.card (Flag (K := K) (V := V))=
    (∑ i∈Finset.range (finrank K V),Nat.card K^i)*
    (∑ i∈Finset.range (finrank K V-1),Nat.card K^i) := by
  let e : Flag (K := K) (V := V) ≃ (Σ a : ℙ K V,{b : ℙ K (Module.Dual K V) // Incident a b}) :=
    { toFun := fun ab => ⟨ab.val.1,⟨ab.val.2,ab.property⟩⟩
      invFun := fun ab => ⟨(ab.1,ab.2.val),ab.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_sigma]
  simp only [card_hyperplanes_through_point,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V rfl]
  simp

theorem card_flags_lower (hdim : finrank K V=5) :
    Nat.card K^7≤Nat.card (Flag (K := K) (V := V)) := by
  rw [card_flags,hdim]
  have h1 : Nat.card K^4≤∑ i∈Finset.range 5,Nat.card K^i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
  have h2 : Nat.card K^3≤∑ i∈Finset.range (5-1),Nat.card K^i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
  have h := Nat.mul_le_mul h1 h2
  rwa [←pow_add] at h

lemma flags_nonempty (hdim : finrank K V=5) : 0<Fintype.card (Flag (K := K) (V := V)) := by
  rw [←Nat.card_eq_fintype_card]
  exact (pow_pos (Nat.card_pos (α := K)) _).trans_le (card_flags_lower hdim)

noncomputable def rectangle (U : Submodule K (Module.Dual K V)) : Finset (Flag (K := K) (V := V)) :=
  Finset.univ.filter fun ab => ab.val.1.submodule≤U.dualCoannihilator ∧ ab.val.2.submodule≤U

omit [FiniteDimensional K V] [Finite K] in
lemma card_rectangle_flags (U : Submodule K (Module.Dual K V)) :
    (rectangle U).card=Nat.card {ab : ℙ K V × ℙ K (Module.Dual K V) //
      ab.1.submodule≤U.dualCoannihilator ∧ ab.2.submodule≤U} := by
  let e : {ab : Flag (K := K) (V := V) //
      ab.val.1.submodule≤U.dualCoannihilator ∧ ab.val.2.submodule≤U} ≃
      {ab : ℙ K V × ℙ K (Module.Dual K V) //
      ab.1.submodule≤U.dualCoannihilator ∧ ab.2.submodule≤U} :=
    { toFun := fun ab => ⟨ab.val.val,ab.property⟩
      invFun := fun ab => ⟨⟨ab.val,by
        apply (incident_iff ab.val.1 ab.val.2).mpr
        have ha := (rep_mem_iff ab.val.1 U.dualCoannihilator).mpr ab.property.1
        have hb := (rep_mem_iff ab.val.2 U).mpr ab.property.2
        exact (Submodule.mem_dualCoannihilator ab.val.1.rep).mp ha ab.val.2.rep hb⟩,ab.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [rectangle,←Fintype.card_subtype,←Nat.card_eq_fintype_card,Nat.card_congr e]

theorem rectangle_mass (hdim : finrank K V=5) (U : Submodule K (Module.Dual K V)) :
    eventMass (uniform (flags_nonempty hdim)) (rectangle U)≤4/(Nat.card K:ℝ)^4 := by
  rw [uniform_event,card_rectangle_flags]
  have hn : (Nat.card K:ℝ)^7≤Fintype.card (Flag (K := K) (V := V)) := by
    rw [←Nat.card_eq_fintype_card]
    exact_mod_cast (card_flags_lower hdim)
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α := K))
  have hc := card_rectangle_le hdim U
  have hd : (0:ℝ)<Fintype.card (Flag (K := K) (V := V)) := by exact_mod_cast flags_nonempty hdim
  calc
    _ ≤ (4*(Nat.card K:ℝ)^3)/(Nat.card K:ℝ)^7 :=
      div_le_div₀ (by positivity) hc (by positivity) hn
    _ = _ := by field_simp
end SharpRamseyFive.RectangleGeometry

namespace SharpRamseyFive.RectangleGeometry
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped LinearAlgebra.Projectivization BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]
  [Fintype (Submodule K (Module.Dual K V))]

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))] in
lemma count_rectangles (hdim : finrank K V=5) :
    (Fintype.card (Submodule K (Module.Dual K V)):ℝ)≤6*(Nat.card K:ℝ)^25 := by
  let : Fintype K := Fintype.ofFinite K
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (Module.Dual K V) := Fintype.ofFinite _
  have hv : Nat.card (Module.Dual K V)=Nat.card K^5 := by
    rw [Nat.card_eq_fintype_card (α := Module.Dual K V),Module.card_eq_pow_finrank (K := K),
      Subspace.dual_finrank_eq,hdim,←Nat.card_eq_fintype_card]
  have h := count_subspaces (K := K) (V := Module.Dual K V)
  rw [Subspace.dual_finrank_eq,hdim,hv,←pow_mul] at h
  norm_num at h
  simpa only [Nat.card_eq_fintype_card,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using
    (show (Fintype.card (Submodule K (Module.Dual K V)):ℝ)≤6*(Fintype.card K:ℝ)^25 by exact_mod_cast h)

omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]
  [Fintype (Submodule K (Module.Dual K V))] in
lemma rectangle_tail_scalar (q : ℝ) (hq : 0<q) :
    6*q^25*Real.exp (-(32*Real.log q))=6/q^7 := by
  have he : Real.exp (32*Real.log q)=q^32 := by
    simpa only [Real.exp_log hq,Nat.cast_ofNat] using Real.exp_nat_mul (Real.log q) 32
  rw [Real.exp_neg,he,show (32:ℕ)=25+7 by norm_num,pow_add,mul_inv_rev]
  have hp : q^25≠0 := pow_ne_zero _ (ne_of_gt hq)
  rw [mul_assoc,mul_comm ((q^7)⁻¹),←mul_assoc,←mul_assoc,mul_inv_cancel_right₀ hp]
  rfl

omit [Fintype (Submodule K (Module.Dual K V))] in
lemma rectangle_mean (hdim : finrank K V=5) (n : ℕ)
    (hn : (n:ℝ)≤(Nat.card K:ℝ)^4*Real.log (Nat.card K))
    (U : Submodule K (Module.Dual K V)) :
    (n:ℝ)*eventMass (uniform (flags_nonempty hdim)) (rectangle U)≤4*Real.log (Nat.card K) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α := K))
  have hq2 : (2:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  have hlog : 0≤Real.log (Nat.card K) := Real.log_nonneg (by linarith)
  calc
    _ ≤ ((Nat.card K:ℝ)^4*Real.log (Nat.card K))*(4/(Nat.card K:ℝ)^4) :=
      mul_le_mul hn (rectangle_mass hdim U) (eventMass_nonneg _ _) (by positivity)
    _ = _ := by field_simp

noncomputable local instance : DecidableEq (Flag (K := K) (V := V)) := Classical.decEq _

theorem rectangle_occupancy_tail (hdim : finrank K V=5) (n : ℕ)
    (hn : (n:ℝ)≤(Nat.card K:ℝ)^4*Real.log (Nat.card K)) :
    eventMass (iid (uniform (flags_nonempty hdim)) (Fin n))
      (Finset.univ.biUnion fun U : Submodule K (Module.Dual K V) =>
        Finset.univ.filter fun x => 40*Real.log (Nat.card K)≤hits (rectangle U) x)
      ≤6/(Nat.card K:ℝ)^7 := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α := K))
  have h := all_occupancy_tail (α := Flag (K := K) (V := V))
    (ι := Submodule K (Module.Dual K V))
    (uniform (flags_nonempty hdim)) (rectangle (K := K) (V := V)) n
    (4*Real.log (Nat.card K)) (40*Real.log (Nat.card K)) (rectangle_mean hdim n hn)
  calc
    _ ≤ (Fintype.card (Submodule K (Module.Dual K V)):ℝ)*
        Real.exp (2*(4*Real.log (Nat.card K))-40*Real.log (Nat.card K)) := h
    _ ≤ (6*(Nat.card K:ℝ)^25)*Real.exp (-(32*Real.log (Nat.card K))) := by
      rw [show 2*(4*Real.log (Nat.card K))-40*Real.log (Nat.card K)=
        -(32*Real.log (Nat.card K)) by ring]
      exact mul_le_mul_of_nonneg_right (count_rectangles hdim) (Real.exp_pos _).le
    _ = _ := rectangle_tail_scalar _ hq
end SharpRamseyFive.RectangleGeometry

end OAI
