import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.AuxiliaryLevels

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem card_incident_points [Finite K] [FiniteDimensional K V] {d : ℕ}
    (hdim : Module.finrank K V = d+1)
    (b : Projectivization K (Module.Dual K V)) :
    Nat.card {a : Projectivization K V // Incident a b} =
      ∑ i ∈ Finset.range d, Nat.card K ^ i := by
  let e : {a : Projectivization K V // Incident a b} ≃
      {a : Projectivization K V // a.submodule ≤ LinearMap.ker b.rep} :=
    Equiv.subtypeEquivRight (fun a => incident_iff_submodule a b)
  rw [Nat.card_congr e, ← Nat.card_congr (projectiveSubmoduleEquiv (LinearMap.ker b.rep))]
  apply Projectivization.card_of_finrank
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  omega

theorem incident_iff_dualAnnihilator (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) :
    Incident a b ↔ b.submodule ≤ a.submodule.dualAnnihilator := by
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
    Submodule.mem_dualAnnihilator]
  change b.rep a.rep = 0 ↔ a.submodule ≤ LinearMap.ker b.rep
  exact incident_iff_submodule a b

theorem card_incident_dual [Finite K] [FiniteDimensional K V] {d : ℕ}
    (hdim : Module.finrank K V = d+1) (a : Projectivization K V) :
    Nat.card {b : Projectivization K (Module.Dual K V) // Incident a b} =
      ∑ i ∈ Finset.range d, Nat.card K^i := by
  let e := Equiv.subtypeEquivRight (fun b => incident_iff_dualAnnihilator a b)
  rw [Nat.card_congr e, ← Nat.card_congr (projectiveSubmoduleEquiv a.submodule.dualAnnihilator)]
  apply Projectivization.card_of_finrank
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq a.submodule
  rw [Projectivization.finrank_submodule] at h
  omega

theorem card_common_incident_dual [Finite K] [FiniteDimensional K V] {d : ℕ}
    (hdim : Module.finrank K V = d+2)
    (a a' : Projectivization K V) (haa : a ≠ a') :
    Nat.card {b : Projectivization K (Module.Dual K V) // Incident a b ∧ Incident a' b} =
      ∑ i ∈ Finset.range d, Nat.card K^i := by
  let W := Submodule.span K (Set.range ![a.rep, a'.rep])
  have hW : Module.finrank K W = 2 := by
    simpa [W] using finrank_span_eq_card (Projectivization.linearIndependent_pair_iff_ne.mpr haa)
  have hpred (b : Projectivization K (Module.Dual K V)) :
      (Incident a b ∧ Incident a' b) ↔ b.submodule ≤ W.dualAnnihilator := by
    rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_dualAnnihilator]
    change _ ↔ W ≤ LinearMap.ker b.rep
    rw [Submodule.span_le]
    simp [Incident, Set.insert_subset_iff, and_comm]
  let e := Equiv.subtypeEquivRight hpred
  rw [Nat.card_congr e, ← Nat.card_congr (projectiveSubmoduleEquiv W.dualAnnihilator)]
  apply Projectivization.card_of_finrank
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

section Design
variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def weightedIncidences (R : X → Y → Prop) (w : X → ℝ) (y : Y) : ℝ :=
  ∑ x, if R x y then w x else 0

theorem design_quadratic (R : X → Y → Prop) (k l : ℝ)
    (hdeg : ∀ x, (Fintype.card {y // R x y} : ℝ) = k)
    (hpair : ∀ x z, x ≠ z → (Fintype.card {y // R x y ∧ R z y} : ℝ) = l)
    (w : X → ℝ) :
    ∑ y, (weightedIncidences R w y)^2 =
      (k-l) * (∑ x, (w x)^2) + l * (∑ x, w x)^2 := by
  have hcount (x z : X) : (Fintype.card {y // R x y ∧ R z y} : ℝ) =
      if x = z then k else l := by
    by_cases h : x = z
    · subst z; simpa using hdeg x
    · simpa [h] using hpair x z h
  have hexpand (y : Y) : (weightedIncidences R w y)^2 =
      ∑ x, ∑ z, if R x y ∧ R z y then w x * w z else 0 := by
    rw [weightedIncidences, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    by_cases hx : R x y <;> by_cases hz : R z y <;> simp [hx,hz]
  have hcoeff (x z : X) : (if x = z then k else l) =
      (if x = z then k-l else 0) + l := by split_ifs <;> ring
  calc
    _ = ∑ x, ∑ z, ∑ y, if R x y ∧ R z y then w x * w z else 0 := by
      simp_rw [hexpand]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ z, (w x * w z) * (if x = z then k else l) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      rw [← hcount]
      simp only [Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul]
      ring
    _ = ∑ x, ∑ z, (w x * w z) * ((if x = z then k-l else 0) + l) := by
      simp_rw [hcoeff]
    _ = (k-l) * (∑ x, (w x)^2) + l * (∑ x, w x)^2 := by
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      simp only [sq, Finset.sum_mul, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl
      · intro x _; ring
      · intro x _; apply Finset.sum_congr rfl; intro z _; ring

theorem design_variance (R : X → Y → Prop) (k l : ℝ)
    (hdeg : ∀ x, (Fintype.card {y // R x y} : ℝ) = k)
    (hpair : ∀ x z, x ≠ z → (Fintype.card {y // R x y ∧ R z y} : ℝ) = l)
    [Nonempty Y] (w : X → ℝ) :
    ∑ y, (weightedIncidences R w y - k / Fintype.card Y * ∑ x, w x)^2 =
      (k-l) * (∑ x, (w x)^2) +
        (l - k^2 / Fintype.card Y) * (∑ x, w x)^2 := by
  have hv : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ y, weightedIncidences R w y = k * ∑ x, w x := by
    unfold weightedIncidences
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [← hdeg x]
    simp [← Finset.sum_filter, Fintype.card_subtype]
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, design_quadratic R k l hdeg hpair w]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]
  field_simp
  ring

end Design

theorem geom_design_identity (q : ℝ) (n : ℕ) :
    (∑ i ∈ range (n+2), q^i)^2 =
      (∑ i ∈ range (n+1), q^i) * (∑ i ∈ range (n+3), q^i) + q^(n+1) := by
  have hk : (∑ i ∈ range (n+2), q^i) = q*(∑ i ∈ range (n+1), q^i)+1 :=
    geom_sum_succ
  have hv : (∑ i ∈ range (n+3), q^i) = q*(∑ i ∈ range (n+2), q^i)+1 :=
    geom_sum_succ
  have hd : (∑ i ∈ range (n+2), q^i) = q^(n+1)+(∑ i ∈ range (n+1), q^i) :=
    geom_sum_succ'
  have hc : q^(n+1) = (∑ i ∈ range (n+2), q^i) -
      (∑ i ∈ range (n+1), q^i) := by linarith
  rw [hv, hc, hk]
  ring

section Projective
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem projective_variance {n : ℕ} (hdim : Module.finrank K V = n+3)
    (w : Projectivization K V → ℝ) :
    ∑ y : Projectivization K (Module.Dual K V),
      (weightedIncidences Incident w y -
        (∑ i ∈ range (n+2), (Nat.card K : ℝ)^i) /
        (∑ i ∈ range (n+3), (Nat.card K : ℝ)^i) * ∑ x, w x)^2 =
      (Nat.card K : ℝ)^(n+1) * ((∑ x, w x^2) -
        (∑ x, w x)^2 / (∑ i ∈ range (n+3), (Nat.card K : ℝ)^i)) := by
  have hv : (Fintype.card (Projectivization K (Module.Dual K V)) : ℝ) =
      ∑ i ∈ range (n+3), (Nat.card K : ℝ)^i := by
    rw [← Nat.card_eq_fintype_card, Projectivization.card_of_finrank K _
      (Subspace.dual_finrank_eq.trans hdim)]
    push_cast
    rfl
  have hvpos : 0 < ∑ i ∈ range (n+3), (Nat.card K : ℝ)^i := by
    apply Finset.sum_pos'
    · intro i hi; positivity
    · exact ⟨0, by simp, by simp⟩
  have : Nonempty (Projectivization K (Module.Dual K V)) := by
    apply Fintype.card_pos_iff.mp
    exact_mod_cast hv ▸ hvpos
  have hg (x : Projectivization K V) :
      (Fintype.card {y : Projectivization K (Module.Dual K V) // Incident x y} : ℝ) =
      ∑ i ∈ range (n+2), (Nat.card K : ℝ)^i := by
    rw [← Nat.card_eq_fintype_card, card_incident_dual (d := n+2) hdim x]
    push_cast
    rfl
  have hp (x z : Projectivization K V) (hxz : x ≠ z) :
      (Fintype.card {y : Projectivization K (Module.Dual K V) //
        Incident x y ∧ Incident z y} : ℝ) =
      ∑ i ∈ range (n+1), (Nat.card K : ℝ)^i := by
    rw [← Nat.card_eq_fintype_card, card_common_incident_dual (d := n+1) hdim x z hxz]
    push_cast
    rfl
  have he := design_variance Incident _ _ hg hp w
  rw [hv] at he
  rw [he]
  have hd : (∑ i ∈ range (n+2), (Nat.card K : ℝ)^i) -
      (∑ i ∈ range (n+1), (Nat.card K : ℝ)^i) = (Nat.card K : ℝ)^(n+1) := by
    rw [geom_sum_succ']; ring
  rw [hd]
  have hg := geom_design_identity (Nat.card K : ℝ) n
  rw [hg]
  field_simp
  ring

theorem projective_variance_le {n : ℕ} (hdim : Module.finrank K V = n+3)
    (w : Projectivization K V → ℝ) :
    ∑ y : Projectivization K (Module.Dual K V),
      (weightedIncidences Incident w y -
        (∑ i ∈ range (n+2), (Nat.card K : ℝ)^i) /
        (∑ i ∈ range (n+3), (Nat.card K : ℝ)^i) * ∑ x, w x)^2 ≤
      (Nat.card K : ℝ)^(n+1) * ∑ x, w x^2 := by
  rw [projective_variance hdim]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sub_le_self _ (by positivity)

noncomputable def incidenceCount (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) : ℕ :=
  ∑ y ∈ T, (S.filter (fun x => Incident x y)).card

theorem projective_mixing_sq {n : ℕ} (hdim : Module.finrank K V = n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    ((incidenceCount S T : ℝ) -
      (∑ i ∈ range (n+2), (Nat.card K : ℝ)^i) /
      (∑ i ∈ range (n+3), (Nat.card K : ℝ)^i) * S.card * T.card)^2 ≤
      (Nat.card K : ℝ)^(n+1) * S.card * T.card := by
  let w : Projectivization K V → ℝ := fun x => if x ∈ S then 1 else 0
  have hsum : ∑ x, w x = (S.card : ℝ) := by simp [w]
  have hsumsq : ∑ x, w x^2 = (S.card : ℝ) := by simp [w]
  have hc (y : Projectivization K (Module.Dual K V)) :
      weightedIncidences Incident w y = ((S.filter (fun x => Incident x y)).card : ℝ) := by
    simp [weightedIncidences, w, ← Finset.sum_filter]
    congr 1
    ext x
    simp [and_comm]
  let p : ℝ := (∑ i ∈ range (n+2), (Nat.card K : ℝ)^i) /
      (∑ i ∈ range (n+3), (Nat.card K : ℝ)^i)
  let f (y : Projectivization K (Module.Dual K V)) := weightedIncidences Incident w y - p*S.card
  have hf : ∑ y ∈ T, f y = (incidenceCount S T : ℝ) - p*S.card*T.card := by
    simp only [f, hc, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      incidenceCount, Nat.cast_sum]
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1:ℝ)) f
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  have hv := projective_variance_le hdim w
  rw [hsum, hsumsq] at hv
  have hsub : ∑ y ∈ T, f y^2 ≤ ∑ y, f y^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun _ _ _ => sq_nonneg _)
  calc
    _ = (∑ y ∈ T, f y)^2 := by rw [hf]
    _ ≤ (T.card : ℝ) * ∑ y ∈ T, f y^2 := hCS
    _ ≤ (T.card : ℝ) * ((Nat.card K : ℝ)^(n+1)*S.card) :=
      mul_le_mul_of_nonneg_left (hsub.trans hv) (by positivity)
    _ = _ := by ring

theorem projective_mixing {n : ℕ} (hdim : Module.finrank K V = n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    |(incidenceCount S T : ℝ) -
      (∑ i ∈ range (n+2), (Nat.card K : ℝ)^i) /
      (∑ i ∈ range (n+3), (Nat.card K : ℝ)^i) * S.card * T.card| ≤
      Real.sqrt ((Nat.card K : ℝ)^(n+1)) * Real.sqrt ((S.card : ℝ)*T.card) := by
  calc
    _ ≤ Real.sqrt ((Nat.card K : ℝ)^(n+1) * S.card * T.card) := by
      simpa only [Real.sqrt_sq_eq_abs] using
        Real.sqrt_le_sqrt (projective_mixing_sq hdim S T)
    _ = _ := by rw [mul_assoc, Real.sqrt_mul (by positivity)]

theorem sparse_product_bound {n : ℕ} (hdim : Module.finrank K V = n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V)))
    (hsparse : (incidenceCount S T : ℝ) ≤ (S.card : ℝ)*T.card/(4*Nat.card K)) :
    (S.card : ℝ)*T.card ≤ 16*(Nat.card K : ℝ)^(n+3) := by
  let q : ℝ := Nat.card K
  let v : ℝ := ∑ i ∈ range (n+3), q^i
  let k : ℝ := ∑ i ∈ range (n+2), q^i
  let a : ℝ := (S.card : ℝ)*T.card
  have hq : 1 < q := by
    change (1:ℝ) < (Nat.card K : ℝ)
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)
  have hk : 1 ≤ k := by
    have h0 : (1:ℝ) ≤ ∑ i ∈ range (n+2), q^i := by
      calc
        _ = q^0 := by simp
        _ ≤ ∑ i ∈ range (n+2), q^i :=
          single_le_sum (fun i hi => by positivity) (by simp)
    exact h0
  have hgeom : v = q*k+1 := geom_sum_succ
  have hv : 0 < v := by nlinarith
  have hp : 1/(2*q) ≤ k/v := by
    apply (div_le_div_iff₀ (by positivity) hv).mpr
    nlinarith
  have ha : 0 ≤ a := by positivity
  have hdev : a/(4*q) ≤ k/v*a-(incidenceCount S T : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hp ha
    change (incidenceCount S T : ℝ) ≤ a/(4*q) at hsparse
    have heq : (1/(2*q))*a = 2*(a/(4*q)) := by ring
    rw [heq] at hmul
    linarith
  have hsq := projective_mixing_sq hdim S T
  change ((incidenceCount S T : ℝ) - k/v*S.card*T.card)^2 ≤ q^(n+1)*S.card*T.card at hsq
  have hsq' : (a/(4*q))^2 ≤ q^(n+1)*a := by
    have hdnon : 0 ≤ k/v*a-(incidenceCount S T : ℝ) :=
      (by positivity : 0 ≤ a/(4*q)).trans hdev
    have h := (sq_le_sq₀ (by positivity : 0 ≤ a/(4*q)) hdnon).mpr hdev
    nlinarith [hsq]
  have hpow : q^(n+3) = q^(n+1)*q^2 := by rw [← pow_add]
  rw [hpow]
  by_cases haz : a = 0
  · change a ≤ _; rw [haz]; positivity
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hq0 : q ≠ 0 := by linarith
  have hcancel : (a/(4*q))^2 * (16*q^2) = a^2 := by field_simp; ring
  have hmult := mul_le_mul_of_nonneg_right hsq' (by positivity : 0 ≤ 16*q^2)
  rw [hcancel] at hmult
  change a ≤ _
  nlinarith [hmult]

end Projective
end SharpLogRamsey.Incidence

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem mixing_cell_scale {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) {B z : ℝ}
    (hB : 1≤B) (hz : 0≤z) (hz1 : z≤1)
    (hcap : (S.card:ℝ)*T.card ≤ B*(Nat.card K:ℝ)^(n+3)*z^2) :
    (incidenceCount S T:ℝ) ≤ 2*B*(Nat.card K:ℝ)^(n+2)*z := by
  let q : ℝ := Nat.card K
  let p : ℝ := (∑ i∈range (n+2),q^i)/(∑ i∈range (n+3),q^i)
  let a : ℝ := (S.card:ℝ)*T.card
  have hq : 0<q := by
    dsimp [q]
    exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hv : 0<∑ i∈range (n+3),q^i :=
    sum_pos' (fun i _ => pow_nonneg hq.le _) ⟨0,by simp,by simp⟩
  have hp : p≤1/q := by
    apply (div_le_div_iff₀ hv hq).mpr
    have he : (∑ i∈range (n+3),q^i)=q*(∑ i∈range (n+2),q^i)+1 := geom_sum_succ
    linarith
  have ha : 0≤a := by dsimp [a]; positivity
  have hzz : z^2≤z := by nlinarith
  have hmean : p*a≤B*q^(n+2)*z := by
    have H := mul_le_mul_of_nonneg_right hp ha
    have H' : a/q≤B*q^(n+2)*z^2 := by
      apply (div_le_iff₀ hq).mpr
      change a≤B*q^(n+3)*z^2 at hcap
      calc
        a ≤ B*q^(n+3)*z^2 := hcap
        _ = _ := by rw [show n+3=(n+2)+1 by omega,pow_succ]; ring
    have H'' := mul_le_mul_of_nonneg_left hzz (show 0≤B*q^(n+2) by positivity)
    calc
      p*a ≤ a/q := by simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using H
      _ ≤ B*q^(n+2)*z^2 := H'
      _ ≤ _ := H''
  have hs := projective_mixing_sq hdim S T
  change ((incidenceCount S T:ℝ)-p*S.card*T.card)^2 ≤ q^(n+1)*S.card*T.card at hs
  simp only [mul_assoc] at hs
  change ((incidenceCount S T:ℝ)-p*a)^2 ≤ q^(n+1)*a at hs
  have hscale : q^(n+1)*a ≤ (B*q^(n+2)*z)^2 := by
    have H := mul_le_mul_of_nonneg_left hcap (pow_nonneg hq.le (n+1))
    have he : q^(n+1)*(B*q^(n+3)*z^2)=B*(q^(n+2)*z)^2 := by
      rw [mul_pow,←pow_mul]
      have he : q^(n+1)*q^(n+3)=q^((n+2)*2) := by rw [←pow_add]; congr 1; omega
      calc
        _ = B*(q^(n+1)*q^(n+3))*z^2 := by ring
        _ = _ := by rw [he]; ring
    change q^(n+1)*a ≤ q^(n+1)*(B*q^(n+3)*z^2) at H
    rw [he] at H
    have hBB : B≤B^2 := by nlinarith
    have H' := mul_le_mul_of_nonneg_right hBB (sq_nonneg (q^(n+2)*z))
    exact H.trans (by nlinarith [H'])
  have hpos : 0≤B*q^(n+2)*z := by positivity
  have hdev := (sq_le_sq₀ (abs_nonneg ((incidenceCount S T:ℝ)-p*a)) hpos).mp
    (by simpa using hs.trans hscale)
  have hh := le_abs_self ((incidenceCount S T:ℝ)-p*a)
  linarith

theorem mixing_loss_log {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V)))
    {A B C : ℝ} (hA : 0<A) (hB : 0<B) (hC : 1≤C)
    (hc : A*B≤C*(Nat.card K:ℝ)^(n+3))
    (hS : 0<S.card) (hT : 0<T.card)
    (hSA : (S.card:ℝ)≤A) (hTB : (T.card:ℝ)≤B)
    (he : 0 < incidenceCount S T) :
    Real.log (incidenceCount S T) ≤
      Real.log (2*C*(Nat.card K:ℝ)^(n+2))-
        (Real.log (A/S.card)+Real.log (B/T.card))/2 := by
  let x := Real.log (A/S.card)
  let y := Real.log (B/T.card)
  let z := Real.exp (-(x+y)/2)
  have hS' : (0:ℝ)<S.card := by exact_mod_cast hS
  have hT' : (0:ℝ)<T.card := by exact_mod_cast hT
  have hx : 0≤x := Real.log_nonneg ((one_le_div hS').mpr hSA)
  have hy : 0≤y := Real.log_nonneg ((one_le_div hT').mpr hTB)
  have hz : 0<z := Real.exp_pos _
  have hz1 : z≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hrS : Real.exp (-x)=(S.card:ℝ)/A := by
    rw [Real.exp_neg,Real.exp_log (div_pos hA hS')]
    simp
  have hrT : Real.exp (-y)=(T.card:ℝ)/B := by
    rw [Real.exp_neg,Real.exp_log (div_pos hB hT')]
    simp
  have hez : z^2=Real.exp (-x)*Real.exp (-y) := by
    rw [sq,←Real.exp_add,show -(x+y)/2+(-(x+y)/2)=(-x)+(-y) by ring,Real.exp_add]
  have hprod : (S.card:ℝ)*T.card=A*B*z^2 := by
    rw [hez,hrS,hrT]
    field_simp
  have H := mixing_cell_scale hdim S T hC hz.le hz1
    (show (S.card:ℝ)*T.card≤C*(Nat.card K:ℝ)^(n+3)*z^2 by
      rw [hprod]
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg z))
  have Hlog := Real.log_le_log (show (0:ℝ)< incidenceCount S T by exact_mod_cast he) H
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  rw [Real.log_mul (by positivity : 2*C*(Nat.card K:ℝ)^(n+2)≠0) hz.ne',
    show Real.log z=-(x+y)/2 from Real.log_exp _] at Hlog
  exact Hlog.trans_eq (by dsimp [x,y]; ring)

end SharpLogRamsey.Incidence

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in

lemma incidenceCount_eq_card (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    incidenceCount S T=((S.product T).filter (fun z => Incident z.1 z.2)).card := by
  classical
  simp only [Finset.product_eq_sprod,incidenceCount,Finset.card_filter]
  rw [Finset.sum_product S T,Finset.sum_comm]

end SharpLogRamsey.Incidence

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def positiveSupport (p : Law α) : Finset α := univ.filter (fun a => 0<p.mass a)

lemma positiveSupport_zero (p : Law α) (a : α) (ha : a∉positiveSupport p) : p.mass a=0 := by
  simp only [positiveSupport,mem_filter,mem_univ,true_and,not_lt] at ha
  exact le_antisymm ha (p.nonneg a)

lemma positiveSupport_cell_mass (p : Law α) (f : α→β) (b : β) :
    ∑ a∈(positiveSupport p).filter (fun a => f a=b),p.mass a=(p.map f).mass b := by
  apply sum_subset (by
    intro a ha
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩)
  intro a ha hna
  apply positiveSupport_zero
  intro hs
  exact hna (mem_filter.mpr ⟨hs,(mem_filter.mp ha).2⟩)

lemma positive_cell_nonempty (p : Law α) (f : α→β) (b : β) (hb : 0<(p.map f).mass b) :
    ((positiveSupport p).filter (fun a => f a=b)).Nonempty := by
  by_contra hn
  have he := not_nonempty_iff_eq_empty.mp hn
  have H := positiveSupport_cell_mass p f b
  rw [he,sum_empty] at H
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Incidence
open SharpLogRamsey.Selection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

noncomputable def endpointLabels
    (p : Law (Projectivization K V × Projectivization K (Module.Dual K V))) :=
  fun z : Projectivization K V × Projectivization K (Module.Dual K V) =>
    (levelIndex p.fst z.1,levelIndex p.snd z.2)

omit [Finite K] [FiniteDimensional K V] in
lemma endpoint_cell_subset
    (p : Law (Projectivization K V × Projectivization K (Module.Dual K V)))
    (hs : ∀ z, 0<p.mass z → Incident z.1 z.2)
    (b : Levels p.fst × Levels p.snd) :
    (positiveSupport p).filter (fun z => endpointLabels p z=b) ⊆
      (((levelSet p.fst b.1).product (levelSet p.snd b.2)).filter (fun z => Incident z.1 z.2)) := by
  intro z hz
  have hp := (mem_filter.mp (mem_filter.mp hz).1).2
  have hl := (mem_filter.mp hz).2
  have ha : (levelIndex p.fst z.1)=b.1 := congrArg Prod.fst hl
  have hb : (levelIndex p.snd z.2)=b.2 := congrArg Prod.snd hl
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,hp.trans_le (p.le_fst z.1 z.2),ha⟩,
      mem_filter.mpr ⟨mem_univ _,hp.trans_le (p.le_snd z.1 z.2),hb⟩⟩,hs z hp⟩

theorem reciprocal_level_losses {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (Projectivization K V × Projectivization K (Module.Dual K V)))
    (hs : ∀ z, 0<p.mass z → Incident z.1 z.2)
    {A B C : ℝ} (hA : 0<A) (hB : 0<B) (hC : 1≤C)
    (hc : A*B≤C*(Nat.card K:ℝ)^(n+3))
    (hSA : ∀ b, ((levelSet p.fst b).card:ℝ)≤A)
    (hTB : ∀ b, ((levelSet p.snd b).card:ℝ)≤B) :
    (∑ b, (p.fst.map (levelIndex p.fst)).mass b*levelLoss p.fst A b)+
      (∑ b, (p.snd.map (levelIndex p.snd)).mass b*levelLoss p.snd B b) ≤
        2*(Real.log (2*C*(Nat.card K:ℝ)^(n+2))-entropy p+
          Real.log (entropy p.fst+2)+Real.log (entropy p.snd+2)+2) := by
  classical
  let l := endpointLabels p
  let loss := fun b : Levels p.fst × Levels p.snd => levelLoss p.fst A b.1+levelLoss p.snd B b.2
  have hcell (b : Levels p.fst × Levels p.snd) (hb : 0<(p.map l).mass b) :
      Real.log ((positiveSupport p).filter (fun z => l z=b)).card ≤
        Real.log (2*C*(Nat.card K:ℝ)^(n+2))-loss b/2 := by
    let S := (positiveSupport p).filter (fun z => l z=b)
    have hn := positive_cell_nonempty p l b hb
    obtain ⟨z,hz⟩ := hn
    have hsub := endpoint_cell_subset p hs b
    have hz' := mem_product.mp (mem_filter.mp (hsub (by simpa only [l] using hz))).1
    have hAS : 0<(levelSet p.fst b.1).card := card_pos.mpr ⟨z.1,hz'.1⟩
    have hBT : 0<(levelSet p.snd b.2).card := card_pos.mpr ⟨z.2,hz'.2⟩
    have hcount : S.card≤ incidenceCount (levelSet p.fst b.1) (levelSet p.snd b.2) := by
      rw [incidenceCount_eq_card]
      exact card_le_card hsub
    have hSn : 0<S.card := card_pos.mpr ⟨z,by simpa only [S,mem_filter] using hz⟩
    have HD := mixing_loss_log hdim (levelSet p.fst b.1) (levelSet p.snd b.2)
      hA hB hC hc hAS hBT (hSA b.1) (hTB b.2) (hSn.trans_le hcount)
    have Hlog : Real.log S.card≤Real.log (incidenceCount (levelSet p.fst b.1) (levelSet p.snd b.2)) :=
      Real.log_le_log (by exact_mod_cast hSn) (by exact_mod_cast hcount)
    exact Hlog.trans HD
  have H := partition_loss p l (positiveSupport p) (positiveSupport_zero p) loss
    (Real.log (2*C*(Nat.card K:ℝ)^(n+2))) (by
      intro b hb
      simpa only [l] using hcell b hb)
  have he : (∑ b, (p.map l).mass b*loss b)=
      (∑ b, (p.fst.map (levelIndex p.fst)).mass b*levelLoss p.fst A b)+
      (∑ b, (p.snd.map (levelIndex p.snd)).mass b*levelLoss p.snd B b) := by
    rw [p.sum_map l loss]
    simp only [loss,l,endpointLabels,mul_add,sum_add_distrib]
    rw [p.fst.sum_map (levelIndex p.fst) (levelLoss p.fst A),
      p.snd.sum_map (levelIndex p.snd) (levelLoss p.snd B)]
    apply congrArg₂ (·+·)
    · simp only [Law.fst,Fintype.sum_prod_type,sum_mul]
    · simp only [Law.snd,Fintype.sum_prod_type,sum_mul]
      rw [sum_comm]
  rw [he] at H
  have HH := endpoint_levels_entropy p
  change entropy (p.map l)≤_ at HH
  linarith

end SharpLogRamsey.Incidence

end

end OAI
