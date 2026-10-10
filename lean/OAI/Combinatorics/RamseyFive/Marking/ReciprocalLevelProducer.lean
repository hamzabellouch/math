import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ProjectiveExpectedLevelLoss
import OAI.Combinatorics.RamseyFive.Entropy.OrderedReciprocalLaw
import OAI.Combinatorics.RamseyFive.Entropy.ReciprocalSupports

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
lemma eventMass_complement (p : Law α) (E : Finset α) :
    eventMass p Eᶜ+eventMass p E=1 := by
  change (∑ a∈Eᶜ,p a)+(∑ a∈E,p a)=1
  rw [Finset.sum_compl_add_sum]
  exact p.sum_one
lemma entropy_swap (p : Law (α×β)) : entropy (swap p)=entropy p := by
  simp only [entropy,Fintype.sum_prod_type,swap_mass]
  rw [Finset.sum_comm]
lemma support_swap_card (p : Law (α×β)) : (support (swap p)).card=(support p).card := by
  simp only [support,Finset.card_filter, Fintype.sum_prod_type]
  change (∑ b : β,∑ a : α,if 0<p (a,b) then (1:ℕ) else 0)=
    ∑ a : α,∑ b : β,if 0<p (a,b) then (1:ℕ) else 0
  exact Finset.sum_comm
lemma relationMass_good_uniform (R : α→β→Prop) (A GA : Finset α) (B GB : Finset β)
    (hA : A⊆GA) (hB : B⊆GB) :
    relationMass (fun a b=>a∈GA ∧ b∈GB ∧ R a b) (uniformWeight A) (uniformWeight B)=
      relationMass R (uniformWeight A) (uniformWeight B) := by
  simp only [relationMass,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases ha : z.1∈A
  · by_cases hb : z.2∈B
    · simp only [hA ha,hB hb,true_and]
    · simp only [uniformWeight,ite_eq_right hb,mul_zero,ite_self]
  · simp only [uniformWeight,ite_eq_right ha,zero_mul,ite_self]
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def reciprocalBadMass (s d C₀ : ℝ) : ℝ := Real.exp (-s)+50*(d+C₀)/s

omit [FiniteDimensional K V] in
theorem reciprocal_bad_endpoints (p : Law (FlagPair K V)) (u s d C₀ : ℝ)
    (hs : 0<s)
    (hA : ((support (first p)).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u))
    (hB : ((support (second p)).card:ℝ)≤32*Real.exp u)
    (hflag : ((support p).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
    (hent : 4*Real.log (Nat.card K)-entropy p≤d) :
    eventMass (first p) (goodFirstEndpoints p (32*Real.exp (5*Real.log (Nat.card K)-u))
      ((Nat.card K:ℝ)^4) s)ᶜ≤reciprocalBadMass s d C₀ ∧
    eventMass (second p) (goodFirstEndpoints (swap p) (32*Real.exp u)
      ((Nat.card K:ℝ)^4) s)ᶜ≤reciprocalBadMass s d C₀ := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hlog : Real.log ((Nat.card K:ℝ)^4)=4*Real.log (Nat.card K) := by rw [Real.log_pow]; norm_num
  have hratio : (C₀*(Nat.card K:ℝ)^4)/(Nat.card K:ℝ)^4=C₀ := by field_simp
  have hbound : Real.exp (-s)+50*(Real.log ((Nat.card K:ℝ)^4)-entropy p+
      (C₀*(Nat.card K:ℝ)^4)/(Nat.card K:ℝ)^4)/s≤reciprocalBadMass s d C₀ := by
    rw [hlog,hratio]
    exact add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hent (le_refl C₀)) (by norm_num : (0:ℝ)≤50)) hs.le)
  constructor
  · exact (bad_first_endpoint_mass p _ _ _ s (by positivity) (by positivity) hs hA hflag).trans hbound
  · have hflag' : ((support (swap p)).card:ℝ)≤C₀*(Nat.card K:ℝ)^4 := by rw [support_swap_card]; exact hflag
    have hh:=bad_first_endpoint_mass (swap p) (32*Real.exp u) ((Nat.card K:ℝ)^4)
      (C₀*(Nat.card K:ℝ)^4) s (by positivity) (by positivity) hs (by simpa only [first_swap] using hB) hflag'
    simpa only [first_swap,entropy_swap] using hh.trans (by simpa only [entropy_swap] using hbound)

structure ReciprocalLevels (p : Law (FlagPair K V)) (u s : ℝ) where
  firstLaw : Law (Finset (ℙ K V))
  secondLaw : Law (Finset (ℙ K (Dual K V)))
  first_good : ∀ A,0<firstLaw A→A.Nonempty ∧
    A⊆goodFirstEndpoints p (32*Real.exp (5*Real.log (Nat.card K)-u)) ((Nat.card K:ℝ)^4) s ∧
    (32*Real.exp (5*Real.log (Nat.card K)-u))*Real.exp (-s)/2≤(A.card:ℝ) ∧
    (A.card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u)
  second_good : ∀ B,0<secondLaw B→B.Nonempty ∧
    B⊆goodFirstEndpoints (swap p) (32*Real.exp u) ((Nat.card K:ℝ)^4) s ∧
    (32*Real.exp u)*Real.exp (-s)/2≤(B.card:ℝ) ∧ (B.card:ℝ)≤32*Real.exp u
  first_dom : ∀ a,(∑ A,firstLaw A*uniformWeight A a)≤4*Real.exp 1*first p a
  second_dom : ∀ b,(∑ B,secondLaw B*uniformWeight B b)≤4*Real.exp 1*second p b

theorem reciprocal_levels_exist (hdim : finrank K V=5)
    (p : Law (FlagPair K V)) (u s d C₀ : ℝ)
    (hinc : ∀ z,0<p z→Incident z.1 z.2) (hs : 0<s)
    (hA : ((support (first p)).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u))
    (hB : ((support (second p)).card:ℝ)≤32*Real.exp u)
    (hflag : ((support p).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
    (hent : 4*Real.log (Nat.card K)-entropy p≤d)
    (hsmall : 2*(d+Real.log 32+Real.log 33+
      2*(Real.log (5*Real.log (Nat.card K)+1)+1))/s+
      2*Real.exp 1*reciprocalBadMass s d C₀≤(1:ℝ)/2) :
    Nonempty (ReciprocalLevels p u s) := by
  obtain ⟨ha,hb⟩:=reciprocal_bad_endpoints p u s d C₀ hs hA hB hflag hent
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hprod : (32*Real.exp (5*Real.log (Nat.card K)-u))*(32*Real.exp u)=
      32^2*(Nat.card K:ℝ)^5 := by
    have he : Real.exp (5*Real.log (Nat.card K)-u)*Real.exp u=(Nat.card K:ℝ)^5 := by
      rw [←Real.exp_add,sub_add_cancel]
      rw [show (5:ℝ)*Real.log (Nat.card K)=(5:ℕ)*Real.log (Nat.card K) from rfl,
        Real.exp_nat_mul,Real.exp_log hq]
    nlinarith only [he]
  obtain ⟨μ,ν,hμ,hν,hdμ,hdν⟩:=endpoint_supports hdim p hinc
    (32*Real.exp (5*Real.log (Nat.card K)-u)) (32*Real.exp u) 32 s d
    (reciprocalBadMass s d C₀) (by positivity) (by positivity) (by norm_num) hs
    hA hB hprod.le hent _ _ ha hb (by simpa only [show (32:ℝ)+1=33 by norm_num] using hsmall)
  refine ⟨⟨μ,ν,?_,?_,hdμ,hdν⟩⟩
  · intro A h
    have hh:=hμ A h
    have hn : 0<(A.card:ℝ):=(by positivity : 0<(32*Real.exp (5*Real.log (Nat.card K)-u))*Real.exp (-s)/2).trans_le hh.2.1
    exact ⟨Finset.card_pos.mp (by exact_mod_cast hn),hh⟩
  · intro B h
    have hh:=hν B h
    have hn : 0<(B.card:ℝ):=(by positivity : 0<(32*Real.exp u)*Real.exp (-s)/2).trans_le hh.2.1
    exact ⟨Finset.card_pos.mp (by exact_mod_cast hn),hh⟩
end
end SharpRamseyFive.Marking

end

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma ReciprocalLevels.first_size {p : Law (FlagPair K V)} {u s : ℝ}
    (L : ReciprocalLevels p u s) (A : Finset (ℙ K V)) (hA : 0<L.firstLaw A) :
    Real.exp (5*Real.log (Nat.card K)-u-s)/2≤(A.card:ℝ) := by
  have h:=(L.first_good A hA).2.2.1
  have he : Real.exp (5*Real.log (Nat.card K)-u)*Real.exp (-s)=
      Real.exp (5*Real.log (Nat.card K)-u-s) := by rw [←Real.exp_add]; congr 1
  nlinarith [Real.exp_pos (5*Real.log (Nat.card K)-u-s)]
omit [Finite K] [FiniteDimensional K V] in
lemma ReciprocalLevels.second_size {p : Law (FlagPair K V)} {u s : ℝ}
    (L : ReciprocalLevels p u s) (B : Finset (ℙ K (Dual K V))) (hB : 0<L.secondLaw B) :
    Real.exp (u-s)/2≤(B.card:ℝ) := by
  have h:=(L.second_good B hB).2.2.1
  have he : Real.exp u*Real.exp (-s)=Real.exp (u-s) := by rw [←Real.exp_add]; congr 1
  nlinarith [Real.exp_pos (u-s)]

omit [Finite K] [FiniteDimensional K V] in
theorem reciprocal_levels_cross (p q : Law (FlagPair K V)) (u v s ρ : ℝ)
    (L : ReciprocalLevels p u s) (R : ReciprocalLevels q v s)
    (hρ : relationMass (fun a b=>a∈goodFirstEndpoints p
        (32*Real.exp (5*Real.log (Nat.card K)-u)) ((Nat.card K:ℝ)^4) s ∧
      b∈goodFirstEndpoints (swap q) (32*Real.exp v) ((Nat.card K:ℝ)^4) s ∧ Incident a b)
      (first p) (second q)≤ρ) :
    (∑ A,∑ B,L.firstLaw A*R.secondLaw B*
      relationMass Incident (uniformWeight A) (uniformWeight B))≤(4*Real.exp 1)^2*ρ := by
  let GA:=goodFirstEndpoints p (32*Real.exp (5*Real.log (Nat.card K)-u)) ((Nat.card K:ℝ)^4) s
  let GB:=goodFirstEndpoints (swap q) (32*Real.exp v) ((Nat.card K:ℝ)^4) s
  have h:=independent_support_domination (fun a b=>a∈GA ∧ b∈GB ∧ Incident a b)
    (first p) (second q) L.firstLaw R.secondLaw id id (4*Real.exp 1)
    (by positivity) L.first_dom R.second_dom
  have he : (∑ A,∑ B,L.firstLaw A*R.secondLaw B*
      relationMass (fun a b=>a∈GA ∧ b∈GB ∧ Incident a b) (uniformWeight A) (uniformWeight B))=
      ∑ A,∑ B,L.firstLaw A*R.secondLaw B*relationMass Incident (uniformWeight A) (uniformWeight B) := by
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    by_cases ha : 0<L.firstLaw A
    · by_cases hb : 0<R.secondLaw B
      · rw [relationMass_good_uniform Incident A GA B GB (L.first_good A ha).2.1 (R.second_good B hb).2.1]
      · rw [show R.secondLaw B=0 from le_antisymm (le_of_not_gt hb) (R.secondLaw.nonneg B)]
        ring
    · rw [show L.firstLaw A=0 from le_antisymm (le_of_not_gt ha) (L.firstLaw.nonneg A)]
      ring
  dsimp only [id_eq] at h
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left hρ (sq_nonneg _))

variable [Fintype I] {n : ℕ}

omit [Finite K] in
theorem ordered_level_sparsity (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : I) (hij : e i<e j)
    (L : ReciprocalLevels (map p (fun x=>x i)) (u i) s)
    (R : ReciprocalLevels (map p (fun x=>x j)) (u j) s) :
    (∑ A,∑ B,L.firstLaw A*R.secondLaw B*
      relationMass Incident (uniformWeight A) (uniformWeight B))≤
      ((4*Real.exp 1)^2*80004)*(entropy (map p (fun x=>x i))+entropy (map p (fun x=>x j))-
        entropy (pair p (fun x=>x i) (fun x=>x j))+orderedCollision p e u s i j) := by
  have h:=reciprocal_levels_cross _ _ _ _ s _ L R
    (ordered_reciprocal_low_conflict hdim p e u s hcons i j hij)
  simpa only [mul_assoc] using h

theorem ordered_good_u_monotone (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : I) (hij : e i<e j)
    (L : ReciprocalLevels (map p (fun x=>x i)) (u i) s)
    (R : ReciprocalLevels (map p (fun x=>x j)) (u j) s)
    (hgood : entropy (map p (fun x=>x i))+entropy (map p (fun x=>x j))-
      entropy (pair p (fun x=>x i) (fun x=>x j))+orderedCollision p e u s i j≤ε)
    (hsmall : ((4*Real.exp 1)^2*80004)*ε≤1/(4*(Nat.card K:ℝ))) :
    u j≤u i+2*s+Real.log 64 := by
  apply reciprocal_u_monotone hdim L.firstLaw R.secondLaw (u i) (u j) s
    L.first_size R.second_size
  exact (ordered_level_sparsity hdim p e u s hcons i j hij L R).trans
    ((mul_le_mul_of_nonneg_left hgood (by positivity)).trans hsmall)
end
end SharpRamseyFive.Marking

end OAI
