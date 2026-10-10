import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.ExposureGood

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Selection
variable {α : Type*} [Fintype α]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

noncomputable def Law.tests (p : Law α) (v : α → V) (ρ : ℝ) : Set (Module.Dual K V) :=
  {f | p.event (univ.filter (fun a => f (v a) ≠ 0)) ≤ ρ}

noncomputable def Law.core (p : Law α) (v : α → V) (ρ : ℝ) : Submodule K V :=
  (Submodule.span K (p.tests (K:=K) v ρ)).dualCoannihilator

omit [FiniteDimensional K V] in
theorem Law.mem_core (p : Law α) (v : α → V) (ρ : ℝ) (x : V) :
    x ∈ p.core (K:=K) v ρ ↔ ∀ f ∈ p.tests (K:=K) v ρ, f x = 0 := by
  unfold Law.core
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h f hf
    exact h f (Submodule.subset_span hf)
  · intro h
    have hs : Submodule.span K (p.tests (K:=K) v ρ) ≤ LinearMap.ker (Module.Dual.eval K V x) := by
      rw [Submodule.span_le]
      exact h
    exact fun f hf => hs hf

omit [FiniteDimensional K V] in
theorem Law.core_le_test (p : Law α) (v : α → V) (ρ : ℝ)
    (f : Module.Dual K V) (hf : p.event (univ.filter (fun a => f (v a) ≠ 0)) ≤ ρ) :
    p.core (K:=K) v ρ ≤ LinearMap.ker f := by
  intro x hx
  exact (p.mem_core (K:=K) v ρ x).mp hx f hf

theorem Law.core_failure_le (p : Law α) (v : α → V) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    p.event (univ.filter (fun a => v a ∉ p.core (K:=K) v ρ)) ≤
      (Module.finrank K V : ℝ)*ρ := by
  obtain ⟨b,hb,hspan,hli⟩ := exists_linearIndependent K (p.tests (K:=K) v ρ)
  let : Finite b := hli.finite
  let : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b ≤ Module.finrank K V := by
    have h := hli.fintype_card_le_finrank
    simpa only [Subspace.dual_finrank_eq] using h
  have hsome (a : α) (ha : v a ∉ p.core (K:=K) v ρ) : ∃ f : b, f.val (v a) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply ha
    rw [p.mem_core (K:=K)]
    have hs : Submodule.span K b ≤ LinearMap.ker (Module.Dual.eval K V (v a)) := by
      rw [Submodule.span_le]
      intro f hf
      exact hn ⟨f,hf⟩
    rw [hspan] at hs
    intro f hf
    exact hs (Submodule.subset_span hf)
  have hpoint (a : α) :
      (if v a ∉ p.core (K:=K) v ρ then p.mass a else 0) ≤
        ∑ f : b, if f.val (v a) ≠ 0 then p.mass a else 0 := by
    by_cases ha : v a ∉ p.core (K:=K) v ρ
    · obtain ⟨f,hf⟩ := hsome a ha
      rw [ite_eq_left ha]
      calc
        _ = (if f.val (v a) ≠ 0 then p.mass a else 0) := (ite_eq_left hf).symm
        _ ≤ ∑ g : b, if g.val (v a) ≠ 0 then p.mass a else 0 :=
          single_le_sum (f := fun g : b => if g.val (v a) ≠ 0 then p.mass a else 0)
            (fun g hg => by split_ifs <;> first | exact p.nonneg _ | positivity) (mem_univ f)
    · rw [ite_eq_right ha]
      exact sum_nonneg fun f hf => by split_ifs <;> first | exact p.nonneg _ | positivity
  calc
    p.event (univ.filter (fun a => v a ∉ p.core (K:=K) v ρ))
      = ∑ a, if v a ∉ p.core (K:=K) v ρ then p.mass a else 0 := by simp only [Law.event,sum_filter]
    _ ≤ ∑ a, ∑ f : b, if f.val (v a) ≠ 0 then p.mass a else 0 := sum_le_sum fun a ha => hpoint a
    _ = ∑ f : b, p.event (univ.filter (fun a => f.val (v a) ≠ 0)) := by
      rw [sum_comm]; simp only [Law.event,sum_filter]
    _ ≤ ∑ _ : b, ρ := sum_le_sum fun f hf => hb f.property
    _ = (Fintype.card b : ℝ)*ρ := by simp
    _ ≤ (Module.finrank K V : ℝ)*ρ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hρ

theorem Law.event_complement (p : Law α) (E : Finset α) :
    p.event E + p.event Eᶜ = 1 := by
  exact (sum_add_sum_compl E p.mass).trans p.total

theorem Law.core_capture (p : Law α) (v : α → V) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    1-(Module.finrank K V : ℝ)*ρ ≤
      p.event (univ.filter (fun a => v a ∈ p.core (K:=K) v ρ)) := by
  have h := p.core_failure_le (K:=K) v hρ
  have hc := p.event_complement (univ.filter (fun a => v a ∈ p.core (K:=K) v ρ))
  have he : (univ.filter (fun a => v a ∈ p.core (K:=K) v ρ))ᶜ =
      univ.filter (fun a => v a ∉ p.core (K:=K) v ρ) := by ext a; simp
  rw [he] at hc
  linarith

variable {β : Type*} [Fintype β]

theorem Law.event_gt_le (p : Law α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    {ρ : ℝ} (_hρ : 0 < ρ) :
    p.event (univ.filter (fun a => ρ < f a))*ρ ≤ ∑ a, p.mass a*f a := by
  rw [Law.event,sum_filter,sum_mul]
  apply sum_le_sum
  intro a ha
  by_cases he : ρ < f a
  · rw [ite_eq_left he]
    exact mul_le_mul_of_nonneg_left he.le (p.nonneg a)
  · rw [ite_eq_right he,zero_mul]
    exact mul_nonneg (p.nonneg a) (hf a)

omit [FiniteDimensional K V] in

theorem Law.cores_orthogonal (p : Law α) (q : Law β) (v : α → V)
    (w : β → Module.Dual K V) {ρ : ℝ} (hρ : 0 < ρ)
    (herror : (p.prod q).event (univ.filter (fun z : α × β => w z.2 (v z.1) ≠ 0)) ≤ ρ^2) :
    (q.core (K:=K) w ρ) ≤ (p.core (K:=K) v ρ).dualAnnihilator := by
  let err : α → ℝ := fun a => q.event (univ.filter (fun b => w b (v a) ≠ 0))
  have hmean : (∑ a, p.mass a*err a) =
      (p.prod q).event (univ.filter (fun z : α × β => w z.2 (v z.1) ≠ 0)) := by
    simp only [err,Law.event,Law.prod,sum_filter,Fintype.sum_prod_type,mul_sum,mul_ite,mul_zero]
  have hbad : p.event (univ.filter (fun a => ρ < err a)) ≤ ρ := by
    have h := p.event_gt_le err (fun a => q.event_nonneg _) hρ
    rw [hmean] at h
    apply (mul_le_mul_iff_left₀ hρ).mp
    nlinarith
  intro f hf
  rw [Submodule.mem_dualAnnihilator]
  have ht : f ∈ p.tests (K:=K) v ρ := by
    change p.event (univ.filter (fun a => f (v a) ≠ 0)) ≤ ρ
    apply le_trans _ hbad
    apply sum_le_sum_of_subset_of_nonneg
    · intro a ha
      simp only [mem_filter,mem_univ,true_and] at ha ⊢
      by_contra hn
      have he : Module.Dual.eval K V (v a) ∈ q.tests (K:=K) w ρ := by
        exact le_of_not_gt hn
      exact ha ((q.mem_core (K:=K) w ρ f).mp hf _ he)
    · intro a ha hb
      exact p.nonneg a
  intro x hx
  exact (p.mem_core (K:=K) v ρ x).mp hx f ht

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def Incident (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) : Prop := b.rep a.rep = 0

theorem incident_iff_submodule (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) :
    Incident a b ↔ a.submodule ≤ LinearMap.ker b.rep := by
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
  rfl

noncomputable def projectiveSubmoduleEquiv (W : Submodule K V) :
    Projectivization K W ≃ {a : Projectivization K V // a.submodule ≤ W} := by
  let f : Projectivization K W → {a : Projectivization K V // a.submodule ≤ W} :=
    fun a => ⟨Projectivization.map W.subtype W.injective_subtype a, by
      induction a using Projectivization.ind with
      | h v hv =>
        rw [Projectivization.map_mk, Projectivization.submodule_mk,
          Submodule.span_singleton_le_iff_mem]
        exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    exact Projectivization.map_injective W.subtype W.injective_subtype
      (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    have hmem : a.rep ∈ W := ha (by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _)
    let v : W := ⟨a.rep, hmem⟩
    have hv : v ≠ 0 := fun h => a.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact a.mk_rep

end SharpLogRamsey.Incidence

namespace SharpLogRamsey.Selection
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]

omit [FiniteDimensional K V] in

theorem card_projective_subspace (W : Submodule K V) :
    Fintype.card {a : Projectivization K V // a.submodule ≤ W} =
      ∑ i ∈ Finset.range (Module.finrank K W), Nat.card K ^ i := by
  rw [← Nat.card_eq_fintype_card,
    ← Nat.card_congr (projectiveSubmoduleEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

omit [FiniteDimensional K V] in

theorem Law.subspace_mass_bound (p : Law (Projectivization K V))
    (W : Submodule K V) (E : Finset (Projectivization K V)) {c : ℝ}
    (hc : 0 ≤ c) (hE : ∀ a ∈ E, a.submodule ≤ W)
    (hcap : ∀ a ∈ E, p.mass a ≤ c) :
    p.event E ≤ c * ∑ i ∈ Finset.range (Module.finrank K W), (Nat.card K : ℝ)^i := by
  have hcard : E.card ≤ Fintype.card {a : Projectivization K V // a.submodule ≤ W} := by
    rw [Fintype.card_subtype]
    apply card_le_card
    intro a ha
    exact mem_filter.mpr ⟨mem_univ _,hE a ha⟩
  calc
    p.event E ≤ ∑ _a ∈ E, c := sum_le_sum hcap
    _ = c*E.card := by simp [mul_comm]
    _ ≤ c * (Fintype.card {a : Projectivization K V // a.submodule ≤ W} : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hc
    _ = _ := by rw [card_projective_subspace]; simp

theorem sum_powers_le_twice {q : ℝ} (hq : 2 ≤ q) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, q^i ≤ 2*q^(n-1) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one]
  clear hn
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hp : 0 ≤ q^m := pow_nonneg (by linarith) _
    have hmul : 2*q^m ≤ q^(m+1) := by
      rw [pow_succ]
      nlinarith
    calc
      _ ≤ 2*q^m+q^(m+1) := by
        simp only [Nat.succ_eq_add_one] at ih
        linarith
      _ ≤ 2*q^(m+1) := by linarith

omit [FiniteDimensional K V] in

theorem Law.subspace_rank_pos (p : Law (Projectivization K V))
    (W : Submodule K V) (E : Finset (Projectivization K V)) {c γ : ℝ}
    (hc : 0 ≤ c) (hγ : 0 < γ) (hmass : γ ≤ p.event E)
    (hE : ∀ a ∈ E, a.submodule ≤ W)
    (hcap : ∀ a ∈ E, p.mass a ≤ c) : 0 < Module.finrank K W := by
  have h := p.subspace_mass_bound W E hc hE hcap
  by_contra hn
  have hz : Module.finrank K W = 0 := by omega
  simp only [hz,range_zero,sum_empty,mul_zero] at h
  linarith

omit [FiniteDimensional K V] in

theorem Law.subspace_mass_le_pow (p : Law (Projectivization K V))
    (W : Submodule K V) (E : Finset (Projectivization K V)) {c γ : ℝ}
    (hc : 0 ≤ c) (hγ : 0 < γ) (hmass : γ ≤ p.event E)
    (hE : ∀ a ∈ E, a.submodule ≤ W)
    (hcap : ∀ a ∈ E, p.mass a ≤ c) :
    γ ≤ 2*c*(Nat.card K : ℝ)^(Module.finrank K W-1) := by
  have hr := p.subspace_rank_pos W E hc hγ hmass hE hcap
  have hq : (2 : ℝ) ≤ Nat.card K := by
    exact_mod_cast (Finite.one_lt_card (α:=K))
  calc
    γ ≤ p.event E := hmass
    _ ≤ c * ∑ i ∈ range (Module.finrank K W), (Nat.card K : ℝ)^i :=
      p.subspace_mass_bound W E hc hE hcap
    _ ≤ c*(2*(Nat.card K : ℝ)^(Module.finrank K W-1)) :=
      mul_le_mul_of_nonneg_left (sum_powers_le_twice hq hr) hc
    _ = _ := by ring

end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]

theorem Law.small_atoms (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) {c : ℝ} (hc : 0 ≤ c) :
    p.event (univ.filter (fun a => p.mass a < c)) ≤ S.card*c := by
  have h (a : α) : (if p.mass a < c then p.mass a else 0) ≤
      if a ∈ S then c else 0 := by
    by_cases ha : a ∈ S
    · rw [ite_eq_left ha]; split_ifs <;> linarith
    · rw [ite_eq_right ha,hs a ha]; split_ifs <;> rfl
  have hh := sum_le_sum fun a (_ : a ∈ univ) => h a
  simpa [Law.event, sum_filter] using hh

theorem negative_log_part (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) (L : ℝ) :
    (∑ a, p.mass a*max (-(Real.log (p.mass a)+L)) 0) ≤ S.card*Real.exp (-L) := by
  have pointwise (a : α) : p.mass a*max (-(Real.log (p.mass a)+L)) 0 ≤
      if a ∈ S then Real.exp (-L) else 0 := by
    by_cases ha : a ∈ S
    · rw [ite_eq_left ha]
      by_cases hp : p.mass a = 0
      · simp [hp,Real.exp_nonneg]
      have hp0 : 0 < p.mass a := lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)
      by_cases hz : 0 ≤ -(Real.log (p.mass a)+L)
      · rw [max_eq_left hz]
        have hh := mul_log_div_ge (p.nonneg a) (Real.exp_nonneg (-L))
          (fun h => False.elim ((Real.exp_ne_zero _) h))
        rw [Real.log_div hp (Real.exp_ne_zero _),Real.log_exp] at hh
        nlinarith
      · rw [max_eq_right (le_of_not_ge hz),mul_zero]
        exact Real.exp_nonneg _
    · rw [ite_eq_right ha,hs a ha,zero_mul]
  have h := sum_le_sum fun a (_ : a ∈ univ) => pointwise a
  simpa using h

theorem positive_log_part (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) (L : ℝ) :
    (∑ a, p.mass a*max (Real.log (p.mass a)+L) 0) ≤
      L-entropy p+S.card*Real.exp (-L) := by
  have pointwise (a : α) : p.mass a*max (Real.log (p.mass a)+L) 0 =
      p.mass a*(Real.log (p.mass a)+L)+
      p.mass a*max (-(Real.log (p.mass a)+L)) 0 := by
    by_cases h : 0 ≤ Real.log (p.mass a)+L
    · rw [max_eq_left h,max_eq_right (by linarith)]; ring
    · rw [max_eq_right (le_of_not_ge h),max_eq_left (by linarith)]; ring
  simp_rw [pointwise,sum_add_distrib,mul_add,sum_add_distrib,← sum_mul,p.total,one_mul]
  have h := negative_log_part p S hs L
  unfold entropy
  linarith

theorem Law.heavy_atoms (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) (L : ℝ) {K : ℝ} (hK : 0 < K) :
    p.event (univ.filter (fun a => Real.exp (K-L) < p.mass a)) ≤
      (L-entropy p+S.card*Real.exp (-L))/K := by
  apply (le_div_iff₀ hK).mpr
  have h (a : α) : (if Real.exp (K-L) < p.mass a then p.mass a else 0)*K ≤
      p.mass a*max (Real.log (p.mass a)+L) 0 := by
    by_cases ha : Real.exp (K-L) < p.mass a
    · rw [ite_eq_left ha]
      have hp : 0 < p.mass a := (Real.exp_pos _).trans ha
      have hh := Real.log_lt_log (Real.exp_pos (K-L)) ha
      rw [Real.log_exp] at hh
      have hle : K ≤ max (Real.log (p.mass a)+L) 0 :=
        (by linarith : K ≤ Real.log (p.mass a)+L).trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left hle (p.nonneg a)
    · rw [ite_eq_right ha,zero_mul]
      exact mul_nonneg (p.nonneg _) (le_max_right _ _)
  have hh := (sum_le_sum fun a (_ : a ∈ univ) => h a).trans (positive_log_part p S hs L)
  simpa only [Law.event,sum_filter,sum_mul] using hh

theorem Law.bad_conditional_mass (p : Law (α × β)) (E : Finset (α × β))
    {ρ : ℝ} (hρ : 0 < ρ) :
    p.snd.event (univ.filter (fun b =>
      ρ < (p.condFst b).event (univ.filter (fun a => (a,b) ∈ E)))) ≤ p.event E/ρ := by
  apply (le_div_iff₀ hρ).mpr
  have hh (b : β) :
      (if ρ < (p.condFst b).event (univ.filter (fun a => (a,b) ∈ E))
        then p.snd.mass b else 0)*ρ ≤ ∑ a, if (a,b) ∈ E then p.mass (a,b) else 0 := by
    have he : p.snd.mass b*((p.condFst b).event (univ.filter (fun a => (a,b) ∈ E))) =
        ∑ a, if (a,b) ∈ E then p.mass (a,b) else 0 := by
      simp only [Law.event,sum_filter,mul_sum,mul_ite,mul_zero,p.snd_mul_condFst]
    rw [← he]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left h.le (p.snd.nonneg b)
    · rw [zero_mul]
      exact mul_nonneg (p.snd.nonneg b) ((p.condFst b).event_nonneg _)
  have h := sum_le_sum fun b (_ : b ∈ univ) => hh b
  have he : (∑ z, if z ∈ E then p.mass z else 0) = p.event E := by
    rw [← sum_filter]
    simp [Law.event]
  change (∑ b with ρ < (p.condFst b).event (univ.filter (fun a => (a,b) ∈ E)), p.snd.mass b)*ρ ≤ _
  rw [sum_filter,sum_mul,← he,Fintype.sum_prod_type,sum_comm]
  exact h

end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

def Law.condSnd (p : Law (A × B)) (a : A) : Law B :=
  (p.cond Prod.fst a).map Prod.snd

lemma Law.fst_mul_condSnd (p : Law (A × B)) (a : A) (b : B) :
    p.fst.mass a*(p.condSnd a).mass b = p.mass (a,b) := by
  have h := p.cond_map_weight Prod.fst Prod.snd a b
  rw [Law.map_fst] at h
  change p.fst.mass a*((p.cond Prod.fst a).map Prod.snd).mass b = _
  rw [h]
  simp [Law.map, Fintype.sum_prod_type, sum_filter, Prod.mk.injEq, and_comm, ite_and]

lemma Law.condSnd_mass (p : Law (A × B)) (a : A) (ha : p.fst.mass a ≠ 0) (b : B) :
    (p.condSnd a).mass b = p.mass (a,b)/p.fst.mass a := by
  apply (eq_div_iff ha).mpr
  rw [mul_comm, p.fst_mul_condSnd]

lemma Law.paired_cond_mass (p : Law (A × B)) (q : Law (C × D))
    (a : A) (b : B) (c : C) (y : D) (v : ℝ) :
    (p.fst.mass a*q.snd.mass y)*
      (((p.condSnd a).mass b*(q.condFst y).mass c)*v) =
    (p.mass (a,b)*q.mass (c,y))*v := by
  calc
    _ = (p.fst.mass a*(p.condSnd a).mass b)*
      (q.snd.mass y*(q.condFst y).mass c)*v := by ring
    _ = _ := by rw [p.fst_mul_condSnd,q.snd_mul_condFst]

lemma Law.product_disintegration (p : Law (A × B)) (q : Law (C × D))
    (F : (A × B) → (C × D) → ℝ) :
    (∑ z : (A × B) × (C × D), (p.prod q).mass z * F z.1 z.2) =
    ∑ ay : A × D, (p.fst.prod q.snd).mass ay *
      ∑ bc : B × C, ((p.condSnd ay.1).prod (q.condFst ay.2)).mass bc *
        F (ay.1,bc.1) (bc.2,ay.2) := by
  simp only [Law.prod, Fintype.sum_prod_type, mul_sum]
  simp_rw [p.paired_cond_mass q]
  apply sum_congr rfl
  intro a _
  calc
    _ = ∑ b : B, ∑ y : D, ∑ c : C, p.mass (a,b)*q.mass (c,y)*F (a,b) (c,y) := by
      apply sum_congr rfl
      intro b _
      exact sum_comm
    _ = _ := sum_comm

lemma Law.product_event_disintegration (p : Law (A × B)) (q : Law (C × D))
    (E : (A × B) → (C × D) → Prop) :
    (p.prod q).event (univ.filter (fun z => E z.1 z.2)) =
    ∑ ay : A × D, (p.fst.prod q.snd).mass ay *
      ((p.condSnd ay.1).prod (q.condFst ay.2)).event
        (univ.filter (fun bc : B × C => E (ay.1,bc.1) (bc.2,ay.2))) := by
  simpa only [Law.event, sum_filter, mul_ite, mul_one, mul_zero] using
    p.product_disintegration q (fun ab cy => if E ab cy then 1 else 0)

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

end
end SharpLogRamsey.Selection
end

end OAI
