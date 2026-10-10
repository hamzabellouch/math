import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.EndpointCurrent

namespace OAI

section
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {α : Type*} [Fintype α]

lemma Law.event_sdiff_lower (p : Law α) (S T : Finset α) :
    p.event S-p.event T ≤ p.event (S\T) := by
  have hsubset : S ⊆ (S \ T) ∪ T := by
    intro atom hmem
    by_cases hremoved : atom ∈ T
    · exact mem_union_right _ hremoved
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hmem, hremoved⟩)
  exact sub_le_iff_le_add.mpr ((p.event_mono hsubset).trans (p.event_union_le _ _))

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]

omit [Finite K] in

lemma Law.core_nonheavy_mass (p : Law (Projectivization K V))
    {ρ ε : ℝ} (hρ : 0 ≤ ρ) (bad : Finset (Projectivization K V))
    (hbad : p.event bad ≤ ε) :
    1-(Module.finrank K V:ℝ)*ρ-ε ≤
      p.event ((univ.filter (fun b => b.rep ∈ p.core (K := K) Projectivization.rep ρ))\bad) := by
  have h := p.core_capture (K := K) Projectivization.rep hρ
  have hh := p.event_sdiff_lower (univ.filter (fun b => b.rep ∈ p.core (K := K) Projectivization.rep ρ)) bad
  linarith

omit [FiniteDimensional K V] in

theorem Law.subspace_log_dimension (p : Law (Projectivization K V))
    (W : Submodule K V) (E : Finset (Projectivization K V)) {A κ γ : ℝ}
    (hA : 0 < A) (hγ : 0 < γ) (hκ : Real.log (2/γ) ≤ κ) (d : ℕ)
    (hmass : γ ≤ p.event E) (hE : ∀ a ∈ E, a.submodule ≤ W)
    (hcap : ∀ a ∈ E, p.mass a ≤ A*Real.exp (2*κ)/(Nat.card K:ℝ)^d) :
    (d:ℝ)+1-(Real.log A+3*κ)/Real.log (Nat.card K) ≤ Module.finrank K W := by
  have hq : (1:ℝ) < Nat.card K := by exact_mod_cast Finite.one_lt_card (α := K)
  have hq0 := lt_trans zero_lt_one hq
  have hc : 0 < A*Real.exp (2*κ)/(Nat.card K:ℝ)^d := by positivity
  have h := p.subspace_mass_le_pow W E hc.le hγ hmass hE hcap
  have hr := p.subspace_rank_pos W E hc.le hγ hmass hE hcap
  have hl := Real.log_le_log hγ h
  rw [Real.log_mul (mul_pos (by norm_num) hc).ne' (pow_ne_zero _ hq0.ne'),
    Real.log_mul (by norm_num) hc.ne', Real.log_div (by positivity) (pow_ne_zero _ hq0.ne'),
    Real.log_mul hA.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_pow, Real.log_pow] at hl
  have hcast : ((Module.finrank K W-1:ℕ):ℝ) = (Module.finrank K W:ℝ)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast] at hl
  rw [Real.log_div (by norm_num) hγ.ne'] at hκ
  have hlog : 0 < Real.log (Nat.card K) := Real.log_pos hq
  have hh : (d:ℝ)+1-(Module.finrank K W:ℝ) ≤ (Real.log A+3*κ)/Real.log (Nat.card K) := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith
  linarith

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {K V A : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] [Fintype A]

lemma conditional_atom_cap {m z M κ L : ℝ} (hM : 0 < M)
    (hm : exp (-κ)/M ≤ m) (hz : z≤exp (κ-L)) :
    z/m≤M*exp (2*κ-L) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hl : exp (-κ)≤ m*M := (div_le_iff₀ hM).mp hm
  apply (div_le_iff₀ hm0).mpr
  calc
    z ≤ exp (κ-L) := hz
    _ = exp (2*κ-L)*exp (-κ) := by rw [← exp_add]; congr 1; ring
    _ ≤ exp (2*κ-L)*(m*M) := mul_le_mul_of_nonneg_left hl (exp_pos _).le
    _ = _ := by ring

theorem conditional_core_dimension (p : Law (Projectivization K V))
    (z : Projectivization K V→ℝ) (m M κ ρ ε : ℝ) (d : ℕ)
    (hM : 0 < M) (hm : exp (-κ)/M ≤ m)
    (hp : ∀ b,p.mass b=z b/m) (hρ : 0≤ρ)
    (hheavy : p.event (univ.filter (fun b => exp (κ-(d:ℝ)*log (Nat.card K))<z b))≤ε)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ) :
    (d:ℝ)+1-(log M+3*κ)/log (Nat.card K)≤
      Module.finrank K (p.core (K:=K) Projectivization.rep ρ) := by
  let bad := univ.filter (fun b : Projectivization K V => exp (κ-(d:ℝ)*log (Nat.card K))<z b)
  let E := (univ.filter (fun b => b.rep∈p.core (K:=K) Projectivization.rep ρ))\bad
  have hmass := p.core_nonheavy_mass hρ bad hheavy
  apply p.subspace_log_dimension (p.core (K:=K) Projectivization.rep ρ) E hM hγ hκ d hmass
  · intro b hb
    rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]
    exact (mem_filter.mp (mem_sdiff.mp hb).1).2
  · intro b hb
    have hz : z b≤exp (κ-(d:ℝ)*log (Nat.card K)) := by
      have hn := (mem_sdiff.mp hb).2
      simpa only [bad,mem_filter,mem_univ,true_and,not_lt] using hn
    rw [hp b]
    have hh := conditional_atom_cap hM hm hz
    have he : exp (2*κ-(d:ℝ)*log (Nat.card K))=exp (2*κ)/(Nat.card K:ℝ)^d := by
      rw [exp_sub,exp_nat_mul,exp_log]
      exact_mod_cast (Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
    rw [he] at hh
    simpa only [mul_div_assoc] using hh

theorem goodSecond_core_dimension (p : Law (Projectivization K V×A))
    (M κ ρ ε : ℝ) (d : ℕ) (a : A) (hM : 0 < M) (hρ : 0≤ρ)
    (hgood : goodSecond p M ((d:ℝ)*log (Nat.card K)) κ ε a)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ) :
    (d:ℝ)+1-(log M+3*κ)/log (Nat.card K)≤
      Module.finrank K ((p.condFst a).core (K:=K) Projectivization.rep ρ) := by
  have hm : p.snd.mass a≠0 := (lt_of_lt_of_le (by positivity) hgood.1).ne'
  exact conditional_core_dimension (p.condFst a) (fun b => p.mass (b,a))
    (p.snd.mass a) M κ ρ ε d hM hgood.1 (p.condFst_mass a hm) hρ hgood.2 hγ hκ

end
end SharpLogRamsey.Selection

end

end OAI
