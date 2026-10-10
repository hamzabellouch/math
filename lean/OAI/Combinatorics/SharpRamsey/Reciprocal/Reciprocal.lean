import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.CoreDimensions

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

def goodFirst (p : Law (A×B)) (M L κ ε : ℝ) (a : A) : Prop :=
  exp (-κ)/M ≤ p.fst.mass a ∧
  (p.condSnd a).event (univ.filter (fun b => exp (κ-L)<p.mass (a,b)))≤ε

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]

theorem goodFirst_core_dimension (p : Law (A×Projectivization K V))
    (M κ ρ ε : ℝ) (d : ℕ) (a : A) (hM : 0 < M) (hρ : 0≤ρ)
    (hgood : goodFirst p M ((d:ℝ)*log (Nat.card K)) κ ε a)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ) :
    (d:ℝ)+1-(log M+3*κ)/log (Nat.card K)≤
      Module.finrank K (firstCore (K:=K) p Projectivization.rep ρ a) := by
  have hm : p.fst.mass a≠0 :=
    (lt_of_lt_of_le (div_pos (exp_pos (-κ)) hM) hgood.1).ne'
  exact conditional_core_dimension (p.condSnd a) (fun b => p.mass (a,b))
    (p.fst.mass a) M κ ρ ε d hM hgood.1 (p.condSnd_mass a hm) hρ hgood.2 hγ hκ

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem reciprocal_open_incidence (p : Law ((A × B) × (A × B)))
    (v : B → V) (w : A → Module.Dual K V) {ρ : ℝ} (hρ : 0 < ρ)
    (goodA : A → Prop) (goodB : B → Prop)
    {r s : ℕ} (hsum : Module.finrank K V < r+s)
    (hW : ∀ a, goodA a → r ≤ Module.finrank K (firstCore (K := K) p.fst v ρ a))
    (hU : ∀ y, goodB y → s ≤ Module.finrank K (secondCore p.snd w ρ y))
    (hconsistent : ∀ z, p.mass z ≠ 0 →
      w z.1.1 (v z.2.2) = 0 → w z.2.1 (v z.1.2) = 0) :
    (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay : A × B =>
      goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0)) ≤ 2*mutualInfo p/ρ^2 := by
  have he := exceptional_core_mass p.fst p.snd v w hρ goodA goodB
  have heq : (univ.filter (fun ay : A × B =>
      (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
      ¬coreContained p.fst p.snd v w ρ ay.1 ay.2)) =
      univ.filter (fun ay : A × B => goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) := by
    ext ay
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨And.left, fun h => ⟨h,?_⟩⟩
    exact not_contained_of_rank_sum _ _ (hW _ h.1) (hU _ h.2.1) hsum
  rw [heq] at he
  have hz : p.event (univ.filter (fun z : (A × B) × (A × B) =>
      w z.1.1 (v z.2.2) = 0 ∧ w z.2.1 (v z.1.2) ≠ 0)) = 0 := by
    apply sum_eq_zero
    intro z hz
    by_contra hn
    exact (mem_filter.mp hz).2.2 (hconsistent z hn (mem_filter.mp hz).2.1)
  have ht := mutualInfo_event_transfer p (univ.filter (fun z : (A × B) × (A × B) =>
      w z.1.1 (v z.2.2) = 0 ∧ w z.2.1 (v z.1.2) ≠ 0))
  rw [hz,add_zero] at ht
  apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
  simpa only [mul_comm] using he.trans ht

lemma open_band_rank {σ e u v : ℝ} {d r a b : ℕ}
    (hu : (r:ℝ)-1 < (u-e)/σ)
    (hv : (r:ℝ) > (v+e)/σ)
    (ha : (u-e)/σ ≤ a) (hb : (d:ℝ)+1-(v+e)/σ ≤ b) :
    d+1 < a+b := by
  have har : r ≤ a := by
    by_contra hn
    have hn' : (a:ℝ)+1 ≤ r := by exact_mod_cast (show a+1 ≤ r by omega)
    linarith
  have hreal : (d:ℝ)+1-r < b := by linarith
  have hab : d+1 < b+r := by exact_mod_cast (show (d:ℝ)+1 < (b:ℝ)+r by linarith)
  omega

lemma integer_band_rank {e u v σ : ℝ} {d r a b : ℕ}
    (hu : (r:ℝ)-1 < (u-e)/σ)
    (hv : (v+e)/σ < (r:ℝ)+1)
    (ha : (u-e)/σ ≤ a) (hb : (d:ℝ)+1-(v+e)/σ ≤ b) :
    r ≤ a ∧ d+1-r ≤ b := by
  constructor
  · by_contra hn
    have hn' : (a:ℝ)+1 ≤ r := by exact_mod_cast (show a+1 ≤ r by omega)
    linarith
  · have hreal : (d:ℝ)-r < b := by linarith
    have hab : d < b+r := by exact_mod_cast (show (d:ℝ) < (b:ℝ)+r by linarith)
    omega

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

private lemma round_core_rank {r a : ℕ} {x : ℝ}
    (hx : (r:ℝ)-1<x) (ha : x≤a) : r≤a := by
  by_contra hn
  have hn' : (a:ℝ)+1≤r := by exact_mod_cast (show a+1≤r by omega)
  linarith

theorem projective_open_incidence
    (p : Law ((Projectivization K (Module.Dual K V)×Projectivization K V)×
      (Projectivization K (Module.Dual K V)×Projectivization K V)))
    (MA MB κ ρ ε : ℝ) (d r : ℕ) (hMA : 0<MA) (hMB : 0<MB) (hρ : 0<ρ)
    (hd : Module.finrank K V=d+1) (hr : r≤d+1)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ)
    (hu : (r:ℝ)-1 < (d:ℝ)+1-(log MA+3*κ)/log (Nat.card K))
    (hv : (d:ℝ)+1-r < (d:ℝ)+1-(log MB+3*κ)/log (Nat.card K))
    (hconsistent : ∀ z,p.mass z≠0 →
      z.1.1.rep z.2.2.rep=0 → z.2.1.rep z.1.2.rep=0) :
    (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay =>
      goodFirst p.fst MA ((d:ℝ)*log (Nat.card K)) κ ε ay.1 ∧
      goodSecond p.snd MB ((d:ℝ)*log (Nat.card K)) κ ε ay.2 ∧
      ay.1.rep ay.2.rep=0))≤2*mutualInfo p/ρ^2 := by
  apply reciprocal_open_incidence p Projectivization.rep Projectivization.rep hρ _ _
    (r:=r) (s:=d+2-r) (by omega) _ _ hconsistent
  · intro a ha
    exact round_core_rank hu (goodFirst_core_dimension p.fst MA κ ρ ε d a hMA hρ.le ha hγ hκ)
  · intro y hy
    have hh := goodSecond_core_dimension p.snd MB κ ρ ε d y hMB hρ.le hy
      (by simpa only [Subspace.dual_finrank_eq] using hγ)
      (by simpa only [Subspace.dual_finrank_eq] using hκ)
    apply round_core_rank (x:=(d:ℝ)+1-(log MB+3*κ)/log (Nat.card K)) _ hh
    have hc : ((d+2-r:ℕ):ℝ)=(d:ℝ)+2-r := by
      rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_ofNat]
    rw [hc]
    linarith

theorem projective_integer_ranks
    (p q : Law (Projectivization K (Module.Dual K V)×Projectivization K V))
    (MA MB κ ρ ε : ℝ) (d r : ℕ) (hMA : 0<MA) (hMB : 0<MB) (hρ : 0≤ρ)
    (hr : r≤d+1)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ)
    (hu : (r:ℝ)-1 < (d:ℝ)+1-(log MA+3*κ)/log (Nat.card K))
    (hv : (d:ℝ)-r < (d:ℝ)+1-(log MB+3*κ)/log (Nat.card K))
    (a : Projectivization K (Module.Dual K V)) (y : Projectivization K V)
    (ha : goodFirst p MA ((d:ℝ)*log (Nat.card K)) κ ε a)
    (hy : goodSecond q MB ((d:ℝ)*log (Nat.card K)) κ ε y) :
    r≤Module.finrank K (firstCore (K:=K) p Projectivization.rep ρ a) ∧
    d+1-r≤Module.finrank K (secondCore q Projectivization.rep ρ y) := by
  constructor
  · exact round_core_rank hu (goodFirst_core_dimension p MA κ ρ ε d a hMA hρ ha hγ hκ)
  · have hh := goodSecond_core_dimension q MB κ ρ ε d y hMB hρ hy
      (by simpa only [Subspace.dual_finrank_eq] using hγ)
      (by simpa only [Subspace.dual_finrank_eq] using hκ)
    apply round_core_rank (x:=(d:ℝ)+1-(log MB+3*κ)/log (Nat.card K)) _ hh
    have hc : ((d+1-r:ℕ):ℝ)=(d:ℝ)+1-r := by
      rw [Nat.cast_sub hr,Nat.cast_add,Nat.cast_one]
    rw [hc]
    linarith

end
end SharpLogRamsey.Selection

end

end OAI
