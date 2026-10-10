import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.EndpointSupports

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype ι] [DecidableEq ι]

omit [Finite K] [FiniteDimensional K V] in
lemma directedCollision_le_reciprocal
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (ρ : ℝ) (r s : ℕ) (i j : ι) :
    (directedCollision p Projectivization.rep Projectivization.rep ρ r s i j : ℝ) ≤
      (reciprocalCharges p Projectivization.rep Projectivization.rep ρ r s i j : ℝ) := by
  unfold reciprocalCharges
  exact_mod_cast (le_add_right (le_refl _) :
    directedCollision p Projectivization.rep Projectivization.rep ρ r s i j ≤ _)

theorem integer_good_event_le
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (MA MB κ ρ ε c a : ℝ) (d r : ℕ)
    (hMA : 0<MA) (hMB : 0<MB) (hρ : 0<ρ) (hc : 0<c)
    (hcap : c≤1-(Module.finrank K V:ℝ)*ρ) (hr : r≤d+1)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ)
    (hu : (r:ℝ)-1 < (d:ℝ)+1-(log MA+3*κ)/log (Nat.card K))
    (hv : (d:ℝ)-r < (d:ℝ)+1-(log MB+3*κ)/log (Nat.card K))
    (hconsistent : ∀ x,p.mass x≠0 →
      (x i).1.rep (x j).2.rep=0 → (x j).1.rep (x i).2.rep=0)
    (hcharge : (pairInformation p i j:ℝ)+
      (reciprocalCharges p Projectivization.rep Projectivization.rep ρ r (d+1-r) i j:ℝ)≤a) :
    ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay =>
      goodFirst (p.marginal i) MA ((d:ℝ)*log (Nat.card K)) κ ε ay.1 ∧
      goodSecond (p.marginal j) MB ((d:ℝ)*log (Nat.card K)) κ ε ay.2 ∧
      ay.1.rep ay.2.rep=0)) ≤ 2*a/ρ^2 + 2*a/c^2 := by
  apply (projective_integer_incidence p i j MA MB κ ρ ε c d r
    hMA hMB hρ hc hcap hr hγ hκ hu hv hconsistent).trans
  have hdir := directedCollision_le_reciprocal p ρ r (d+1-r) i j
  have hn : (0:ℝ)≤(reciprocalCharges p Projectivization.rep Projectivization.rep
      ρ r (d+1-r) i j:ℝ) := NNReal.coe_nonneg _
  apply add_le_add <;> apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  · linarith only [hcharge, hn]
  · linarith only [hcharge, hdir]

theorem open_good_event_le
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (MA MB κ ρ ε a : ℝ) (d r : ℕ)
    (hMA : 0<MA) (hMB : 0<MB) (hρ : 0<ρ)
    (hd : Module.finrank K V=d+1) (hr : r≤d+1)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ)
    (hu : (r:ℝ)-1 < (d:ℝ)+1-(log MA+3*κ)/log (Nat.card K))
    (hv : (d:ℝ)+1-r < (d:ℝ)+1-(log MB+3*κ)/log (Nat.card K))
    (hconsistent : ∀ x,p.mass x≠0 →
      (x i).1.rep (x j).2.rep=0 → (x j).1.rep (x i).2.rep=0)
    (hinfo : (pairInformation p i j:ℝ)≤a) :
    ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay =>
      goodFirst (p.marginal i) MA ((d:ℝ)*log (Nat.card K)) κ ε ay.1 ∧
      goodSecond (p.marginal j) MB ((d:ℝ)*log (Nat.card K)) κ ε ay.2 ∧
      ay.1.rep ay.2.rep=0)) ≤ 2*a/ρ^2 := by
  let p₂ := p.map (fun x => (x i,x j))
  have hi : p₂.fst=p.marginal i := by
    exact (Law.map_fst p₂).symm.trans (p.map_map (fun x => (x i,x j)) Prod.fst)
  have hj : p₂.snd=p.marginal j := by
    exact (Law.map_snd p₂).symm.trans (p.map_map (fun x => (x i,x j)) Prod.snd)
  have hcon : ∀ z,p₂.mass z≠0 →
      z.1.1.rep z.2.2.rep=0 → z.2.1.rep z.1.2.rep=0 := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := p.map_support (fun x => (x i,x j)) z hz
    exact hconsistent x hx
  have h := projective_open_incidence p₂ MA MB κ ρ ε d r hMA hMB hρ
    hd hr hγ hκ hu hv hcon
  rw [hi,hj] at h
  apply h.trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinfo (by norm_num))
    (sq_nonneg ρ)

omit [Finite K] [FiniteDimensional K V] in
theorem auxiliary_three_estimates
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (MA MB L κ ε z : ℝ)
    (A : AuxiliarySupport (p.marginal i).fst
      (univ.filter (goodFirst (p.marginal i) MA L κ ε)) MA κ)
    (B : AuxiliarySupport (p.marginal j).snd
      (univ.filter (goodSecond (p.marginal j) MB L κ ε)) MB κ)
    (hz : ((p.marginal i).fst.prod (p.marginal j).snd).event
      (univ.filter (fun ay => goodFirst (p.marginal i) MA L κ ε ay.1 ∧
        goodSecond (p.marginal j) MB L κ ε ay.2 ∧ ay.1.rep ay.2.rep=0)) ≤ z) :
    let SA := fun b => levelSet (p.marginal i).fst b ∩
      univ.filter (goodFirst (p.marginal i) MA L κ ε)
    let SB := fun b => levelSet (p.marginal j).snd b ∩
      univ.filter (goodSecond (p.marginal j) MB L κ ε)
    (∑ a, ∑ b, A.law.mass a * B.law.mass b *
      ((((SA a ×ˢ SB b).filter (fun ay => ay.1.rep ay.2.rep=0)).card:ℝ) /
        ((SA a).card * (SB b).card))) ≤ (4*exp 1)^2*z ∧
    (∑ a, A.law.mass a * SupportMixtures.pairing (SupportMixtures.kernel (SA a))
      (fun y => if goodSecond (p.marginal j) MB L κ ε y then (p.marginal j).snd.mass y else 0)
      (fun x y => if x.rep y.rep=0 then 1 else 0)) ≤ (4*exp 1)*z ∧
    (∑ b, B.law.mass b * SupportMixtures.pairing
      (fun x => if goodFirst (p.marginal i) MA L κ ε x then (p.marginal i).fst.mass x else 0)
      (SupportMixtures.kernel (SB b))
      (fun x y => if x.rep y.rep=0 then 1 else 0)) ≤ (4*exp 1)*z := by
  dsimp only
  have h₂ := actual_auxiliary_incidence (p.marginal i).fst (p.marginal j).snd
    (univ.filter (goodFirst (p.marginal i) MA L κ ε))
    (univ.filter (goodSecond (p.marginal j) MB L κ ε)) MA MB κ
    A.law B.law A.density B.density (fun x y => x.rep y.rep=0)
  have h₁A := actual_auxiliary_target_left (p.marginal i).fst (p.marginal j).snd
    (univ.filter (goodFirst (p.marginal i) MA L κ ε))
    (univ.filter (goodSecond (p.marginal j) MB L κ ε)) MA κ
    A.law A.density (fun x y => x.rep y.rep=0)
  have h₁B := actual_auxiliary_target_right (p.marginal i).fst (p.marginal j).snd
    (univ.filter (goodFirst (p.marginal i) MA L κ ε))
    (univ.filter (goodSecond (p.marginal j) MB L κ ε)) MB κ
    B.law B.density (fun x y => x.rep y.rep=0)
  simp only [mem_filter, mem_univ, true_and] at h₂ h₁A h₁B
  exact ⟨h₂.trans (mul_le_mul_of_nonneg_left hz (sq_nonneg _)),
    h₁A.trans (mul_le_mul_of_nonneg_left hz (by positivity)),
    h₁B.trans (mul_le_mul_of_nonneg_left hz (by positivity))⟩

end
end SharpLogRamsey.Selection

end

end OAI
