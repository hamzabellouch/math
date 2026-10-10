import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.EndpointScales

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section

lemma Law.map_image_support {A B : Type*} [Fintype A] [Fintype B]
    (p : Law A) (S : Finset A) (f : A→B)
    (hS : ∀ a,a∉S→p.mass a=0) :
    ∀ b,b∉S.image f→(p.map f).mass b=0 := by
  intro b hb
  by_contra he
  obtain ⟨a,ha,rfl⟩:=p.map_support f b he
  exact hb (mem_image.mpr ⟨a,by by_contra h; exact ha (hS a h),rfl⟩)

lemma reciprocal_source_scales {σ β D : ℝ} (hσ : 0<σ) (hD : σ^β≤D) :
    σ^(4*β)≤D*σ^(3*β) ∧ D*σ^β≤(D*σ^(3*β))*σ^(-2*β) := by
  constructor
  · calc
      _ = σ^β*σ^(3*β) := by rw [←rpow_add hσ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (rpow_nonneg hσ.le _)
  · rw [mul_assoc,←rpow_add hσ,show 3*β+-2*β=β by ring]

theorem eventually_actual_reciprocal (n : ℕ) (β : ℝ) (hβ : 0<β) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (Projectivization K V)]
      [Fintype (Projectivization K (Module.Dual K V))],
      Module.finrank K V=n+3 → log (Nat.card K)=σ →
      ∀ (p : Law (Projectivization K (Module.Dual K V)×Projectivization K V))
        (S : Finset (Projectivization K (Module.Dual K V)×Projectivization K V)) (D u : ℝ),
        (∀ a,a∉S→p.mass a=0) →
        (∀ a,0<p.mass a→a.1.rep a.2.rep=0) →
        ((S.image Prod.fst).card:ℝ)≤1024*exp (((n+3:ℕ):ℝ)*σ-u) →
        ((S.image Prod.snd).card:ℝ)≤1024*exp u →
        (S.card:ℝ)≤64*(Nat.card K:ℝ)^(n+2) → σ^β≤D →
        ((n+2:ℕ):ℝ)*σ-entropy p≤D*σ^β →
        let MA:=1024*exp (((n+3:ℕ):ℝ)*σ-u)
        let MB:=1024*exp u
        let L:=((n+2:ℕ):ℝ)*σ
        let κ:=D*σ^(3*β)
        Nonempty (AuxiliarySupport p.fst (univ.filter (goodFirst p MA L κ (1/50))) MA κ) ∧
        Nonempty (AuxiliarySupport p.snd (univ.filter (goodSecond p MB L κ (1/50))) MB κ) ∧
        p.fst.event (univ.filter (fun a=>¬goodFirst p MA L κ (1/50) a))≤3251*σ^(-2*β) ∧
        p.snd.event (univ.filter (fun b=>¬goodSecond p MB L κ (1/50) b))≤3251*σ^(-2*β) := by
  filter_upwards [eventually_reciprocal_auxiliary_choices n β (1024^2) 64 hβ
      (by norm_num) (by norm_num),eventually_ge_atTop (1:ℝ)] with σ he hσ
  intro K V _ _ _ _ _ _ _ hdim hlog p S D u hs hf hA hB hS hD hdef
  have hσ0 : 0<σ := by linarith
  have hq : (0:ℝ)<Nat.card K := by
    exact_mod_cast (show 0<Nat.card K from Nat.zero_lt_one.trans Finite.one_lt_card)
  have hA0 : 0<1024*exp (((n+3:ℕ):ℝ)*σ-u) := by positivity
  have hB0 : 0<1024*exp u := by positivity
  have ha := p.map_image_support S Prod.fst hs
  have hb := p.map_image_support S Prod.snd hs
  rw [Law.map_fst] at ha
  rw [Law.map_snd] at hb
  have hcap : (1024*exp (((n+3:ℕ):ℝ)*σ-u))*(1024*exp u)≤
      1024^2*(Nat.card K:ℝ)^(n+3) := by
    rw [show (1024*exp (((n+3:ℕ):ℝ)*σ-u))*(1024*exp u)=
      1024^2*exp (((n+3:ℕ):ℝ)*σ) by rw [show ((n+3:ℕ):ℝ)*σ=(((n+3:ℕ):ℝ)*σ-u)+u by ring,exp_add]; ring_nf]
    rw [←hlog,exp_nat_mul,exp_log hq]
  have hsc:=reciprocal_source_scales hσ0 hD
  have hch:=he K V hdim hlog p S (S.image Prod.fst) (S.image Prod.snd) _ _ _ _
    hs hf ha hb hA0 hB0 hA hB hcap hS hsc.1 hsc.2 hdef
  have hp : (S.card:ℝ)*exp (-(((n+2:ℕ):ℝ)*σ))≤64 := by
    have hh:=mul_le_mul_of_nonneg_right hS (le_of_lt (exp_pos (-(((n+2:ℕ):ℝ)*σ))))
    have hn : exp (((n+2:ℕ):ℝ)*σ)=(Nat.card K:ℝ)^(n+2) := by
      rw [←hlog,exp_nat_mul,exp_log hq]
    rw [←hn,mul_assoc,←exp_add,add_neg_cancel,exp_zero,mul_one] at hh
    exact hh
  have herr:=actual_endpoint_errors p S (S.image Prod.fst) (S.image Prod.snd) hs ha hb
    _ _ _ _ σ β (D*σ^β) 64 hA0 hB0 hA hB hσ hβ.le (by norm_num) hsc.1 hsc.2 hdef hp
  exact ⟨hch.1,hch.2,by norm_num only at herr ⊢; exact herr⟩

end
end SharpLogRamsey.Selection

end

end OAI
