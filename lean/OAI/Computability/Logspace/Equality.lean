import OAI.Computability.Logspace.Amplification
import OAI.Computability.Logspace.UniformEstimator

namespace OAI

/-!
A fixed-precision deterministic estimator and the equality L = RL = BPL.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Umbra
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Night Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Vessel Gamut
noncomputable section
open scoped Classical
variable {q w h:ℕ}
open Elect

namespace Scope.Sane

lemma shard (t:ℝ)(z:ℤ)(hp:in01 t)(hz:|(z:ℝ) - (2:ℝ)^6*t|≤2):
    |((min 64 z.toNat:ℕ):ℝ)/64-t|≤1/32:=by
      have h:=abs_le.1 hz; obtain ⟨h1,h2⟩:=hp
      have he:(2:ℝ)^6=64:=by norm_num
      rw [he] at h
      apply abs_le.2
      by_cases hc : z<0
      · have hh:(z:ℝ)<0:=by exact_mod_cast hc
        have hm:z.toNat=0:=by omega
        rw [hm,min_eq_right (by omega),Nat.cast_zero,zero_div];constructor <;> linarith
      have hm:(z:ℝ)=(z.toNat:ℝ):=by exact_mod_cast (show z= (z.toNat:ℤ) by omega)
      by_cases hs:z.toNat<64
      · rw [min_eq_right hs.le]; constructor<;>linarith
      have hh:64 ≤ z.toNat:= le_of_not_gt hs
      have hh':(64:ℝ) ≤ z.toNat:=by exact_mod_cast hh
      rw [min_eq_left hh]
      push_cast; constructor<;>linarith

lemma plump (r:Rock q w h) (x:Word) (s: Pool (r.n x)) :
      let m:=r.matter0 x
      in01 (m.oracleV s m.i):=by
      intro m
      let u:= m.view
      unfold Matter.oracleV forecast current;dsimp only
      split
      · unfold Peek.activeV; unfold Axis.color
        split;exact unit_mem _; exact ⟨le_rfl,by norm_num⟩
      exact ⟨le_rfl,by norm_num⟩

theorem delivered (r:Rock q w h)(p:MintV)(v:Tags){k:ℕ} (hs:Sane r p v k)(hS:r.P.Space):
   ∃ f:PT ℕ ℕ, Kn f ∧ ∀ (x:Word) (s:Pool (r.n x)),
                        let m:=r.matter0 x
                        |r.survey f x s-m.oracleV s m.i| ≤ 1/32:=by
   obtain ⟨f,hf,h⟩:=realization (prog0 p r v)
   exact ⟨solve r v f,shake r v hf,
          fun x s=> shard _ _ (plump r x s) (hs.bells0 x s hS (show Agent f r p v from h))⟩

end Scope.Sane

/-- One deterministic estimator works for every input and every finite sampling environment,
with additive error at most `1 / 32` for the normalized oracle value. -/
theorem fixed_precision_estimator (r:Rock q w h)(e:r.w.Proof)(hp:6≤r.pad)(he:e.T.bank≤Est.box r.pad)(hS:r.P.Space):
    ∃ f:PT ℕ ℕ, Kn f ∧ ∀ (x:Word) (s:Pool (r.n x)),
                        let m:=r.matter0 x
                        |r.survey f x s-m.oracleV s m.i| ≤ 1/32:=by
    obtain ⟨p,v,k,h1,h2⟩:=Codex.enacted r 6 e
    have h: Scope.Sane r p v k:=⟨h1,h2.ge,fun x=>⟨⟨e,r.prompts e hp he x⟩,h1.coast0⟩⟩
    exact Scope.Sane.delivered r p v h hS
end
end ExactDerandomization.Umbra
namespace ExactDerandomization
open Analysis Relay Grain Hie Stage Net Umbra

/-- Every bounded-error probabilistic logspace language has a deterministic logspace decider. -/
theorem BPL_subset_L : BPL ⊆ L:=by
   classical
   intro A hA
   obtain ⟨q,w,h,M,h1,c,k,hc,hx⟩:= hA
   obtain ⟨cs,hz,hl⟩:=h1
   let P:Base.Source q w h:=⟨M,cs,c,k⟩
   obtain ⟨v,⟨p⟩⟩:= Wares.choose
   obtain ⟨m,hm⟩:= exists_nat_gt p.T.bank
   let r:Rock q w h:= ⟨P,v,max m 6⟩
   have he:6≤r.pad:=le_max_right ..
   have hr:p.T.bank ≤ Est.box r.pad:=by
      have hh:m ≤ r.pad:=le_max_left ..
      have hp : (r.pad:ℝ) ≤ Est.box r.pad :=by have := Est.box_big r.pad;linarith
      refine (hm.trans_le (le_trans ?_ hp)).le; exact_mod_cast hh
   have ht:r.P.Space:=hl
   obtain ⟨f,hf,hQ⟩:= fixed_precision_estimator r p he hr ht
   apply r.convince ht p he hr f hf (fun x s _=> hQ x s)
   · intro x; exact (hx x).2.1
   intro x; exact (hx x).2.2

/-- Deterministic, one-sided randomized, and two-sided randomized logarithmic space coincide. -/
theorem exact_logarithmic_space_derandomization :
     L=RL ∧ RL=BPL:=by
   have ht:= RL_subset_BPL.trans BPL_subset_L
   exact ⟨Set.Subset.antisymm L_subset_RL ht,
                           Set.Subset.antisymm RL_subset_BPL (BPL_subset_L.trans L_subset_RL)⟩

end ExactDerandomization

end

end OAI
