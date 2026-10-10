import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.GeometricCover

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Incidence Projection PublicFamilies
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]

def HeaderOK (q b : ℝ) (r N T Z W Udual a c : ℕ) : Prop :=
  0<a ∧ 0<c ∧ a≤Z ∧ c≤W ∧
  (9/10:ℝ)*N≤a ∧ (T:ℝ)/(3*q)≤c ∧
  q^(r+3)*exp (-(b+log 4))≤(a:ℝ)*c ∧ (a:ℝ)*c≤2*q^(r+3) ∧
  (W:ℝ)≤100*Udual/q

theorem quotient_header_library (r : ℕ)
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V)))
    (N T : ℕ) (b τ P H : ℝ) (hN : 0<N) (hT : 0<T)
    (hNU : N≤U.card) (hTU : T≤UT.card) (hP : 300≤P) (hH : 0≤H)
    (z : Projectivization K V)
    (low : ∀ a c,HeaderOK (Nat.card K) b r N T
      (projected U z).card (quotientCut UT z).card UT.card a c →
      Validated (Nat.card K) P H (r+3) (projected U z) (quotientCut UT z) a c (400*τ)) :
    ∃ F : Finset (Finset (Projectivization K (V ⧸ z.submodule))),
      (∀ W∈F,W⊆projected U z ∧ (W.card:ℝ)≤300000*(Nat.card K:ℝ)^(r+4)/T) ∧
      (∀ S T',S⊆projected U z → T'⊆quotientCut UT z →
        HeaderOK (Nat.card K) b r N T
          (projected U z).card (quotientCut UT z).card UT.card S.card T'.card →
        (incidenceCount S T':ℝ)≤400*τ*S.card*T'.card/Nat.card K →
        ∃ W∈F,(99/100:ℝ)*S.card≤(S∩W).card) ∧
      log ((F.card:ℝ)+1)≤log ((((U.card+1)*(UT.card+1):ℕ):ℝ)+1)+
        2*H*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P) := by
  let q : ℝ := Nat.card K
  have hq : 0<q := by dsimp only [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have ht : (0:ℝ)<T := by exact_mod_cast hT
  let d := log ((U.card:ℝ)/N)
  let e := log ((UT.card:ℝ)/T)
  have hd : 0≤d := log_nonneg ((le_div_iff₀ hn).mpr
    (by simpa only [one_mul] using (show (N:ℝ)≤U.card by exact_mod_cast hNU)))
  have he : 0≤e := log_nonneg ((le_div_iff₀ ht).mpr
    (by simpa only [one_mul] using (show (T:ℝ)≤UT.card by exact_mod_cast hTU)))
  let L := 2*H*q*P*(d+e+P)
  have hL : 0≤L := by dsimp only [L]; positivity
  let Good := HeaderOK q b r N T (projected U z).card (quotientCut UT z).card UT.card
  let Size := fun W : Finset (Projectivization K (V ⧸ z.submodule)) =>
    W⊆projected U z ∧ (W.card:ℝ)≤300000*q^(r+4)/T
  let Eligible := fun (S : Finset (Projectivization K (V ⧸ z.submodule)))
    (T' : Finset (Projectivization K (Module.Dual K (V ⧸ z.submodule)))) =>
    S⊆projected U z ∧ T'⊆quotientCut UT z ∧
      (incidenceCount S T':ℝ)≤400*τ*S.card*T'.card/q
  let Capture := fun S W : Finset (Projectivization K (V ⧸ z.submodule)) =>
    (99/100:ℝ)*S.card≤(S∩W).card
  have hex : ∀ a≤U.card,∀ c≤UT.card,Good a c → ∃ F : Finset (Finset (Projectivization K (V ⧸ z.submodule))),
      (∀ W∈F,Size W) ∧
      (∀ S T',S.card=a → T'.card=c → Eligible S T' → ∃ W∈F,Capture S W) ∧
      log ((F.card:ℝ)+1)≤L := by
    intro a ha c hc hg
    obtain ⟨F,hFs,hFc,hFl⟩ := low a c hg
    obtain ⟨hapos,hcpos,haZ,hcW,hNa,hTc,_hlo,_hhi,hcut⟩ := hg
    have ha' : (0:ℝ)<a := by exact_mod_cast hapos
    have hc' : (0:ℝ)<c := by exact_mod_cast hcpos
    refine ⟨F,?_,?_,?_⟩
    · intro W hW
      refine ⟨(hFs W hW).1,(hFs W hW).2.trans ?_⟩
      apply (div_le_div_iff₀ hc' ht).mpr
      have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ (by positivity : 0<3*q)).mp hTc)
        (show 0≤100000*q^(r+3) by positivity)
      dsimp only [q] at hh ⊢
      rw [show r+4=(r+3)+1 by omega,pow_succ]
      convert hh using 1 <;> ring
    · intro S T' hSa hT'c hh
      obtain ⟨hS,hT',hsp⟩ := hh
      have hsp' : (incidenceCount S T':ℝ)≤(400*τ)*(a:ℝ)*c/Nat.card K := by
        simpa only [hSa,hT'c] using hsp
      obtain ⟨W,hW,hcap⟩ := hFc S T' hS hSa hT' hT'c hsp'
      exact ⟨W,hW,by simpa only [Capture,hSa] using hcap⟩
    · have hgaps := quotient_gap_bounds hq hn ht ha' hc' hNa hTc
        (show (a:ℝ)≤(projected U z).card by exact_mod_cast haZ)
        (show (c:ℝ)≤(quotientCut UT z).card by exact_mod_cast hcW)
        (show ((projected U z).card:ℝ)≤U.card by exact_mod_cast projected_card_le U z) hcut
      have hh : log (((projected U z).card:ℝ)/a)+
          log (((quotientCut UT z).card:ℝ)/c)+P≤2*(d+e+P) := by
        dsimp only [d,e] at *
        linarith only [hgaps.1,hgaps.2,hP,hd,he]
      have hm := mul_le_mul_of_nonneg_left hh (show 0≤H*q*P by positivity)
      apply hFl.trans
      convert hm using 1; dsimp only [L,d,e,q]; ring
  obtain ⟨F,hFs,hFc,hFl⟩ := size_header_library U.card UT.card Good Size Eligible Capture L hL hex
  refine ⟨F,hFs,?_,hFl⟩
  intro S T' hS hT' hg hsp
  apply hFc S T'
  · exact (card_le_card hS).trans (projected_card_le U z)
  · apply (card_le_card hT').trans
    rw [quotientCut_card]
    exact card_filter_le _ _
  · exact hg
  · exact ⟨hS,hT',hsp⟩

end
end SharpLogRamsey.GeometricCover

end

end OAI
