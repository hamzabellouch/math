import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.QuotientHeader
import OAI.Combinatorics.SharpRamsey.Geometry.ProjectionMessageCost

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Incidence Projection PublicFamilies CapComposition Validation
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedProjectionFullDescription_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedProjectionFullDescription_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedProjectionFullDescription_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

theorem projection_description (i : ℕ) (hdim : Module.finrank K V=i+5)
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V)))
    (N T : ℕ) (b τ P H : ℝ) (hN : 100≤N) (hT : 0<T)
    (hNU : N≤U.card) (hTU : T≤UT.card) (hP : 300≤P) (hH : 0≤H)
    (hτ : 0<τ) (hτsmall : τ≤1/8000)
    (hsmall : (N:ℝ)≤(Nat.card K:ℝ)^(i+3)/100000)
    (hlarge : 1000000*(Nat.card K:ℝ)≤T)
    (hprod : (Nat.card K:ℝ)^(i+5)*exp (-b)≤(N:ℝ)*T)
    (hhalf : sqrt (100*(300000*(Nat.card K:ℝ)^(i+5)/T)/(Nat.card K:ℝ)^(i+3))≤1/2)
    (hpow : (Nat.card K:ℝ)*(sqrt (100*(300000*(Nat.card K:ℝ)^(i+5)/T)/
      (Nat.card K:ℝ)^(i+3)))^7≤1)
    (low : ∀ (z : Projectivization K V) a c,
      HeaderOK (Nat.card K) b (i+1) N T
        (projected U z).card (quotientCut UT z).card UT.card a c →
      Validated (Nat.card K) P H (i+4) (projected U z) (quotientCut UT z) a c (400*τ)) :
    ∃ F : Finset (Finset (Projectivization K V)),
      (∀ W∈F,W⊆U ∧ (W.card:ℝ)≤900000*(Nat.card K:ℝ)^(i+5)/T) ∧
      (∀ S T',S⊆U → S.card=N → T'⊆UT → T'.card=T →
        (incidenceCount S T':ℝ)≤τ*(N:ℝ)*T/Nat.card K →
        ∃ W∈F,(N:ℝ)/2≤(S∩W).card) ∧
      log ((F.card:ℝ)+1)≤(16*H+24*(i:ℝ)+200)*(Nat.card K:ℝ)*P*
        (log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P) := by
  let q : ℝ := Nat.card K
  have hq : (1:ℝ)≤q := by dsimp only [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have ht : (0:ℝ)<T := by exact_mod_cast hT
  let d := log ((U.card:ℝ)/N)
  let e := log ((UT.card:ℝ)/T)
  have hd : 0≤d := log_nonneg ((le_div_iff₀ hn).mpr
    (by simpa only [one_mul] using (show (N:ℝ)≤U.card by exact_mod_cast hNU)))
  have he : 0≤e := log_nonneg ((le_div_iff₀ ht).mpr
    (by simpa only [one_mul] using (show (T:ℝ)≤UT.card by exact_mod_cast hTU)))
  let Z := q*P*(d+e+P)
  have hZq : q≤Z := by
    have hh : 1≤P*(d+e+P) := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have hm := mul_le_mul_of_nonneg_left hh hq0.le
    simpa only [mul_one,mul_assoc,Z] using hm
  have hZ : 0≤Z := hq0.le.trans hZq
  let L := log ((((U.card+1)*(UT.card+1):ℕ):ℝ)+1)+2*H*Z
  have hL : 0≤L := add_nonneg (log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _))) (by positivity)
  have hf : ∀ z : Projectivization K V,∃ F : Finset (Finset (Projectivization K (V ⧸ z.submodule))),
      (∀ W∈F,W⊆projected U z ∧ (W.card:ℝ)≤300000*q^(i+5)/T) ∧
      (∀ S T',S⊆projected U z → T'⊆quotientCut UT z →
        HeaderOK q b (i+1) N T (projected U z).card (quotientCut UT z).card UT.card S.card T'.card →
        (incidenceCount S T':ℝ)≤400*τ*S.card*T'.card/q →
        ∃ W∈F,(99/100:ℝ)*S.card≤(S∩W).card) ∧ log ((F.card:ℝ)+1)≤L := by
    intro z
    obtain ⟨F,hFs,hFc,hFl⟩ := quotient_header_library (i+1) U UT N T b τ P H (by omega) hT hNU hTU hP hH z
      (by intro a c hg; simpa only [show i+1+3=i+4 by omega] using low z a c hg)
    refine ⟨F,?_,hFc,?_⟩
    · simpa only [show i+1+4=i+5 by omega] using hFs
    · simpa only [L,Z,d,e,q,mul_assoc] using hFl
  choose F hF using hf
  let M : ℕ := ⌈exp L⌉₊
  have hM : ∀ z,(F z).card≤M := fun z => card_le_ceil_exp _ L (hF z).2.2
  let m := 300000*q^(i+5)/T
  let A := powers (liftedLibrary U F) U 8
  let caps := A.filter (fun W => W⊆U ∧ (W.card:ℝ)≤3*m)
  have hAc : A.card≤(Fintype.card (Projectivization K V)*M)^8 :=
    (powers_card _ _ _).trans (Nat.pow_le_pow_left (liftedLibrary_card U F M hM) 8)
  refine ⟨caps,?_,?_,?_⟩
  · intro W hW
    have hh := (mem_filter.mp hW).2
    refine ⟨hh.1,?_⟩
    convert hh.2 using 1 ; dsimp only [m,q] ; ring
  · intro S T' hSU hSn hT'U hTt hsp
    have hcover : ∀ z,
      (9/10:ℝ)*S.card≤(projected S z).card →
      (T'.card:ℝ)/(3*Nat.card K)≤(quotientCut T' z).card →
      ((quotientCut T' z).card:ℝ)≤2*T'.card/Nat.card K →
      ((quotientCut UT z).card:ℝ)≤100*UT.card/Nat.card K →
      (S.card:ℝ)*T'.card/(4*Nat.card K)≤(projected S z).card*(quotientCut T' z).card →
      (incidenceCount (projected S z) (quotientCut T' z):ℝ)≤
        400*τ*(projected S z).card*(quotientCut T' z).card/Nat.card K →
      ∃ W∈F z,(99/100:ℝ)*(projected S z).card≤(projected S z∩W).card := by
      intro z h90 hlo _hhi hcut hpr hqs
      apply (hF z).2.1 _ _ (projected_mono hSU z) (quotientCut_mono hT'U z)
      · have ha : 0<(projected S z).card := by
          have hh : (0:ℝ)<(projected S z).card := by rw [hSn] at h90; nlinarith
          exact_mod_cast hh
        have hc : 0<(quotientCut T' z).card := by
          have hh : (0:ℝ)<(quotientCut T' z).card :=
            (by rw [hTt]; positivity : (0:ℝ)<(T'.card:ℝ)/(3*Nat.card K)).trans_le hlo
          exact_mod_cast hh
        refine ⟨ha,hc,card_le_card (projected_mono hSU z),card_le_card (quotientCut_mono hT'U z),
          by simpa only [hSn] using h90,by simpa only [hTt] using hlo,?_,?_,hcut⟩
        · have hh := div_le_div_of_nonneg_right hprod (show 0≤4*q by positivity)
          have heq := quotient_product hq0 (i+1) (b:=b)
          rw [show i+1+3=i+4 by omega,show i+1+4=i+5 by omega] at heq
          rw [←heq] at hh
          apply hh.trans
          simpa only [hSn,hTt,show i+1+3=i+4 by omega] using hpr
        · let : Finite (V ⧸ z.submodule) := Module.finite_of_finite K
          let : Fintype (Projectivization K (V ⧸ z.submodule)) := Fintype.ofFinite _
          let : Finite (Module.Dual K (V ⧸ z.submodule)) := Module.finite_of_finite K
          let : Fintype (Projectivization K (Module.Dual K (V ⧸ z.submodule))) := Fintype.ofFinite _
          have hdimq : Module.finrank K (V ⧸ z.submodule)=(i+1)+3 := by
            have hh := quotient_dimension z
            omega
          apply sparse_product_bound_two hdimq
          apply hqs.trans
          have hh := mul_le_mul_of_nonneg_right (show 400*τ≤1/20 by linarith)
            (show 0≤((projected S z).card:ℝ)*(quotientCut T' z).card/q by positivity)
          convert hh using 1 <;> ring
      · exact hqs
    have hdim' : Module.finrank K V=(i+2)+3 := by omega
    obtain ⟨W,hWA,hWU,hWsize,hWcap,_⟩ := eight_projection_library hdim' U S hSU UT T' hT'U τ m hτ
      (by dsimp only [m]; positivity) (by simpa only [hSn] using hN)
      (by simpa only [hSn,show i+2+1=i+3 by omega] using hsmall)
      (by simpa only [hTt] using hlarge) (by simpa only [hSn,hTt] using hsp)
      F M hM (fun z W hW => (hF z).1 W hW |>.2) hcover
      (by simpa only [m,q,show i+2+1=i+3 by omega] using hhalf)
      (by simpa only [m,q,show i+2+1=i+3 by omega] using hpow)
    exact ⟨W,mem_filter.mpr ⟨hWA,hWU,hWsize⟩,by simpa only [hSn] using hWcap⟩
  · have hh := power_pair_log (by decide : (8:ℕ)≠0) (show caps.card≤(Fintype.card (Projectivization K V)*M)^8 from (card_filter_le A (fun W => W⊆U ∧ (W.card:ℝ)≤3*m)).trans hAc)
    have hc := projective_log_card (i+5) hdim
    have hMlog := log_ceil_exp hL
    have hheader := header_log_le (i+5) hdim U UT
    simp only [Nat.cast_ofNat] at hh
    change log ((caps.card:ℝ)+1)≤_ at hh
    have hsum : log ((caps.card:ℝ)+1)≤8*(((i+5:ℕ):ℝ)+1)*q+8*L+16 := by
      dsimp only [M] at hh
      dsimp only [q] at *
      linarith
    have hLbound : L≤(2*(i:ℝ)+13)*q+2*H*Z := by
      dsimp only [L]
      dsimp only [q] at *
      push_cast at hheader ⊢
      linarith
    have hqZ := mul_le_mul_of_nonneg_left hZq (show 0≤24*(i:ℝ)+152 by positivity)
    have h1Z : 1≤Z := hq.trans hZq
    have hfinal : log ((caps.card:ℝ)+1)≤(16*H+24*(i:ℝ)+200)*Z := by
      push_cast at hsum
      nlinarith only [hsum,hLbound,hqZ,h1Z]
    simpa only [Z,q,d,e,mul_assoc] using hfinal

end
end SharpLogRamsey.GeometricCover

end

end OAI
