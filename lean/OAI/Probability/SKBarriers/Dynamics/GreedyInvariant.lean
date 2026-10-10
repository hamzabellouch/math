import Mathlib
import OAI.Probability.SKBarriers.Dynamics.GreedyStep
import OAI.Probability.SKBarriers.Dynamics.GreedyRecursion

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem greedy_marker_windows {n : ℕ} (hn : 0 < n) (μ : ProbabilityMeasure ℝ)
    (pool : ℕ → Finset (Config n)) (fallback : ℕ → Config n)
    (hf : ∀ j, fallback j ∈ pool j) (base : ℕ → Config n) (x : ℕ → Config n)
    (r : ℕ → ℝ) (B H p m : ℕ) (t ρ d b b' q : ℝ)
    (hp : 0 < p) (hB : 0 < B) (hHB : H < B) (hH : ⌈2/b^2⌉₊ ≤ H)
    (ht : 0 < t) (hρ : 0 < ρ) (hd : 0 ≤ d) (hb : 0 < b)
    (hpack : 3*t < b^2/2) (hcsmall : 3*t < b) (hEst : 6*p*ρ^20 < t)
    (hsmall' : 2*t+6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100) < b')
    (hsep' : 12*p*ρ^20+4*(n:ℝ)^(-(1:ℝ)/100) < 3*ρ)
    (hwidth : ρ^8 < t/2)
    (hsmall : 6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+d/2 < ρ^8)
    (hsep : 6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+ρ^20+3*d/2 ≤ 2*ρ)
    (hd' : d/2 ≤ ρ^20) (heta : 2*(n:ℝ)^(-(1:ℝ)/100) < 2*ρ^20)
    (hq : 2*t+6*p*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+2*ρ^20 < q)
    (hr : ∀ i < p, r i ∈ Icc t (2*t))
    (hspacing : ∀ i j, i < j → j < p → 3*ρ ≤ r j-r i)
    (hmass : ∀ i < p, (μ : Measure ℝ).real (Icc (r i-2*ρ^8) (r i+2*ρ^8)) ≤ ρ^4)
    (hjump : ∀ z k, k < m → |overlap z (x (k+1))-overlap z (x k)| ≤ d)
    (hcoverage : ∀ j < p, ∀ v : ℕ → Config n, (∀ i < j, v i ∈ pool i) →
      ∀ u ≤ m, (∀ i, j/B*B ≤ i → i < j → |overlap (v i) (x u)| ≤ 3*t) →
      ∃ w ∈ pool j, q ≤ overlap w (x u) ∧
        ∀ i, j/B*B ≤ i → i < j → |overlap (v i) w| ≤ 3*t)
    (hsigned : ∀ i j, i < j → j < p → ∀ v ∈ pool i, ∀ w ∈ pool j, ∀ k ≤ m,
      (![v,w,x k] : ReplicaConfig n 3) ∉ signedLockingSet n q b)
    (hbank : ∀ i k j, i < k → k < j → j < p → ∀ v ∈ pool i, ∀ z ∈ pool k, ∀ w ∈ pool j,
      (![z,v,w] : ReplicaConfig n 3) ∉ signedLockingSet n b b' ∧
      (![z,v,flip w] : ReplicaConfig n 3) ∉ signedLockingSet n b b')
    (hnarrow : ∀ i j, i < j → j < p → ∀ v ∈ pool i, ∀ w ∈ pool j, ∀ k ≤ m,
      (![v,x k,w] : ReplicaConfig n 3) ∉ narrowLockingSet n μ t ρ)
    (hpass : overlap (bankPick pool fallback B x t q 0 base 0) (x m) ≤ 0) :
    ∃ k ≤ m, ∀ a, a*B < p →
      |overlap (greedyReference base (bankPick pool fallback B x t q) x r b m (a*B)) (x k)-r (a*B)| ≤ 6*p*ρ^20 := by
  classical
  let pick := bankPick pool fallback B x t q
  let S := greedyRun base pick x r b m
  have hε : 0 < ρ^20 := pow_pos hρ _
  have hη : 0 ≤ 2*(n:ℝ)^(-(1:ℝ)/100) := by positivity
  have htwo : 2*t < q := by
    have hEp : 0 ≤ 6*(p:ℝ)*ρ^20 := by positivity
    linarith only [hq,hEp,hε,hη]
  have hmem (j i : ℕ) (hi : i < j) : (S j).refs i ∈ pool i := by
    rw [show (S j).refs i=greedyReference base pick x r b m i from greedyRun_refs _ _ _ _ _ _ _ _ hi]
    exact bankPick_mem pool fallback hf B x t q i _ _
  have hfirst := bankPick_spec pool fallback B x t q 0 base 0
    (hcoverage 0 hp base (by intros; omega) 0 (by omega) (by intros; omega))
  have hanchor (j : ℕ) (hj : 0 < j) : q ≤ overlap ((S j).refs 0) (x 0) := by
    rw [show (S j).refs 0=greedyReference base pick x r b m 0 from greedyRun_refs _ _ _ _ _ _ _ _ hj]
    exact hfirst.1
  have HI : ∀ j ≤ p, (S j).time ≤ m ∧ BlockProtected B j (S j).kept ∧
      (∀ i ∈ (S j).kept, |overlap ((S j).refs i) (x (S j).time)-r i| ≤ 6*j*ρ^20) ∧
      (∀ i ∈ (S j).kept, ∀ k ∈ (S j).kept, i < k →
        |overlap ((S j).refs i) ((S j).refs k)-r i| ≤ 6*j*ρ^20) := by
    intro j hjp
    induction j with
    | zero => simp [S,greedyRun,BlockProtected]
    | succ j ih =>
      have hjp' : j < p := by omega
      obtain ⟨hτ,hblock,hpath,hpair⟩ := ih (by omega)
      have hEr : 6*(j:ℝ)*ρ^20 ≤ 6*p*ρ^20 := by gcongr
      have hA := greedyRun_range base pick x r b m j
      have hcand := hcoverage j hjp' (S j).refs (hmem j) (S j).time hτ (by
        intro i hil hij
        have hlo : (j-1)/B*B ≤ j/B*B := Nat.mul_le_mul_right B (Nat.div_le_div_right (Nat.sub_le j 1))
        have himem := hblock.1 i (hlo.trans hil) hij
        have hh := hpath i himem
        have hri := hr i (hij.trans hjp')
        have hh' := abs_add_le (overlap ((S j).refs i) (x (S j).time)-r i) (r i)
        rw [sub_add_cancel,abs_of_pos (ht.trans_le hri.1)] at hh'
        linarith only [hh',hh,hri.2,hEr,hEst])
      have hsel := bankPick_spec pool fallback B x t q j (S j).refs (S j).time hcand
      let w := pick j (S j).refs (S j).time
      have hw : w ∈ pool j := bankPick_mem pool fallback hf B x t q j _ _
      by_cases hj0 : j=0
      · subst j
        have hband := firstCrossing_band (fun k => overlap w (x k)) (r 0) d m
          (by change r 0 < overlap (bankPick pool fallback B x t q 0 base 0) (x 0); linarith only [hfirst.1,(hr 0 hp).2,htwo])
          (by change overlap (bankPick pool fallback B x t q 0 base 0) (x m) ≤ r 0; linarith only [hpass,(hr 0 hp).1,ht])
          (hjump w)
        dsimp [w, S, greedyRun] at hband
        change _ ≤ m ∧ _ ∧ _ ∧ _
        simp only [S,greedyRun,zero_add,Nat.cast_one,mul_one]
        simp only [Finset.empty_sdiff,Finset.insert_empty,Finset.mem_singleton,ite_true]
        refine ⟨hband.1,?_,?_,?_⟩
        · constructor
          · intro i _ hi
            have : i=0 := by omega
            simpa only [Finset.mem_singleton] using this
          · intro k hk
            have : k*B=0 := by omega
            simpa only [Finset.mem_singleton] using this
        · intro i hi
          subst i
          simp only [Function.update_self]
          rw [abs_le]
          constructor <;> linarith only [hband.2.1,hband.2.2,hd',hε]
        · intro i hi k hk hik
          omega
      · have hj : 0 < j := Nat.pos_of_ne_zero hj0
        have Hstep := greedy_locking_step hn μ (S j).refs w x (S j).kept r B H j (S j).time
          t ρ (6*j*ρ^20) d b b' q hj hB hHB hH ht hρ (by positivity) hd hb hpack hcsmall
          (hEr.trans_lt hEst) (by linarith only [hsmall',hEr]) (by linarith only [hsep',hEr]) hwidth
          (by linarith only [hsmall,hEr]) (by linarith only [hsep,hEr]) hd' heta
          (by linarith only [hq,hEr]) (fun i hi => hr i (hi.trans_lt hjp'))
          (fun i k hik hk => hspacing i k hik (hk.trans_lt hjp')) (fun i hi => hmass i (hi.trans hjp'))
          hA hblock hpath hpair (hanchor j hj) hsel.1
          (by
            intro hmod
            apply hsel.2 (j-1) _ (by omega)
            have hh : j%B+j/B*B=j := by simpa only [Nat.mul_comm B] using Nat.mod_add_div j B
            have hpos : 0 < j%B := Nat.pos_of_ne_zero hmod
            omega)
          (fun z k hk => hjump z k (hk.trans_le hτ))
          (fun i hi => hsigned i j (hA i hi) hjp' _ (hmem j i (hA i hi)) w hw _ hτ)
          (fun i hi k hk hik => hbank i k j hik (hA k hk) hjp' _ (hmem j i (hA i hi)) _ (hmem j k (hA k hk)) w hw)
          (fun i hi k hk => hnarrow i j (hA i hi) hjp' _ (hmem j i (hA i hi)) w hw k (hk.trans hτ))
        obtain ⟨hs,hcard,hprot,hzero,htime,hband,href,hnewpath⟩ := Hstep
        have hinc : 6*(j:ℝ)*ρ^20+2*(n:ℝ)^(-(1:ℝ)/100)+2*ρ^20 ≤ 6*(j+1:ℕ)*ρ^20 := by
          simp only [Nat.cast_add,Nat.cast_one]
          nlinarith only [heta,hε]
        have hmono : 6*(j:ℝ)*ρ^20 ≤ 6*(j+1:ℕ)*ρ^20 := by
          simp only [Nat.cast_add,Nat.cast_one]; nlinarith only [hε]
        change _ ≤ m ∧ _ ∧ _ ∧ _
        simp only [S,greedyRun,ite_eq_right hj0]
        refine ⟨htime.trans hτ,hprot,?_,?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with he | hi
          · subst i
            rw [Function.update_self,abs_le]
            have hc : 2*ρ^20 ≤ 6*(j+1:ℕ)*ρ^20 := by
              have hjr : (0:ℝ) ≤ j := by positivity
              simp only [Nat.cast_add,Nat.cast_one]; nlinarith only [mul_nonneg hjr hε.le,hε]
            constructor <;> linarith only [hband.1,hband.2,hd',hc]
          · have him : i ∈ (S j).kept := (Finset.mem_sdiff.mp hi).1
            rw [Function.update_of_ne (ne_of_lt (hA i him))]
            exact (hnewpath i hi).trans hinc
        · intro i hi k hk hik
          have hil : i < j := by
            rcases Finset.mem_insert.mp hk with rfl | hk
            · exact hik
            · exact hik.trans (hA k (Finset.mem_sdiff.mp hk).1)
          have him : i ∈ (S j).kept\(S j).kept.filter (fun i => b < |overlap ((S j).refs i) w|) := by
            exact (Finset.mem_insert.mp hi).resolve_left (ne_of_lt hil)
          rw [Function.update_of_ne (ne_of_lt hil)]
          rcases Finset.mem_insert.mp hk with rfl | hk
          · rw [Function.update_self]
            exact (href i him).trans (by linarith only [hinc,hε])
          · have hkl := hA k (Finset.mem_sdiff.mp hk).1
            rw [Function.update_of_ne (ne_of_lt hkl)]
            exact (hpair i (Finset.mem_sdiff.mp him).1 k (Finset.mem_sdiff.mp hk).1 hik).trans hmono
  obtain ⟨hτ,hprotected,hpath,_⟩ := HI p le_rfl
  refine ⟨(S p).time,hτ,?_⟩
  intro a ha
  have hmem := hprotected.2 a ha
  rw [← greedyRun_refs base pick x r b m p (a*B) ha]
  exact hpath (a*B) hmem

end SK.Analytic

end
end

end OAI
