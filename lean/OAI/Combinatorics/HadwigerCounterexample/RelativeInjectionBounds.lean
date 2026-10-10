import OAI.Combinatorics.HadwigerCounterexample.TableInjectionTransfer

namespace OAI

/-! # Relative Injection Bounds -/

noncomputable section
namespace HadwigerCounterexample

open Matrix LinearMap Module Submodule Function Finset Filter
open scoped BigOperators Topology
variable {p : Shape} {n N : ℕ}

def fringe (N : ℕ) := bp (-0.01*N)
def shine (N : ℕ) := bp (0.01*N)
def edgeError (N : ℕ) := bp (-0.005*N)

private theorem fire_budget (K : ℕ) (p : Shape) {l D : ℝ}
    (hd : 0 ≤D) (hh : 2*K+l+200*(D+2 : ℝ) ≤ p.h) :
    ∀ᶠ N : ℕ in atTop,
      bp (D*N)*(fireBill p (N/100) K (shine N)/(pushCost (bp (-l)) K)^(N/100)) ≤ fringe N := by
  have he := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (1+p.h*(K:ℝ)))
  filter_upwards [he,eventually_ge_atTop 100] with N hN hk
  change (1+p.h*(K:ℝ))≤(N:ℝ) at hN
  let k := N/100
  have ht : N ≤ 200*k := by
    have h1 : 1 ≤ N/100 := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hk)
    have h := Nat.div_add_mod' N 100
    unfold k; omega
  have ht' : (N:ℝ)≤200*k := by exact_mod_cast ht
  have h1 : (D+2)*N≤ (p.h-(2*K+(l:ℝ)))*k := by
    have h := mul_le_mul_of_nonneg_left ht' (show 0≤D+2 by linarith)
    have h' := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg k : 0≤(k:ℝ))
    linarith only [h,h']
  change bp _*(fireBill p k K (shine N)/_ ^ k)≤_
  unfold fireBill pushCost shine fringe
  rw [←bp_sub, ← bp_mul_nat, ← bp_one,←bp_add,←bp_add,←bp_sub,←bp_add]
  apply bp_le
  linarith only [h1,hN,(Nat.cast_nonneg N : 0≤(N:ℝ))]

set_option maxHeartbeats 1000000 in
theorem guard_grid (g K : ℕ) (D ε : ℝ) (hd : 0≤D) (he : 0<ε) :
    ∀ᶠ h : ℕ in atTop,∀ p : Shape,p.g=g → p.h=h →
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,let N:=M*n;
    ∀ (P : UnitType p n N×UnitType p n N→Prop),
    named P (bp (D*N)) → named (P ∘ Prod.swap) (bp (D*N)) →
    ∀ w (b : Fpins p n N) (m : Mixer p n), (∀ x,planRank (b x)≤ K) →
    IsLaw w → bySide p w m (shine N) → (∀ x,w x≠0 → ∀ i,frameLaw m (onSide x i)) →
    pr (pairW w w) (fun x => P x ∧ ¬ secureAt p b x) ≤
      ε*pr (pairW w w) P+edgeError N := by
  let W := 8*num (Comp g×Bool)
  obtain ⟨k,hk⟩ : ∃ k : ℕ,W*(3*bp (-(k:ℝ)))≤ ε := by
    have hh : Tendsto (fun n : ℕ => W*(3*bp (-(n:ℝ)))) atTop (𝓝 0) := by
      have hi := ((bp_nat_vanish (by norm_num : 0<(1:ℝ))).const_mul 3).const_mul W
      simpa using hi
    obtain ⟨n,hn⟩ := (hh.eventually (gt_mem_nhds he)).exists
    exact ⟨n,hn.le⟩
  let l := bp (-(k:ℝ))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (2*K+(k:ℝ)+200*(D+2)))] with h hH p hg hp

  have heq : (8*num (Place p):ℝ)*(3*l) ≤ ε := by
    change (8*num (Comp p.g×Bool):ℝ)*(3*l) ≤ _
    rwa [hg]
  have hFire : ∀ᶠ N : ℕ in atTop,
      bp (D*N)*(fireBill p (N/100) K (shine N)/(pushCost l K)^(N/100)) ≤ fringe N :=
    fire_budget K p hd (hp.symm ▸ hH)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      8*num (Place p)*(fringe N +fringe N)≤edgeError N := by
    filter_upwards [bp_poly_dom_nat (by norm_num : 0<(0.005:ℝ)) (8*num (Place p)*2) 0] with N hN
    unfold fringe edgeError
    rw [←two_mul,←mul_assoc]
    refine (mul_le_mul_of_nonneg_right (show _≤bp (0.005*N) from by simpa using hN.le)
      (bp_pos _).le).trans_eq ?_
    rw [←bp_add]; congr 1; ring
  filter_upwards [eventually_grid hFire,eventually_grid hsmall,
    columns_budget p (δ:=1) zero_lt_one 2 1 (by norm_num) zero_le_one,
    eventually_grid (tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (10*((k:ℝ)+1))))] with M hM hT hS hY
  filter_upwards [hM,hT,eventually_ge_atTop 1,hY] with n hM hT hn hY
  dsimp only
  intro P hP hQ w b m hb hw hW hx
  let N := M*n
  have hN : 2*num (Full p n)+1≤N := (hS n hn).trans_eq (one_mul _)
  have hρ : rhUp (shine N) (2*fringe N)*2 * bp (num (Row p n)+(N/100:ℕ)-N)≤l := by
    change 10*((k:ℝ)+1) ≤ N at hY
    have hh : 100*((N/100:ℕ):ℝ)≤N := by exact_mod_cast (show 100*(N/100) ≤ N from Nat.mul_div_le _ _)
    unfold rhUp shine fringe
    rw [show 2*bp (-0.01*N)/2=bp (-0.01*N) from (by ring), ← bp_neg, ←bp_one,
      ←bp_add,←bp_add,←bp_add]
    apply bp_le
    linarith only [hY,hN,hh,row_le p n]
  have hl : 0<l:=bp_pos _
  have hX := secure_bound hP hQ (bp_pos _ : 0<fringe N) (bp_pos _).le hl w b K (N/100) hb
    hw m hW hx (by linarith only [hN]) hρ
  let V := pr (pairW w w) P
  have hv : 0≤V := pr_nonneg (pairW_law hw hw).nz
  have hi := mul_le_mul_of_nonneg_right heq hv
  refine hX.trans ?_
  change (8*num (Place p))*(3*l*V+_ + bp (D*N)* _)≤ε*V+_
  calc _ ≤ (8*num (Place p))*(3*l*V+fringe N + fringe N) :=
      mul_le_mul_of_nonneg_left (add_le_add (show 3*l*V+fringe N ≤ _ from le_rfl) (show _ ≤ fringe N from hM)) (by unfold num; positivity)
       _ ≤ _ := by linarith only [hi,hT]

end HadwigerCounterexample

end

end OAI
