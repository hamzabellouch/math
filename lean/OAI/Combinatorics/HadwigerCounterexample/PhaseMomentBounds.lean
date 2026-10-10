import OAI.Combinatorics.HadwigerCounterexample.IndependentPhaseBounds

namespace OAI

/-! # Phase Moment Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {A : Type} [Fintype A]

theorem poweravg (w f : Wgt A) (s : ℕ) :
    avg w f ^ s=avg (draws (Fin s) w) (fun x => ∏ i : Fin s,f (x i)) := by
  classical
  change _=avg (prodW _) (prodW (fun _ : Fin s => f))
  rw [prodW_avg]; simp

def sweep (p : Shape) {N} (f : A→Ambient p N) (w g : Wgt A) (S : Party)
    (q : PhasePair p N) := avg w (fun x => g x*wsign (joinPhase p q S (f x)))

theorem phase_power (p : Shape) {N} (f : A→Ambient p N) (w g : Wgt A) (S : Party) (s : ℕ)
    (hw : IsLaw w) (hg : ∀ x,|g x|≤1) (hs : S≠0) :
    avg (freeH p N) (fun q => (sweep p f w g S q)^s) ≤
      avg (draws (Fin s) w) (fun x => bp (- (p.h:ℝ)*epoch p (∑ i,f (x i)))) := by
  classical
  simp_rw [sweep,poweravg]
  rw [avg_avg]
  refine avg_mono (draws_law hw).nz fun x => ?_
  let y := ∑ i : Fin s,f (x i)
  have hh := free_phase y hs
  simp_rw [Finset.prod_mul_distrib,← wsign_sum,←map_sum,avg_mul']
  let T := ∏ i : Fin s,g (x i)
  have hi : T≤1 := by
    have he : |T| ≤ ∏ (_ : Fin s), (1:ℝ) := by
      unfold T; rw [Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hg _)
    exact (le_abs_self _).trans (by simpa using he)
  exact ((mul_le_mul_of_nonneg_right hi hh.1).trans_eq (one_mul _)).trans hh.2

theorem abs_sweep (p : Shape) {N} (f : A→Ambient p N) (w g : Wgt A) (S : Party)
    (hw : IsLaw w) (hg : ∀ x,|g x|≤1) :
    ∀ q,|sweep p f w g S q| ≤1 := by
  intro q
  apply (abs_avg_le hw.nz).trans (hw.avg_le (fun x => ?_))
  rw [abs_mul, wsign_abs,mul_one]; exact hg x

def exponentErr (p : Shape) (m b : ℕ) (c : ℝ) :=
  let s := 2^m*(2*b)
  ((2:ℝ)^s*(2:ℝ)^s)*c^b + bp (- (p.h:ℝ)*b/2)

theorem rare_sweep (p : Shape) {N} (f : A→Ambient p N) (w g : Wgt A) (S : Party)
    (hw : IsLaw w) (hg : ∀ x,|g x| ≤1) (hs : S≠0) (r m b : ℕ) (hr : ∀ x,epoch p (f x) ≤ r)
    (hm : 16*r<m) (hb : 1≤b)
    (c ψ : ℝ) (hc : 0≤c) (hh : ∀ t : Cov p N,
      (∀ i, cdSign p t i ≤ r*(2^m*(2*b))) → pr w (fun i => covered p t (f i)) ≤ c)
    (hψ : 0<ψ) :
    pr (freeH p N) (fun y => ψ ≤ |sweep p f w g S y|) ≤
      exponentErr p m b c / ψ^(2^m*(2*b)) := by
  classical
  let s := 2^m*(2*b)
  let v := draws (Fin s) w
  let y := sweep p f w g S
  have he := phase_power p f w g S s hw hg hs
  have ht : avg (freeH p N) (fun q => (y q)^s) ≤ exponentErr p m b c := by
    apply le_trans he
    let k (x : Fin s→A) := epoch p (∑ i,f (x i))
    let t := bp (-(p.h:ℝ)*b / 2)
    have hg (x : Fin s→A) :
        bp (-(p.h:ℝ)*k x) ≤ ind (2*k x ≤ b)+t := by
      by_cases hl : 2*k x ≤ b
      · rw [ind_one hl]
        refine (bp_le (show -(p.h:ℝ)*k x ≤0 by
          exact mul_nonpos_of_nonpos_of_nonneg (by simp) (by positivity))).trans ?_
        rw [bp_zero]
        exact le_add_of_nonneg_right (bp_pos _).le
      rw [ind_zero hl,zero_add]
      apply bp_le
      have hh : (b:ℝ) ≤ 2*(k x:ℝ) := by exact_mod_cast (le_of_not_ge hl)
      have he := mul_le_mul_of_nonneg_left hh (show 0≤(p.h:ℝ) from Nat.cast_nonneg _)
      linarith only [he]
    have hv : IsLaw v := draws_law hw
    refine le_trans (avg_mono hv.nz hg) ?_
    rw [avg_add,hv.avg_const]
    exact add_le_add_left (no_cover_rank p f w hw m b r hb hm hr c hc hh) _
  have hEv : Even s := ⟨2^m*b, by unfold s; ring⟩
  have hi : avg (freeH p N) (fun q => |y q|^s) ≤ exponentErr p m b c := by
    have hs (q) : |y q|^s=y q^s := hEv.pow_abs _
    simp_rw [hs]; exact ht
  change pr (freeH p N) _ ≤ _/ψ^s
  apply (le_div_iff₀ (pow_pos hψ s)).mpr
  rw [mul_comm]
  let u := freeH p N
  have hu : IsLaw u := freeH_law p N
  refine (mul_le_mul_of_nonneg_left (pr_mono (q:=fun q => ψ^s ≤ |y q|^s) hu.nz
    (fun q h => pow_le_pow_left₀ hψ.le h s)) (pow_pos hψ s).le).trans ?_
  exact (le_avg_markov hu.nz (fun q => pow_nonneg (abs_nonneg (y q)) s) _).trans hi

theorem epoch_count (p : Shape) (N r : ℕ) :
    nbr (fun x : Ambient p N => epoch p x ≤ r) ≤ bp (2*(r:ℝ)*num (Comp p.g)*N) := by
  classical
  let P := fun (M : Mat (Fin N) (Fin N)) => M.rank ≤r
  have hi : ∀ x : Ambient p N,epoch p x ≤ r → ∀ i,P (x i) := fun x hx i =>
    (Finset.single_le_sum (fun i _ => Nat.zero_le ((x i).rank)) (Finset.mem_univ i)).trans hx
  have hg : nbr (fun x : Ambient p N => ∀ i,P (x i)) =
      ∏ _ : Comp p.g,nbr P := by
    unfold nbr; simp_rw [ind_all]
    change tot (prodW (β:=fun _ : Comp p.g => Mat (Fin N) (Fin N)) (fun i a => ind (P a))) = _
    exact prodW_tot _
  refine (tot_mono (fun x => ind_mono (hi x))).trans ?_
  change nbr _ ≤ _
  rw [hg]
  let t := bp ((num (Fin N)+num (Fin N))*r)
  refine (Finset.prod_le_prod₀ (g:=fun _ => t) (fun _ _ => nbr_nonneg P) (fun _ _ =>
    nbr_matrix_rank r)).trans_eq ?_
  simp only [t,Finset.prod_const,Finset.card_univ,← bp_mul_nat,num,Fintype.card_fin]
  congr 1; ring

def noSweepBudget (p : Shape) (N m b r : ℕ) (c ψ H : ℝ) :=
  bp (2*(r:ℝ)*num (Comp p.g)*N) * (H*chanPrice p^2 *(exponentErr p m b c/ψ^(2^m*(2*b))))

set_option maxHeartbeats 800000 in
theorem pitch_no_cover (p : Shape) {N n} (Δ : UnitType p n N→ Ambient p N) {w}
    (hw : IsLaw w) (S R : Party) (hs : S ≠ 0)
    (r m b : ℕ) (hr : ∀ x,epoch p (Δ x) ≤ r)
    (hm : 16*r<m) (hb : 1≤b)
    (c ψ H : ℝ) (hc : 0≤c) (hh : ∀ t : Cov p N,
      (∀ i, cdSign p t i ≤ r*(2^m*(2*b))) → pr w (fun i => covered p t (Δ i)) ≤ c)
    (hψ : 0<ψ) (hH : 0≤H) (mix : Mixer p n)
    (hN : 2*num (Full p n)-N≤ -1)
    (hc' : ∀ x,w x ≤ H * pairW (raw mix N) (raw mix N) x) :
    |pitch p Δ w S R| ≤ ψ+noSweepBudget p N m b r c ψ H := by
  classical
  let g (v : Ambient p N) (x : UnitType p n N) := wsign (tone p x R v)
  have hg v x : |g v x|≤1 := by simp [g]
  let y (v : Ambient p N) := sweep p Δ w (g v) S
  let Q := exponentErr p m b c / ψ^(2^m*(2*b))
  have h v := rare_sweep p Δ w (g v) S hw (hg v) hs r m b hr hm hb c ψ hc hh hψ
  let F' (v : Ambient p N) (x : UnitType p n N) := y v (listens p x)
  let A := {v : Ambient p N//epoch p v ≤ r}
  let B (x : UnitType p n N) := ∃ v : A, ψ ≤ |F' v.val x|
  have ha (x) : |F' (Δ x) x| ≤ ψ+ind (B x) := by
    by_cases h : ψ ≤ |F' (Δ x) x|
    · rw [ind_one (show B x from ⟨⟨Δ x,hr x⟩,h⟩)]
      exact (abs_sweep p Δ w _ S hw (hg _) _).trans (by linarith)
    exact le_trans (le_of_not_ge h) (le_add_of_nonneg_right (ind_nonneg _))
  have hZ : pitch p Δ w S R = avg w (fun x => F' (Δ x) x) := by
    rw [pitch,pairW_avg,avg_avg]
    simp_rw [wsign_add]
    rfl
  rw [hZ]
  refine ((abs_avg_le hw.nz).trans (avg_mono hw.nz ha)).trans ?_
  rw [avg_add,hw.avg_const]
  apply add_le_add_right
  have hz (v : A) :
      pr w (fun x => ψ ≤ |F' v.val x|) ≤ H*chanPrice p^2 * Q := by
    let P (y' : PhasePair p N) := ψ ≤ |y v.val y'|
    calc pr w (fun x => ψ ≤ |F' v.val x|)
      _ = pr (mapW w (listens p)) P := (mapW_pr w (listens p) P).symm
      _ ≤ _ := (pr_cap (phase_cap hH mix hc' hN) P).trans
         (mul_le_mul_of_nonneg_left (h _) (mul_nonneg hH (sq_nonneg _)))
  refine (pr_exists_le hw.nz (fun v : A => fun x => ψ ≤ |F' v.val x|)).trans ?_
  refine (Finset.sum_le_sum fun i _ => hz i).trans ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  unfold noSweepBudget
  apply mul_le_mul_of_nonneg_right
  · exact (nbr_eq_card (fun v : Ambient p N => epoch p v≤r)).symm.trans_le (epoch_count p N r)
  · exact mul_nonneg (mul_nonneg hH (sq_nonneg _)) ((pr_nonneg (freeH_law p N).nz).trans
      (h (0:Ambient p N)))

end HadwigerCounterexample

end

end OAI
