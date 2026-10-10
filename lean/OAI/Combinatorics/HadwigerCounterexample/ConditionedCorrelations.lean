import OAI.Combinatorics.HadwigerCounterexample.BilinearBlockCorrelation

namespace OAI

/-! # Conditioned Correlations -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter Matrix LinearMap Function
open scoped BigOperators
variable {p : Shape} {I A : Type} [Fintype I] [Fintype A]
variable {n : ℕ}

set_option maxHeartbeats 600000 in
theorem spark_condition (p : Shape) (M : Moment p n) (s t : Label p.b) (l j : Tag p.g)
    (f g : Flavor p.g) (B) (hB : f.keeps l B) (hB' : g.keeps j B)
    (w u : Wgt (Knobs p.g n)) (hw : ∀ i,|w i|≤1) (hu : ∀ i,|u i|≤1)
    (μ δ : Wgt (Knobs p.g n)) (hμ : IsLaw μ) (hδ : IsLaw δ)
    (C : ℝ) (hC : 0<C)
    (hc : ∀ i,μ i ≤ C*unif i) (hc' : ∀ i,δ i ≤ C*unif i)
    (hM : n ≤ 5*blockRank B s t M) :
    let Q i z := evmat M (spring p l s f i) (spring p j t g z)
    |avg (pairW μ δ) (fun x => wsign (Q x.1 x.2)*(w x.1*u x.2))|≤
      C^2*bp (-(n:ℝ)/10) := by
  classical
  intro Q
  let V := Knobs p.g n
  let fit (f p : Wgt V) := fun i => p i*f i/(C*unif i)
  have h0 (i : V) : 0<C*unif i := by rw [unif_apply]; positivity
  have hh (t p : Wgt V) (ht : ∀ i, |t i|≤1) (hp : IsLaw p) (h : ∀ i,p i≤C*unif i) i :
      |fit t p i|≤1 := by
    unfold fit; rw [abs_div,abs_of_pos (h0 i),abs_mul,abs_of_nonneg (hp.nz _)]
    refine (div_le_one (h0 i)).mpr ?_
    exact ((mul_le_mul_of_nonneg_left (ht _) (hp.nz _)).trans_eq (mul_one _)).trans (h _)
  let F (x : V×V) := wsign (Q x.1 x.2)*(w x.1*u x.2)
  let Z (x : V×V) := wsign (Q x.1 x.2)*(fit w μ x.1*fit u δ x.2)
  have he :
      avg (pairW μ δ) F=C^2 * avg (pairW unif unif) Z := by
    unfold avg; rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    unfold Z F fit pairW
    have h1 := h0 i.1; have h2 := h0 i.2
    have h3 : unif i.1 ≠ 0 := by rw [unif_apply]; positivity
    have h4 : unif i.2 ≠ 0 := by rw [unif_apply]; positivity
    field_simp
  change |avg (pairW μ δ) F|≤_
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg _)]
  have hi : (n:ℝ)≤5*blockRank B s t M := by exact_mod_cast hM
  exact mul_le_mul_of_nonneg_left ((spark_uncap p M s t l j f g B hB hB'
    _ _ (hh w μ hw hμ hc) (hh u δ hu hδ hc')).trans (bp_le (by linarith only [hi]))) (sq_nonneg _)

def litFire (p : Shape) {n N : ℕ} (x : UnitType p n N) :=
  ∀ (s t : Label p.b) (c : Vec (Notches p)), c≠0 →
    n≤5*blockRank Block.Z s t (issue p c x)

theorem litFire_calendar (p : Shape) (C : ℝ) (M : ℕ) (hM : 4≤M) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n), 2*num (Full p n)<N →
    ∀ w : Wgt (UnitType p n N),
      (∀ i,w i ≤ bp (C*N)*pairW (raw m N) (raw m N) i) →
      pr w (fun i => ¬litFire p i) ≤ bp (-(n:ℝ)*n/8) := by
  classical
  let I := Label p.b × Label p.b × Vec (Notches p)
  have ht := bp_poly_dom_nat (a:=1) zero_lt_one (num I) 0
  filter_upwards [issue_live p,ht,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (8*(C*M+1)))]
    with n hn hp hab N m hN w h
  change 8*(C*M+1)≤ (n:ℝ) at hab
  refine (pr_cap h _).trans ?_
  let Q (i : I) (x : UnitType p n N) :=
     i.2.2≠0 ∧ 5*blockRank Block.Z i.1 i.2.1 (issue p i.2.2 x)<n
  let v := pairW (raw m N) (raw m N)
  have hv : IsLaw v := pairW_law (raw_law m hN) (raw_law m hN)
  have he (i : I) : pr v (Q i)≤bp (-(n:ℝ)*n/4) := by
    by_cases h : i.2.2=0
    · simp only [Q,h,ne_eq,not_true,false_and,pr_false]; exact (bp_pos _).le
    exact (pr_mono hv.nz fun x h => h.2).trans
      (hn N (by unfold N; nlinarith only [Nat.mul_le_mul_right n hM]) hN m _ _ i.2.2 h)
  have hh (x : UnitType p n N) (h : ¬litFire p x) : ∃ i,Q i x := by
    unfold litFire at h
    push Not at h
    obtain ⟨s,t,c,hc,h⟩ := h; exact ⟨(s,t,c),hc,h⟩
  have hi : pr v (fun x=> ¬litFire p x) ≤ num I*bp (-(n:ℝ)*n/4) :=
    (le_trans (pr_mono hv.nz hh) (pr_exists_le hv.nz Q)).trans ((sum_le_sum
      fun i _ => he i).trans_eq (by simp [num]))
  refine (mul_le_mul_of_nonneg_left hi (bp_pos _).le).trans ?_
  simp only [pow_zero,mul_one,one_mul] at hp
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp.le
    (bp_pos (-(n:ℝ)*n/4)).le) (bp_pos (C*N)).le).trans
  rw [← bp_add,← bp_add]
  apply bp_le
  unfold N; push_cast
  nlinarith only [mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n : 0≤(n:ℝ))]
end HadwigerCounterexample

end

end OAI
