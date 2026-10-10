import OAI.Analysis.FourierLLogL.Thermal.History
import OAI.Analysis.FourierLLogL.Dyadic.Snap
import OAI.Analysis.FourierLLogL.Compress.Params

/-! # Applying compression on a subgrid -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate Real
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Period Real Compress.Params

variable {M l : ℕ}

/-- Sum of coeffs on multiples equals expectation over annihilator -/
def summesh (h : l ≤ M) (A : Form M) : ℝ := ∑ i : Grid l, q A (raise h i)
private lemma expU_wave (v : Grid M) : expU (wave v) = if v=0 then 1 else 0 := by
  have hi := congrArg Complex.re (expU_chi v)
  rw [expU_cx,re_Cx] at hi
  rw [expU_ex]
  split_ifs with H <;> simp only [H,ite_eq_left,Complex.one_re] at hi
  · subst v; exact hi
  · exact hi

lemma summesh_eq (h : l ≤ M) (A : Form M) :
    summesh h A = expU fun x => boltz A (raise (show M-l ≤ M by omega) x) := by
  classical
  let k := M-l
  have hk : k ≤ M := by unfold k; omega
  have he (i : Grid k) : boltz A (raise hk i) =
      ∑ t, q A t * wave (cut hk t) i := by
    rw [← boltz_series]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [wave,chi_comm,cut_chi,chi_comm i _,wave]
  change summesh h A = expU fun x : Grid k => boltz A (raise hk x)
  simp_rw [he,expU_sum,expU_ex, Ex_lmul, ← expU_ex,expU_wave,mul_ite,mul_one,mul_zero]
  let s : Finset (Grid M) := Finset.univ.image (raise h)
  have H : Finset.univ.filter (fun i => cut hk i=0) = s := by
    ext x
    simp only [s,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    exact annihilator h x
  rw [← Finset.sum_filter,H]
  unfold s summesh
  exact (Finset.sum_image (by intro i _ j _ he; exact raise_inj _ he)).symm

lemma summesh_bounds (h : l ≤ M) {A : Form M} {R : ℝ} (hi : 2^(M-l) ≤ R) (hA : S M R ≤ A) :
    side (M-l) ≤ summesh h A ∧ summesh h A ≤ 12*side (M-l) := by
  rw [summesh_eq]
  let r := M-l
  have hr : r ≤ M := Nat.sub_le _ _
  let f (x : Grid r) := boltz A (raise hr x)
  change side r ≤ expU f ∧ _
  constructor
  · have H := Finset.single_le_sum (s:=Finset.univ) (f:=f)
      (fun i _ => (boltz_pos _ _).le) (Finset.mem_univ (0 : Grid r))
    have Hz : f 0 = 1 := by simp [f,boltz,form_at_zero]
    unfold expU
    rw [smul_eq_mul]
    rw [Hz] at H
    have := side_pos r; nlinarith
  · let g : ℝ := 2^r
    have hg : 0 ≤ g := by unfold g; positivity
    have he (x : Grid r) :
        form (S M g) (raise hr x) = form (S r g) x := by
      simp_rw [form_S,cost,wave_at_one,raised_pos]
    apply le_trans (b:=q (S r g) 0)
    · rw [q_origin,expU_ex,expU_ex]
      exact Ex_mono _ fun i => exp_monotone <| neg_le_neg <| (he i).ge.trans <|
        form_mono ((S_mono hg hi).trans hA) _
    · have HH := q_S_upper' g (by unfold g; positivity) (M:=r) le_rfl
      rwa [side_pow_two,← div_eq_mul_inv]

lemma S_one_pos {R : ℝ} (h : 1 ≤ R) : 0 < S M R 1 := by
  simp [S]; nlinarith

def fq (hh : l ≤ M) (A : Form M) (hA : 0 ≤ A) : Law (Grid l) :=
  proportional (fun i : Grid l => q A (raise hh i)) (fun _ => q_nonneg hA _) (by
    have H := Finset.single_le_sum (s:=Finset.univ) (f:=fun i => q A (raise hh i))
      (fun i _ => q_nonneg hA _) (Finset.mem_univ (0:Grid l))
    rw [map_zero] at H
    exact lt_of_lt_of_le (q_origin_pos A) H)

lemma fq_apply (hh : l ≤ M) (A : Form M) (hA : 0 ≤ A) (i : Grid l) :
    fq hh A hA i = q A (raise hh i) / summesh hh A := rfl

def fq_cost (hh : l ≤ M) (A : Form M) (i : Grid l) := -log (cred A (raise hh i))

def raiseChar (hh : l ≤ M) (t : Grid M) : AddChar (Grid l) ℂ :=
    phaseChar (cut hh t)

lemma raiseChar_eq (hh : l ≤ M) (t : Grid M) (i : Grid l) :
    raiseChar hh t i = chi (raise hh i) t := by rw [cut_chi,chi_comm]; rfl

lemma fq_spec (hh : l ≤ M) (A : Form M) (hA : 0 ≤ A)
    {R : ℝ} (hr : 2^(M-l) ≤ R) (h : S M R ≤ A) :
    let p := fq hh A hA
    let c := fq_cost hh A
    (∀ x, 0 < p x) ∧ (∀ x, 0 ≤ c x) ∧ c 0=0 ∧
      (∀ x, (↑(exp (-c x)):ℂ)=(label A).Cx (fun t => raiseChar hh t x)) ∧
      (∀ x, -log (p x) = -log (p 0) + c x) ∧
      -log (p 0) ≤ F A - log (2^(M-l):ℝ)+12 := by
  have hi := summesh_bounds hh hr h
  have hp : 0 < summesh hh A := lt_of_lt_of_le (side_pos _) hi.1
  have hz (x : Grid M) : 0 < q A x := q_pos_one hA
    (lt_of_lt_of_le (S_one_pos (le_trans (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hr)) (h _)) x
  have he (x : Grid M) : 0 < cred A x := div_pos (hz x) (hz 0)
  refine ⟨fun x => div_pos (hz _) hp,fun x => neg_nonneg.mpr ?_,?_,?_,?_,?_⟩
  · apply Real.log_nonpos (he _).le
    exact (le_abs_self _).trans (cred_norm _ _)
  · simp [fq_cost,cred,(hz _).ne']
  · intro x
    simp_rw [fq_cost,neg_neg,exp_log (he _),raiseChar_eq]
    exact cred_eq _ _
  · intro x
    simp_rw [fq_apply,Real.log_div (hz _).ne' hp.ne',fq_cost,map_zero,cred,
      Real.log_div (hz _).ne' (hz _).ne']
    ring
  · rw [fq_apply,map_zero,Real.log_div (hz _).ne' hp.ne']
    have HH := log_le_log hp hi.2
    rw [log_mul (by norm_num) (side_pos _).ne', side_pow_two, Real.log_inv] at HH
    unfold F
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<12)]

/-- Snap parameter l associated with a node and h. -/
def snapExp (j : ℕ) (p : Node) :=
    p.lev-(40*ell j+6)
def snapGrid (j : ℕ) (p : Node) (M : ℕ) := M-snapExp j p
def sig (j : ℕ) := 1/(slow j:ℝ)^40
def sepRad (j : ℕ) := 1/(slow j:ℝ)^30

lemma snap_le (j : ℕ) (p : Node) : snapGrid j p M ≤ M := Nat.sub_le _ _
lemma step_scale (j : ℕ) {p : Node} (hp : p.lev ≤ M) :
    let l := snapGrid j p M
    M-l ≤ p.lev ∧ (2:ℝ)^(M-l) ≤ p.invlen ∧
      p.invlen ≤ 64*(slow j:ℝ)^40 * 2^(M-l) ∧
      ∀ u : Grid M, rad (u-raise (snap_le j p) (down (snap_le j p) u)) ≤ sig j*p.invlen/20 := by
  intro l
  let n := M-l
  have he : n = p.lev - (40*ell j+6) := by dsimp only [n,l,snapGrid,snapExp]; omega
  have hn : n ≤ p.lev := by omega
  have ht : (slow j:ℝ)^40*64 = (2:ℝ)^(40*ell j+6) := by
    simp only [slow,Nat.cast_pow,Nat.cast_ofNat]
    rw [← pow_mul,pow_add]; norm_num; rw [mul_comm (ell j)]
  refine ⟨hn,pow_le_pow_right₀ (by norm_num) hn,?_,?_⟩
  · rw [mul_comm 64,ht,← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  intro u
  have HH := snap_dist (snap_le (M:=M) j p) u
  apply HH.trans
  have hc : 0 < (slow j:ℝ)^40 := pow_pos (by exact_mod_cast slow_pos j) _
  by_cases hd : n=0
  · change (2:ℝ)^n-1 ≤ _
    rw [hd,pow_zero,sub_self]
    have := p.invlen_pos; unfold sig; positivity
  have hv : p.invlen = (2:ℝ)^n * ((slow j:ℝ)^40*64) := by
    rw [ht,← pow_add]; unfold invlen
    congr 1; omega
  rw [hv,sig]
  change (2:ℝ)^n-1 ≤ _
  have hs : 0 < (slow j:ℝ) := by exact_mod_cast slow_pos j
  field_simp
  have H : 0 < (2:ℝ)^n := by positivity
  nlinarith

end FourierLLogL.Dyadic.Thermal

end OAI
