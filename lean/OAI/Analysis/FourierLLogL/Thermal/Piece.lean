import OAI.Analysis.FourierLLogL.Thermal.History

/-! # Finite input pieces and spectra, using counting measure for the observation coordinate -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate Real
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic
open Law Node Period Real
namespace Node
variable {M : ℕ}
def child (p : Node) : Bool → Node
| false => p.L
| true => p.R
lemma child_ok (p : Node) (h : p.valid) (hv : p.lev < M) (b) :
    ok (p.child b) M := by cases b <;> exact ⟨by first | exact p.valid_L.mpr h | exact p.valid_R.mpr h,hv⟩
lemma child_len (p : Node) (b : Bool) : (p.child b).len=p.len/2 := by
  cases b; exact p.len_L; exact p.len_R
lemma child_below (p : Node) (b : Bool) : (p.child b).below p := by
  cases b; exact p.below_left; exact p.below_right
end Node

namespace Thermal
variable {M : ℕ}
open scoped Classical

/-- Observation type-A. -/
def channel (A : Form M) (x : Grid M) : Law (Grid M) :=
  (label A).send (fun z => x+z)

lemma channel_apply (A : Form M) (x z : Grid M) :
    channel A x z = label A (z-x) := by
  rw [channel,send_apply,prob_eq]
  simp_rw [add_comm x, ← eq_sub_iff_add_eq]
  simp

lemma ch_K (A : Form M) (x z : Grid M) :
    channel A x z = side M * K A (z-x) := by rw [channel_apply,label_apply]

lemma ch_pos (A : Form M) (x z : Grid M) : 0 < channel A x z := by rw [channel_apply]; exact label_pos _ _

lemma ch_ex (A : Form M) (f : Grid M → ℝ) (x : Grid M) :
    (channel A x).Ex f = (label A).Ex fun z => f (x+z) := Ex_send _ _ _

lemma ch_noise (A : Form M) (f : Grid M → ℝ) (x : Grid M) :
    (channel A x).Ex (fun z => f (z-x)) = (label A).Ex f := by
  rw [ch_ex]; simp

/-- Local normalized subdensity (as mass weights, counting-grid). Its total is m/α. -/
def wt (p : Node) (a : Grid M → ℝ) (α : ℝ) (y : Grid M) : ℝ :=
    p.dice M y * a y / α

lemma wt_nonneg (p : Node) {a : Grid M → ℝ} (ha : 0 ≤ a) {α : ℝ} (hα : 0 ≤ α) (y) :
    0 ≤ wt p a α y := div_nonneg (mul_nonneg ((p.dice M).nonneg y) (ha y)) hα

lemma wt_total (p : Node) (hp : p.ok M) (a : Grid M → ℝ) (α : ℝ) :
    ∑ y, wt p a α y = p.avg a / α := by simp_rw [wt, ← Finset.sum_div, avg_ex hp,Ex]

/-- Law of a local piece when normalization is its positive mean; used as proof-carrying
relation to any specified law. -/
def PieceLaw (p : Node) (a : Grid M → ℝ) (P : Law (Grid M)) := ∀ y, P y = wt p a (p.avg a) y

lemma make_piece (p : Node) (hp : p.ok M) {a : Grid M → ℝ} (ha : 0 ≤ a) (hm : 0 < p.avg a) :
    ∃ P : Law (Grid M), PieceLaw p a P := by
  refine ⟨⟨wt p a (p.avg a),wt_nonneg p ha hm.le,by rw [wt_total _ hp,div_self hm.ne']⟩,fun i => rfl⟩

lemma piece_support {p : Node} (hp : p.ok M) {a : Grid M → ℝ}
    {P : Law (Grid M)} (h : PieceLaw p a P) (x : Grid M) (hx : 0 < P x) :
    x ∈ p.block M := by
  by_contra hh; rw [h,wt,dice_apply hp,ite_eq_right hh,zero_mul,zero_div] at hx
  exact lt_irrefl _ hx

lemma piece_density {p : Node} {a : Grid M → ℝ} {P : Law (Grid M)}
    (h : PieceLaw p a P) {d : ℝ} (h1 : ∀ x, a x ≤ exp d)
    (hm : exp (-d) ≤ p.avg a) (x : Grid M) :
    P x ≤ exp (2*d)*p.dice M x := by
  rw [h,wt]
  apply (div_le_iff₀ (lt_of_lt_of_le (exp_pos _) hm)).mpr
  have HE : exp (2*d)*exp (-d) = exp d := by rw [← exp_add]; congr; ring
  calc
    _ ≤ p.dice M x * exp d := by
      exact mul_le_mul_of_nonneg_left (h1 _) ((p.dice M).nonneg _)
    _ = exp (2*d)*p.dice M x * exp (-d) := by rw [mul_comm _ (p.dice _ _),mul_assoc,HE]
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (mul_nonneg (exp_nonneg _) ((p.dice M).nonneg _))

lemma wt_half {p : Node} (h : p.valid) (hp : p.lev < M) (a : Grid M → ℝ) (α : ℝ)
    (x : Grid M) (b : Bool) :
    wt (p.child b) a α x = if x ∈ (p.child b).block M then 2*wt p a α x else 0 := by
  rw [wt,dice_apply (child_ok p h hp b)]
  split_ifs with hh
  · rw [wt,dice_apply ⟨h,hp.le⟩,ite_eq_left (block_of_below (child_below _ _) _ hh),child_len]
    field_simp
  simp

/-- Observation law weighted by the local subpiece. -/
def omegaObs (p : Node) (a : Grid M → ℝ) (α : ℝ) (A : Form M) (y z : Grid M) :=
    wt p a α y * channel A y z
def Mz (p : Node) (a : Grid M → ℝ) (α : ℝ) (A : Form M) (z : Grid M) :=
    ∑ y, omegaObs p a α A y z
def fz (p : Node) (a : Grid M → ℝ) (α : ℝ) (A : Form M) (u z : Grid M) : ℂ :=
    ∑ y, (omegaObs p a α A y z:ℂ) * chi u y
def energyZ (p : Node) (a : Grid M → ℝ) (α : ℝ) (A : Form M) (u : Grid M) :=
    ∑ z, ‖fz p a α A u z‖^2 / Mz p a α A z

def high (p : Node) (a : Grid M → ℝ) (α : ℝ) (A : Form M) (b : ℝ) (u : Grid M) :=
    ∃ B, b^2 ≤ energyZ (p.child B) a α A u

lemma density_nonneg (p : Node) {a : Grid M → ℝ} (ha : 0 ≤ a) {α : ℝ} (hα : 0 ≤ α)
    (A : Form M) (y z : Grid M) : 0 ≤ omegaObs p a α A y z :=
  mul_nonneg (wt_nonneg p ha hα _) ((channel A y).nonneg z)

lemma mass_nonneg (p : Node) {a : Grid M → ℝ} (ha : 0 ≤ a) {α : ℝ} (hα : 0 ≤ α)
    (A : Form M) (z : Grid M) : 0 ≤ Mz p a α A z :=
  Finset.sum_nonneg fun _ _ => density_nonneg _ ha hα _ _ _

lemma mass_total (p : Node) (hp : p.ok M) (a : Grid M → ℝ) (α : ℝ)
    (A : Form M) : ∑ z, Mz p a α A z = p.avg a / α := by
  unfold Mz; rw [Finset.sum_comm]; simp_rw [omegaObs,← Finset.mul_sum,Law.total,mul_one]
  rw [wt_total _ hp]

lemma fz_norm (p : Node) {a : Grid M → ℝ} (ha : 0 ≤ a) {α : ℝ} (hα : 0 ≤ α)
    (A : Form M) (u z : Grid M) : ‖fz p a α A u z‖ ≤ Mz p a α A z := by
  apply le_trans (norm_sum_le _ _)
  simp_rw [norm_mul, Complex.norm_real,norm_chi,mul_one, Real.norm_eq_abs,
    abs_of_nonneg (density_nonneg _ ha hα _ _ _)]
  exact le_rfl

lemma energyZ_le (p : Node) {a : Grid M → ℝ} (ha : 0 ≤ a) {α : ℝ} (hα : 0 ≤ α)
    (A : Form M) (u : Grid M) : energyZ p a α A u ≤ ∑ z, ‖fz p a α A u z‖ := by
  apply Finset.sum_le_sum; intro z _
  have hi := fz_norm p ha hα A u z
  rcases eq_or_lt_of_le (mass_nonneg _ ha hα _ z) with H | H
  · rw [← H,div_zero]; exact norm_nonneg _
  · refine (div_le_iff₀ H).mpr ?_
    nlinarith [norm_nonneg (fz p a α A u z)]


def polar (z : ℂ) := ((↑(‖z‖⁻¹:ℝ)) : ℂ) * conj z

lemma polar_identity (z : ℂ) : (polar z * z).re = ‖z‖ := by
  by_cases hz : z=0
  · subst z; simp
  · unfold polar
    rw [mul_assoc,mul_comm (conj z),Complex.mul_conj,← Complex.sq_norm,← Complex.ofReal_mul,
       Complex.ofReal_re]
    have hN : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
    field_simp

lemma polar_unit (z : ℂ) : ‖polar z‖ ≤ 1 := by
  by_cases hz : z=0
  · subst z; simp [polar]
  rw [polar,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),
    Complex.norm_conj, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

lemma piece_child_bias {p : Node} (hp : p.valid) (hv : p.lev < M)
    {a : Grid M → ℝ} (ha : 0 ≤ a) {α : ℝ} (hα : 0 < α)
    {P : Law (Grid M)} (hP : PieceLaw p a P) (hm : 0 < p.avg a) (hm' : p.avg a ≤ 2*α)
    (A : Form M) (u : Grid M) (B : Bool) {b : ℝ}
    (hb : b^2 ≤ energyZ (p.child B) a α A u) :
    ∃ v : Grid M → ℂ, (∀ z, ‖v z‖ ≤ 1) ∧
      b^2/4 ≤ P.Ex fun x => if x∈(p.child B).block M then
        (channel A x).Ex fun z => (v z*chi u x).re else 0 := by
  let f := fz (p.child B) a α A u
  let v : Grid M → ℂ := fun z => polar (f z)
  let J := P.Ex fun x => if x∈(p.child B).block M then
        (channel A x).Ex fun z => (v z*chi u x).re else 0
  have he1 (y z : Grid M) :
      omegaObs (p.child B) a α A y z = if y∈(p.child B).block M
        then (2*p.avg a / α) * (P y*channel A y z) else 0 := by
    rw [omegaObs,wt_half hp hv,hP]
    split_ifs
    · rw [wt,wt]; field_simp
    exact zero_mul _
  have he2 (z : Grid M) :
      ‖f z‖ = ∑ y, omegaObs (p.child B) a α A y z * (v z*chi u y).re := by
    rw [← polar_identity]
    change (v z* (_)).re = _
    dsimp only [f,fz]
    rw [Finset.mul_sum,Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm,Complex.re_ofReal_mul]
  have he :
      ∑ z, ‖f z‖ = (2*p.avg a / α)*J := by
    simp_rw [he2,he1]
    rw [Finset.sum_comm]
    unfold J Ex
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h : i ∈ (child p B).block M
    · simp_rw [ite_eq_left h,Finset.mul_sum,mul_assoc]
    simp [h]
  have h0 := hb.trans (energyZ_le _ ha hα.le _ _)
  change b^2 ≤ ∑ z, ‖f z‖ at h0; rw [he] at h0
  have hp1 : 0 < 2*p.avg a/α := by positivity
  have hi1 : 2*p.avg a/α ≤ 4 := by apply (div_le_iff₀ hα).mpr; linarith
  have hj : 0 ≤ J := nonneg_of_mul_nonneg_right ((sq_nonneg _).trans h0) hp1
  exact ⟨v,fun i => polar_unit _,by change b^2/4 ≤ J; nlinarith⟩

end Thermal
end FourierLLogL.Dyadic

end OAI
