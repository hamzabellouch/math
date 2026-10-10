import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EffectiveProfiles

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology


open Set Filter
open scoped Topology BigOperators
namespace ShearFlows

structure QBall where
  center : ℚ
  radius : ℚ
  deriving DecidableEq

namespace QBall

def Contains (b : QBall) (x : ℝ) : Prop := |x - (b.center : ℝ)| ≤ b.radius

def exact (q : ℚ) : QBall := ⟨q,0⟩
def add (b c : QBall) : QBall := ⟨b.center+c.center,b.radius+c.radius⟩
def mul (b c : QBall) : QBall :=
  ⟨b.center*c.center, |b.center| * c.radius+|c.center| * b.radius+b.radius*c.radius⟩
def pow (b : QBall) : ℕ → QBall :=
  Nat.rec (exact 1) (fun _ acc => mul acc b)

def invLower (δ : ℚ) (b : QBall) : QBall :=
  ⟨(max δ b.center)⁻¹, b.radius/δ^2⟩

theorem contains_exact (q : ℚ) : (exact q).Contains q := by simp [Contains, exact]

theorem radius_nonneg {b : QBall} {x : ℝ} (h : b.Contains x) : 0 ≤ b.radius := by
  exact_mod_cast (abs_nonneg _).trans h

theorem contains_add {b c : QBall} {x y : ℝ} (hb : b.Contains x) (hc : c.Contains y) :
    (b.add c).Contains (x+y) := by
  dsimp [Contains, add] at *
  push_cast
  calc
    |x + y - ((b.center : ℝ) + c.center)| = |(x - b.center)+(y-c.center)| := by ring_nf
    _ ≤ |x-b.center|+|y-c.center| := abs_add_le _ _
    _ ≤ _ := add_le_add hb hc

theorem contains_mul {b c : QBall} {x y : ℝ} (hb : b.Contains x) (hc : c.Contains y) :
    (b.mul c).Contains (x*y) := by
  have hb0 : (0 : ℝ) ≤ b.radius := by exact_mod_cast radius_nonneg hb
  have hc0 : (0 : ℝ) ≤ c.radius := by exact_mod_cast radius_nonneg hc
  dsimp [Contains, mul] at *
  push_cast
  calc
    |x*y - (b.center : ℝ)*c.center| =
        |(b.center : ℝ)*(y-c.center)+(c.center : ℝ)*(x-b.center)+
          (x-b.center)*(y-c.center)| := by ring_nf
    _ ≤ |(b.center : ℝ)*(y-c.center)|+|(c.center : ℝ)*(x-b.center)|+
        |(x-b.center)*(y-c.center)| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |(b.center : ℝ)| * |y-c.center|+|(c.center : ℝ)| * |x-b.center|+
        |x-b.center| * |y-c.center| := by simp only [abs_mul]
    _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hb (abs_nonneg _)))
        (mul_le_mul hb hc (abs_nonneg _) hb0)

theorem contains_pow {b : QBall} {x : ℝ} (h : b.Contains x) (n : ℕ) :
    (b.pow n).Contains (x^n) := by
  induction n with
  | zero => simpa [QBall.pow] using contains_exact 1
  | succ n ih => exact contains_mul ih h

theorem contains_invLower {b : QBall} {x : ℝ} (hb : b.Contains x)
    {δ : ℚ} (hδ : 0 < δ) (hx : (δ : ℝ) ≤ x) : (b.invLower δ).Contains x⁻¹ := by
  have hd : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hp : 0 < x := hd.trans_le hx
  have hm : (δ : ℝ) ≤ max (δ : ℝ) (b.center : ℝ) := le_max_left _ _
  have hmp : (0 : ℝ) < max (δ : ℝ) (b.center : ℝ) := hd.trans_le hm
  have hdist : |x-max (δ : ℝ) (b.center : ℝ)| ≤ |x-(b.center : ℝ)| := by
    rcases le_total (δ : ℝ) (b.center : ℝ) with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr hx),
        abs_of_nonneg (sub_nonneg.mpr (h.trans hx))]
      linarith
  dsimp [Contains, invLower]
  push_cast
  rw [inv_sub_inv hp.ne' hmp.ne', abs_div, abs_mul,
    abs_of_pos hp, abs_of_pos hmp, abs_sub_comm]
  exact div_le_div₀ (by exact_mod_cast radius_nonneg hb) (hdist.trans hb)
    (sq_pos_of_pos hd) (by nlinarith [mul_le_mul hx hm hd.le hp.le])

def Converges (b : ℕ → QBall) (x : ℝ) : Prop :=
  Tendsto (fun n => ((b n).center : ℝ)) atTop (𝓝 x) ∧
  Tendsto (fun n => ((b n).radius : ℝ)) atTop (𝓝 0)

theorem converges_exact (q : ℚ) : Converges (fun _ => exact q) q :=
  ⟨tendsto_const_nhds, by simp [QBall.exact]⟩

theorem Converges.add {b c : ℕ → QBall} {x y : ℝ}
    (hb : Converges b x) (hc : Converges c y) : Converges (fun n => (b n).add (c n)) (x+y) := by
  constructor
  · simpa [QBall.add] using hb.1.add hc.1
  · simpa [QBall.add] using hb.2.add hc.2

theorem Converges.mul {b c : ℕ → QBall} {x y : ℝ}
    (hb : Converges b x) (hc : Converges c y) : Converges (fun n => (b n).mul (c n)) (x*y) := by
  constructor
  · simpa [QBall.mul] using hb.1.mul hc.1
  · simpa [QBall.mul] using ((hb.1.abs.mul hc.2).add (hc.1.abs.mul hb.2)).add (hb.2.mul hc.2)

theorem Converges.pow {b : ℕ → QBall} {x : ℝ} (hb : Converges b x) (k : ℕ) :
    Converges (fun n => (b n).pow k) (x^k) := by
  induction k with
  | zero => simpa [QBall.pow] using converges_exact 1
  | succ k ih => exact ih.mul hb

theorem Converges.invLower {b : ℕ → QBall} {x : ℝ} (hb : Converges b x)
    {δ : ℚ} (hδ : 0 < δ) (hx : (δ : ℝ) ≤ x) : Converges (fun n => (b n).invLower δ) x⁻¹ := by
  have hxp : (0 : ℝ) < x := (Rat.cast_pos.mpr hδ).trans_le hx
  constructor
  · simpa [QBall.invLower, max_eq_right hx] using
      (tendsto_const_nhds.max hb.1).inv₀ (show max (δ : ℝ) x ≠ 0 by rw [max_eq_right hx]; exact hxp.ne')
  · simpa [QBall.invLower] using hb.2.div_const ((δ : ℝ)^2)

end QBall

def expTerms (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, q^k / k.factorial

def expIndex (q : ℚ) (n : ℕ) : ℕ := n + ⌈2*|q|⌉₊ + 1

def expBall (q : ℚ) (n : ℕ) : QBall :=
  ⟨expTerms q (expIndex q n), 2*|q|^(expIndex q n)/(expIndex q n).factorial⟩

theorem expTerms_cast (q : ℚ) (n : ℕ) :
    (expTerms q n : ℝ) = ∑ k ∈ Finset.range n, (q : ℝ)^k / k.factorial := by
  simp [expTerms]

theorem expBall_contains (q : ℚ) (n : ℕ) : (expBall q n).Contains (Real.exp q) := by
  have hN : 2*|(q : ℝ)| ≤ (expIndex q n : ℝ) := by
    have hh : 2*|(q : ℝ)| ≤ (⌈2*|q|⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil (2*|q|)
    dsimp [expIndex]
    push_cast
    linarith
  have hc : ‖(q : ℂ)‖ / ((expIndex q n).succ : ℝ) ≤ 1/2 := by
    rw [show (q : ℂ) = ((q : ℝ) : ℂ) by norm_cast, Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ (by positivity)).2
    push_cast
    linarith
  have hb := Complex.exp_bound' hc
  have he : (Real.exp (q : ℝ) : ℂ) -
      (∑ k ∈ Finset.range (expIndex q n), (q : ℝ)^k/(k.factorial : ℝ) : ℝ) =
      Complex.exp (q : ℂ) - ∑ k ∈ Finset.range (expIndex q n), (q : ℂ)^k/k.factorial := by
    simp
  rw [← he, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb
  change |Real.exp (q : ℝ) - (expTerms q (expIndex q n) : ℝ)| ≤ _
  rw [expTerms_cast]
  convert! hb using 1
  simp only [expBall, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_abs, Rat.cast_natCast, Complex.norm_ratCast]
  ring

theorem expIndex_tendsto (q : ℚ) : Tendsto (expIndex q) atTop atTop := by
  exact tendsto_atTop_mono (fun n => by dsimp [expIndex]; omega) tendsto_id

theorem expBall_converges (q : ℚ) : QBall.Converges (expBall q) (Real.exp q) := by
  have hs := NormedSpace.expSeries_div_hasSum_exp (q : ℝ)
  have ht := NormedSpace.expSeries_div_hasSum_exp |(q : ℝ)|
  constructor
  · have hh := hs.tendsto_sum_nat.comp (expIndex_tendsto q)
    simpa [expBall, expTerms_cast, ← Real.exp_eq_exp_ℝ, Function.comp_def] using hh
  · have hh := (ht.summable.tendsto_atTop_zero.comp (expIndex_tendsto q)).const_mul 2
    simpa [expBall, Function.comp_def, mul_div_assoc] using hh

def glueBall (q : ℚ) (n : ℕ) : QBall :=
  if q ≤ 0 then .exact 0 else expBall (-q⁻¹) n

theorem glueBall_contains (q : ℚ) (n : ℕ) : (glueBall q n).Contains (expNegInvGlue q) := by
  unfold glueBall
  split_ifs with hq
  · have hqr : (q : ℝ) ≤ 0 := by exact_mod_cast hq
    simpa [expNegInvGlue.zero_of_nonpos hqr] using QBall.contains_exact 0
  · have hqr : ¬(q : ℝ) ≤ 0 := by exact_mod_cast hq
    simpa [expNegInvGlue, hqr] using expBall_contains (-q⁻¹) n

theorem glueBall_converges (q : ℚ) : QBall.Converges (glueBall q) (expNegInvGlue q) := by
  change QBall.Converges (fun n => glueBall q n) _
  by_cases hq : q ≤ 0
  · have hqr : (q : ℝ) ≤ 0 := by exact_mod_cast hq
    simpa [glueBall, hq, expNegInvGlue.zero_of_nonpos hqr] using QBall.converges_exact 0
  · have hqr : ¬(q : ℝ) ≤ 0 := by exact_mod_cast hq
    simpa [glueBall, hq, expNegInvGlue, hqr] using expBall_converges (-q⁻¹)

namespace ProfileExpr

def enclose : ProfileExpr → ℚ → ℕ → QBall
  | .const r, _, _ => .exact r
  | .coord, q, _ => .exact q
  | .glue k a b, q, n => (QBall.exact ((a*q+b)⁻¹^k)).mul (glueBall (a*q+b) n)
  | .denom k a b, q, n =>
    (((glueBall (a*q+b) n).add (glueBall (1-(a*q+b)) n)).invLower (1/9)).pow k
  | .add f g, q, n => (f.enclose q n).add (g.enclose q n)
  | .mul f g, q, n => (f.enclose q n).mul (g.enclose q n)

theorem enclose_contains (e : ProfileExpr) (q : ℚ) (n : ℕ) :
    (e.enclose q n).Contains (e.val q) := by
  induction e with
  | const r => exact QBall.contains_exact r
  | coord => exact QBall.contains_exact q
  | glue k a b =>
    simpa [enclose, val, gluePower] using
      QBall.contains_mul (QBall.contains_exact ((a*q+b)⁻¹^k)) (glueBall_contains (a*q+b) n)
  | denom k a b =>
    have hb := QBall.contains_add (glueBall_contains (a*q+b) n) (glueBall_contains (1-(a*q+b)) n)
    have hd : (1/9 : ℚ) > 0 := by norm_num
    have he : (1/9 : ℝ) ≤ expNegInvGlue (a*q+b) + expNegInvGlue (1-(a*q+b)) := transitionDen_ge _
    simpa [enclose, val, denomPower, transitionDen] using
      QBall.contains_pow (QBall.contains_invLower hb hd (by simpa using he)) k
  | add f g hf hg => exact QBall.contains_add hf hg
  | mul f g hf hg => exact QBall.contains_mul hf hg

theorem enclose_converges (e : ProfileExpr) (q : ℚ) :
    QBall.Converges (e.enclose q) (e.val q) := by
  induction e with
  | const r => exact QBall.converges_exact r
  | coord => exact QBall.converges_exact q
  | glue k a b =>
    simpa [enclose, val, gluePower] using
      QBall.Converges.mul (QBall.converges_exact ((a*q+b)⁻¹^k)) (glueBall_converges (a*q+b))
  | denom k a b =>
    have hb := QBall.Converges.add (glueBall_converges (a*q+b)) (glueBall_converges (1-(a*q+b)))
    have hd : (1/9 : ℚ) > 0 := by norm_num
    have he : (1/9 : ℝ) ≤ expNegInvGlue (a*q+b) + expNegInvGlue (1-(a*q+b)) := transitionDen_ge _
    simpa [enclose, val, denomPower, transitionDen] using
      QBall.Converges.pow (QBall.Converges.invLower hb hd (by simpa using he)) k
  | add f g hf hg => exact QBall.Converges.add hf hg
  | mul f g hf hg => exact QBall.Converges.mul hf hg

end ProfileExpr
end ShearFlows

end

end OAI
