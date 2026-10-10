import OAI.MathematicalPhysics.RapidForcing.RationalProfiles

namespace OAI

section

open scoped BigOperators Topology
open Set Filter
namespace RapidForcing.EffectiveProfile

def Expr.approx (e : Expr) (q ε : ℚ) : Part Ball :=
  Nat.rfindOpt fun k => if (e.numeric q k).radius ≤ ε then some (e.numeric q k) else none

lemma Expr.approx_spec (e : Expr) (q ε : ℚ) {b : Ball} (hb : b ∈ e.approx q ε) :
    b.Covers (e.value q) ∧ b.radius ≤ ε := by
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hb
  split_ifs at hk with hk'
  · have heq : b = e.numeric q k := (Option.mem_some_iff.mp hk).symm
    subst b
    exact ⟨(e.numeric_encloses q).1 k, hk'⟩
  · cases hk

lemma Expr.approx_dom (e : Expr) (q ε : ℚ) (hε : 0 < ε) : (e.approx q ε).Dom := by
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨k, hk⟩ := ((e.numeric_encloses q).2.eventually (Iio_mem_nhds hε')).exists
  have hk' : (e.numeric q k).radius ≤ ε := by exact_mod_cast hk.le
  apply Nat.rfindOpt_dom.mpr
  exact ⟨k, e.numeric q k, by simp [hk']⟩

inductive Formula (d : ℕ) where
  | const : ℚ → Formula d
  | var : Fin d → Formula d
  | add : Formula d → Formula d → Formula d
  | mul : Formula d → Formula d → Formula d
  | profile : Expr → Formula d → Formula d

namespace Formula
variable {d : ℕ}

noncomputable def value : Formula d → (Fin d → ℝ) → ℝ
  | .const q, _ => q
  | .var i, x => x i
  | .add a b, x => a.value x + b.value x
  | .mul a b, x => a.value x * b.value x
  | .profile e a, x => e.value (a.value x)

def neg (a : Formula d) : Formula d := .mul (.const (-1)) a

def sub (a b : Formula d) : Formula d := .add a b.neg

@[simp] lemma value_neg (a : Formula d) (x : Fin d → ℝ) :
    a.neg.value x = -a.value x := by simp [neg, value]
@[simp] lemma value_sub (a b : Formula d) (x : Fin d → ℝ) :
    (a.sub b).value x = a.value x - b.value x := by simp [sub, value, sub_eq_add_neg]

def bound (R : ℚ) : Formula d → ℚ
  | .const q => |q|
  | .var _ => |R|
  | .add a b => a.bound R + b.bound R
  | .mul a b => a.bound R * b.bound R
  | .profile e _ => e.bound

lemma bound_nonneg (a : Formula d) (R : ℚ) : 0 ≤ a.bound R := by
  induction a with
  | const q => exact abs_nonneg _
  | var i => exact abs_nonneg _
  | add a b ha hb => exact add_nonneg ha hb
  | mul a b ha hb => exact mul_nonneg ha hb
  | profile e a ha => exact e.bound_nonneg

lemma abs_value_le (a : Formula d) (R : ℚ) (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ |(R : ℝ)|) : |a.value x| ≤ (a.bound R : ℝ) := by
  induction a with
  | const q => simp [value, bound]
  | var i => simpa [value, bound] using hx i
  | add a b ha hb =>
    exact (abs_add_le _ _).trans (by simpa [bound] using add_le_add ha hb)
  | mul a b ha hb =>
    simpa [value, bound, abs_mul] using mul_le_mul ha hb (abs_nonneg _)
      (show (0 : ℝ) ≤ a.bound R by exact_mod_cast a.bound_nonneg R)
  | profile e a ha => exact e.abs_value_le _

def diff (i : Fin d) : Formula d → Formula d
  | .const _ => .const 0
  | .var j => .const (if j = i then 1 else 0)
  | .add a b => .add (a.diff i) (b.diff i)
  | .mul a b => .add (.mul (a.diff i) b) (.mul a (b.diff i))
  | .profile e a => .mul (.profile e.diff a) (a.diff i)

lemma contDiff (a : Formula d) : ContDiff ℝ (⊤ : ℕ∞) a.value := by
  induction a with
  | const q => exact contDiff_const
  | var i => exact contDiff_apply ℝ ℝ i
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | profile e a ha => exact e.contDiff.comp ha

lemma hasDerivAt_line (a : Formula d) (i : Fin d) (x : Fin d → ℝ) (t : ℝ) :
    HasDerivAt (fun s => a.value (x + s • Pi.single i (1 : ℝ)))
      ((a.diff i).value (x + t • Pi.single i 1)) t := by
  induction a with
  | const q => simpa [diff, value] using hasDerivAt_const t (q : ℝ)
  | var j =>
    by_cases h : j = i
    · subst j
      simpa [diff, value, Pi.single_apply] using (hasDerivAt_id t).const_add (x i)
    · simpa [diff, value, Pi.single_apply, h, Ne.symm h] using hasDerivAt_const t (x j)
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | profile e a ha => exact (e.hasDerivAt _).comp t ha

lemma fderiv_apply_single (a : Formula d) (i : Fin d) (x : Fin d → ℝ) :
    fderiv ℝ a.value x (Pi.single i 1) = (a.diff i).value x := by
  have hline : HasDerivAt (fun s : ℝ => x + s • Pi.single i (1 : ℝ))
      (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ))).const_add x
  have hf : HasFDerivAt a.value (fderiv ℝ a.value x) (x + (0 : ℝ) • Pi.single i 1) := by
    simpa using (a.contDiff.differentiable (by simp) x).hasFDerivAt
  have h := hf.comp_hasDerivAt 0 hline
  simpa using h.unique (a.hasDerivAt_line i x 0)

def evalAt (a : Formula d) (q : Fin d → ℚ) (ε : ℚ) : Part Ball :=
  match a with
  | .const r => Part.some (Ball.exact r)
  | .var i => Part.some (Ball.exact (q i))
  | .add a b => do
      let u ← a.evalAt q (ε / 2)
      let v ← b.evalAt q (ε / 2)
      pure (u.add v)
  | .mul a b =>
      let R := 1 + ∑ i, |q i|
      let η := min 1 (ε / (4 * (a.bound R + b.bound R + 2)))
      do
        let u ← a.evalAt q η
        let v ← b.evalAt q η
        pure (u.mul v)
  | .profile e a => do
      let u ← a.evalAt q (ε / (2 * (e.diff.bound + 1)))
      let v ← e.approx u.center (ε / 2)
      pure ⟨v.center, v.radius + e.diff.bound * u.radius⟩

lemma Ball.Covers.center_le {a : Ball} {x : ℝ} (h : a.Covers x) {B : ℚ}
    (hB : |x| ≤ (B : ℝ)) : |a.center| ≤ B + a.radius := by
  have he : |(a.center : ℝ)| ≤ (B : ℝ) + a.radius := by
    calc
      _ ≤ |(a.center : ℝ) - x| + |x| := by simpa using abs_sub_le (a.center : ℝ) x 0
      _ ≤ (a.radius : ℝ) + B := add_le_add h hB
      _ = _ := by ring
  exact_mod_cast he

lemma numeric_operand_bound (a : Formula d) (q : Fin d → ℚ) :
    |a.value (fun i => q i)| ≤ (a.bound (1 + ∑ i, |q i|) : ℝ) := by
  apply a.abs_value_le
  intro i
  have h : |q i| ≤ 1 + ∑ j, |q j| := by
    have := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => abs_nonneg (q j))
      (Finset.mem_univ i)
    linarith
  have hp : (0 : ℚ) ≤ 1 + ∑ j, |q j| := by positivity
  exact_mod_cast (show |q i| ≤ |1 + (∑ j, |q j|)| by simpa [abs_of_nonneg hp] using h)

lemma evalAt_spec (a : Formula d) (q : Fin d → ℚ) (ε : ℚ) (hε : 0 < ε)
    {r : Ball} (hr : r ∈ a.evalAt q ε) :
    r.Covers (a.value (fun i => q i)) ∧ r.radius ≤ ε := by
  induction a generalizing ε r with
  | const c =>
    have he : r = Ball.exact c := Part.mem_some_iff.mp hr
    subst r
    exact ⟨Ball.covers_exact c, hε.le⟩
  | var i =>
    have he : r = Ball.exact (q i) := Part.mem_some_iff.mp hr
    subst r
    exact ⟨Ball.covers_exact _, hε.le⟩
  | add a b ha hb =>
    obtain ⟨u, hu, hrest⟩ := Part.mem_bind_iff.mp hr
    obtain ⟨v, hv, hr⟩ := Part.mem_bind_iff.mp hrest
    have he : r = u.add v := Part.mem_some_iff.mp hr
    subst r
    obtain ⟨hu, hu'⟩ := ha _ (by positivity) hu
    obtain ⟨hv, hv'⟩ := hb _ (by positivity) hv
    refine ⟨hu.add hv, ?_⟩
    change u.radius + v.radius ≤ ε
    linarith
  | mul a b ha hb =>
    let R : ℚ := 1 + ∑ i, |q i|
    let B : ℚ := a.bound R + b.bound R + 2
    let η : ℚ := min 1 (ε / (4 * B))
    have hB : 0 < B := by dsimp [B]; linarith [a.bound_nonneg R, b.bound_nonneg R]
    have hη : 0 < η := lt_min (by norm_num) (by positivity)
    obtain ⟨u, hu, hrest⟩ := Part.mem_bind_iff.mp hr
    obtain ⟨v, hv, hr⟩ := Part.mem_bind_iff.mp hrest
    have he : r = u.mul v := Part.mem_some_iff.mp hr
    subst r
    obtain ⟨hu, hu'⟩ := ha _ hη hu
    obtain ⟨hv, hv'⟩ := hb _ hη hv
    have huc := Ball.Covers.center_le hu (a.numeric_operand_bound q)
    have hvc := Ball.Covers.center_le hv (b.numeric_operand_bound q)
    have hu0 := hu.radius_nonneg
    have hv0 := hv.radius_nonneg
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηε : η * (4 * B) ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have huc' : |u.center| ≤ a.bound R + 1 := by
      change |u.center| ≤ a.bound R + u.radius at huc
      linarith
    have hvc' : |v.center| ≤ b.bound R + 1 := by
      change |v.center| ≤ b.bound R + v.radius at hvc
      linarith
    have hB0 : 0 ≤ b.bound R + 1 := by linarith [b.bound_nonneg R]
    have hA0 : 0 ≤ a.bound R + 1 := by linarith [a.bound_nonneg R]
    refine ⟨hu.mul hv, ?_⟩
    change |u.center| * v.radius + |v.center| * u.radius + u.radius * v.radius ≤ ε
    calc
      _ ≤ (a.bound R + 1) * η + (b.bound R + 1) * η + η * η := by
        gcongr
      _ ≤ (a.bound R + b.bound R + 3) * η := by nlinarith
      _ ≤ (4 * B) * η := by
        apply mul_le_mul_of_nonneg_right _ hη.le
        dsimp [B]
        linarith [a.bound_nonneg R, b.bound_nonneg R]
      _ ≤ ε := by simpa [mul_comm] using hηε
  | profile e a ha =>
    obtain ⟨u, hu, hrest⟩ := Part.mem_bind_iff.mp hr
    obtain ⟨v, hv, hr⟩ := Part.mem_bind_iff.mp hrest
    have he : r = ⟨v.center, v.radius + e.diff.bound * u.radius⟩ := Part.mem_some_iff.mp hr
    subst r
    have hL : 0 < 2 * (e.diff.bound + 1) := by linarith [e.diff.bound_nonneg]
    obtain ⟨hu, hu'⟩ := ha _ (div_pos hε hL) hu
    obtain ⟨hv, hv'⟩ := e.approx_spec _ _ hv
    refine ⟨?_, ?_⟩
    · change |(v.center : ℝ) - e.value (a.value (fun i => q i))| ≤ _
      have hd : |e.value u.center - e.value (a.value (fun i => q i))| ≤
          (e.diff.bound : ℝ) * |(u.center : ℝ) - a.value (fun i => q i)| :=
        e.lipschitz.dist_le_mul _ _
      have he : |e.value u.center - e.value (a.value (fun i => q i))| ≤
          (e.diff.bound : ℝ) * (u.radius : ℝ) :=
        hd.trans (mul_le_mul_of_nonneg_left hu
          (by exact_mod_cast e.diff.bound_nonneg))
      exact (abs_sub_le _ _ _).trans (by simpa using add_le_add hv he)
    · change v.radius + e.diff.bound * u.radius ≤ ε
      have hmul := (le_div_iff₀ hL).mp hu'
      have hu0 := hu.radius_nonneg
      have hL0 := e.diff.bound_nonneg
      nlinarith

lemma evalAt_dom (a : Formula d) (q : Fin d → ℚ) (ε : ℚ) (hε : 0 < ε) :
    (a.evalAt q ε).Dom := by
  induction a generalizing ε with
  | const c => trivial
  | var i => trivial
  | add a b ha hb => exact ⟨ha _ (by positivity), hb _ (by positivity), trivial⟩
  | mul a b ha hb =>
    have hpos : 0 < min 1 (ε / (4 * (a.bound (1 + ∑ i, |q i|) +
        b.bound (1 + ∑ i, |q i|) + 2))) := by
      apply lt_min (by norm_num)
      apply div_pos hε
      have := a.bound_nonneg (1 + ∑ i, |q i|)
      have := b.bound_nonneg (1 + ∑ i, |q i|)
      positivity
    exact ⟨ha _ hpos, hb _ hpos, trivial⟩
  | profile e a ha =>
    have hp : 0 < ε / (2 * (e.diff.bound + 1)) := by
      apply div_pos hε
      have := e.diff.bound_nonneg
      positivity
    refine ⟨ha _ hp, ?_⟩
    exact ⟨e.approx_dom _ _ (by positivity), trivial⟩

end Formula
end RapidForcing.EffectiveProfile

end

end OAI
