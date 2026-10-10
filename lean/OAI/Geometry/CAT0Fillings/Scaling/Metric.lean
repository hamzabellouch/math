import Mathlib
import OAI.Geometry.CAT0Fillings.Rearrangement.Inverse

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open RadialSobolev

lemma power_mul_dimension {n : ℕ} (hn : 0 < n) : (n:ℝ)*fillingPower n = n+1 := by
  unfold fillingPower
  field [Nat.cast_ne_zero.mpr hn.ne']
lemma fillingPower_gt_one {n : ℕ} (hn : 0 < n) : 1 < fillingPower n := by
  unfold fillingPower
  exact (lt_div_iff₀ (Nat.cast_pos.mpr hn)).mpr (by linarith)
lemma normalized_scale {n : ℕ} (hn : 0 < n) {m c : ℝ} (hm : 0 < m)
    (hc : fillingCoefficient n < c) :
    ∃ l : ℝ, 0 < l ∧ 0 < l^n*m ∧ l^n*m < sphereArea n ∧
      c*fillingPower n*(l^n*m)^(fillingPower n-1) = 1/(n:ℝ) := by
  have hn0 : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hnp : 0 < (n+1:ℝ) := by positivity
  have hs : 0 < sphereArea n := mul_pos hnp (omega_pos (by omega))
  have hc0 := (fillingCoefficient_pos hn).trans hc
  let r := 1/((n+1:ℝ)*c)
  have hr : 0 < r := by dsimp [r]; positivity
  have hroot : r < (sphereArea n)^(1/(n:ℝ)) := by
    apply (div_lt_iff₀ (mul_pos hnp hc0)).mpr
    have h := (div_lt_iff₀ (mul_pos hnp (Real.rpow_pos_of_pos hs _))).mp hc
    nlinarith
  have hsr : ((sphereArea n)^(1/(n:ℝ)))^n = sphereArea n := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hs.le,one_div_mul_cancel hn0.ne',Real.rpow_one]
  have hM : r^n < sphereArea n := by
    rw [←hsr]
    exact pow_lt_pow_left₀ hroot hr.le (by omega)
  have hp : fillingPower n-1 = 1/(n:ℝ) := by
    unfold fillingPower
    field [hn0.ne']
  have hMr : (r^n)^(1/(n:ℝ)) = r := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le,mul_one_div_cancel hn0.ne',Real.rpow_one]
  let l := (r^n/m)^(1/(n:ℝ))
  have hl : 0 < l := Real.rpow_pos_of_pos (div_pos (pow_pos hr _) hm) _
  have hmass : l^n*m = r^n := by
    dsimp [l]
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ r^n/m),
      one_div_mul_cancel hn0.ne',Real.rpow_one,div_mul_cancel₀ _ hm.ne']
  refine ⟨l,hl,by rw [hmass]; positivity,by rwa [hmass],?_⟩
  rw [hmass,hp,hMr]
  dsimp [r,fillingPower]
  field [hn0.ne',hc0.ne']
end CAT0Fillings
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings

def ScaledSpace (X : Type*) (_c : ℝ≥0) := X
namespace ScaledSpace
variable {X : Type*} [m : MetricSpace X] (c : ℝ≥0) [NeZero c]
instance : TopologicalSpace (ScaledSpace X c) := inferInstanceAs (TopologicalSpace X)
instance [MeasurableSpace X] : MeasurableSpace (ScaledSpace X c) := inferInstanceAs (MeasurableSpace X)
def toBase (x : ScaledSpace X c) : X := x
def ofBase (x : X) : ScaledSpace X c := x
omit m [NeZero c] in
lemma to_of (x : X) : toBase c (ofBase c x) = x := rfl
omit m [NeZero c] in
lemma of_to (x : ScaledSpace X c) : ofBase c (toBase c x) = x := rfl
noncomputable instance : MetricSpace (ScaledSpace X c) :=
  MetricSpace.ofDistTopology
    (fun x y : ScaledSpace X c => (c:ℝ)*dist (toBase c x) (toBase c y))
    (by intro x; simp)
    (by intro x y; rw [dist_comm])
    (by intro x y z; simpa only [mul_add] using mul_le_mul_of_nonneg_left (dist_triangle (toBase c x) (toBase c y) (toBase c z)) c.coe_nonneg)
    (by
      have hc : 0 < (c:ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero (NeZero.ne c))
      intro s
      change @IsOpen X inferInstance (fun x => ofBase c x ∈ s) ↔ _
      have ho := @Metric.isOpen_iff X m.toPseudoMetricSpace (fun x => ofBase c x ∈ s)
      apply ho.trans
      constructor
      · intro hs x hx
        obtain ⟨e,he,hb⟩ := hs (toBase c x) hx
        refine ⟨c*e,mul_pos hc he,fun y hy => hb (a := toBase c y) ?_⟩
        rw [mem_ball,dist_comm]
        exact (mul_lt_mul_iff_right₀ hc).mp hy
      · intro hs x hx
        obtain ⟨e,he,hb⟩ := hs (ofBase c x) hx
        refine ⟨e/c,div_pos he hc,fun y hy => hb (ofBase c y) ?_⟩
        change (c:ℝ)*dist x y < e
        rw [mem_ball,dist_comm] at hy
        simpa only [mul_comm] using (lt_div_iff₀ hc).mp hy)
    (by
      intro x y h
      have he := dist_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (NNReal.coe_ne_zero.mpr (NeZero.ne c)))
      exact congrArg (ofBase c) he)
instance [CompactSpace X] : CompactSpace (ScaledSpace X c) := inferInstanceAs (CompactSpace X)
instance [Nonempty X] : Nonempty (ScaledSpace X c) := inferInstanceAs (Nonempty X)
instance [MeasurableSpace X] [BorelSpace X] : BorelSpace (ScaledSpace X c) := inferInstanceAs (BorelSpace X)
lemma dist_eq (x y : ScaledSpace X c) : dist x y = (c:ℝ)*dist (toBase c x) (toBase c y) := rfl
lemma up_lipschitz : LipschitzWith c (ofBase (X := X) c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact le_rfl
lemma down_lipschitz : LipschitzWith c⁻¹ (toBase (X := X) c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq,NNReal.coe_inv]
  have hc : (c:ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (NeZero.ne c)
  rw [←mul_assoc,inv_mul_cancel₀ hc,one_mul]

lemma isCAT0 (hX : IsCAT0 X) : IsCAT0 (ScaledSpace X c) := by
  obtain ⟨s,he,hs,hc⟩ := hX
  refine ⟨fun x y t => ofBase c (s (toBase c x) (toBase c y) t),?_,?_,?_⟩
  · intro x y
    exact ⟨congrArg (ofBase c) (he (toBase c x) (toBase c y)).1,
      congrArg (ofBase c) (he (toBase c x) (toBase c y)).2⟩
  · intro x y u v hu hv
    simp only [dist_eq,to_of]
    rw [hs (toBase c x) (toBase c y) u v hu hv]
    ring
  · intro o x y u v hu hv
    have h := mul_le_mul_of_nonneg_left (hc (toBase c o) (toBase c x) (toBase c y) u v hu hv) (sq_nonneg (c:ℝ))
    simp only [dist_eq,to_of]
    convert h using 1 <;> first | rfl | ring
end ScaledSpace
end CAT0Fillings
end

end OAI
