import OAI.Analysis.CoulombTransport.Model

namespace OAI

universe uE uA

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.CoulombEstimates

/-- The reciprocal is uniformly Lipschitz away from zero. -/
theorem abs_inv_sub_inv_le {a b eta L : ℝ}
    (heta : 0 < eta) (ha : eta ≤ a) (hb : eta ≤ b)
    (hL : |a - b| ≤ L) :
    |a⁻¹ - b⁻¹| ≤ L / eta ^ 2 := by
  have ha0 : 0 < a := heta.trans_le ha
  have hb0 : 0 < b := heta.trans_le hb
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL
  have hab : eta ^ 2 ≤ a * b := by
    nlinarith [mul_le_mul ha hb (le_of_lt heta) (le_of_lt ha0)]
  have heq : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm]
  exact (div_le_div_of_nonneg_right hL (le_of_lt (mul_pos ha0 hb0))).trans
    (div_le_div_of_nonneg_left hL0 (sq_pos_of_pos heta) hab)

/-- Moving both endpoints by at most `delta` changes distance by at most `2 * delta`. -/
theorem abs_dist_sub_dist_le {E : Type uE} [PseudoMetricSpace E]
    {x y x' y' : E} {delta : ℝ}
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) :
    |dist x y - dist x' y'| ≤ 2 * delta := by
  have h := abs_dist_sub_le x x' y
  have h' := abs_dist_sub_le y y' x'
  calc
    |dist x y - dist x' y'| ≤
        |dist x y - dist x' y| + |dist x' y - dist x' y'| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le (dist x y - dist x' y) (dist x' y - dist x' y')
    _ ≤ dist x x' + dist y y' := by
      exact add_le_add h (by simpa only [dist_comm] using h')
    _ ≤ 2 * delta := by linarith

/-- Coulomb pair interaction has a quantitative oscillation estimate on separated products. -/
theorem abs_inv_dist_sub_inv_dist_le {E : Type uE} [PseudoMetricSpace E]
    {x y x' y' : E} {eta delta : ℝ}
    (heta : 0 < eta) (hxy : eta ≤ dist x y) (hxy' : eta ≤ dist x' y')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) :
    |(dist x y)⁻¹ - (dist x' y')⁻¹| ≤ (2 * delta) / eta ^ 2 :=
  abs_inv_sub_inv_le heta hxy hxy' (abs_dist_sub_dist_le hx hy)

/-- Real-valued three-particle Coulomb cost on an arbitrary metric space. -/
def realCost {E : Type uE} [PseudoMetricSpace E] (x y z : E) : ℝ :=
  (dist x y)⁻¹ + (dist x z)⁻¹ + (dist y z)⁻¹

/-- Uniform boundedness of the Coulomb cost on a separated triple. -/
theorem realCost_le {E : Type uE} [PseudoMetricSpace E]
    {x y z : E} {eta : ℝ} (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z) :
    realCost x y z ≤ 3 / eta := by
  have h1 := one_div_le_one_div_of_le heta hxy
  have h2 := one_div_le_one_div_of_le heta hxz
  have h3 := one_div_le_one_div_of_le heta hyz
  simp only [one_div] at h1 h2 h3
  unfold realCost
  rw [div_eq_mul_inv]
  linarith

/-- Oscillation of the three-particle Coulomb cost on separated, small cells. -/
theorem abs_realCost_sub_realCost_le {E : Type uE} [PseudoMetricSpace E]
    {x y z x' y' z' : E} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    |realCost x y z - realCost x' y' z'| ≤ (6 * delta) / eta ^ 2 := by
  have h1 := abs_inv_dist_sub_inv_dist_le heta hxy hxy' hx hy
  have h2 := abs_inv_dist_sub_inv_dist_le heta hxz hxz' hx hz
  have h3 := abs_inv_dist_sub_inv_dist_le heta hyz hyz' hy hz
  have habs : |realCost x y z - realCost x' y' z'| ≤
      |(dist x y)⁻¹ - (dist x' y')⁻¹| +
      |(dist x z)⁻¹ - (dist x' z')⁻¹| +
      |(dist y z)⁻¹ - (dist y' z')⁻¹| := by
    unfold realCost
    calc
      _ = |((dist x y)⁻¹ - (dist x' y')⁻¹) +
          ((dist x z)⁻¹ - (dist x' z')⁻¹) +
          ((dist y z)⁻¹ - (dist y' z')⁻¹)| := by congr 1; ring
      _ ≤ _ := abs_add_three _ _ _
  calc
    _ ≤ _ := habs
    _ ≤ (2 * delta) / eta ^ 2 + (2 * delta) / eta ^ 2 +
        (2 * delta) / eta ^ 2 := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- The real formula agrees with the extended-valued cost away from collisions. -/
theorem coulombCost_eq_ofReal_realCost {x y z : E3}
    (hxy : 0 < dist x y) (hxz : 0 < dist x z) (hyz : 0 < dist y z) :
    coulombCost (x, (y, z)) = ENNReal.ofReal (realCost x y z) := by
  unfold realCost
  rw [ENNReal.ofReal_add (add_nonneg (inv_nonneg.mpr dist_nonneg)
        (inv_nonneg.mpr dist_nonneg)) (inv_nonneg.mpr dist_nonneg),
    ENNReal.ofReal_add (inv_nonneg.mpr dist_nonneg) (inv_nonneg.mpr dist_nonneg),
    ENNReal.ofReal_inv_of_pos hxy, ENNReal.ofReal_inv_of_pos hxz,
    ENNReal.ofReal_inv_of_pos hyz]
  rfl

/-- The exact extended-valued Coulomb cost is uniformly bounded on separated triples. -/
theorem coulombCost_le_of_separated {x y z : E3} {eta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z) :
    coulombCost (x, (y, z)) ≤ ENNReal.ofReal (3 / eta) := by
  rw [coulombCost_eq_ofReal_realCost (heta.trans_le hxy)
    (heta.trans_le hxz) (heta.trans_le hyz)]
  exact ENNReal.ofReal_le_ofReal (realCost_le heta hxy hxz hyz)

/-- Separated triples have finite Coulomb cost. -/
theorem coulombCost_lt_top_of_separated {x y z : E3} {eta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z) :
    coulombCost (x, (y, z)) < ⊤ :=
  (coulombCost_le_of_separated heta hxy hxz hyz).trans_lt ENNReal.ofReal_lt_top

/-- One-sided extended-valued oscillation bound, suitable for lower integrals. -/
theorem coulombCost_le_add_of_separated {x y z x' y' z' : E3} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    coulombCost (x, (y, z)) ≤ coulombCost (x', (y', z')) +
      ENNReal.ofReal ((6 * delta) / eta ^ 2) := by
  have hdelta : 0 ≤ delta := dist_nonneg.trans hx
  have hcost : 0 ≤ realCost x' y' z' := by unfold realCost; positivity
  have herr : 0 ≤ (6 * delta) / eta ^ 2 := by positivity
  have h := (abs_sub_le_iff.mp (abs_realCost_sub_realCost_le heta
    hxy hxz hyz hxy' hxz' hyz' hx hy hz)).1
  have hle : realCost x y z ≤ realCost x' y' z' + (6 * delta) / eta ^ 2 := by
    linarith
  rw [coulombCost_eq_ofReal_realCost (heta.trans_le hxy)
      (heta.trans_le hxz) (heta.trans_le hyz),
    coulombCost_eq_ofReal_realCost (heta.trans_le hxy')
      (heta.trans_le hxz') (heta.trans_le hyz'),
    ← ENNReal.ofReal_add hcost herr]
  exact ENNReal.ofReal_le_ofReal hle

/-- Pairwise separation of the coordinates of a triple. -/
def Separated (eta : ℝ) (t : Triple) : Prop :=
  eta ≤ dist t.1 t.2.1 ∧ eta ≤ dist t.1 t.2.2 ∧ eta ≤ dist t.2.1 t.2.2

/-- A lower-integral bound requiring only almost-everywhere separation. -/
theorem lintegral_coulombCost_le_of_ae_separated (mu : Measure Triple) {eta : ℝ}
    (heta : 0 < eta) (hsep : ∀ᵐ t ∂mu, Separated eta t) :
    (∫⁻ t, coulombCost t ∂mu) ≤ ENNReal.ofReal (3 / eta) * mu Set.univ := by
  calc
    _ ≤ ∫⁻ _t : Triple, ENNReal.ofReal (3 / eta) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hsep] with t ht
      rcases t with ⟨x, y, z⟩
      exact coulombCost_le_of_separated heta ht.1 ht.2.1 ht.2.2
    _ = _ := lintegral_const _

/-- On finite measures, almost-everywhere separation guarantees finite cost. -/
theorem lintegral_coulombCost_lt_top_of_ae_separated (mu : Measure Triple)
    [IsFiniteMeasure mu] {eta : ℝ}
    (heta : 0 < eta) (hsep : ∀ᵐ t ∂mu, Separated eta t) :
    (∫⁻ t, coulombCost t ∂mu) < ⊤ :=
  (lintegral_coulombCost_le_of_ae_separated mu heta hsep).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top mu Set.univ))

/-- A uniform graph-cost bound; no regularity of the maps is needed for this bound. -/
theorem graphCost_le_of_ae_separated (mu : Measure E3) {T2 T3 : E3 → E3} {eta : ℝ}
    (heta : 0 < eta) (hsep : ∀ᵐ x ∂mu, Separated eta (x, (T2 x, T3 x))) :
    graphCost mu T2 T3 ≤ ENNReal.ofReal (3 / eta) * mu Set.univ := by
  unfold graphCost
  calc
    _ ≤ ∫⁻ _x : E3, ENNReal.ofReal (3 / eta) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hsep] with x hx
      exact coulombCost_le_of_separated heta hx.1 hx.2.1 hx.2.2
    _ = _ := lintegral_const _

/-- The finite-cost condition in finite Monge approximation follows from separation. -/
theorem graphCost_lt_top_of_ae_separated (mu : Measure E3) [IsFiniteMeasure mu]
    {T2 T3 : E3 → E3} {eta : ℝ}
    (heta : 0 < eta) (hsep : ∀ᵐ x ∂mu, Separated eta (x, (T2 x, T3 x))) :
    graphCost mu T2 T3 < ⊤ :=
  (graphCost_le_of_ae_separated mu heta hsep).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top mu Set.univ))

/-- Integrating the pointwise oscillation bound under a common parametrization. -/
theorem lintegral_coulombCost_le_add_of_ae_close
    {A : Type uA} [MeasurableSpace A] (mu : Measure A) {P Q : A → Triple} {eta delta : ℝ}
    (heta : 0 < eta)
    (hsepP : ∀ᵐ a ∂mu, Separated eta (P a))
    (hsepQ : ∀ᵐ a ∂mu, Separated eta (Q a))
    (hclose : ∀ᵐ a ∂mu, dist (P a).1 (Q a).1 ≤ delta ∧
      dist (P a).2.1 (Q a).2.1 ≤ delta ∧ dist (P a).2.2 (Q a).2.2 ≤ delta) :
    (∫⁻ a, coulombCost (P a) ∂mu) ≤ (∫⁻ a, coulombCost (Q a) ∂mu) +
      ENNReal.ofReal ((6 * delta) / eta ^ 2) * mu Set.univ := by
  calc
    _ ≤ ∫⁻ a, coulombCost (Q a) + ENNReal.ofReal ((6 * delta) / eta ^ 2) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hsepP, hsepQ, hclose] with a hP hQ hc
      exact coulombCost_le_add_of_separated heta hP.1 hP.2.1 hP.2.2
        hQ.1 hQ.2.1 hQ.2.2 hc.1 hc.2.1 hc.2.2
    _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const]

end Problem356.CoulombEstimates

end

end OAI
