import OAI.Analysis.DiamondDistortion.Transfers

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Diamond
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma old_upper {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ} (f : Vertex (k+1) → X) {L : ℝ}
    (hu : ∀ u v,‖f u-f v‖ ≤ L*distance (k+1) u v) :
    ∀ u v,‖f (Sum.inl u)-f (Sum.inl v)‖ ≤ L*distance k u v := by
  intro u v
  simpa only [distance_old] using hu (Sum.inl u) (Sum.inl v)

def FixedBoundGain (X : Type*) [NormedAddCommGroup X] (D c : ℝ) : Prop :=
  ∀ (x : X) (z : ℕ → X),1 ≤ ‖x‖ → ‖x‖ ≤ D →
    (∀ i,‖z i‖ ≤ 2*D) → (∀ i j,i ≠ j → 1 ≤ ‖z i-z j‖) →
    ∃ i,‖x‖+c < max ‖x+z i‖ ‖x-z i‖

lemma actual_additive_growth {D c : ℝ} (hD : 1 ≤ D) (hX : FixedBoundGain X D c)
    (k : ℕ) (f : Vertex k → X)
    (hl : ∀ u v,1*distance k u v ≤ ‖f u-f v‖)
    (hu : ∀ u v,‖f u-f v‖ ≤ D*distance k u v) :
    ∃ e : Edge k,1+(k:ℝ)*c ≤ ‖slope f e‖ ∧
      (k ≠ 0 → 1+(k:ℝ)*c < ‖slope f e‖) := by
  induction k with
  | zero => exact ⟨(),by simpa using slope_lower f hl (),by simp⟩
  | succ n ih =>
    obtain ⟨e,he,_⟩ := ih (fun v => f (Sum.inl v)) (old_lower f hl) (old_upper f hu)
    have hx := slope_lower (fun v => f (Sum.inl v)) (old_lower f hl) e
    have hxD := slope_upper (fun v => f (Sum.inl v)) (old_upper f hu) e
    have hp : ∀ i,‖slope (fun v => f (Sum.inl v)) e+deviation f e i‖ ≤ D := by
      intro i
      rw [slope_plus_deviation]
      exact slope_upper f hu _
    have hm : ∀ i,‖slope (fun v => f (Sum.inl v)) e-deviation f e i‖ ≤ D := by
      intro i
      rw [slope_minus_deviation]
      exact slope_upper f hu _
    have hd : ∀ i,‖deviation f e i‖ ≤ 2*D := by
      intro i
      have h := norm_deviation_le (hp i) (hm i)
      linarith
    have hs : ∀ i j,i ≠ j → 1 ≤ ‖deviation f e i-deviation f e j‖ := by
      intro i j hij
      have h := deviation_separated f hl e hij
      linarith
    obtain ⟨i,hi⟩ := hX _ (deviation f e) hx hxD hd hs
    rcases lt_max_iff.mp hi with hi | hi
    · rw [slope_plus_deviation] at hi
      have hh : 1+((n+1:ℕ):ℝ)*c < ‖slope f (e,i,false)‖ := by push_cast; linarith
      exact ⟨(e,i,false),hh.le,fun _ => hh⟩
    · rw [slope_minus_deviation] at hi
      have hh : 1+((n+1:ℕ):ℝ)*c < ‖slope f (e,i,true)‖ := by push_cast; linarith
      exact ⟨(e,i,true),hh.le,fun _ => hh⟩

theorem fixed_bound {D c s : ℝ} (_hc : 0 < c) (hX : FixedBoundGain X D c)
    (k : ℕ) (f : Vertex k → X) (hf : HasDistortion k f D s) :
    1+(k:ℝ)*c ≤ D ∧ (k ≠ 0 → 1+(k:ℝ)*c < D) := by
  obtain ⟨hD,_,h⟩ := normalized_distortion f hf
  have hu : ∀ u v,‖s⁻¹ • f u-s⁻¹ • f v‖ ≤ D*distance k u v := by
    intro u v
    simpa only [mul_one] using (h u v).2
  obtain ⟨e,he,he'⟩ := actual_additive_growth hD hX k (fun v => s⁻¹ • f v)
    (fun u v => (h u v).1) hu
  have hb := slope_upper (fun v => s⁻¹ • f v) hu e
  exact ⟨he.trans hb,fun hk => (he' hk).trans_le hb⟩

/-- The unconditional segment lens supplies the fixed-distortion bounded-family
    input as well, with a concrete positive choice of c_D. -/
lemma fixed_bound_of_quadratic {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (hX : QuadraticLens X) {D : ℝ} (hD : 1 ≤ D) :
    FixedBoundGain X D (1/(64*D)) := by
  have hD0 : 0 < D := by linarith
  let c : ℝ := 1/(64*D)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcD : D*c=1/64 := by dsimp [c]; field_simp
  have hcsmall : c ≤ 1/64 := by
    have h := mul_le_mul_of_nonneg_right hD hc.le
    nlinarith
  intro x z hx hxD hz hs
  by_contra! hn
  have hp : ∀ i,‖x+z i‖ ≤ ‖x‖+c := fun i => (le_max_left _ _).trans (hn i)
  have hm : ∀ i,‖x-z i‖ ≤ ‖x‖+c := fun i => (le_max_right _ _).trans (hn i)
  have h := hX x z (‖x‖+c) 1 (by positivity) (by norm_num) hp hm hs
  have hmul := mul_le_mul_of_nonneg_right hxD hc.le
  have hsq := (sq_le_sq₀ hc.le (by norm_num : (0:ℝ) ≤ 1/64)).mpr hcsmall
  nlinarith

/-- Uniform distortion means one finite constant, with a separate map and a
    separate positive scale for each depth. -/
def UniformEmbeddings (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ D : ℝ,∀ k : ℕ,∃ (f : Vertex k → X) (s : ℝ),HasDistortion k f D s

end Diamond

theorem atomic_distortion (k : ℕ) (f : Diamond.Vertex k → ForestDual) (D s : ℝ)
    (hf : Diamond.HasDistortion k f D s) : 1+(k:ℝ)/16 ≤ D^2 := by
  have h := headline.1 k f D s hf
  have hk : (0:ℝ) ≤ k := by positivity
  linarith

theorem direct_atomic_obstruction : ¬ Diamond.UniformEmbeddings ForestDual := by
  rintro ⟨D,h⟩
  obtain ⟨k,hk⟩ := exists_nat_gt (4*D^2)
  obtain ⟨f,s,hf⟩ := h k
  have hb := headline.1 k f D s hf
  linarith

theorem infinite_obstruction : ¬ Diamond.UniformEmbeddings InfinitePredual := by
  rintro ⟨D,h⟩
  obtain ⟨k,hk⟩ := exists_nat_gt (4*D^2)
  obtain ⟨f,s,hf⟩ := h k
  have hb := headline.2 k f D s hf
  linarith

end DiamondDistortion

end

end OAI
