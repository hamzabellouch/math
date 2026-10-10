import OAI.Analysis.DiamondDistortion.DiamondGraph

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Diamond
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma norm_center_le {x y : X} {R : ℝ} (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖x‖ ≤ R := by
  have he : x=(1/2:ℝ) • ((x+y)+(x-y)) := by module
  calc
    ‖x‖ = (1/2:ℝ)*‖(x+y)+(x-y)‖ := by
      conv_lhs => rw [he]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    _ ≤ (1/2:ℝ)*(‖x+y‖+‖x-y‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ R := by linarith

lemma norm_deviation_le {x y : X} {R : ℝ} (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖y‖ ≤ R := norm_center_le (x := y) (y := x) (by simpa only [add_comm] using hp)
      (by simpa only [norm_sub_rev] using hm)

lemma slope_lower {k : ℕ} (f : Vertex k → X) {s : ℝ}
    (hl : ∀ u v,s*distance k u v ≤ ‖f u-f v‖) (e : Edge k) : s ≤ ‖slope f e‖ := by
  have he := hl (endpoint k e false) (endpoint k e true)
  rw [distance_edge] at he
  rw [slope,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(2:ℝ)^k),norm_sub_rev]
  calc
    s = (2:ℝ)^k*(s*(1/(2:ℝ)^k)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

lemma slope_upper {k : ℕ} (f : Vertex k → X) {L : ℝ}
    (hu : ∀ u v,‖f u-f v‖ ≤ L*distance k u v) (e : Edge k) : ‖slope f e‖ ≤ L := by
  have he := hu (endpoint k e false) (endpoint k e true)
  rw [distance_edge] at he
  rw [slope,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(2:ℝ)^k),norm_sub_rev]
  calc
    _ ≤ (2:ℝ)^k*(L*(1/(2:ℝ)^k)) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by field_simp

lemma old_lower {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ} (f : Vertex (k+1) → X) {s : ℝ}
    (hl : ∀ u v,s*distance (k+1) u v ≤ ‖f u-f v‖) :
    ∀ u v,s*distance k u v ≤ ‖f (Sum.inl u)-f (Sum.inl v)‖ := by
  intro u v
  simpa only [distance_old] using hl (Sum.inl u) (Sum.inl v)

/-- Abstract multiplicative backward iteration, retaining every all-pairs lower
    bound and making no assertion of an attained stage supremum. -/
lemma iterate_contraction {s D c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hstep : ∀ (x : X) (z : ℕ → X) (R : ℝ),0 ≤ R → R ≤ D → s ≤ ‖x‖ →
      (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
      (∀ i j,i ≠ j → 2*s ≤ ‖z i-z j‖) → ‖x‖ ≤ c*R)
    (k : ℕ) (f : Vertex k → X) {L : ℝ} (hL : 0 ≤ L) (hLD : L ≤ D)
    (hl : ∀ u v,s*distance k u v ≤ ‖f u-f v‖)
    (hb : ∀ e,‖slope f e‖ ≤ L) : s ≤ c^k*L := by
  induction k generalizing L with
  | zero => simpa using (slope_lower f hl ()).trans (hb ())
  | succ n ih =>
    have hold : ∀ e,‖slope (fun v => f (Sum.inl v)) e‖ ≤ c*L := by
      intro e
      apply hstep _ (deviation f e) L hL hLD (slope_lower _ (old_lower f hl) e)
      · intro i
        simpa only [slope_plus_deviation] using hb (e,i,false)
      · intro i
        simpa only [slope_minus_deviation] using hb (e,i,true)
      · exact fun _ _ hij => deviation_separated f hl e hij
    have hcL : c*L ≤ D := (mul_le_of_le_one_left hL hc1).trans hLD
    have h := ih (fun v => f (Sum.inl v)) (mul_nonneg hc hL) hcL (old_lower f hl) hold
    simpa only [pow_succ,mul_assoc] using h

/-- Abstract additive backward iteration. The existence of old edges ensures
    nonnegativity of each improved bound, including the last nonempty stage. -/
lemma iterate_additive {s D δ : ℝ} (hδ : 0 ≤ δ)
    (hstep : ∀ (x : X) (z : ℕ → X) (R : ℝ),0 ≤ R → R ≤ D → s ≤ ‖x‖ →
      (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
      (∀ i j,i ≠ j → 2*s ≤ ‖z i-z j‖) → ‖x‖ ≤ R-δ)
    (k : ℕ) (f : Vertex k → X) {L : ℝ} (hL : 0 ≤ L) (hLD : L ≤ D)
    (hl : ∀ u v,s*distance k u v ≤ ‖f u-f v‖)
    (hb : ∀ e,‖slope f e‖ ≤ L) : s+(k:ℝ)*δ ≤ L := by
  induction k generalizing L with
  | zero => simpa using (slope_lower f hl ()).trans (hb ())
  | succ n ih =>
    have hold : ∀ e,‖slope (fun v => f (Sum.inl v)) e‖ ≤ L-δ := by
      intro e
      apply hstep _ (deviation f e) L hL hLD (slope_lower _ (old_lower f hl) e)
      · intro i
        simpa only [slope_plus_deviation] using hb (e,i,false)
      · intro i
        simpa only [slope_minus_deviation] using hb (e,i,true)
      · exact fun _ _ hij => deviation_separated f hl e hij
    have hnew : 0 ≤ L-δ := (norm_nonneg _).trans (hold (baseEdge n))
    have h := ih (fun v => f (Sum.inl v)) hnew (by linarith) (old_lower f hl) hold
    push_cast
    linarith

def SquareLens (X : Type*) [NormedAddCommGroup X] (b : ℝ) : Prop :=
  ∀ (x : X) (z : ℕ → X) (R ε : ℝ),0 ≤ R → 0 < ε →
    (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
    (∀ i j,i ≠ j → ε ≤ ‖z i-z j‖) → ‖x‖^2+b*ε^2 ≤ R^2

lemma squared_stretch_loss_general {b : ℝ} (hX : SquareLens X b) (k : ℕ) (f : Vertex k → X)
    {s B : ℝ} (hs : 0 < s)
    (hl : ∀ u v,s*distance k u v ≤ ‖f u-f v‖)
    (hb : ∀ e,‖slope f e‖^2 ≤ B) : s^2*(1+4*b*(k:ℝ)) ≤ B := by
  induction k generalizing B with
  | zero =>
    have h := slope_lower f hl ()
    have h0 := hb ()
    norm_num
    nlinarith [sq_nonneg (s-‖slope f ()‖)]
  | succ n ih =>
    have hB : 0 ≤ B := (sq_nonneg _).trans (hb (baseEdge (n+1)))
    have hold : ∀ e,‖slope (fun v => f (Sum.inl v)) e‖^2 ≤ B-4*b*s^2 := by
      intro e
      have hp : ∀ i,‖slope (fun v => f (Sum.inl v)) e+deviation f e i‖ ≤ Real.sqrt B := by
        intro i
        rw [slope_plus_deviation]
        exact (Real.le_sqrt (norm_nonneg _) hB).mpr (hb _)
      have hm : ∀ i,‖slope (fun v => f (Sum.inl v)) e-deviation f e i‖ ≤ Real.sqrt B := by
        intro i
        rw [slope_minus_deviation]
        exact (Real.le_sqrt (norm_nonneg _) hB).mpr (hb _)
      have h := hX (slope (fun v => f (Sum.inl v)) e) (deviation f e)
        (Real.sqrt B) (2*s) (Real.sqrt_nonneg _) (by positivity) hp hm
        (fun _ _ hij => deviation_separated f hl e hij)
      rw [Real.sq_sqrt hB] at h
      nlinarith
    have hind := ih (fun v => f (Sum.inl v)) (old_lower f hl) hold
    push_cast
    nlinarith only [hind]

lemma squared_transfer {b : ℝ} (_hb : 0 < b) (hX : SquareLens X b)
    (k : ℕ) (f : Vertex k → X) (D s : ℝ) (h : HasDistortion k f D s) :
    1+4*b*(k:ℝ) ≤ D^2 := by
  obtain ⟨hD,hs,h⟩ := h
  have hbound : ∀ e,‖slope f e‖^2 ≤ (D*s)^2 := by
    intro e
    have hh := slope_upper f (fun u v => (h u v).2) e
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) hs.le)).mpr hh
  have h' := squared_stretch_loss_general hX k f hs (fun u v => (h u v).1) hbound
  have hp : 0 < s^2 := sq_pos_of_pos hs
  have hmul : s^2*(1+4*b*(k:ℝ)) ≤ s^2*D^2 := by nlinarith only [h']
  exact (mul_le_mul_iff_right₀ hp).mp hmul

lemma normalized_distortion {k : ℕ} (f : Vertex k → X) {D s : ℝ}
    (h : HasDistortion k f D s) :
    HasDistortion k (fun v => s⁻¹ • f v) D 1 := by
  obtain ⟨hD,hs,h⟩ := h
  refine ⟨hD,by norm_num,?_⟩
  intro u v
  rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
  have hl := mul_le_mul_of_nonneg_left (h u v).1 (inv_nonneg.mpr hs.le)
  have hu := mul_le_mul_of_nonneg_left (h u v).2 (inv_nonneg.mpr hs.le)
  have he : s⁻¹*(s*distance k u v)=distance k u v := by field_simp
  have he' : s⁻¹*(D*s*distance k u v)=D*distance k u v := by field_simp
  rw [he] at hl
  rw [he'] at hu
  simpa only [one_mul,mul_one] using And.intro hl hu

lemma upper_one_normalization {k : ℕ} (f : Vertex k → X) {D s : ℝ}
    (h : HasDistortion k f D s) :
    ∀ u v,D⁻¹*distance k u v ≤ ‖(D*s)⁻¹ • f u-(D*s)⁻¹ • f v‖ ∧
      ‖(D*s)⁻¹ • f u-(D*s)⁻¹ • f v‖ ≤ distance k u v := by
  obtain ⟨hD,hs,h⟩ := h
  have hD0 : 0 < D := by linarith
  have hDs : 0 < D*s := mul_pos hD0 hs
  intro u v
  rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hDs.le)]
  have hl := mul_le_mul_of_nonneg_left (h u v).1 (inv_nonneg.mpr hDs.le)
  have hu := mul_le_mul_of_nonneg_left (h u v).2 (inv_nonneg.mpr hDs.le)
  have he : (D*s)⁻¹*(s*distance k u v)=D⁻¹*distance k u v := by field_simp
  have he' : (D*s)⁻¹*(D*s*distance k u v)=distance k u v := by field_simp
  rw [he] at hl
  rw [he'] at hu
  exact ⟨hl,hu⟩

def RadialLens (X : Type*) [NormedAddCommGroup X] (C : ℝ) : Prop :=
  ∀ (x : X) (z : ℕ → X) (R ε : ℝ),0 ≤ R → 0 < ε →
    (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
    (∀ i j,i ≠ j → ε ≤ ‖z i-z j‖) → ε^2/4 ≤ C^2*R*(R-‖x‖)

theorem radial_transfer {C : ℝ} (hC : 0 < C) (hX : RadialLens X C)
    (k : ℕ) (f : Vertex k → X) (D s : ℝ) (hf : HasDistortion k f D s) :
    (k:ℝ) ≤ C^2*D*(D-1) := by
  obtain ⟨hD,_,h⟩ := normalized_distortion f hf
  have hD0 : 0 < D := by linarith
  have hP : 0 < C^2*D := mul_pos (sq_pos_of_pos hC) hD0
  let δ : ℝ := 1/(C^2*D)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hstep : ∀ (x : X) (z : ℕ → X) (R : ℝ),0 ≤ R → R ≤ D → 1 ≤ ‖x‖ →
      (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
      (∀ i j,i ≠ j → 2*1 ≤ ‖z i-z j‖) → ‖x‖ ≤ R-δ := by
    intro x z R hR hRD hx hp hm hsep
    have he := hX x z R 2 hR (by norm_num) hp hm (by simpa using hsep)
    have hxr := norm_center_le (hp 0) (hm 0)
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRD (sq_nonneg C)) (sub_nonneg.mpr hxr)
    have hh : 1 ≤ C^2*D*(R-‖x‖) := by norm_num at he; exact he.trans hmul
    have hh' : δ ≤ R-‖x‖ := (div_le_iff₀ hP).mpr (by nlinarith only [hh])
    linarith
  have hi := iterate_additive hδ hstep k (fun v => s⁻¹ • f v) hD0.le le_rfl
    (fun u v => by simpa using (h u v).1)
    (fun e => slope_upper _ (fun u v => by simpa using (h u v).2) e)
  have hquot : (k:ℝ)/(C^2*D) ≤ D-1 := by
    dsimp [δ] at hi
    rw [mul_one_div] at hi
    linarith
  have hmul := (div_le_iff₀ hP).mp hquot
  nlinarith only [hmul]

def UnitLensBound (X : Type*) [NormedAddCommGroup X] (ε ρ : ℝ) : Prop :=
  ∀ (x : X) (z : ℕ → X), (∀ i,‖x+z i‖ ≤ 1) → (∀ i,‖x-z i‖ ≤ 1) →
    (∀ i j,i ≠ j → ε ≤ ‖z i-z j‖) → ‖x‖ ≤ ρ

theorem backward {α ρ : ℝ} (hα : 0 < α) (_hα1 : α ≤ 1) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hX : UnitLensBound X (2*α) ρ) (k : ℕ) (f : Vertex k → X)
    (hl : ∀ u v,α*distance k u v ≤ ‖f u-f v‖)
    (hu : ∀ u v,‖f u-f v‖ ≤ distance k u v) : α ≤ ρ^k := by
  have hstep : ∀ (x : X) (z : ℕ → X) (R : ℝ),0 ≤ R → R ≤ 1 → α ≤ ‖x‖ →
      (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
      (∀ i j,i ≠ j → 2*α ≤ ‖z i-z j‖) → ‖x‖ ≤ ρ*R := by
    intro x z R hR hR1 hx hp hm hs
    have hxr := norm_center_le (hp 0) (hm 0)
    have hR0 : 0 < R := lt_of_lt_of_le hα (hx.trans hxr)
    have hscale (u : X) : ‖R⁻¹ • u‖=R⁻¹*‖u‖ := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR)]
    have hi : R⁻¹*R=1 := inv_mul_cancel₀ hR0.ne'
    have hinv : 1 ≤ R⁻¹ := by
      rw [← one_div]
      exact (le_div_iff₀ hR0).mpr (by simpa using hR1)
    have hb := hX (R⁻¹ • x) (fun i => R⁻¹ • z i)
      (fun i => by
        rw [← smul_add,hscale]
        exact (mul_le_mul_of_nonneg_left (hp i) (inv_nonneg.mpr hR)).trans hi.le)
      (fun i => by
        rw [← smul_sub,hscale]
        exact (mul_le_mul_of_nonneg_left (hm i) (inv_nonneg.mpr hR)).trans hi.le)
      (fun i j hij => by
        rw [← smul_sub,hscale]
        exact (le_mul_of_one_le_left (by positivity : 0 ≤ 2*α) hinv).trans
          (mul_le_mul_of_nonneg_left (hs i j hij) (inv_nonneg.mpr hR)))
    rw [hscale] at hb
    have hh := mul_le_mul_of_nonneg_left hb hR
    rw [← mul_assoc,mul_inv_cancel₀ hR0.ne',one_mul] at hh
    simpa only [mul_comm] using hh
  have h := iterate_contraction hρ hρ1.le hstep k f (by norm_num : (0:ℝ) ≤ 1) le_rfl hl
    (fun e => slope_upper f (fun u v => by simpa using hu u v) e)
  simpa only [mul_one] using h

end Diamond

end DiamondDistortion

end

end OAI
