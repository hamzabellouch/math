import OAI.Analysis.DiamondDistortion.WeakLenses

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace PathApplications
open Midpoint
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The positive-flow and trimming inputs, with their distinct coefficient B. -/
def FlowInput (A : Heads ι X) (B : ℝ) : Prop :=
  ∀ (H : ι) (p y : X),A.projection H p=p → A.projection H y=0 →
    ‖y‖^2 ≤ B*(‖p+y‖^2+‖p-y‖^2-2*‖p‖^2)

lemma flow_square (A : Heads ι X) {B : ℝ} (hB : 0 < B) (hinput : FlowInput A B) :
    A.SquareInput (1/(2*B)) := by
  intro H p y R hP hY hR hp hm
  have hh := hinput H p y hP hY
  have hp2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hp
  have hm2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hm
  have hmul := mul_le_mul_of_nonneg_left (show ‖p+y‖^2+‖p-y‖^2-2*‖p‖^2 ≤
    2*(R^2-‖p‖^2) by linarith) hB.le
  have hmain : ‖y‖^2/(2*B) ≤ R^2-‖p‖^2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one,one_mul] using (show ‖p‖^2+‖y‖^2/(2*B) ≤ R^2 by linarith)

lemma square_depth (A : Heads ι X) {a : ℝ} (ha : 0 < a) (hinput : A.SquareInput a)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    1+a*(k:ℝ) ≤ D^2 := by
  have h := Diamond.squared_transfer (show 0 < a/4 by positivity) (A.square_lens ha hinput) k f D s hf
  convert h using 1; ring

def linearC : ℝ := 6*(Real.sqrt 2+1)
lemma linearC_pos : 0 < linearC := by unfold linearC; positivity

theorem linear_flow (A : Heads ι X) (hinput : FlowInput A (linearC^2))
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/(2*linearC^2) ≤ D^2 ∧ (k:ℝ) ≤ 2*linearC^2*D^2 := by
  have hC := linearC_pos
  have h := square_depth A (show 0 < 1/(2*linearC^2) by positivity)
    (flow_square A (show 0 < linearC^2 by positivity) hinput) k f hf
  have hh : 1+(k:ℝ)/(2*linearC^2) ≤ D^2 := by simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one,one_mul] using h
  refine ⟨hh,?_⟩
  have hdiv : (k:ℝ)/(2*linearC^2) ≤ D^2 := by linarith
  exact (div_le_iff₀ (by positivity)).mp hdiv |>.trans_eq (mul_comm _ _)

theorem linear_trimming (A : Heads ι X) (hinput : FlowInput A 242)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/484 ≤ D^2 := by
  have h := square_depth A (by norm_num : (0:ℝ) < 1/(2*242))
    (flow_square A (by norm_num) hinput) k f hf
  convert h using 1; ring

/-- Exact arbitrary-displacement cancellation input (unlike a pure-tail assertion). -/
def ArbitraryTailInput (A : Heads ι X) (C : ℝ) : Prop :=
  ∀ (H : ι) (p y : X) (R : ℝ),A.projection H p=p → 0 ≤ R →
    ‖p+y‖ ≤ R → ‖p-y‖ ≤ R → ‖y-A.projection H y‖ ≤ C*Real.sqrt (R^2-‖p‖^2)

lemma arbitrary_tail_square (A : Heads ι X) {C : ℝ} (hC : 0 < C)
    (hinput : ArbitraryTailInput A C) : A.SquareInput (1/C^2) := by
  intro H p y R hP hY hR hp hm
  have hh := hinput H p y R hP hR hp hm
  rw [hY,sub_zero] at hh
  have hc := Diamond.norm_center_le hp hm
  have hrad : 0 ≤ R^2-‖p‖^2 := sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) hR).mpr hc)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ C*Real.sqrt (R^2-‖p‖^2))).mpr hh
  rw [mul_pow,Real.sq_sqrt hrad] at hs
  have hd : ‖y‖^2/C^2 ≤ R^2-‖p‖^2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one,one_mul] using (show ‖p‖^2+‖y‖^2/C^2 ≤ R^2 by linarith)

theorem quadratic_cost (A : Heads ι X) (hinput : ArbitraryTailInput A 8)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/64 ≤ D^2 := by
  have h := square_depth A (by norm_num : (0:ℝ) < 1/8^2)
    (arbitrary_tail_square A (by norm_num) hinput) k f hf
  convert h using 1; ring

/-- The independent stopped-flow intrinsic input, with no change to its energy average. -/
def StoppedInput (A : Heads ι X) : Prop :=
  ∀ (H : ι) (p y : X),A.projection H p=p → A.projection H y=0 →
    ‖p‖^2+‖y‖^2/144 ≤ (‖p+y‖^2+‖p-y‖^2)/2

theorem stopped_flow (A : Heads ι X) (hinput : StoppedInput A)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    (k:ℝ) ≤ 144*D^2 := by
  have hi : A.SquareInput (1/144) := by
    intro H p y R hP hY hR hp hm
    have hh := hinput H p y hP hY
    have hp2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hp
    have hm2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hm
    linarith
  have hh := square_depth A (by norm_num) hi k f hf
  linarith

def StartInput (A : Heads ι X) : Prop :=
  ∀ (H : ι) (p y : X),A.projection H p=p → A.projection H y=0 →
    ‖p‖^2+‖y‖^2/64 ≤ max (‖p+y‖^2) (‖p-y‖^2)

lemma start_square (A : Heads ι X) (hinput : StartInput A) : A.SquareInput (1/64) := by
  intro H p y R hP hY hR hp hm
  have hh := (hinput H p y hP hY).trans (max_le
    ((sq_le_sq₀ (norm_nonneg _) hR).mpr hp) ((sq_le_sq₀ (norm_nonneg _) hR).mpr hm))
  linarith

theorem start_cost (A : Heads ι X) (hinput : StartInput A)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/128 ≤ D^2 := by
  have hh := square_depth A (by norm_num) (start_square A hinput) k f hf
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  linarith

def clippingC (D : ℝ) : ℝ := 1/(8*D)
def clippingQ (D : ℝ) : ℝ := Real.sqrt (1+4*(clippingC D)^2)
def clippingGamma (D : ℝ) : ℝ := clippingC D/2-(clippingQ D-1)*D

lemma clipping_bounds {D : ℝ} (hD : 1 ≤ D) :
    0 < clippingC D ∧ 1 ≤ clippingQ D ∧ clippingC D/4 ≤ clippingGamma D := by
  have hD0 : 0 < D := by linarith
  have hc : 0 < clippingC D := by unfold clippingC; positivity
  have hQ0 : 0 ≤ clippingQ D := by unfold clippingQ; positivity
  have hQsq : (clippingQ D)^2=1+4*(clippingC D)^2 := Real.sq_sqrt (by positivity)
  have hQ1 : 1 ≤ clippingQ D := by nlinarith
  have hQt : clippingQ D-1 ≤ 2*(clippingC D)^2 := by
    nlinarith [sq_nonneg (clippingQ D-1)]
  have hcD : clippingC D*D=1/8 := by unfold clippingC; field_simp
  have hmul := mul_le_mul_of_nonneg_right hQt hD0.le
  refine ⟨hc,hQ1,?_⟩
  unfold clippingGamma
  nlinarith

/-- Actual-child selection at the clipping half-gain. No infinite supremum is attained. -/
lemma clipping_actual_child (A : Heads ι X) (hinput : A.ParametricInput (1/2) 4)
    {D : ℝ} (hD : 1 ≤ D) {x : X} (z : ℕ → X) (hxD : ‖x‖ ≤ D)
    (hs : ∀ i j,i ≠ j → 2 ≤ ‖z i-z j‖) :
    ∃ i,‖x‖+clippingGamma D/(2*clippingQ D) < max ‖x+z i‖ ‖x-z i‖ := by
  obtain ⟨hc,hQ,hg⟩ := clipping_bounds hD
  have hQp : 0 < clippingQ D := by linarith
  have hgp : 0 < clippingGamma D := lt_of_lt_of_le (by positivity) hg
  by_contra! hn
  have hp := fun i => (le_max_left ‖x+z i‖ ‖x-z i‖).trans (hn i)
  have hm := fun i => (le_max_right ‖x+z i‖ ‖x-z i‖).trans (hn i)
  have hh := A.parametric_lens (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<4) hc hinput z hp hm hs
  have he : clippingQ D*(clippingGamma D/(2*clippingQ D))=clippingGamma D/2 := by field_simp
  change ‖x‖+1/2*clippingC D*(2/2) ≤ clippingQ D*(‖x‖+clippingGamma D/(2*clippingQ D)) at hh
  rw [mul_add,he] at hh
  have hm := mul_le_mul_of_nonneg_left hxD (show 0 ≤ clippingQ D-1 by linarith)
  unfold clippingGamma at *
  nlinarith

theorem linear_clipping (A : Heads ι X) (hinput : A.ParametricInput (1/2) 4)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)*clippingGamma D/(2*clippingQ D) ≤ D := by
  obtain ⟨hc,hQ,hg⟩ := clipping_bounds hf.1
  have hQp : 0 < clippingQ D := by linarith
  have hgp : 0 < clippingGamma D := lt_of_lt_of_le (by positivity) hg
  let δ := clippingGamma D/(2*clippingQ D)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hstep : ∀ (x : X) (z : ℕ → X) (R : ℝ),0 ≤ R → R ≤ D → 1 ≤ ‖x‖ →
      (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
      (∀ i j,i ≠ j → 2*1 ≤ ‖z i-z j‖) → ‖x‖ ≤ R-δ := by
    intro x z R hR hRD hx hp hm hs
    have hxD := (Diamond.norm_center_le (hp 0) (hm 0)).trans hRD
    obtain ⟨i,hi⟩ := clipping_actual_child A hinput hf.1 z hxD (by simpa using hs)
    have hh := hi.trans_le (max_le (hp i) (hm i))
    linarith
  obtain ⟨_,_,hnorm⟩ := Diamond.normalized_distortion f hf
  have hh := Diamond.iterate_additive hδ.le hstep k (fun v => s⁻¹ • f v)
    (show 0 ≤ D by linarith [hf.1]) le_rfl (fun u v => (hnorm u v).1)
    (fun e => Diamond.slope_upper _ (fun u v => by simpa using (hnorm u v).2) e)
  simpa only [δ,mul_div_assoc] using hh

lemma unit_from_square {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {b α ρ : ℝ} (hX : Diamond.SquareLens X b)
    (hα : 0 < α) (hρ : 0 ≤ ρ) (hgap : 1-b*(2*α)^2 ≤ ρ^2) :
    Diamond.UnitLensBound X (2*α) ρ := by
  intro x z hp hm hs
  have hh := hX x z 1 (2*α) (by norm_num) (by positivity) hp hm hs
  exact (sq_le_sq₀ (norm_nonneg _) hρ).mp (by nlinarith)

theorem tail_seven (A : Heads ι X) (hinput : ArbitraryTailInput A 7)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (1-(D⁻¹)^2/2000)^k := by
  have hD : 0 < D := by linarith [hf.1]
  have hα : 0 < D⁻¹ := inv_pos.mpr hD
  have hα1 : D⁻¹ ≤ 1 := (inv_le_one₀ hD).mpr hf.1
  have hα2 : (D⁻¹)^2 ≤ 1 := by nlinarith
  have hρ : 0 ≤ 1-(D⁻¹)^2/2000 := by linarith
  have hρ1 : 1-(D⁻¹)^2/2000 < 1 := by nlinarith [sq_pos_of_pos hα]
  have hsquare := A.square_lens (by norm_num : (0:ℝ)<1/7^2)
    (arbitrary_tail_square A (by norm_num) hinput)
  have hgap : 1-(1/(7:ℝ)^2/4)*(2*D⁻¹)^2 ≤ (1-(D⁻¹)^2/2000)^2 := by nlinarith [sq_nonneg ((D⁻¹)^2)]
  have hlens := unit_from_square hsquare hα hρ hgap
  have hnorm := Diamond.upper_one_normalization f hf
  exact Diamond.backward hα hα1 hρ hρ1 hlens k (fun v => (D*s)⁻¹ • f v)
    (fun u v => (hnorm u v).1) (fun u v => (hnorm u v).2)

/-- The pruning parameter is not optimized or silently replaced by the 7-bound. -/
theorem tail_pruning (A : Heads ι X) (hinput : ArbitraryTailInput A 9)
    {D s γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 1/2)
    (hparameter : 9*Real.sqrt ((1+γ)^2-(1-2*γ)^2) < 2*D⁻¹/3)
    (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (1-γ)^k := by
  have hD : 0 < D := by linarith [hf.1]
  have hα : 0 < D⁻¹ := inv_pos.mpr hD
  have hα1 : D⁻¹ ≤ 1 := (inv_le_one₀ hD).mpr hf.1
  have hrad : 0 ≤ (1+γ)^2-(1-2*γ)^2 := by nlinarith
  have hsq := (sq_lt_sq₀ (by positivity : 0 ≤ 9*Real.sqrt ((1+γ)^2-(1-2*γ)^2))
    (by positivity : 0 ≤ 2*D⁻¹/3)).mpr hparameter
  rw [mul_pow,Real.sq_sqrt hrad] at hsq
  have hgap : 1-(1/(9:ℝ)^2/4)*(2*D⁻¹)^2 ≤ (1-γ)^2 := by nlinarith
  have hsquare := A.square_lens (by norm_num : (0:ℝ)<1/9^2)
    (arbitrary_tail_square A (by norm_num) hinput)
  have hlens := unit_from_square hsquare hα (show 0 ≤ 1-γ by linarith) hgap
  have hnorm := Diamond.upper_one_normalization f hf
  exact Diamond.backward hα hα1 (by linarith) (by linarith) hlens k
    (fun v => (D*s)⁻¹ • f v) (fun u v => (hnorm u v).1) (fun u v => (hnorm u v).2)

def incomparableK : ℝ := Real.sqrt 2+Real.sqrt 6
lemma incomparableK_gt_one : 1 < incomparableK := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp := Real.sqrt_nonneg 2
  have h6 := Real.sqrt_nonneg 6
  unfold incomparableK
  nlinarith

theorem incomparable_segments (A : Heads ι X) (hinput : A.RadialInput incomparableK)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (1-(D⁻¹/incomparableK)^2)^k := by
  have hD : 0 < D := by linarith [hf.1]
  have hα : 0 < D⁻¹ := inv_pos.mpr hD
  have hα1 : D⁻¹ ≤ 1 := (inv_le_one₀ hD).mpr hf.1
  have hK : 0 < incomparableK := lt_trans (by norm_num) incomparableK_gt_one
  have ht : 0 < D⁻¹/incomparableK := by positivity
  have ht1 : D⁻¹/incomparableK < 1 := (div_lt_one hK).mpr (hα1.trans_lt incomparableK_gt_one)
  have hρ : 0 ≤ 1-(D⁻¹/incomparableK)^2 := by nlinarith
  have hlens : Diamond.UnitLensBound X (2*D⁻¹) (1-(D⁻¹/incomparableK)^2) := by
    intro x z hp hm hs
    have hh := A.radial_lens hK hinput x z 1 (2*D⁻¹) (by norm_num) (by positivity) hp hm hs
    have hdiv : (D⁻¹)^2/incomparableK^2 ≤ 1-‖x‖ := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    rw [div_pow]
    linarith
  have hnorm := Diamond.upper_one_normalization f hf
  exact Diamond.backward hα hα1 hρ (by nlinarith [sq_pos_of_pos ht]) hlens k
    (fun v => (D*s)⁻¹ • f v) (fun u v => (hnorm u v).1) (fun u v => (hnorm u v).2)

/-- Component-to-sum finite-codimensional input, exactly at arbitrary unit centers. -/
def ComponentSumInput (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (e : ℝ),0 < e → e ≤ 1/16 → ∀ u : X,‖u‖=1 →
  ∃ F : Submodule ℝ X,IsClosed (F : Set X) ∧ FiniteDimensional ℝ (X ⧸ F) ∧
    ∀ y : X,y ∈ F → max ‖u+y‖ ‖u-y‖ ≤ 1+e → ‖y‖ ≤ 17*(2*e)^((1:ℝ)/6)

theorem component_sum (hinput : ComponentSumInput X) {D s e : ℝ}
    (he : 0 < e) (he16 : e ≤ 1/16) (hsmall : 17*(2*e)^((1:ℝ)/6) < 1/(2*D))
    (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    (1+e/2)^k ≤ D := by
  have hD : 0 < D := by linarith [hf.1]
  have hg : QuotientGain X (1/(2*D)) e := by
    intro u hu
    obtain ⟨F,hF,hfin,h⟩ := hinput e he he16 u hu
    refine ⟨F,hF,hfin,?_⟩
    intro y hy hnorm
    by_contra! hn
    have hh := h y hy hn.le
    linarith
  exact Diamond.quotient_transfer (by positivity) he le_rfl hg k f hf

end PathApplications

end DiamondDistortion

end

end OAI
